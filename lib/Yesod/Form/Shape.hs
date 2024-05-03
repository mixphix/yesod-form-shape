{-# LANGUAGE DerivingVia #-}

module Yesod.Form.Shape
  ( Entry (Entry, enctype, view, parse)
  , type Attrs
  , numberEntry
  , maybeNumberEntry
  , textEntry
  , textareaEntry
  , boolEntry
  , Shape
  , ShapeS (OmitS, NeedS, ManyS, FreeS)
  , ShapeType (Omit, Need, Many, Free)
  , Shaped (shaped)
  , selectEntry
  , FormFor
  , Decorate (Decorate, decorate)
  , type FormEntry
  , pattern FormEntry
  , type FormExit
  , pattern FormExit
  , runEntry
  , form
  , generateFormPost
  , runFormPost
  , generateFormGet
  , runFormGet
  , identifyForm
  )
where

import Control.Arrow (Arrow (..))
import Control.Monad (guard)
import Control.Monad.RWS
  ( MonadReader (..)
  , MonadWriter (..)
  , RWST
  , asks
  , evalRWST
  )
import Data.Byteable (constEqBytes)
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.Functor.Compose (Compose (..))
import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..))
import Data.Functor.Invariant
import Data.Functor.Product
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty (..), nonEmpty, toList)
import Data.Map qualified as Map
import Data.Maybe
import Data.Semigroup (Endo (..))
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Network.HTTP.Types (Method, methodGet, methodPost)
import Network.Wai (Request (requestMethod))
import Text.Read (readMaybe)
import Yesod.Core
import Yesod.Form
  ( Enctype (UrlEncoded)
  , Env
  , FileEnv
  , FormMessage (..)
  , FormResult (..)
  , Ints (IntSingle)
  , Option (..)
  , OptionList (..)
  , Textarea (..)
  , newFormIdent
  )

type Attrs = [(Text, Text)]

-- |
-- A 'Entry' is what this library calls the abstraction
-- for handling data exchanges through Web forms.
data Entry app ty = Entry
  { enctype :: Enctype
  -- ^ 'UrlEncoded' or 'Multipart'
  , view :: Attrs -> Either Text ty -> WidgetFor app ()
  -- ^
  -- @'view' attrs value@ should return a single DOM element
  -- representing the form widget with attributes @attrs@ and initial value @value@.
  , parse :: [Text] -> [FileInfo] -> HandlerFor app (Either (SomeMessage app) ty)
  -- ^ @'parse' myEnv myFileEnv@ is only ever applied to the values from the DOM element's @name@ attribute.
  }

instance Invariant (Entry app) where
  invmap :: (ty -> tz) -> (tz -> ty) -> Entry app ty -> Entry app tz
  invmap source target entry =
    Entry
      { enctype = entry.enctype
      , view = \attrs value -> entry.view attrs (invmap target source value)
      , parse = \myEnv myFileEnv -> invmap source target <$> entry.parse myEnv myFileEnv
      }

parseWith ::
  (RenderMessage app FormMessage) =>
  ([Char] -> Maybe ty) ->
  [Text] ->
  Either (SomeMessage app) ty
parseWith f = \case
  [] -> Left (SomeMessage MsgValueRequired)
  [x] -> case f (Text.unpack x) of
    Nothing -> Left (SomeMessage $ MsgInvalidEntry x)
    Just fx -> Right fx
  xs -> Left (SomeMessage $ MsgInvalidEntry (Text.unlines xs))

parseWith_ ::
  (RenderMessage app FormMessage) =>
  ([Char] -> Maybe ty) ->
  [Text] ->
  Either (SomeMessage app) (Maybe ty)
parseWith_ f = \case
  [] -> Right Nothing
  [x] -> case f (Text.unpack x) of
    Nothing -> Left (SomeMessage $ MsgInvalidEntry x)
    Just fx -> Right (Just fx)
  xs -> Left (SomeMessage $ MsgInvalidEntry (Text.unlines xs))

numberEntry ::
  forall n app.
  (RenderMessage app FormMessage, Num n, Read n, Show n) =>
  Entry app n
numberEntry = do
  Entry
    { enctype = UrlEncoded
    , view = \((:) ("required", "required") -> attrs) value -> do
        [whamlet|<input type="number" *{attrs} value="#{either (const "") show value}">|]
    , parse = \myEnv _ -> pure (parseWith readMaybe myEnv)
    }

maybeNumberEntry ::
  forall n app.
  (RenderMessage app FormMessage, Num n, Read n, Show n) =>
  Entry app (Maybe n)
maybeNumberEntry = do
  Entry
    { enctype = UrlEncoded
    , view = \attrs value -> do
        [whamlet|<input type="number" *{attrs} value="#{either (const "") (maybe "" show) value}">|]
    , parse = \myEnv _ -> pure (parseWith_ readMaybe myEnv)
    }

textEntry :: (RenderMessage app FormMessage) => Entry app Text
textEntry = do
  Entry
    { enctype = UrlEncoded
    , view = \attrs value -> do
        [whamlet|<input type="text" *{attrs}>#{either (const "") id value}|]
    , parse = \myEnv _ -> pure case myEnv of
        [] -> Right ""
        [x] -> Right x
        xs -> Left (SomeMessage $ MsgInvalidEntry (Text.unlines xs))
    }

textareaEntry :: (RenderMessage app FormMessage) => Entry app Textarea
textareaEntry =
  Entry
    { enctype = UrlEncoded
    , view = \attrs value -> do
        [whamlet|<input type="textarea" *{attrs}>#{either (const $ Textarea "") id value}|]
    , parse = \myEnv _ -> pure case myEnv of
        [] -> Right (Textarea "")
        [x] -> Right (Textarea x)
        xs -> Left (SomeMessage $ MsgInvalidEntry (Text.unlines xs))
    }

boolEntry :: (RenderMessage app FormMessage) => Entry app Bool
boolEntry =
  Entry
    { enctype = UrlEncoded
    , view = \attrs value -> do
        [whamlet|<input type="checkbox" *{attrs} value="1" :value == Right True:checked>|]
    , parse = \myEnv _ -> pure case myEnv of
        [] -> Right False
        ["1"] -> Right True
        [_] -> Right False
        xs -> Left (SomeMessage $ MsgInvalidEntry (Text.unlines xs))
    }

type FormFor app =
  RWST
    (Maybe (Env, FileEnv), app, [Lang])
    Enctype
    Ints
    (HandlerFor app)

newtype Decorate app = Decorate {decorate :: WidgetFor app () -> WidgetFor app ()}
  deriving (Semigroup, Monoid) via Endo (WidgetFor app ())

type FormEntry app =
  Product (Entry app) (Product (Const (Attrs, Decorate app)) Identity)

-- |
-- @'FormEntry' entry attrs value decor@ specifies how to interpret a value of @ty@ through a 'Entry'.
pattern FormEntry ::
  Entry app ty ->
  [(Text, Text)] ->
  ty ->
  (WidgetFor app () -> WidgetFor app ()) ->
  FormEntry app ty
pattern FormEntry entry attrs value decor =
  Pair entry (Pair (Const (attrs, Decorate decor)) (Identity value))

{-# COMPLETE FormEntry #-}

type FormExit app = Product FormResult (Const (WidgetFor app ()))

-- |
-- A @'FormExit' result widget@ is what you get back from a @'FormEntry' entry attrs value decor@,
-- after you've done some stuff in the @'FormFor' app@ monad.
pattern FormExit :: FormResult ty -> WidgetFor app () -> FormExit app ty
pattern FormExit result widget = Pair result (Const widget)

{-# COMPLETE FormExit #-}

runEntry ::
  (RenderMessage app FormMessage) =>
  FormEntry app ty ->
  FormFor app (FormExit app ty)
runEntry (FormEntry entry attrs0 value decorate) = do
  tell entry.enctype
  (envs, app, langs) <- ask
  (name, attrs) <- case lookup "name" attrs0 of
    Just name -> pure (name, attrs0)
    Nothing -> do
      name <- newFormIdent
      pure (name, ("name", name) : attrs0)
  (result, widget) <-
    fmap (entry.view attrs) <$> case envs of
      Nothing -> pure (FormMissing, Right value)
      Just (env, fileEnv) -> do
        let myEnv = Map.findWithDefault [] name env
            myFileEnv = Map.findWithDefault [] name fileEnv
        lift (entry.parse myEnv myFileEnv) <&> \case
          Right x -> (FormSuccess x, Right x)
          Left (SomeMessage msg) ->
            ( FormFailure [renderMessage app langs msg]
            , Left $ Text.intercalate ", " myEnv
            )
  pure $ FormExit result (decorate widget)

-- | The transformation representing the exchange from 'FormEntry' to 'FormExit'.
form ::
  (RenderMessage app FormMessage) =>
  FormEntry app ty ->
  Compose (FormFor app) (FormExit app) ty
form = Compose . runEntry

data ShapeType
  = Omit
  | Need
  | Many
  | Free

type ShapeS :: ShapeType -> Type
data ShapeS shape where
  OmitS :: ShapeS Omit
  NeedS :: ShapeS Need
  ManyS :: ShapeS Many
  FreeS :: ShapeS Free

-- | > class Shaped shape where shape :: ShapeS shape
class Shaped shape where shaped :: ShapeS shape

instance Shaped Omit where shaped = OmitS
instance Shaped Need where shaped = NeedS
instance Shaped Many where shaped = ManyS
instance Shaped Free where shaped = FreeS

-- |
-- @
-- type family Shape shape = ty | ty -> shape where
--   Shape Omit = Maybe
--   Shape Need = Identity
--   Shape Many = NonEmpty
--   Shape Free = []
-- @
type Shape :: ShapeType -> Type -> Type
type family Shape shape = ty | ty -> shape where
  Shape Omit = Maybe
  Shape Need = Identity
  Shape Many = NonEmpty
  Shape Free = []

shapeAttrs ::
  forall shape.
  (Shaped shape) =>
  Const [(Text, Text)] (ShapeS shape)
shapeAttrs = case shaped @shape of
  OmitS -> Const []
  NeedS -> Const [("required", "required")]
  ManyS -> Const [("required", "required"), ("multiple", "multiple")]
  FreeS -> Const [("multiple", "multiple")]

-- |
-- The 'Entry' for a @<select>@ element with options from the supplied 'OptionList'
-- and a @shape@ parameter to handle the selection quantity.
selectEntry ::
  forall shape ty app.
  (RenderMessage app FormMessage, Eq ty, Shaped shape) =>
  OptionList ty ->
  Entry app (Shape shape ty)
selectEntry ol =
  Entry
    { enctype = UrlEncoded
    , view = \attrs value -> do
        let Const s = shapeAttrs @shape
            selected :: ty -> Bool = case value of
              Left _ -> const False
              Right val -> case shaped @shape of
                OmitS -> maybe (const False) (==) val
                NeedS -> (== runIdentity val)
                ManyS -> flip elem (toList val)
                FreeS -> flip elem val
        [whamlet|
          <select *{s <> attrs}>
            $case ol
              $of OptionList{olOptions}
                $forall o <- olOptions
                  <option :selected o.optionInternalValue:selected value="#{o.optionExternalValue}">
                    #{o.optionDisplay}
              $of OptionListGrouped{olOptionsGrouped}
                $forall (group, ol) <- olOptionsGrouped
                  <optgroup label="#{group}">
                    $forall o <- ol
                      <option :selected o.optionInternalValue:selected value="#{o.optionExternalValue}">
                        #{o.optionDisplay}
        |]
    , parse = \myEnv _ -> do
        let olReadMaybe = case ol of
              OptionList{..} -> olReadExternal
              OptionListGrouped{..} -> olReadExternalGrouped
            olRead :: Text -> Either (SomeMessage app) ty
            olRead x = case olReadMaybe x of
              Nothing -> Left (SomeMessage (MsgInvalidEntry x))
              Just y -> Right y
        case shaped @shape of
          OmitS -> pure case myEnv of
            [] -> Right Nothing
            [x] -> Just <$> olRead x
            _ -> Left (SomeMessage $ MsgInvalidEntry "Duplicated")
          NeedS -> pure case myEnv of
            [] -> Left (SomeMessage MsgValueRequired)
            [x] -> Identity <$> olRead x
            _ -> Left (SomeMessage $ MsgInvalidEntry "Duplicated")
          ManyS -> pure case nonEmpty myEnv of
            Nothing -> Left (SomeMessage MsgValueRequired)
            Just xs -> traverse olRead xs
          FreeS -> pure $ traverse olRead myEnv
    }

runFormPostWithEnv ::
  (RenderMessage app FormMessage) =>
  (Html -> FormFor app (FormExit app ty)) ->
  Maybe (Env, FileEnv) ->
  HandlerFor app (FormExit app ty, Enctype)
runFormPostWithEnv mk envs = do
  YesodRequest{reqToken} <- getRequest
  app <- getYesod
  langs <- languages
  let postKey = defaultCsrfParamName
      (withKey, invalidPostKey) = case reqToken of
        Nothing -> (mempty, \env -> isJust (env Map.!? postKey))
        Just token ->
          ( [shamlet|<input type="hidden" name="#{postKey}" value="#{token}">|]
          , \env -> case env Map.!? postKey of
              Just [tokenR] ->
                -- The use of 'constEqBytes' prevents timing attacks.
                not $ Text.encodeUtf8 tokenR `constEqBytes` Text.encodeUtf8 token
              _ -> True
          )
      validatePostKey (FormExit result widget) = case (result, envs) of
        (FormSuccess{}, Just (env, _))
          | invalidPostKey env ->
              FormExit (FormFailure [renderMessage app langs MsgCsrfWarning]) widget
        (_, Nothing) -> FormExit FormMissing widget
        _ -> FormExit result widget
  first validatePostKey <$> evalRWST (mk withKey) (envs, app, langs) (IntSingle 0)

generateFormPost ::
  (RenderMessage app FormMessage) =>
  (Html -> FormFor app (FormExit app ty)) ->
  HandlerFor app (WidgetFor app (), Enctype)
generateFormPost mk = runFormPostWithEnv mk Nothing <&> first \(FormExit _ w) -> w

methodEnv :: Method -> HandlerFor app (Maybe (Env, FileEnv))
methodEnv method = do
  let monoid = flip foldr Map.empty \(k, v) -> Map.insertWith (<>) k [v]
  YesodRequest{reqGetParams, reqWaiRequest} <- getRequest
  traverse (\() -> (monoid *** monoid) <$> runRequestBody) do
    guard (requestMethod reqWaiRequest == method)
    guard (method /= methodGet || isJust (lookup getKey reqGetParams))

runFormPost ::
  (RenderMessage app FormMessage) =>
  (Html -> FormFor app (FormExit app ty)) ->
  HandlerFor app (FormExit app ty, Enctype)
runFormPost mk = runFormPostWithEnv mk =<< methodEnv methodPost

getKey :: Text
getKey = "_hasdata"

runFormGetWithEnv ::
  (RenderMessage app FormMessage) =>
  (Html -> FormFor app (FormExit app ty)) ->
  Maybe (Env, FileEnv) ->
  HandlerFor app (FormExit app ty, Enctype)
runFormGetWithEnv mk envs = do
  app <- getYesod
  langs <- languages
  evalRWST
    (mk [shamlet|<input type="hidden" name="#{getKey}">|])
    (envs, app, langs)
    (IntSingle 0)

generateFormGet ::
  (RenderMessage app FormMessage) =>
  (Html -> FormFor app (FormExit app ty)) ->
  HandlerFor app (WidgetFor app (), Enctype)
generateFormGet mk = runFormGetWithEnv mk Nothing <&> first \(FormExit _ w) -> w

runFormGet ::
  (RenderMessage app FormMessage) =>
  (Html -> FormFor app (FormExit app ty)) ->
  HandlerFor app (FormExit app ty, Enctype)
runFormGet mk = runFormGetWithEnv mk =<< methodEnv methodGet

identifyForm :: Text -> (Html -> FormFor app ty) -> (Html -> FormFor app ty)
identifyForm me mk withKey = do
  let i = "_identifier" :: Text
      amHere = elem me . Map.findWithDefault [] i
      withKey' = withKey <> [shamlet|<input type="hidden" name="#{i}" value="#{me}">|]
  (mk withKey' &) =<< asks \case
    (Just (env, _), _, _) | not (amHere env) -> local \(_, app, langs) -> (Nothing, app, langs)
    _ -> id
