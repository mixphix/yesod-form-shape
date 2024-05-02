module Yesod.Form.Shape
  ( Portal (..)
  , numberPortal
  , maybeNumberPortal
  , textPortal
  , textareaPortal
  , boolPortal
  , Shaped
  , Shape (..)
  , ShapeType (..)
  , selectPortal
  , FormFor
  , pattern FormInput
  , pattern FormOutput
  , runInput
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
import Data.Functor.Compose
import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..))
import Data.Functor.Invariant
import Data.Functor.Product
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty (..), nonEmpty, toList)
import Data.Map qualified as Map
import Data.Maybe
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

-- |
-- A 'Portal' is what this library calls the abstraction
-- for handling data exchanges through Web forms.
data Portal app ty = Portal
  { enctype :: Enctype
  -- ^ 'UrlEncoded' or 'Multipart'
  , view :: [(Text, Text)] -> Either Text ty -> WidgetFor app ()
  -- ^
  -- @'view' attrs initial@ should return a single DOM element
  -- representing the form widget with attributes @attrs@ and initial value @initial@.
  , parse :: [Text] -> [FileInfo] -> HandlerFor app (Either (SomeMessage app) ty)
  -- ^ @'parse' myEnv myFileEnv@ is only ever applied to the values from the DOM element's @name@ attribute.
  }

instance Invariant (Portal app) where
  invmap :: (ty -> tz) -> (tz -> ty) -> Portal app ty -> Portal app tz
  invmap source target p =
    Portal
      { enctype = p.enctype
      , view = \attrs initial -> p.view attrs (invmap target source initial)
      , parse = \myEnv myFileEnv -> invmap source target <$> p.parse myEnv myFileEnv
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

numberPortal ::
  forall n app.
  (RenderMessage app FormMessage, Num n, Read n, Show n) =>
  Portal app n
numberPortal = do
  Portal
    { enctype = UrlEncoded
    , view = \((:) ("required", "required") -> attrs) initial -> do
        [whamlet|<input type="number" *{attrs} value="#{either (const "") show initial}">|]
    , parse = \myEnv _ -> pure (parseWith readMaybe myEnv)
    }

maybeNumberPortal ::
  forall n app.
  (RenderMessage app FormMessage, Num n, Read n, Show n) =>
  Portal app (Maybe n)
maybeNumberPortal = do
  Portal
    { enctype = UrlEncoded
    , view = \attrs initial -> do
        [whamlet|<input type="number" *{attrs} value="#{either (const "") (maybe "" show) initial}">|]
    , parse = \myEnv _ -> pure (parseWith_ readMaybe myEnv)
    }

textPortal :: (RenderMessage app FormMessage) => Portal app Text
textPortal = do
  Portal
    { enctype = UrlEncoded
    , view = \attrs initial -> do
        [whamlet|<input type="text" *{attrs}>#{either (const "") id initial}|]
    , parse = \myEnv _ -> pure case myEnv of
        [] -> Right ""
        [x] -> Right x
        xs -> Left (SomeMessage $ MsgInvalidEntry (Text.unlines xs))
    }

textareaPortal :: (RenderMessage app FormMessage) => Portal app Textarea
textareaPortal =
  Portal
    { enctype = UrlEncoded
    , view = \attrs initial -> do
        [whamlet|<input type="textarea" *{attrs}>#{either (const $ Textarea "") id initial}|]
    , parse = \myEnv _ -> pure case myEnv of
        [] -> Right (Textarea "")
        [x] -> Right (Textarea x)
        xs -> Left (SomeMessage $ MsgInvalidEntry (Text.unlines xs))
    }

boolPortal :: (RenderMessage app FormMessage) => Portal app Bool
boolPortal =
  Portal
    { enctype = UrlEncoded
    , view = \attrs initial -> do
        [whamlet|<input type="checkbox" *{attrs} value="1" :initial == Right True:checked>|]
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

type FormInput app =
  Compose
    (Product Identity (Const (WidgetFor app () -> WidgetFor app ())))
    ( Compose
        (Product Identity (Const [(Text, Text)]))
        (Product Identity (Portal app))
    )

-- |
-- @'FormInput' portal attrs initial wrap@ specifies how to interpret a value of @ty@ through a 'Portal'.
pattern FormInput ::
  Portal app ty ->
  [(Text, Text)] ->
  ty ->
  (WidgetFor app () -> WidgetFor app ()) ->
  FormInput app ty
pattern FormInput portal attrs initial wrap =
  Compose
    ( Pair
        ( Identity
            ( Compose
                ( Pair
                    (Identity (Pair (Identity initial) portal))
                    (Const attrs)
                  )
              )
          )
        (Const wrap)
      )

{-# COMPLETE FormInput #-}

type FormOutput app = Product FormResult (Const (WidgetFor app ()))

-- |
-- A @'FormOutput' result widget@ is what you get back from a @'FormInput' portal attrs initial wrap@,
-- after you've done some stuff in the @'FormFor' app@ monad.
pattern FormOutput :: FormResult ty -> WidgetFor app () -> FormOutput app ty
pattern FormOutput result widget = Pair result (Const widget)

{-# COMPLETE FormOutput #-}

runInput ::
  (RenderMessage app FormMessage) =>
  FormInput app ty ->
  FormFor app (FormOutput app ty)
runInput (FormInput p attrs0 initial wrap) = do
  tell p.enctype
  (envs, app, langs) <- ask
  (name, attrs) <- case lookup "name" attrs0 of
    Just name -> pure (name, attrs0)
    Nothing -> do
      name <- newFormIdent
      pure (name, ("name", name) : attrs0)
  (result, widget) <-
    fmap (p.view attrs) <$> case envs of
      Nothing -> pure (FormMissing, Right initial)
      Just (env, fileEnv) -> do
        let myEnv = Map.findWithDefault [] name env
            myFileEnv = Map.findWithDefault [] name fileEnv
        lift (p.parse myEnv myFileEnv) <&> \case
          Right x -> (FormSuccess x, Right x)
          Left (SomeMessage msg) ->
            ( FormFailure [renderMessage app langs msg]
            , Left $ Text.intercalate ", " myEnv
            )
  pure $ FormOutput result (wrap widget)

-- | The transformation representing the exchange from 'FormInput' to 'FormOutput'.
form ::
  (RenderMessage app FormMessage) =>
  FormInput app ty ->
  Compose (FormFor app) (FormOutput app) ty
form = Compose . runInput

data ShapeType
  = Omit
  | Need
  | Many
  | Free

type Shape :: ShapeType -> Type
data Shape shape where
  OmitS :: Shape Omit
  NeedS :: Shape Need
  ManyS :: Shape Many
  FreeS :: Shape Free

-- | > class SelectShape shape where shape :: Shape shape
class SelectShape shape where shaped :: Shape shape

instance SelectShape Omit where shaped = OmitS
instance SelectShape Need where shaped = NeedS
instance SelectShape Many where shaped = ManyS
instance SelectShape Free where shaped = FreeS

-- |
-- @
-- type family Shaped shape = ty | ty -> shape where
--   Shaped Omit = Maybe
--   Shaped Need = Identity
--   Shaped Many = NonEmpty
--   Shaped Free = []
-- @
type Shaped :: ShapeType -> Type -> Type
type family Shaped shape = ty | ty -> shape where
  Shaped Omit = Maybe
  Shaped Need = Identity
  Shaped Many = NonEmpty
  Shaped Free = []

shapeAttrs ::
  forall shape.
  (SelectShape shape) =>
  Const [(Text, Text)] (Shape shape)
shapeAttrs = case shaped @shape of
  OmitS -> Const []
  NeedS -> Const [("required", "required")]
  ManyS -> Const [("required", "required"), ("multiple", "multiple")]
  FreeS -> Const [("multiple", "multiple")]

-- |
-- The 'Portal' for a @<select>@ element with options from the supplied 'OptionList'
-- and a @shape@ parameter to handle the selection quantity.
selectPortal ::
  forall shape ty app.
  (RenderMessage app FormMessage, Eq ty, SelectShape shape) =>
  OptionList ty ->
  Portal app (Shaped shape ty)
selectPortal ol =
  Portal
    { enctype = UrlEncoded
    , view = \attrs initial -> do
        let Const s = shapeAttrs @shape
            selected :: ty -> Bool = case initial of
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
  (Html -> FormFor app (FormOutput app ty)) ->
  Maybe (Env, FileEnv) ->
  HandlerFor app (FormOutput app ty, Enctype)
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
      validatePostKey (FormOutput result widget) = case (result, envs) of
        (FormSuccess{}, Just (env, _))
          | invalidPostKey env ->
              FormOutput (FormFailure [renderMessage app langs MsgCsrfWarning]) widget
        (_, Nothing) -> FormOutput FormMissing widget
        _ -> FormOutput result widget
  first validatePostKey <$> evalRWST (mk withKey) (envs, app, langs) (IntSingle 0)

generateFormPost ::
  (RenderMessage app FormMessage) =>
  (Html -> FormFor app (FormOutput app ty)) ->
  HandlerFor app (WidgetFor app (), Enctype)
generateFormPost mk = runFormPostWithEnv mk Nothing <&> first \(FormOutput _ w) -> w

methodEnv :: Method -> HandlerFor app (Maybe (Env, FileEnv))
methodEnv method = do
  let monoid = flip foldr Map.empty \(k, v) -> Map.insertWith (<>) k [v]
  YesodRequest{reqGetParams, reqWaiRequest} <- getRequest
  traverse (\() -> (monoid *** monoid) <$> runRequestBody) do
    guard (requestMethod reqWaiRequest == method)
    guard (method /= methodGet || isJust (lookup getKey reqGetParams))

runFormPost ::
  (RenderMessage app FormMessage) =>
  (Html -> FormFor app (FormOutput app ty)) ->
  HandlerFor app (FormOutput app ty, Enctype)
runFormPost mk = runFormPostWithEnv mk =<< methodEnv methodPost

getKey :: Text
getKey = "_hasdata"

runFormGetWithEnv ::
  (RenderMessage app FormMessage) =>
  (Html -> FormFor app (FormOutput app ty)) ->
  Maybe (Env, FileEnv) ->
  HandlerFor app (FormOutput app ty, Enctype)
runFormGetWithEnv mk envs = do
  app <- getYesod
  langs <- languages
  evalRWST
    (mk [shamlet|<input type="hidden" name="#{getKey}">|])
    (envs, app, langs)
    (IntSingle 0)

generateFormGet ::
  (RenderMessage app FormMessage) =>
  (Html -> FormFor app (FormOutput app ty)) ->
  HandlerFor app (WidgetFor app (), Enctype)
generateFormGet mk = runFormGetWithEnv mk Nothing <&> first \(FormOutput _ w) -> w

runFormGet ::
  (RenderMessage app FormMessage) =>
  (Html -> FormFor app (FormOutput app ty)) ->
  HandlerFor app (FormOutput app ty, Enctype)
runFormGet mk = runFormGetWithEnv mk =<< methodEnv methodGet

identifyForm :: Text -> (Html -> FormFor app ty) -> (Html -> FormFor app ty)
identifyForm me mk withKey = do
  let i = "_identifier" :: Text
      amHere = elem me . Map.findWithDefault [] i
      withKey' = withKey <> [shamlet|<input type="hidden" name="#{i}" value="#{me}">|]
  (mk withKey' &) =<< asks \case
    (Just (env, _), _, _) | not (amHere env) -> local \(_, app, langs) -> (Nothing, app, langs)
    _ -> id
