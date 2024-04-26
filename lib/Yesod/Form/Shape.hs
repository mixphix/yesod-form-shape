module Yesod.FormFor.Shape
  ( Field (..)
  , numberField
  , maybeNumberField
  , textField
  , textareaField
  , boolField
  , FormFor
  , Form
  , input
  , Shaped
  , Shape (..)
  , ShapeType (..)
  , select
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
import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..))
import Data.Functor.Invariant
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
-- @
-- data Field app shape ty = Field
--   { enctype :: Enctype
--   , view ::
--       [(Text, Text)] ->
--       Either Text ty ->
--       WidgetFor app ()
--   , parse ::
--       [Text] ->
--       [FileInfo] ->
--       HandlerFor app (Either (SomeMessage app) ty)
--   }
-- @
data Field app ty = Field
  { enctype :: Enctype
  , view :: [(Text, Text)] -> Either Text ty -> WidgetFor app ()
  , parse :: [Text] -> [FileInfo] -> HandlerFor app (Either (SomeMessage app) ty)
  }

instance Invariant (Field app) where
  invmap ::
    (ty -> tz) -> (tz -> ty) -> Field app ty -> Field app tz
  invmap source target field =
    field
      { view = \attrs evalue -> field.view attrs (invmap target source evalue)
      , parse = \myEnv myFileEnv -> field.parse myEnv myFileEnv <&> invmap source target
      }

parseWith ::
  (RenderMessage app FormMessage) =>
  ([Char] -> Maybe ty) ->
  [Text] ->
  HandlerFor app (Either (SomeMessage app) ty)
parseWith f =
  pure . \case
    [] -> Left (SomeMessage MsgValueRequired)
    [x] -> case f (Text.unpack x) of
      Nothing -> Left (SomeMessage $ MsgInvalidEntry x)
      Just fx -> Right fx
    xs -> Left (SomeMessage $ MsgInvalidEntry (Text.unlines xs))

parseWith_ ::
  (RenderMessage app FormMessage) =>
  ([Char] -> Maybe ty) ->
  [Text] ->
  HandlerFor app (Either (SomeMessage app) (Maybe ty))
parseWith_ f =
  pure . \case
    [] -> Right Nothing
    [x] -> case f (Text.unpack x) of
      Nothing -> Left (SomeMessage $ MsgInvalidEntry x)
      Just fx -> Right (Just fx)
    xs -> Left (SomeMessage $ MsgInvalidEntry (Text.unlines xs))

numberField ::
  forall n app.
  (RenderMessage app FormMessage, Num n, Read n, Show n) =>
  Field app n
numberField = do
  Field
    { enctype = UrlEncoded
    , view = \attrs evalue -> do
        [whamlet|<input type="number" *{attrs} value="#{either (const "") show evalue}">|]
    , parse = \myEnv _ -> parseWith readMaybe myEnv
    }

maybeNumberField ::
  forall n app.
  (RenderMessage app FormMessage, Num n, Read n, Show n) =>
  Field app (Maybe n)
maybeNumberField = do
  Field
    { enctype = UrlEncoded
    , view = \attrs evalue -> do
        [whamlet|<input type="number" *{attrs} value="#{either (const "") (maybe "" show) evalue}">|]
    , parse = \myEnv _ -> parseWith_ readMaybe myEnv
    }

textField :: (RenderMessage app FormMessage) => Field app Text
textField = do
  Field
    { enctype = UrlEncoded
    , view = \attrs evalue -> do
        [whamlet|<input type="text" *{attrs}>#{either (const "") id evalue}|]
    , parse = \myEnv _ -> pure case myEnv of
        [] -> Right ""
        [x] -> Right x
        xs -> Left (SomeMessage $ MsgInvalidEntry (Text.unlines xs))
    }

textareaField :: (RenderMessage app FormMessage) => Field app Textarea
textareaField =
  Field
    { enctype = UrlEncoded
    , view = \attrs evalue -> do
        [whamlet|<input type="textarea" *{attrs}>#{either (const $ Textarea "") id evalue}|]
    , parse = \myEnv _ -> pure case myEnv of
        [] -> Right (Textarea "")
        [x] -> Right (Textarea x)
        xs -> Left (SomeMessage $ MsgInvalidEntry (Text.unlines xs))
    }

boolField :: (RenderMessage app FormMessage) => Field app Bool
boolField =
  Field
    { enctype = UrlEncoded
    , view = \attrs evalue -> do
        [whamlet|<input type="checkbox" *{attrs} value="1" :Right True == evalue:checked>|]
    , parse = \myEnv _ -> pure case myEnv of
        [] -> Right False
        ["1"] -> Right True
        [_] -> Right False
        xs -> Left (SomeMessage $ MsgInvalidEntry (Text.unlines xs))
    }

-- |
-- @
-- type FormFor app =
--   RWST
--     (Maybe (Env, FileEnv), app, [Lang])
--     Enctype
--     Ints
--     (HandlerFor app)
-- @
type FormFor app =
  RWST
    (Maybe (Env, FileEnv), app, [Lang])
    Enctype
    Ints
    (HandlerFor app)

type Form app ty = FormFor app (FormResult ty, WidgetFor app ())

requireName :: Text -> [(Text, Text)] -> [(Text, Text)]
requireName name attrs = case lookup "name" attrs of
  Nothing -> ("name", name) : attrs
  _ -> attrs

input ::
  (RenderMessage app FormMessage) =>
  (Field app ty -> [(Text, Text)] -> ty -> Form app ty)
input field attributes initial = do
  tell field.enctype
  (envs, app, langs) <- ask
  name <- maybe newFormIdent pure (lookup "name" attributes)
  second (field.view $ requireName name attributes) <$> case envs of
    Nothing -> pure (FormMissing, Right initial)
    Just (env, fileEnv) -> do
      let myEnv = Map.findWithDefault [] name env
          myFiles = Map.findWithDefault [] name fileEnv
      lift (field.parse myEnv myFiles) <&> \case
        Right x -> (FormSuccess x, Right x)
        Left (SomeMessage msg) ->
          ( FormFailure [renderMessage app langs msg]
          , Left (Text.intercalate ", " myEnv)
          )

data ShapeType
  = Omit
  | Need
  | Many
  | Free
instance Show (Shape shape) where
  show = \case
    OmitS -> "Omit"
    NeedS -> "Need"
    ManyS -> "Many"
    FreeS -> "Free"

type Shape :: ShapeType -> Type
data Shape shape where
  OmitS :: Shape Omit
  NeedS :: Shape Need
  ManyS :: Shape Many
  FreeS :: Shape Free

-- | > class FieldShape shape where shape :: Shape shape
class FieldShape shape where shaped :: Shape shape

instance FieldShape Omit where shaped = OmitS
instance FieldShape Need where shaped = NeedS
instance FieldShape Many where shaped = ManyS
instance FieldShape Free where shaped = FreeS

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
  (FieldShape shape) =>
  Const [(Text, Text)] (Shape shape)
shapeAttrs = case shaped @shape of
  OmitS -> Const []
  NeedS -> Const [("required", "required")]
  ManyS -> Const [("required", "required"), ("multiple", "multiple")]
  FreeS -> Const [("multiple", "multiple")]

select ::
  forall shape ty app.
  (RenderMessage app FormMessage, Eq ty, FieldShape shape) =>
  OptionList ty ->
  [(Text, Text)] ->
  Shaped shape ty ->
  FormFor app (FormResult (Shaped shape ty), WidgetFor app ())
select ol = input do
  Field
    { enctype = UrlEncoded
    , view = \attrs evalue -> do
        let Const s = shapeAttrs @shape
            selected :: ty -> Bool = case evalue of
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

runFormWithEnv ::
  Form app ty ->
  Maybe (Env, FileEnv) ->
  HandlerFor app ((FormResult ty, WidgetFor app ()), Enctype)
runFormWithEnv form envs = do
  app <- getYesod
  langs <- languages
  evalRWST form (envs, app, langs) (IntSingle 0)

runFormPostWithEnv ::
  (RenderMessage app FormMessage) =>
  (Html -> Form app ty) ->
  Maybe (Env, FileEnv) ->
  HandlerFor app ((FormResult ty, WidgetFor app ()), Enctype)
runFormPostWithEnv mk envs = do
  YesodRequest{reqToken} <- getRequest
  app <- getYesod
  langs <- languages

  let postKey = defaultCsrfParamName
      (withKey, valid) = flip (maybe (mempty, isNothing)) reqToken \token ->
        ( [shamlet|<input type="hidden" name="#{postKey}" value="#{token}">|]
        , \case
            Just [tokenR] ->
              -- The use of 'constEqBytes' prevents timing attacks.
              Text.encodeUtf8 tokenR `constEqBytes` Text.encodeUtf8 token
            _ -> False
        )

  runFormWithEnv (mk withKey) envs <&> (first . first) case envs of
    Just (env, _) -> \case
      FormSuccess{}
        | not $ valid (env Map.!? postKey) ->
            FormFailure [renderMessage app langs MsgCsrfWarning]
      result -> result
    Nothing -> const FormMissing

generateFormPost ::
  (RenderMessage app FormMessage) =>
  (Html -> Form app ty) ->
  HandlerFor app (WidgetFor app (), Enctype)
generateFormPost mk = first snd <$> runFormPostWithEnv mk Nothing

methodEnv :: Method -> HandlerFor app (Maybe (Env, FileEnv))
methodEnv method = do
  let monoid = flip foldr Map.empty \(k, v) -> Map.insertWith (<>) k [v]
  YesodRequest{reqGetParams, reqWaiRequest} <- getRequest
  traverse (\() -> (monoid *** monoid) <$> runRequestBody) do
    guard (requestMethod reqWaiRequest == method)
    guard (method /= methodGet || isJust (lookup getKey reqGetParams))

runFormPost ::
  (RenderMessage app FormMessage) =>
  (Html -> Form app ty) ->
  HandlerFor app ((FormResult ty, WidgetFor app ()), Enctype)
runFormPost mk = runFormPostWithEnv mk =<< methodEnv methodPost

getKey :: Text
getKey = "_hasdata"

runFormGetWithEnv ::
  (RenderMessage app FormMessage) =>
  (Html -> Form app ty) ->
  Maybe (Env, FileEnv) ->
  HandlerFor app ((FormResult ty, WidgetFor app ()), Enctype)
runFormGetWithEnv mk =
  runFormWithEnv $ mk [shamlet|<input type="hidden" name="#{getKey}">|]

generateFormGet ::
  (RenderMessage app FormMessage) =>
  (Html -> Form app ty) ->
  HandlerFor app (WidgetFor app (), Enctype)
generateFormGet mk = first snd <$> runFormGetWithEnv mk Nothing

runFormGet ::
  (RenderMessage app FormMessage) =>
  (Html -> Form app ty) ->
  HandlerFor app ((FormResult ty, WidgetFor app ()), Enctype)
runFormGet mk = runFormGetWithEnv mk =<< methodEnv methodGet

identifyForm :: Text -> (Html -> Form app ty) -> (Html -> Form app ty)
identifyForm me mk withKey = do
  let i = "_identifier"
      amHere = elem me . Map.findWithDefault [] i
  (mk (withKey <> [shamlet|<input type="hidden" name="#{i}" value="#{me}">|]) &)
    =<< asks \case
      (Just (env, _), _, _) | not (amHere env) ->
        local \(_, app, langs) -> (Nothing, app, langs)
      _ -> id
