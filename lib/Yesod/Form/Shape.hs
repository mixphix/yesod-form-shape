module Yesod.Form.Shape
  ( FieldFor (..)
  , FieldShape
  , Shape (..)
  , ShapeType (..)
  , shapeInstance
  , DefaultField (..)
  , input
  , input'
  , select
  , singleField
  , textField
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
import Data.Data
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.Functor.Const (Const (Const))
import Data.Functor.Identity (Identity (..))
import Data.Functor.Invariant
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty (..), nonEmpty, toList)
import Data.Map qualified as Map
import Data.Maybe
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Traversable (for)
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

-- | > class Shaped shape where shape :: Shape shape
class Shaped shape where shaped :: Shape shape

instance Shaped Omit where shaped = OmitS
instance Shaped Need where shaped = NeedS
instance Shaped Many where shaped = ManyS
instance Shaped Free where shaped = FreeS

-- Shape shape shape shape shape shape shape shape shape shape.

-- |
-- @
-- type family FieldShape shape = ty | ty -> shape where
--   FieldShape Omit = Maybe
--   FieldShape Need = Identity
--   FieldShape Many = NonEmpty
--   FieldShape Free = []
-- @
type FieldShape :: ShapeType -> Type -> Type
type family FieldShape shape = ty | ty -> shape where
  FieldShape Omit = Maybe
  FieldShape Need = Identity
  FieldShape Many = NonEmpty
  FieldShape Free = []

shapeInstance ::
  forall c shape.
  (Shaped shape, c Maybe, c Identity, c NonEmpty, c []) =>
  (forall r. ((c (FieldShape shape)) => r) -> r)
shapeInstance x = case shaped @shape of
  OmitS -> x
  NeedS -> x
  ManyS -> x
  FreeS -> x

shapeAttrs :: forall shape. (Shaped shape) => Const [(Text, Text)] (Shape shape)
shapeAttrs = case shaped @shape of
  OmitS -> Const []
  NeedS -> Const [("required", "required")]
  ManyS -> Const [("required", "required"), ("multiple", "multiple")]
  FreeS -> Const [("multiple", "multiple")]

-- |
-- @
-- data FieldFor app shape ty = Field
--   { enctype :: Enctype
--   , view ::
--       [(Text, Text)] ->
--       Either Text (FieldShape shape ty) ->
--       WidgetFor app ()
--   , parse ::
--       [Text] ->
--       [FileInfo] ->
--       HandlerFor app (Either (SomeMessage app) (FieldShape shape ty))
--   }
-- @
data FieldFor app shape ty = Field
  { enctype :: Enctype
  , view ::
      [(Text, Text)] ->
      Either Text (FieldShape shape ty) ->
      WidgetFor app ()
  , parse ::
      [Text] ->
      [FileInfo] ->
      HandlerFor app (Either (SomeMessage app) (FieldShape shape ty))
  }

instance (Shaped shape) => Invariant (FieldFor app shape) where
  invmap ::
    (ty -> tz) -> (tz -> ty) -> FieldFor app shape ty -> FieldFor app shape tz
  invmap source target field =
    field
      { view = \attrs evalue -> shapeInstance @Invariant @shape do
          field.view attrs (invmap target source <$> evalue)
      , parse = \myEnv myFileEnv -> shapeInstance @Invariant @shape do
          field.parse myEnv myFileEnv <&> fmap (invmap source target)
      }

unsupported :: Shape shape -> [Char] -> ty
unsupported shape ty =
  error $ "Shape " <> show shape <> " unsupported for " <> ty

parseSingle ::
  (RenderMessage app FormMessage) =>
  Shape shape ->
  [Char] ->
  ([Char] -> Maybe ty) ->
  [Text] ->
  HandlerFor app (Either (SomeMessage app) (FieldShape shape ty))
parseSingle shape ty f = \case
  [] -> pure case shape of
    OmitS -> Right Nothing
    NeedS -> Left (SomeMessage MsgValueRequired)
    _ -> unsupported shape ty
  [x] -> pure case f (Text.unpack x) of
    Nothing -> Left (SomeMessage $ MsgInvalidEntry x)
    Just fx -> case shape of
      OmitS -> Right (Just fx)
      NeedS -> Right (Identity fx)
      _ -> unsupported shape ty
  xs -> pure $ Left (SomeMessage $ MsgInvalidEntry (Text.unlines xs))

-- | Suitable for 'Omit' and 'Need' for types with inverse 'Show' and 'Read'.
singleField ::
  forall ty shape app.
  (RenderMessage app FormMessage, Read ty, Show ty, Typeable ty) =>
  Shape shape ->
  FieldFor app shape ty
singleField shape = do
  let ty = show (typeOf (undefined :: ty))
  Field
    { enctype = UrlEncoded
    , view = \attrs evalue -> do
        let value :: [Char] = case evalue of
              Left _ -> ""
              Right v -> case shape of
                OmitS -> maybe "" show v
                NeedS -> show (runIdentity v)
                _ -> unsupported shape ty
        [whamlet|<input type="number" *{attrs} value="#{value}">|]
    , parse = \myEnv _ -> parseSingle shape ty readMaybe myEnv
    }

textField ::
  forall shape app.
  (RenderMessage app FormMessage) =>
  Shape shape ->
  FieldFor app shape Text
textField shape = do
  Field
    { enctype = UrlEncoded
    , view = \attrs evalue -> do
        let value :: [Char] = case evalue of
              Left _ -> ""
              Right v -> case shape of
                OmitS -> maybe "" show v
                NeedS -> show (runIdentity v)
                _ -> unsupported shape "Text"
        [whamlet|<input type="number" *{attrs} value="#{value}">|]
    , parse = \myEnv _ -> case myEnv of
        [] -> pure case shape of
          OmitS -> Right Nothing
          NeedS -> Left (SomeMessage MsgValueRequired)
          _ -> unsupported shape "Text"
        [x] -> pure case shape of
          OmitS -> Right (Just x)
          NeedS -> Right (Identity x)
          _ -> unsupported shape "Text"
        xs -> pure $ Left (SomeMessage $ MsgInvalidEntry (Text.unlines xs))
    }

class (RenderMessage app FormMessage) => DefaultField app shape ty where
  defaultField :: FieldFor app shape ty

instance (RenderMessage app FormMessage) => DefaultField app Omit Int where
  defaultField = singleField OmitS

instance (RenderMessage app FormMessage) => DefaultField app Need Int where
  defaultField = singleField NeedS

instance (RenderMessage app FormMessage) => DefaultField app Omit Integer where
  defaultField = singleField OmitS

instance (RenderMessage app FormMessage) => DefaultField app Need Integer where
  defaultField = singleField NeedS

instance (RenderMessage app FormMessage) => DefaultField app Omit Double where
  defaultField = singleField OmitS

instance (RenderMessage app FormMessage) => DefaultField app Need Double where
  defaultField = singleField NeedS

instance (RenderMessage app FormMessage) => DefaultField app Omit Text where
  defaultField = textField OmitS

instance (RenderMessage app FormMessage) => DefaultField app Need Text where
  defaultField = textField NeedS

instance (RenderMessage app FormMessage) => DefaultField app Omit Textarea where
  defaultField = invmap Textarea unTextarea (textField OmitS)

instance (RenderMessage app FormMessage) => DefaultField app Need Textarea where
  defaultField = invmap Textarea unTextarea (textField NeedS)

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

input ::
  forall shape ty app.
  (RenderMessage app FormMessage, Shaped shape) =>
  WidgetFor app () ->
  FieldFor app shape ty ->
  [(Text, Text)] ->
  Maybe (FieldShape shape ty) ->
  FormFor app (FormResult (FieldShape shape ty), WidgetFor app ())
input label field attributes initial = do
  let Const sAttrs = shapeAttrs @shape
      view evalue = label <> field.view (sAttrs <> attributes) evalue
  tell field.enctype
  (envs, app, langs) <- ask
  name <- maybe newFormIdent pure (lookup "name" attributes)
  second view <$> case envs of
    Nothing -> pure (FormMissing, maybe (Left "") Right initial)
    Just (env, fileEnv) -> do
      let myEnv = Map.findWithDefault [] name env
          files = Map.findWithDefault [] name fileEnv
      lift (field.parse myEnv files) <&> \case
        Right x -> (FormSuccess x, Right x)
        Left (SomeMessage msg) ->
          ( FormFailure [renderMessage app langs msg]
          , Left (Text.intercalate ", " myEnv)
          )

input' ::
  forall shape ty app.
  (RenderMessage app FormMessage, Shaped shape, DefaultField app shape ty) =>
  WidgetFor app () ->
  [(Text, Text)] ->
  Maybe (FieldShape shape ty) ->
  FormFor app (FormResult (FieldShape shape ty), WidgetFor app ())
input' label = input label defaultField

select ::
  forall shape ty app.
  (RenderMessage app FormMessage, Eq ty, Shaped shape) =>
  WidgetFor app () ->
  OptionList ty ->
  [(Text, Text)] ->
  Maybe (FieldShape shape ty) ->
  FormFor app (FormResult (FieldShape shape ty), WidgetFor app ())
select label options = input label do
  Field
    { enctype = UrlEncoded
    , view = \attrs evalue -> do
        let selected :: ty -> Bool = case evalue of
              Left _ -> const False
              Right val -> case shaped @shape of
                OmitS -> maybe (const False) (==) val
                NeedS -> (== runIdentity val)
                ManyS -> flip elem (toList val)
                FreeS -> flip elem val
        [whamlet|
          <select *{attrs}>
            $case options
              $of OptionList{olOptions}
                $forall option <- olOptions
                  <option :selected option.optionInternalValue:selected value="#{option.optionExternalValue}">
                    #{option.optionDisplay}
              $of OptionListGrouped{olOptionsGrouped}
                $forall (group, options) <- olOptionsGrouped
                  <optgroup label="#{group}">
                    $forall option <- options
                      <option :selected option.optionInternalValue:selected value="#{option.optionExternalValue}">
                        #{option.optionDisplay}
        |]
    , parse = \myEnv _ -> do
        let olRead = case options of
              OptionList{..} -> olReadExternal
              OptionListGrouped{..} -> olReadExternalGrouped
        case shaped @shape of
          OmitS -> pure case myEnv of
            [] -> Right Nothing
            [x] -> case olRead x of
              Nothing -> Left (SomeMessage $ MsgInvalidEntry x)
              Just y -> Right (Just y)
            _ -> Left (SomeMessage $ MsgInvalidEntry "Duplicated")
          NeedS -> pure case myEnv of
            [] -> Left (SomeMessage MsgValueRequired)
            [x] -> case olRead x of
              Nothing -> Left (SomeMessage $ MsgInvalidEntry x)
              Just y -> Right (Identity y)
            _ -> Left (SomeMessage $ MsgInvalidEntry "Duplicated")
          ManyS -> pure case nonEmpty myEnv of
            Nothing -> Left (SomeMessage MsgValueRequired)
            Just xs -> for xs \x -> case olRead x of
              Nothing -> Left (SomeMessage $ MsgInvalidEntry x)
              Just y -> Right y
          FreeS -> pure $ for myEnv \x -> case olRead x of
            Nothing -> Left (SomeMessage $ MsgInvalidEntry x)
            Just y -> Right y
    }

runFormWithEnv ::
  FormFor app ty ->
  Maybe (Env, FileEnv) ->
  HandlerFor app (ty, Enctype)
runFormWithEnv form envs = do
  app <- getYesod
  langs <- languages
  evalRWST form (envs, app, langs) (IntSingle 0)

-- | > type Csrf form = Html -> form
type Csrf form = Html -> form

runFormPostWithEnv ::
  (RenderMessage app FormMessage) =>
  Csrf (FormFor app (FormResult ty, WidgetFor app ())) ->
  Maybe (Env, FileEnv) ->
  HandlerFor app ((FormResult ty, WidgetFor app ()), Enctype)
runFormPostWithEnv cform envs = do
  YesodRequest{reqToken} <- getRequest
  app <- getYesod
  langs <- languages

  let postKey = defaultCsrfParamName
      (csrf, valid) = flip (maybe (mempty, isNothing)) reqToken \token ->
        ( [shamlet|<input type="hidden" name="#{postKey}" value="#{token}">|]
        , \case
            Just [tokenR] ->
              -- The use of 'constEqBytes' prevents timing attacks.
              Text.encodeUtf8 tokenR `constEqBytes` Text.encodeUtf8 token
            _ -> False
        )

  runFormWithEnv (cform csrf) envs <&> (first . first) case envs of
    Just (env, _) -> \case
      FormSuccess{}
        | not $ valid (env Map.!? postKey) ->
            FormFailure [renderMessage app langs MsgCsrfWarning]
      result -> result
    Nothing -> const FormMissing

generateFormPost ::
  (RenderMessage app FormMessage) =>
  Csrf (FormFor app (FormResult ty, WidgetFor app ())) ->
  HandlerFor app (WidgetFor app (), Enctype)
generateFormPost cform = first snd <$> runFormPostWithEnv cform Nothing

methodEnv :: Method -> HandlerFor app (Maybe (Env, FileEnv))
methodEnv method = do
  let monoid = flip foldr Map.empty \(k, v) -> Map.insertWith (<>) k [v]
  YesodRequest{reqGetParams, reqWaiRequest} <- getRequest
  traverse (\() -> (monoid *** monoid) <$> runRequestBody) do
    guard (requestMethod reqWaiRequest == method)
    guard (method /= methodGet || isJust (lookup getKey reqGetParams))

runFormPost ::
  (RenderMessage app FormMessage) =>
  Csrf (FormFor app (FormResult ty, WidgetFor app ())) ->
  HandlerFor app ((FormResult ty, WidgetFor app ()), Enctype)
runFormPost cform = runFormPostWithEnv cform =<< methodEnv methodPost

getKey :: Text
getKey = "_hasdata"

runFormGetWithEnv ::
  (RenderMessage app FormMessage) =>
  Csrf (FormFor app ty) ->
  Maybe (Env, FileEnv) ->
  HandlerFor app (ty, Enctype)
runFormGetWithEnv cform =
  runFormWithEnv $ cform [shamlet|<input type="hidden" name="#{getKey}">|]

generateFormGet ::
  (RenderMessage app FormMessage) =>
  Csrf (FormFor app (FormResult ty, WidgetFor app ())) ->
  HandlerFor app (WidgetFor app (), Enctype)
generateFormGet cform = first snd <$> runFormGetWithEnv cform Nothing

runFormGet ::
  (RenderMessage app FormMessage) =>
  Csrf (FormFor app (FormResult ty, WidgetFor app ())) ->
  HandlerFor app ((FormResult ty, WidgetFor app ()), Enctype)
runFormGet cform = runFormGetWithEnv cform =<< methodEnv methodGet

identifyForm :: Text -> Csrf (FormFor app ty) -> Csrf (FormFor app ty)
identifyForm me cform csrf = do
  let i = "_identifier"
      amHere = elem me . Map.findWithDefault [] i
  (cform (csrf <> [shamlet|<input type="hidden" name="#{i}" value="#{me}">|]) &)
    =<< asks \case
      (Just (env, _), _, _) | not (amHere env) ->
        local \(_, app, langs) -> (Nothing, app, langs)
      _ -> id
