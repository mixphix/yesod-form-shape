module Yesod.Form.Shape
  ( FieldFor (..)
  , FieldShape
  , Shape (..)
  , ShapeType (..)
  , input
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
import Data.Functor.Const (Const (Const))
import Data.Functor.Identity (Identity (..))
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty (..), nonEmpty, toList)
import Data.Map qualified as Map
import Data.Maybe (isJust, isNothing)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Traversable (for)
import Network.HTTP.Types (Method, methodGet, methodPost)
import Network.Wai (Request (requestMethod))
import Yesod.Core
import Yesod.Form
  ( Enctype (UrlEncoded)
  , Env
  , FileEnv
  , FormMessage (MsgCsrfWarning)
  , FormResult (..)
  , Ints (IntSingle)
  , Option (..)
  , OptionList (..)
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
-- type family FieldShape shape = x | x -> shape where
--   FieldShape Omit = Maybe
--   FieldShape Need = Identity
--   FieldShape Many = NonEmpty
--   FieldShape Free = []
-- @
type FieldShape :: ShapeType -> Type -> Type
type family FieldShape shape = x | x -> shape where
  FieldShape Omit = Maybe
  FieldShape Need = Identity
  FieldShape Many = NonEmpty
  FieldShape Free = []

shapeAttrs :: forall shape. (Shaped shape) => Const [(Text, Text)] (Shape shape)
shapeAttrs = case shaped @shape of
  OmitS -> Const []
  NeedS -> Const [("required", "required")]
  ManyS -> Const [("required", "required"), ("multiple", "multiple")]
  FreeS -> Const [("multiple", "multiple")]

-- |
-- @
-- data FieldFor app shape x = Field
--   { enctype :: Enctype
--   , view ::
--       [(Text, Text)] ->
--       Either Text (FieldShape shape x) ->
--       WidgetFor app ()
--   , parse ::
--       [Text] ->
--       [FileInfo] ->
--       HandlerFor app (Either (SomeMessage app) (FieldShape shape x))
--   }
-- @
data FieldFor app shape x = Field
  { enctype :: Enctype
  , view ::
      [(Text, Text)] ->
      Either Text (FieldShape shape x) ->
      WidgetFor app ()
  , parse ::
      [Text] ->
      [FileInfo] ->
      HandlerFor app (Either (SomeMessage app) (FieldShape shape x))
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

input ::
  forall shape x app.
  (RenderMessage app FormMessage, Shaped shape) =>
  WidgetFor app () ->
  FieldFor app shape x ->
  [(Text, Text)] ->
  Maybe (FieldShape shape x) ->
  FormFor app (FormResult (FieldShape shape x), WidgetFor app ())
input label field attributes initial = do
  let Const shape = shapeAttrs @shape
  tell field.enctype
  (envs, app, langs) <- ask
  name <- maybe newFormIdent pure (lookup "name" attributes)
  fmap ((label <>) . field.view (shape <> attributes)) <$> case envs of
    Nothing -> pure (FormMissing, maybe (Left "") Right initial)
    Just (env, fileEnv) -> do
      let inputs = Map.findWithDefault [] name env
          files = Map.findWithDefault [] name fileEnv
      lift (field.parse inputs files) <&> \case
        Right x -> (FormSuccess x, Right x)
        Left (SomeMessage e) ->
          ( FormFailure [renderMessage app langs e]
          , Left (Text.intercalate ", " inputs)
          )

select ::
  forall shape x app.
  (RenderMessage app FormMessage, Eq x, Shaped shape) =>
  WidgetFor app () ->
  OptionList x ->
  [(Text, Text)] ->
  Maybe (FieldShape shape x) ->
  FormFor app (FormResult (FieldShape shape x), WidgetFor app ())
select label options attributes initial = do
  let Const shape = shapeAttrs @shape
      parse ::
        [Text] -> HandlerFor app (Either (SomeMessage app) (FieldShape shape x))
      parse inputs = do
        let olRead = case options of
              OptionList{..} -> olReadExternal
              OptionListGrouped{..} -> olReadExternalGrouped
        case shaped @shape of
          OmitS -> pure case inputs of
            [] -> Right Nothing
            [x] -> case olRead x of
              Nothing -> Left $ SomeMessage ("unknown option: " <> x)
              Just y -> Right (Just y)
            _ -> Left "multiple given when one expected"
          NeedS -> pure case inputs of
            [] -> Left "input is required"
            [x] -> case olRead x of
              Nothing -> Left $ SomeMessage ("unknown option: " <> x)
              Just y -> Right (Identity y)
            _ -> Left "multiple given when one expected"
          ManyS -> pure case nonEmpty inputs of
            Nothing -> Left "input is required"
            Just xs -> for xs \x -> case olRead x of
              Nothing -> Left $ SomeMessage ("unknown option: " <> x)
              Just y -> Right y
          FreeS -> pure $ for inputs \x -> case olRead x of
            Nothing -> Left $ SomeMessage ("unknown option: " <> x)
            Just y -> Right y
      view ::
        [(Text, Text)] -> Either Text (FieldShape shape x) -> WidgetFor app ()
      view attrs evalue = do
        let selected :: x -> Bool = case evalue of
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
  tell UrlEncoded
  (envs, app, langs) <- ask
  name <- maybe newFormIdent pure (lookup "name" attributes)
  fmap ((label <>) . view (shape <> attributes)) <$> case envs of
    Nothing -> pure (FormMissing, maybe (Left "") Right initial)
    Just (env, _) -> do
      let inputs = Map.findWithDefault [] name env
      lift (parse inputs) <&> \case
        Right x -> (FormSuccess x, Right x)
        Left (SomeMessage e) ->
          ( FormFailure [renderMessage app langs e]
          , Left (Text.intercalate ", " inputs)
          )

runFormWithEnv ::
  FormFor app x ->
  Maybe (Env, FileEnv) ->
  HandlerFor app (x, Enctype)
runFormWithEnv form envs = do
  app <- getYesod
  langs <- languages
  evalRWST form (envs, app, langs) (IntSingle 0)

-- | > type Xsrf form = Html -> form
type Xsrf form = Html -> form

runFormPostWithEnv ::
  (RenderMessage app FormMessage) =>
  Xsrf (FormFor app (FormResult x, WidgetFor app ())) ->
  Maybe (Env, FileEnv) ->
  HandlerFor app ((FormResult x, WidgetFor app ()), Enctype)
runFormPostWithEnv xform envs = do
  YesodRequest{reqToken} <- getRequest
  app <- getYesod
  langs <- languages

  let postKey = defaultCsrfParamName
      (xsrf, valid) = flip (maybe (mempty, isNothing)) reqToken \token ->
        ( [shamlet|<input type="hidden" name="#{postKey}" value="#{token}">|]
        , \case
            Just [tokenR] ->
              -- The use of 'constEqBytes' prevents timing attacks.
              Text.encodeUtf8 tokenR `constEqBytes` Text.encodeUtf8 token
            _ -> False
        )

  runFormWithEnv (xform xsrf) envs <&> (first . first) \case
    FormSuccess{}
      | Just (env, _) <- envs
      , not (valid $ env Map.!? postKey) ->
          FormFailure [renderMessage app langs MsgCsrfWarning]
    _ | Nothing <- envs -> FormMissing
    result -> result

generateFormPost ::
  (RenderMessage app FormMessage) =>
  Xsrf (FormFor app (FormResult x, WidgetFor app ())) ->
  HandlerFor app (WidgetFor app (), Enctype)
generateFormPost xform = first snd <$> runFormPostWithEnv xform Nothing

methodEnv :: Method -> HandlerFor app (Maybe (Env, FileEnv))
methodEnv method = do
  let monoid = flip foldr Map.empty \(k, v) -> Map.insertWith (<>) k [v]
  YesodRequest{reqGetParams, reqWaiRequest} <- getRequest
  traverse (\() -> (monoid *** monoid) <$> runRequestBody) do
    guard (requestMethod reqWaiRequest == method)
    guard (method /= methodGet || isJust (lookup getKey reqGetParams))

runFormPost ::
  (RenderMessage app FormMessage) =>
  Xsrf (FormFor app (FormResult x, WidgetFor app ())) ->
  HandlerFor app ((FormResult x, WidgetFor app ()), Enctype)
runFormPost xform = runFormPostWithEnv xform =<< methodEnv methodPost

getKey :: Text
getKey = "_hasdata"

runFormGetWithEnv ::
  (RenderMessage app FormMessage) =>
  Xsrf (FormFor app x) ->
  Maybe (Env, FileEnv) ->
  HandlerFor app (x, Enctype)
runFormGetWithEnv xform =
  runFormWithEnv $ xform [shamlet|<input type="hidden" name="#{getKey}">|]

generateFormGet ::
  (RenderMessage app FormMessage) =>
  Xsrf (FormFor app (FormResult x, WidgetFor app ())) ->
  HandlerFor app (WidgetFor app (), Enctype)
generateFormGet xform = first snd <$> runFormGetWithEnv xform Nothing

runFormGet ::
  (RenderMessage app FormMessage) =>
  Xsrf (FormFor app (FormResult x, WidgetFor app ())) ->
  HandlerFor app ((FormResult x, WidgetFor app ()), Enctype)
runFormGet xform = runFormGetWithEnv xform =<< methodEnv methodGet

identifyForm :: Text -> Xsrf (FormFor app x) -> Xsrf (FormFor app x)
identifyForm me xform xsrf = do
  let i = "_identifier"
      amHere = elem me . Map.findWithDefault [] i
  (xform (xsrf <> [shamlet|<input type="hidden" name="#{i}" value="#{me}">|]) &)
    =<< asks \case
      (Just (env, _), _, _) | not (amHere env) ->
        local \(_, app, langs) -> (Nothing, app, langs)
      _ -> id
