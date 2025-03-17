{-# LANGUAGE UndecidableInstances #-}

module Yesod.Form.Shape
  ( Attrs
  , requireAttr
  , replaceAttr
  , Input (..)
  , msgInvalidEntries
  , ShapeS (OmitS, NeedS, ManyS, FreeS)
  , Shape (Omit, Need, Many, Free)
  , KnownShape (shapeS)
  , OptionalShape
  , RequiredShape
  , SingleShape
  , MultipleShape
  , shapeInstance
  , selectInstance
  , shapeAttrs
  , Select
  , select
  , FormFor
  , type FormInput
  , pattern FormInput
  , type FormOutput
  , pattern FormOutput
  , Entry (..)
  , entry
  , runInput
  , form
  , actionForm
  , recordForm
  , recordFormM
  , generateFormPost
  , runFormPost
  , generateFormGet
  , runFormGet
  , identifyForm
  , Decorate (..)
  , Design (..)
  , designInput
  , LabelPos (..)
  , Label (..)
  , simpleLabel
  , asteriskLabel
  , designDecorate

    -- ** ToOption
  , ToOption (toOption)
  , toOptions
  , toOptionGroups

    -- * re-exports
  , Enctype (..)
  , Env
  , FileEnv
  , FormMessage (..)
  , FormResult (..)
  , Option (..)
  , OptionList (..)
  , Textarea (..)
  , newFormIdent
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
import Data.Default
import Data.Foldable
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.Functor.Compose (Compose (..))
import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..))
import Data.Functor.Invariant
import Data.Functor.Product
import Data.Kind (Constraint, Type)
import Data.List.NonEmpty (NonEmpty (..), nonEmpty)
import Data.Map qualified as Map
import Data.Maybe
import Data.Semigroup (Endo (..))
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Text.Read qualified as Text
import Data.Time
import GHC.Natural (Natural)
import GHC.TypeError (ErrorMessage (Text), TypeError)
import Network.HTTP.Types (Method, methodGet, methodPost)
import Network.Wai (Request (requestMethod))
import Prairie (Cases (Cases), Record (..), type (~>))
import Text.Shakespeare.Text (st)
import Yesod.Core
import Yesod.Form
  ( Enctype (..)
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
import Yesod.Form.Functions (addClass)

type Attrs = [(Text, Text)]

tshow :: (Show x) => x -> Text
tshow = Text.pack . show

lowerDashed :: Text -> Text
lowerDashed = Text.intercalate "-" . Text.words . Text.toLower

-- | Format according to the 'defaultTimeLocale'.
fmtdef :: (FormatTime t) => String -> t -> Text
fmtdef fmt = Text.pack . formatTime defaultTimeLocale fmt

-- | Parse according to the 'defaultTimeLocale'.
prsdef :: (ParseTime t) => String -> Text -> Maybe t
prsdef fmt = parseTimeM False defaultTimeLocale fmt . Text.unpack

msgInvalidEntries ::
  (RenderMessage app FormMessage) => [Text] -> SomeMessage app
msgInvalidEntries = SomeMessage . MsgInvalidEntry . Text.intercalate ", "

-- |
-- An 'Input' is what this library calls the abstraction for handling
-- data exchanges through Web forms, reminiscent of the @<input>@ tag,
-- though it might instead produce a @<select>@ or @<textarea>@.
data Input app ty = Input
  { enctype :: Enctype
  -- ^ 'UrlEncoded' or 'Multipart'
  , view :: Attrs -> Either Text ty -> WidgetFor app ()
  -- ^
  -- @'view' attrs value@ should return a single DOM element representing
  -- the form widget with attributes @attrs@ and initial value @value@.
  , parse :: [Text] -> [FileInfo] -> HandlerFor app (Either (SomeMessage app) ty)
  -- ^ @'parse' myEnv myFileEnv@ is only ever applied to the values from the DOM element's @name@ attribute.
  }

instance Invariant (Input app) where
  invmap :: (ty -> tz) -> (tz -> ty) -> Input app ty -> Input app tz
  invmap source target input =
    Input
      { enctype = input.enctype
      , view = \attrs value -> input.view attrs (invmap target source value)
      , parse = \myEnv myFileEnv -> invmap source target <$> input.parse myEnv myFileEnv
      }

type FormFor app =
  RWST
    (Maybe (Env, FileEnv), app, [Lang])
    Enctype
    Ints
    (HandlerFor app)

newtype Decorate app = Decorate {decorate :: WidgetFor app () -> WidgetFor app ()}
  deriving (Semigroup, Monoid) via Endo (WidgetFor app ())

type FormInput app =
  Product (Input app) (Product (Const (Attrs, Decorate app)) Maybe)

-- |
-- @'FormInput' entry attrs value decor@ specifies how to interpret a value of @ty@ through a 'Input'.
pattern FormInput ::
  Decorate app ->
  Input app ty ->
  Attrs ->
  Maybe ty ->
  FormInput app ty
pattern FormInput decor entry attrs value =
  Pair entry (Pair (Const (attrs, decor)) value)

{-# COMPLETE FormInput #-}

type FormOutput app = Product FormResult (Const (WidgetFor app ()))

-- |
-- A @'FormOutput' result widget@ is what you get back from a @'FormInput' entry attrs value decor@,
-- after you've done some stuff in the @'FormFor' app@ monad.
pattern FormOutput :: FormResult ty -> WidgetFor app () -> FormOutput app ty
pattern FormOutput result widget = Pair result (Const widget)

{-# COMPLETE FormOutput #-}

runInput ::
  forall app ty.
  (RenderMessage app FormMessage) =>
  FormInput app ty ->
  FormFor app (FormResult ty, WidgetFor app ())
runInput (FormInput d input attrs0 value) = do
  tell input.enctype
  (envs, app, langs) <- ask
  (name, attrs) <- case lookup "name" attrs0 of
    Just name -> pure (name, attrs0)
    Nothing -> do
      name <- newFormIdent
      pure (name, ("name", name) : attrs0)
  (result, widget) <-
    fmap (input.view attrs) <$> case envs of
      Nothing -> pure (FormMissing, maybe (Left "No initial value") Right value)
      Just (env, fileEnv) -> do
        let myEnv = Map.findWithDefault [] name env
            myFileEnv = Map.findWithDefault [] name fileEnv
        lift (input.parse myEnv myFileEnv) <&> \case
          Right x -> (FormSuccess x, Right x)
          Left (SomeMessage msg) ->
            ( FormFailure [renderMessage app langs msg]
            , Left (Text.intercalate ", " myEnv)
            )
  pure (result :: FormResult ty, d.decorate widget)

-- | The transformation representing the exchange from 'FormInput' to 'FormOutput'.
form ::
  (RenderMessage app FormMessage) =>
  FormInput app ~> Compose (FormFor app) (FormOutput app)
form = Compose . fmap (uncurry FormOutput) . runInput

actionForm ::
  (RenderMessage app FormMessage) =>
  Compose (FormFor app) (FormInput app) ~> Compose (FormFor app) (FormOutput app)
actionForm (Compose entryAction) = Compose (fmap (uncurry FormOutput) . runInput =<< entryAction)

recordForm ::
  (Record rec, RenderMessage app FormMessage) =>
  Cases rec (FormInput app) ->
  FormFor app (FormResult rec, Cases rec (Const (WidgetFor app ())))
recordForm (Cases input) =
  sequenceRecordA (Cases $ form . input) <&> \(Cases exit) ->
    ( tabulateRecordA $ Cases \f -> case exit f of FormOutput r _ -> r
    , Cases \f -> case exit f of FormOutput _ w -> Const w
    )

recordFormM ::
  (Record rec, RenderMessage app FormMessage) =>
  Cases rec (Compose (FormFor app) (FormInput app)) ->
  FormFor app (FormResult rec, Cases rec (Const (WidgetFor app ())))
recordFormM (Cases input) =
  sequenceRecordA (Cases $ actionForm . input) <&> \(Cases exit) ->
    ( tabulateRecordA $ Cases \f -> case exit f of FormOutput r _ -> r
    , Cases \f -> case exit f of FormOutput _ w -> Const w
    )

data Shape
  = Omit
  | Need
  | Many
  | Free

type ShapeS :: Shape -> Type
data ShapeS shape where
  OmitS :: ShapeS Omit
  NeedS :: ShapeS Need
  ManyS :: ShapeS Many
  FreeS :: ShapeS Free

class KnownShape shape where shapeS :: ShapeS shape
instance KnownShape Omit where shapeS = OmitS
instance KnownShape Need where shapeS = NeedS
instance KnownShape Many where shapeS = ManyS
instance KnownShape Free where shapeS = FreeS

-- | permits 0
type OptionalShape :: Shape -> Constraint
type family OptionalShape shape where
  OptionalShape Omit = ()
  OptionalShape Need = TypeError ('Text "Need is not a OptionalShape")
  OptionalShape Many = TypeError ('Text "Many is not a OptionalShape")
  OptionalShape Free = ()

-- | does not permit 0
type RequiredShape :: Shape -> Constraint
type family RequiredShape shape where
  RequiredShape Omit = TypeError ('Text "Omit is not a RequiredShape")
  RequiredShape Need = ()
  RequiredShape Many = ()
  RequiredShape Free = TypeError ('Text "Free is not a RequiredShape")

-- | does not permit more than 1
type SingleShape :: Shape -> Constraint
type family SingleShape shape where
  SingleShape Omit = ()
  SingleShape Need = ()
  SingleShape Many = TypeError ('Text "Many is not a SingleShape")
  SingleShape Free = TypeError ('Text "Free is not a SingleShape")

-- | permits more than 1
type MultipleShape :: Shape -> Constraint
type family MultipleShape shape where
  MultipleShape Omit = TypeError ('Text "Omit is not a MultipleShape")
  MultipleShape Need = TypeError ('Text "Need is not a MultipleShape")
  MultipleShape Many = ()
  MultipleShape Free = ()

-- |
-- @
-- type family Select shape = ty | ty -> shape where
--   Select Omit = Maybe
--   Select Need = Identity
--   Select Many = NonEmpty
--   Select Free = []
-- @
type Select :: Shape -> Type -> Type
type family Select shape = ty | ty -> shape where
  Select Omit = Maybe
  Select Need = Identity
  Select Many = NonEmpty
  Select Free = []

shapeInstance ::
  forall c shape ty.
  (KnownShape shape, c (Maybe ty), c (Identity ty), c (NonEmpty ty), c [ty]) =>
  (forall r. ((c (Select shape ty)) => r) -> r)
shapeInstance x = case shapeS @shape of
  OmitS -> x
  NeedS -> x
  ManyS -> x
  FreeS -> x

selectInstance ::
  forall c shape.
  (KnownShape shape, c Maybe, c Identity, c NonEmpty, c []) =>
  (forall r. ((c (Select shape)) => r) -> r)
selectInstance x = case shapeS @shape of
  OmitS -> x
  NeedS -> x
  ManyS -> x
  FreeS -> x

shapeAttrs :: forall shape. (KnownShape shape) => Const Attrs shape
shapeAttrs = case shapeS @shape of
  OmitS -> Const []
  NeedS -> Const [("required", "required")]
  ManyS -> Const [("required", "required"), ("multiple", "multiple")]
  FreeS -> Const [("multiple", "multiple")]

-- |
-- The 'Input' for a @<select>@ element with options from the supplied 'OptionList'
-- and a @shape@ parameter to handle the selection quantity.
select ::
  forall shape ty app.
  (RenderMessage app FormMessage, Eq ty, KnownShape shape) =>
  OptionList ty ->
  Input app (Select shape ty)
select ol =
  Input
    { enctype = UrlEncoded
    , view = \attrs value -> do
        let Const s = shapeAttrs @shape
            selected :: ty -> Bool = case value of
              Left _ -> const False
              Right val -> case shapeS @shape of
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
        case shapeS @shape of
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
            Just env -> traverse olRead env
          FreeS -> pure $ traverse olRead myEnv
    }

runFormPostWithEnv ::
  (RenderMessage app FormMessage) =>
  (Html -> FormFor app (FormResult ty, x)) ->
  Maybe (Env, FileEnv) ->
  HandlerFor app ((FormResult ty, x), Enctype)
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
      validatePostKey (result, widget) = case (result, envs) of
        (FormSuccess{}, Just (env, _))
          | invalidPostKey env ->
              (FormFailure [renderMessage app langs MsgCsrfWarning], widget)
        (_, Nothing) -> (FormMissing, widget)
        _ -> (result, widget)
  first validatePostKey <$> evalRWST (mk withKey) (envs, app, langs) (IntSingle 0)

generateFormPost ::
  (RenderMessage app FormMessage) =>
  (Html -> FormFor app (FormResult ty, x)) ->
  HandlerFor app (x, Enctype)
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
  (Html -> FormFor app (FormResult ty, x)) ->
  HandlerFor app ((FormResult ty, x), Enctype)
runFormPost mk = runFormPostWithEnv mk =<< methodEnv methodPost

getKey :: Text
getKey = "_hasdata"

runFormGetWithEnv ::
  (RenderMessage app FormMessage) =>
  (Html -> FormFor app (FormResult ty, x)) ->
  Maybe (Env, FileEnv) ->
  HandlerFor app ((FormResult ty, x), Enctype)
runFormGetWithEnv mk envs = do
  app <- getYesod
  langs <- languages
  evalRWST
    (mk [shamlet|<input type="hidden" name="#{getKey}">|])
    (envs, app, langs)
    (IntSingle 0)

generateFormGet ::
  (RenderMessage app FormMessage) =>
  (Html -> FormFor app (FormResult ty, x)) ->
  HandlerFor app (x, Enctype)
generateFormGet mk = first snd <$> runFormGetWithEnv mk Nothing

runFormGet ::
  (RenderMessage app FormMessage) =>
  (Html -> FormFor app (FormResult ty, x)) ->
  HandlerFor app ((FormResult ty, x), Enctype)
runFormGet mk = runFormGetWithEnv mk =<< methodEnv methodGet

identifyForm :: Text -> (Html -> FormFor app ty) -> (Html -> FormFor app ty)
identifyForm me mk withKey = do
  let i = "_identifier" :: Text
      amHere = elem me . Map.findWithDefault [] i
      withKey' = withKey <> [shamlet|<input type="hidden" name="#{i}" value="#{me}">|]
  (mk withKey' &) =<< asks \case
    (Just (env, _), _, _) | not (amHere env) -> local \(_, app, langs) -> (Nothing, app, langs)
    _ -> id

data Design app = Design
  { label :: Label app
  , before :: WidgetFor app ()
  , self :: Decorate app
  , after :: WidgetFor app ()
  , parent :: Decorate app
  }

designInput :: Design app -> Input app ty -> Attrs -> Maybe ty -> FormInput app ty
designInput = FormInput . designDecorate

data LabelPos = LabelBefore | LabelAfter
data Label app = Label
  { labelPos :: Maybe (Text, LabelPos)
  , attrs :: Attrs
  , self :: Decorate app
  }

simpleLabel :: LabelPos -> Maybe Text -> Design app
simpleLabel pos l =
  Design
    (Label (l <&> (,pos)) mempty mempty)
    mempty
    mempty
    mempty
    (Decorate \w -> [whamlet|<div .form-group>^{w}|])

asteriskLabel :: LabelPos -> Maybe Text -> Design app
asteriskLabel pos l =
  Design
    ( Label (l <&> (,pos)) mempty $
        Decorate (<> [whamlet|<sup><i class="fa fa-asterisk text-danger"></i>|])
    )
    mempty
    mempty
    mempty
    (Decorate \w -> [whamlet|<div .form-group>^{w}|])

designDecorate :: Design app -> Decorate app
designDecorate Design{..} = Decorate \(self.decorate -> w) -> parent.decorate do
  before
  let labelAttrs = addClass "form-label" label.attrs
  case label.labelPos of
    Just (t, LabelBefore) -> [whamlet|<label *{labelAttrs}>#{t}|] <> w
    Just (t, LabelAfter) -> w <> [whamlet|<label *{labelAttrs}>#{t}|]
    Nothing -> w
  after

-- Options

-- | Create an 'Option' value for a type in a standard way.
class ToOption ty where
  toOption :: ty -> Option ty

toOptions :: (ToOption ty, Functor f, Foldable f) => f ty -> OptionList ty
toOptions os =
  let options = fmap toOption os
   in OptionList
        { olOptions = toList options
        , olReadExternal = (Map.!?) $ flip foldMap' options \o ->
            Map.singleton o.optionExternalValue o.optionInternalValue
        }

toOptionGroups ::
  (ToOption ty, Functor f, Foldable f) => f (Text, f ty) -> OptionList ty
toOptionGroups os =
  let options = fmap (fmap toOption) <$> os
   in OptionListGrouped
        { olOptionsGrouped = toList $ fmap (fmap toList) options
        , olReadExternalGrouped = (Map.!?) $
            flip foldMap' options \(_, opts) -> flip foldMap' opts \o ->
              Map.singleton o.optionExternalValue o.optionInternalValue
        }

instance ToOption Bool where
  toOption b = let bt | b = "Yes" | otherwise = "No" in Option bt b bt
instance ToOption Ordering where
  toOption o =
    let ot = case o of
          LT -> "Less than"
          EQ -> "Equal to"
          GT -> "Greater than"
     in Option ot o (lowerDashed ot)
instance ToOption Int where toOption n = Option (tshow n) n (tshow n)
instance ToOption Integer where toOption n = Option (tshow n) n (tshow n)
instance ToOption Natural where toOption n = Option (tshow n) n (tshow n)
instance ToOption Double where toOption n = Option (tshow n) n (tshow n)
instance ToOption String where
  toOption s = Option (Text.pack s) s (lowerDashed $ Text.pack s)
instance ToOption Text where toOption s = Option s s (lowerDashed s)
instance ToOption DayOfWeek where toOption wk = Option (tshow wk) wk (tshow wk)
instance (ToOption a) => ToOption (Maybe a) where
  toOption = maybe (Option "\x2002" Nothing "nothing") (fmap Just . toOption)
instance (ToOption e, ToOption a) => ToOption (Either e a) where
  toOption = \case
    Left e -> let Option ed _ ev = toOption e in Option ed (Left e) (ev <> "-L")
    Right a -> let Option ad _ av = toOption a in Option ad (Right a) (av <> "-R")
instance (ToOption a, ToOption b) => ToOption (a, b) where
  toOption (a, b) =
    let Option oaDisplay _ oaValue = toOption a
        Option obDisplay _ obValue = toOption b
     in Option [st|#{oaDisplay} / #{obDisplay}|] (a, b) [st|#{oaValue}-#{obValue}|]

-- Entries
parse0With ::
  (RenderMessage app FormMessage) =>
  ([Char] -> Maybe ty) ->
  [Text] ->
  Either (SomeMessage app) (Maybe ty)
parse0With f = \case
  [] -> Right Nothing
  env -> Just <$> parse1With f env

parse1With ::
  (RenderMessage app FormMessage) =>
  ([Char] -> Maybe ty) ->
  [Text] ->
  Either (SomeMessage app) ty
parse1With f = \case
  [] -> Left (SomeMessage MsgValueRequired)
  [x] -> case f (Text.unpack x) of
    Nothing -> Left (SomeMessage $ MsgInvalidEntry x)
    Just fx -> Right fx
  env -> Left (msgInvalidEntries env)

parse0WithNum ::
  (RenderMessage app FormMessage, Number n) =>
  (Text -> Maybe n) ->
  [Text] ->
  Either (SomeMessage app) (Maybe n)
parse0WithNum f = \case
  [] -> Right Nothing
  [""] -> Right Nothing
  env -> Just <$> parse1WithNum f env

parse1WithNum ::
  (RenderMessage app FormMessage, Number n) =>
  (Text -> Maybe n) ->
  [Text] ->
  Either (SomeMessage app) n
parse1WithNum f = \case
  [] -> Left (SomeMessage MsgValueRequired)
  [x] -> case f x of
    Nothing -> Left (SomeMessage $ MsgInvalidNumber x)
    Just fx -> Right fx
  env -> Left (msgInvalidEntries env)

requireAttr :: (Applicative m) => Text -> m Text -> Attrs -> m (Text, Attrs)
requireAttr attr value attrs = case lookup attr attrs of
  Nothing -> value <&> \new -> (new, (attr, new) : attrs)
  Just old -> pure (old, attrs)

replaceAttr :: (Applicative m) => Text -> m Text -> Attrs -> m Attrs
replaceAttr attr value attrs = case lookup attr attrs of
  Nothing -> value <&> \new -> (attr, new) : attrs
  Just old -> value <&> \new -> (attr, new) : filter ((old /=) . fst) attrs

-- | An 'Entry' provides the ability to produce a standard 'Input' for a type.
-- The 'EntryAuxiliary' type allows specifying extra relevant information.
class Entry app ty where
  type EntryAuxiliary app ty
  entry' ::
    EntryAuxiliary app ty ->
    Maybe Text ->
    Attrs ->
    Maybe ty ->
    Compose (FormFor app) (FormInput app) ty

entry ::
  (Entry app ty, Default (EntryAuxiliary app ty)) =>
  (Maybe Text -> Attrs -> Maybe ty -> Compose (FormFor app) (FormInput app) ty)
entry = entry' def

instance
  (RenderMessage app FormMessage) =>
  Entry app Bool
  where
  type EntryAuxiliary app _ = ()
  entry' () l attrs value = Compose $ pure do
    designInput
      Design
        { label =
            Label (l <&> (,LabelAfter)) [("class", "form-check-label")] mempty
        , before = mempty
        , self = Decorate \w -> [whamlet|<div .form-check>^{w}|]
        , after = mempty
        , parent = Decorate \w -> [whamlet|<div .form-group>^{w}|]
        }
      Input
        { enctype = UrlEncoded
        , view = \a v -> do
            [whamlet|<input type="checkbox" *{a} value="1" :v == Right True:checked>|]
        , parse = \myEnv _ -> pure case myEnv of
            [] -> Right False
            ["1"] -> Right True
            [_] -> Right False
            env -> Left (msgInvalidEntries env)
        }
      (addClass "form-check-input" attrs)
      value

fileInput ::
  forall shape app.
  ( KnownShape shape
  , RenderMessage app FormMessage
  ) =>
  Maybe Text ->
  Attrs ->
  FormFor app (FormInput app (Select shape FileInfo))
fileInput l attrs = pure do
  designInput
    Design
      { label =
          Label
            (Just (fromMaybe "Choose file" l, LabelAfter))
            [("class", "custom-file-label")]
            mempty
      , before = mempty
      , self = mempty
      , after = mempty
      , parent = Decorate \w -> [whamlet|<div .custom-file>^{w}|]
      }
    Input
      { enctype = Multipart
      , view = \a _ -> do
          let Const s = shapeAttrs @shape
          -- addScriptEither urlBootstrapCustomFileInputJs
          toWidget [julius|$(document).ready(function() {bsCustomFileInput.init();});|]
          [whamlet|<input *{s <> a} type="file">|]
      , parse = \_ files -> pure $ case shapeS @shape of
          OmitS -> case files of
            [] -> Right Nothing
            (i : _) -> Right (Just i)
          NeedS -> case files of
            [] -> Left (SomeMessage MsgValueRequired)
            (i : _) -> Right (Identity i)
          ManyS -> case files of
            [] -> Left (SomeMessage MsgValueRequired)
            (i : is) -> Right (i :| is)
          FreeS -> Right files
      }
    (addClass "custom-file-input" attrs)
    undefined

instance (RenderMessage app FormMessage) => Entry app (Maybe FileInfo) where
  type EntryAuxiliary app _ = ()
  entry' () l attrs _ = Compose $ fileInput l attrs
instance (RenderMessage app FormMessage) => Entry app FileInfo where
  type EntryAuxiliary app _ = ()
  entry' () l attrs _ = Compose $ invmap runIdentity Identity <$> fileInput l attrs
instance (RenderMessage app FormMessage) => Entry app (NonEmpty FileInfo) where
  type EntryAuxiliary app _ = ()
  entry' () l attrs _ = Compose $ fileInput l attrs
instance (RenderMessage app FormMessage) => Entry app [FileInfo] where
  type EntryAuxiliary app _ = ()
  entry' () l attrs _ = Compose $ fileInput l attrs

-- dateEntry ::
--   forall shape app.
--   (KnownShape shape, RenderMessage app FormMessage, YesodBootstrapDatepicker app) =>
--   Maybe Text ->
--   Attrs ->
--   Select shape Day ->
--   FormFor app (FormInput app (Select shape Day))
-- dateEntry l attrs0 value = do
--   (ident, attrs) <- requireAttr "id" newIdent do
--     [ ("data-date-clear-btn", "1")
--       , ("data-date-autoclose", "1")
--       , ("data-date-today-btn", "linked")
--       , ("data-date-format", "mm/dd/yyyy")
--       , ("data-date-today-highlight", "true")
--       ]
--       <> attrs0
--   let multidate :: Bool = case shapeS @shape of
--         OmitS -> False
--         NeedS -> False
--         ManyS -> True
--         FreeS -> True
--   pure $
--     designInput
--       (simpleLabel LabelBefore l)
--       Input
--         { enctype = UrlEncoded
--         , view = \a v -> do
--             let Const s = shapeAttrs @shape
--                 val :: Text = flip (either (const "")) v case shapeS @shape of
--                   OmitS -> maybe "" mdy
--                   NeedS -> mdy . runIdentity
--                   ManyS -> Text.intercalate "," . map mdy . toList
--                   FreeS -> Text.intercalate "," . map mdy
--             addBootstrapDatepicker
--             toWidget
--               [julius|$("##{rawJS ident}").datepicker({multidate: #{toJSON multidate}});|]
--             [whamlet|<input type="date" *{s <> a} value="#{val}">|]
--         , parse = \myEnv _ -> pure case shapeS @shape of
--             OmitS -> parse0With (parseMdy . pack) myEnv
--             NeedS -> parse1With (fmap Identity . parseMdy . pack) myEnv
--             ManyS -> case nonEmpty $ foldMap (Text.splitOn ",") myEnv of
--               Nothing -> Left (SomeMessage MsgValueRequired)
--               Just env -> for env \e -> maybe (Left $ SomeMessage (MsgInvalidEntry e)) Right (parseMdy e)
--             FreeS -> for (foldMap (Text.splitOn ",") myEnv) \e -> maybe (Left $ SomeMessage (MsgInvalidEntry e)) Right (parseMdy e)
--         }
--       attrs
--       value

-- instance (RenderMessage app FormMessage) => Entry app Day where
--   type EntryAuxiliary app _ = ()
--   entry' () l attrs value = Compose $ invmap runIdentity Identity <$> dateEntry l attrs (Identity value)

-- instance
--   (RenderMessage app FormMessage) =>
--   Entry app (Maybe Day)
--   where
--   type EntryAuxiliary app _ = ()
--   entry' () l attrs value = Compose $ dateEntry l attrs value

-- instance
--   (RenderMessage app FormMessage) =>
--   Entry app (NonEmpty Day)
--   where
--   type EntryAuxiliary app _ = ()
--   entry' () l attrs value = Compose $ dateEntry l attrs value

-- instance (RenderMessage app FormMessage) => Entry app [Day] where
--   type EntryAuxiliary app _ = ()
--   entry' () l attrs value = Compose $ dateEntry l attrs value

timeInput ::
  forall shape app.
  (KnownShape shape, SingleShape shape, RenderMessage app FormMessage) =>
  Input app (Select shape TimeOfDay)
timeInput =
  Input
    { enctype = UrlEncoded
    , view = \a v -> do
        let Const s = shapeAttrs @shape
            val :: Text = flip (either (const "")) v case shapeS @shape of
              OmitS -> maybe "" (fmtdef "%R")
              NeedS -> fmtdef "%R" . runIdentity
        [whamlet|<input type="time" *{s <> a} value="#{val}">|]
    , parse = \myEnv _ -> pure case shapeS @shape of
        OmitS -> parse0With (prsdef "%R" . Text.pack) myEnv
        NeedS -> parse1With (fmap Identity . prsdef "%R" . Text.pack) myEnv
    }

instance (RenderMessage app FormMessage) => Entry app TimeOfDay where
  type EntryAuxiliary app _ = ()
  entry' () l attrs value = Compose $ pure do
    designInput
      (asteriskLabel LabelBefore l)
      (invmap runIdentity Identity timeInput)
      attrs
      value

instance (RenderMessage app FormMessage) => Entry app (Maybe TimeOfDay) where
  type EntryAuxiliary app _ = ()
  entry' () l attrs value = Compose $ pure do
    designInput (simpleLabel LabelBefore l) timeInput attrs value

-- instance
--   (RenderMessage app FormMessage) =>
--   Entry app LocalTime
--   where
--   type EntryAuxiliary app _ = ()
--   entry' () l attrs value = Compose do
--     date <- getCompose $ entry Nothing attrs value.localDay
--     time <- getCompose $ entry Nothing attrs value.localTimeOfDay
--     pure $ case (date, time) of
--       (FormInput dateD dateE _ _, FormInput timeD timeE _ _) ->
--         designInput
--           Design
--             { label = Label ((,LabelBefore) <$> l) [] mempty
--             , before = mempty
--             , self = Decorate \w -> [whamlet|<div>^{w}|]
--             , after = mempty
--             , parent = mempty
--             }
--           Input
--             { enctype = dateE.enctype <> timeE.enctype
--             , view = \a v -> do
--                 dateD.decorate $ dateE.view a (fmap localDay v)
--                 timeD.decorate $ timeE.view a (fmap localTimeOfDay v)
--             , parse = \myEnv _ -> pure case myEnv of
--                 [d, t] -> maybe (Left . SomeMessage $ MsgInvalidDatetimeFormat (d <> t)) Right do
--                   localDay <- prsdef "%m/%d/%Y" d
--                   localTimeOfDay <- prsdef "%R" t
--                   pure LocalTime{..}
--                 _ -> Left (msgInvalidEntries myEnv)
--             }
--           attrs
--           value

type Number n = (Eq n, Num n, Read n, Show n)

integralInput ::
  forall shape n app.
  ( KnownShape shape
  , SingleShape shape
  , RenderMessage app FormMessage
  , Number n
  , Integral n
  ) =>
  Maybe (WidgetFor app ()) ->
  Maybe Text ->
  Attrs ->
  Maybe (Select shape n) ->
  FormInput app (Select shape n)
integralInput pre l attrs value =
  designInput
    case pre of
      Nothing -> simpleLabel LabelBefore l
      Just before ->
        (simpleLabel LabelBefore l)
          { before
          , self = Decorate \w -> [whamlet|<div .input-group>^{w}|]
          }
    Input
      { enctype = UrlEncoded
      , view = \a v -> do
          let Const s = shapeAttrs @shape
              val :: String = flip (either (const "")) v case shapeS @shape of
                OmitS -> maybe "" show
                NeedS -> show . runIdentity
          [whamlet|<input type="number" *{s <> a} value="#{val}">|]
      , parse = \myEnv _ -> pure case shapeS @shape of
          OmitS ->
            parse0WithNum
              (either (const Nothing) (Just . fst) . Text.signed Text.decimal)
              myEnv
          NeedS ->
            parse1WithNum
              (either (const Nothing) (Just . fst) . Text.signed Text.decimal)
              myEnv
      }
    attrs
    value

doubleInput ::
  forall shape app.
  ( KnownShape shape
  , SingleShape shape
  , RenderMessage app FormMessage
  ) =>
  Maybe (WidgetFor app ()) ->
  Maybe Text ->
  Attrs ->
  Maybe (Select shape Double) ->
  FormInput app (Select shape Double)
doubleInput pre l attrs value =
  designInput
    case pre of
      Nothing -> simpleLabel LabelBefore l
      Just before ->
        (simpleLabel LabelBefore l)
          { before
          , self = Decorate \w -> [whamlet|<div .input-group>^{w}|]
          }
    Input
      { enctype = UrlEncoded
      , view = \a v -> do
          let Const s = shapeAttrs @shape
              val :: String = flip (either (const "")) v case shapeS @shape of
                OmitS -> maybe "" show
                NeedS -> show . runIdentity
          [whamlet|<input type="number" *{s <> a} value="#{val}">|]
      , parse = \myEnv _ -> pure case shapeS @shape of
          OmitS ->
            parse0WithNum
              (either (const Nothing) (Just . fst) . Text.signed Text.double)
              myEnv
          NeedS ->
            parse1WithNum
              (either (const Nothing) (Just . Identity . fst) . Text.signed Text.double)
              myEnv
      }
    attrs
    value

instance (RenderMessage app FormMessage) => Entry app (Maybe Int) where
  type EntryAuxiliary app _ = ()
  entry' () l attrs val = Compose $ pure (integralInput Nothing l attrs val)
instance (RenderMessage app FormMessage) => Entry app Int where
  type EntryAuxiliary app _ = ()
  entry' () l attrs val = Compose $ pure do
    invmap runIdentity Identity $ integralInput Nothing l attrs (fmap Identity val)

instance (RenderMessage app FormMessage) => Entry app (Maybe Integer) where
  type EntryAuxiliary app _ = ()
  entry' () l attrs val = Compose $ pure (integralInput Nothing l attrs val)
instance (RenderMessage app FormMessage) => Entry app Integer where
  type EntryAuxiliary app _ = ()
  entry' () l attrs val = Compose $ pure do
    invmap runIdentity Identity $ integralInput Nothing l attrs (fmap Identity val)

instance (RenderMessage app FormMessage) => Entry app (Maybe Natural) where
  type EntryAuxiliary app _ = ()
  entry' () l attrs val = Compose $ pure (integralInput Nothing l attrs val)
instance (RenderMessage app FormMessage) => Entry app Natural where
  type EntryAuxiliary app _ = ()
  entry' () l attrs val = Compose $ pure do
    invmap runIdentity Identity $ integralInput Nothing l attrs (fmap Identity val)

instance (RenderMessage app FormMessage) => Entry app (Maybe Double) where
  type EntryAuxiliary app _ = ()
  entry' () l attrs val = Compose $ pure (doubleInput Nothing l attrs val)
instance (RenderMessage app FormMessage) => Entry app Double where
  type EntryAuxiliary app _ = ()
  entry' () l attrs val = Compose $ pure do
    invmap runIdentity Identity $ doubleInput Nothing l attrs (fmap Identity val)

instance (RenderMessage app FormMessage) => Entry app Text where
  type EntryAuxiliary app _ = ()
  entry' () l attrs value = Compose $ pure do
    designInput
      (simpleLabel LabelBefore l)
      Input
        { enctype = UrlEncoded
        , view = \a v -> do
            [whamlet|<input type="text" *{a} value="#{either (const "") id v}">|]
        , parse = \myEnv _ -> pure case myEnv of
            [] -> Right ""
            [x] -> Right x
            env -> Left (msgInvalidEntries env)
        }
      attrs
      value

instance (RenderMessage app FormMessage) => Entry app Textarea where
  type EntryAuxiliary app _ = ()
  entry' () l attrs value = Compose $ pure do
    designInput
      (simpleLabel LabelBefore l)
      Input
        { enctype = UrlEncoded
        , view = \a v -> do
            [whamlet|<input type="textarea" *{a}>#{either (const $ Textarea "") id v}|]
        , parse = \myEnv _ -> pure case myEnv of
            [] -> Right (Textarea "")
            [x] -> Right (Textarea x)
            env -> Left (msgInvalidEntries env)
        }
      attrs
      value
