# yesod-form-shape

This library provides an alternative way to working with input forms in [Yesod](https://www.yesodweb.com/book),
and utilities for creating forms for `Record` types based on their `Field`s (à la [`prairie`](https://github.com/parsonsmatt/prairie)). The following toy example demonstrates `Prairie` and `Yesod.Form.Shape` used synergistically to create a MadLibs-style sentence.

```hs
{-# LANGUAGE UndecidableInstances #-} -- for mkRecord

module Handler.ShapeTest where

import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Invariant
import Data.Text qualified as Text
import Foundation
import Prairie
import Yesod
import Yesod.Form.Shape
import Prelude

tshow :: (Show a) => a -> Text.Text
tshow = Text.pack . show

data Animal = Chicken | Horse | Zebra | Cat | Dog | Hamster
  deriving (Eq, Ord, Enum, Show, Read)
instance ToOption Animal where
  toOption x = Option (tshow x) x (Text.toLower $ tshow x)
instance Entry App Animal where
  -- more complicated entries may require additional information
  -- before creation, e.g. some of the GET or POST parameters
  type EntryAuxiliary App Animal = ()
  entry' () l attrs value = Compose $ pure do
    -- more complicated entries may perform Handler actions before the `pure`,
    -- like getting option lists from a database, or checking a cookie or cache
    designInput
      (simpleLabel LabelBefore l)
      (invmap runIdentity Identity $ select @Need (toOptions [Chicken .. Hamster]))
      attrs
      value

data Verb = Jump | Look | Crawl | Dance deriving (Eq, Ord, Enum, Show, Read)
instance ToOption Verb where
  toOption x = Option (tshow x) x (Text.toLower $ tshow x)
instance Entry App Verb where
  type EntryAuxiliary App Verb = ()
  entry' () l attrs value = Compose $ pure do
    designInput
      (simpleLabel LabelBefore l)
      (invmap runIdentity Identity $ select @Need (toOptions [Jump .. Dance]))
      attrs
      value

data MadLibs = MadLibs
  { animal1 :: Animal
  , animal2 :: Animal
  , verb1 :: Verb
  , count1 :: Int
  , count2 :: Maybe Int
  }
  deriving (Show)
mkRecord ''MadLibs

-- describe the entries of the form for each field individually
madLibsForm :: FormFor App (FormResult MadLibs, Cases MadLibs (Const Widget))
madLibsForm = recordFormM $ Cases \case
  MadLibsAnimal1 -> entry Nothing [("name", "animal1")] Chicken
  MadLibsAnimal2 -> entry Nothing [("name", "animal2")] Hamster
  MadLibsVerb1 -> entry Nothing [("name", "verb1")] Jump
  MadLibsCount1 ->
    entry
      Nothing
      [ ("name", "count1")
      , ("min", "1")
      , ("style", "width: 3em")
      ]
      1
  MadLibsCount2 ->
    entry
      Nothing
      [ ("name", "count2")
      , ("min", "1")
      , ("style", "width: 3em")
      ]
      Nothing

getShapeTestR :: Handler Html
getShapeTestR = postShapeTestR

postShapeTestR :: Handler Html
postShapeTestR = do
  ((formResult, formWidget), enctype) <- Yesod.Form.Shape.runFormPost \csrf -> do
    (result, Cases widget) <- madLibsForm
    pure
      ( result
      , do
          toWidget csrf
          -- stitch together all the widget cases
          [whamlet|
            <div>
              The ^{getConst $ widget MadLibsAnimal1} and the ^{getConst $ widget MadLibsAnimal2} ^{getConst $ widget MadLibsVerb1} high above the moon.
              They also count ^{getConst $ widget MadLibsCount1} stars and ^{getConst $ widget MadLibsCount2} planets.
            <button type="submit">
              Go!
          |]
      )
  defaultLayout do
    setTitle [shamlet|Shape test|]
    [whamlet|
      <div>
        #{show formResult}
        <form enctype="#{enctype}" method="POST">
          ^{formWidget}
    |]
```
