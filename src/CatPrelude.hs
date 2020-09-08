-- | Custom Category-Prelude

module CatPrelude (
    module Prelude
  , module Misc
  , module Category
  , module Data.Distributive
  , module Data.Functor.Rep
  , module GHC.Generics
  , module GHC.Types
  , module Control.Newtype.Generics
  ) where

import Prelude hiding ((*), (+), id, (.), product, sum, unzip, curry, uncurry)

import Misc
import Category

import Control.Newtype.Generics (Newtype(..))
import Data.Distributive
import Data.Functor.Rep
import GHC.Generics ((:*:)(..), (:+:)(..), (:.:)(..), Generic, Generic1, Par1(..), U1(..))
import GHC.Types (Constraint)
