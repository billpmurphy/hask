__version__ = "0.0.1"


#=============================================================================#
# Module imports


import lang
import Data.Char
import Data.Either
import Data.Eq
import Data.Foldable
import Data.Functor
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Num
import Data.Ord
import Data.Ratio
import Data.String
import Data.Traversable
import Data.Tuple
import Control.Applicative
import Control.Monad
import Python.builtins


#=============================================================================#
# Core language

## Typeclass instance declaration
from hask.lang import instance

## Operator sections
from hask.lang import __

## Guard expressions
from hask.lang import guard
from hask.lang import c
from hask.lang import otherwise
from hask.lang import NoGuardMatchException

## Lists/list comprehensions
from hask.lang import L

## ADT creation
from hask.lang import data
from hask.lang import d
from hask.lang import deriving

## Type signatures
from hask.lang import sig
from hask.lang import H
from hask.lang import t
from hask.lang import func
from hask.lang import TypeSignatureError

## Pattern matching
from hask.lang import caseof
from hask.lang import p
from hask.lang import m
from hask.lang import IncompletePatternError

## REPL tools
from hask.lang import _t
from hask.lang import _i
from hask.lang import _q

## Type system/typeclasses
from hask.lang import typeof
from hask.lang import has_instance
from hask.lang import Typeclass
from hask.lang import Hask


#=============================================================================#
# Other imports

# Basic Typeclasses
from hask.Prelude import Read
from hask.Prelude import Show
from hask.Prelude import Eq
from hask.Prelude import Ord
from hask.Prelude import Enum
from hask.Prelude import Bounded
from hask.Prelude import Num
from hask.Prelude import Real
from hask.Prelude import Integral
from hask.Prelude import Fractional
from hask.Prelude import Floating
from hask.Prelude import RealFrac
from hask.Prelude import RealFloat
from hask.Prelude import Functor
from hask.Prelude import Applicative
from hask.Prelude import Monad
from hask.Prelude import Traversable
from hask.Prelude import Foldable


# Standard types
from hask.Prelude import Maybe
from hask.Prelude import Just
from hask.Prelude import Nothing
from hask.Prelude import in_maybe

from hask.Prelude import Either
from hask.Prelude import Left
from hask.Prelude import Right
from hask.Prelude import in_either

from hask.Prelude import Ordering
from hask.Prelude import LT
from hask.Prelude import EQ
from hask.Prelude import GT
