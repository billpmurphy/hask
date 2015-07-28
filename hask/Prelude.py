import fractions

from .lang import H
from .lang import sig
from .lang import t


#=============================================================================#
# Standard types, classes, and related functions
## Basic data types


from Data.Maybe import Maybe
from Data.Maybe import Just
from Data.Maybe import Nothing
from Data.Maybe import in_maybe
from Data.Maybe import maybe

from Data.Either import Either
from Data.Either import Left
from Data.Either import Right
from Data.Either import in_either
from Data.Either import either

from Data.Ord import Ordering
from Data.Ord import LT
from Data.Ord import EQ
from Data.Ord import GT


#=============================================================================#
### Tuples


from Data.Tuple import fst
from Data.Tuple import snd
from Data.Tuple import curry
from Data.Tuple import uncurry


#=============================================================================#
## Basic type classes


from .lang import Read
from .lang import Show
from .lang import show

from Data.Eq import Eq
from Data.Ord import Ord
from Data.Ord import max
from Data.Ord import min
from Data.Ord import compare

from .lang import Enum
from .lang import fromEnum
from .lang import succ
from .lang import pred
from .lang import enumFromThen
from .lang import enumFrom
from .lang import enumFromThenTo
from .lang import enumFromTo

from .lang import Bounded
from Data.Functor import Functor
from Data.Functor import fmap

from Control.Applicative import Applicative
from Control.Monad import Monad
from Data.Foldable import Foldable
from Data.Traversable import Traversable


#=============================================================================#
# Numbers
### Numeric type classes


from Data.Num import Num
from Data.Num import abs
from Data.Num import negate
from Data.Num import signum

from Data.Num import Fractional
from Data.Num import recip

from Data.Num import Integral
from Data.Num import toRatio

from Data.Num import Ratio
from Data.Num import R
from Data.Num import Rational

from Data.Num import Floating
from Data.Num import exp
from Data.Num import sqrt
from Data.Num import log
from Data.Num import pow
from Data.Num import logBase
from Data.Num import sin
from Data.Num import tan
from Data.Num import cos
from Data.Num import asin
from Data.Num import atan
from Data.Num import acos
from Data.Num import sinh
from Data.Num import tanh
from Data.Num import cosh
from Data.Num import asinh
from Data.Num import atanh
from Data.Num import acosh

from Data.Num import Real
from Data.Num import toRational

from Data.Num import RealFrac
from Data.Num import properFraction
from Data.Num import truncate
from Data.Num import round
from Data.Num import ceiling
from Data.Num import floor

from Data.Num import RealFloat
from Data.Num import isNaN
from Data.Num import isInfinite
from Data.Num import isNegativeZero
from Data.Num import atan2


#=============================================================================#
# Numeric functions


@sig(H[(Num, "a")]/ "a" >> "a" >> "a")
def subtract(x, y):
    """
    subtract :: Num a => a -> a -> a

    the same as lambda x, y: y - x
    """
    return y - x


@sig(H[(Integral, "a")]/ "a" >> bool)
def even(x):
    """
    even :: Integral a => a -> Bool

    Returns True if the integral value is even, and False otherwise.
    """
    return x % 2 == 0


@sig(H[(Integral, "a")]/ "a" >> bool)
def odd(x):
    """
    odd :: Integral a => a -> Bool

    Returns True if the integral value is odd, and False otherwise.
    """
    return x % 2 == 1


@sig(H[(Integral, "a")]/ "a" >> "a" >> "a")
def gcd(x, y):
    """
    gcd :: Integral a => a -> a -> a

    gcd(x,y) is the non-negative factor of both x and y of which every common
    factor of x and y is also a factor; for example gcd(4,2) = 2, gcd(-4,6) =
    2, gcd(0,4) = 4. gcd(0,0) = 0. (That is, the common divisor that is
    "greatest" in the divisibility preordering.)
    """
    return fractions.gcd(x, y)


@sig(H[(Integral, "a")]/ "a" >> "a" >> "a")
def lcm(x, y):
    """
    lcm :: Integral a => a -> a -> a

    lcm(x,y) is the smallest positive integer that both x and y divide.
    """
    g = gcd(x, y)
    return 0 if g == 0 else (x * y) / g


#=============================================================================#
# Monads and functors


from Data.Functor import Functor
from Control.Applicative import Applicative
from Control.Monad import Monad


@sig(H[(Monad, "m")]/ t("m", "a") >> t("m", None))
def sequence(xs):
    """
    sequence :: Monad m => [m a] -> m [a]

    Evaluate each action in the sequence from left to right, and collect the
    results.
    """
    raise NotImplementedError()


@sig(H[(Monad, "m")]/ t("m", "a") >> t("m", None))
def sequence_(xs):
    """
    sequence_ :: Monad m => [m a] -> m None

    Evaluate each action in the sequence from left to right, and ignore the
    results.
    """
    raise NotImplementedError()


def mapM(f, xs):
    """
    mapM :: Monad m => (a -> m b) -> [a] -> m [b]

    mapM(f) is equivalent to sequence * map(f)
    """
    return sequence(fmap(f, xs))


def mapM_(f, xs):
    """
    mapM_ :: Monad m => (a -> m b) -> [a] -> m ()

    mapM_(f) is equivalent to sequence_ * map(f)
    """
    return sequence_(fmap(f, xs))




#=============================================================================#
# Miscellaneous functions


@sig(H/ "a" >> "a")
def id(a):
    """
    id :: a -> a

    Identity function.
    """
    return a


@sig(H/ "a" >> "b" >> "a")
def const(a, b):
    """
    const :: a -> b -> a

    Constant function.
    """
    return a


@sig(H/ (H/ "a" >> "b" >> "c") >> "b" >> "a" >> "c")
def flip(f, b, a):
    """
    flip :: (a -> b -> c) -> b -> a -> c

    flip(f) takes its (first) two arguments in the reverse order of f.
    """
    return f(a, b)


@sig(H/ (H/ "a" >> bool) >> (H/ "a" >> "a") >> "a" >> "a")
def until(p, f, a):
    """
    until :: (a -> Bool) -> (a -> a) -> a -> a

    until(p, f, a) yields the result of applying f until p(a) holds.
    """
    while not p(a):
        a = f(a)
    return a


@sig(H/ "a" >> "a" >> "a")
def asTypeOf(a, b):
    """
    asTypeOf :: a -> a -> a

    asTypeOf is a type-restricted version of const. It is usually used as an
    infix operator, and its typing forces its first argument (which is usually
    overloaded) to have the same type as the second.
    """
    return a


@sig(H/ str >> "a")
def error(msg):
    """
    error :: str -> a

    error(msg) stops execution and displays an error message.
    """
    raise Exception(msg)


from .lang import undefined


#=============================================================================#
# List operations

from Data.List import map
from Data.List import filter
from Data.List import head
from Data.List import last
from Data.List import tail
from Data.List import init
from Data.List import null
from Data.List import reverse
from Data.List import length

from Data.List import foldl
from Data.List import foldl1
from Data.List import foldr
from Data.List import foldr1


#=============================================================================#
## Special folds

from Data.List import and_
from Data.List import or_
from Data.List import any
from Data.List import all
from Data.List import sum
from Data.List import product
from Data.List import concat
from Data.List import concatMap
from Data.List import maximum
from Data.List import minimum


#=============================================================================#
## Building lists
### Scans

from Data.List import scanl
from Data.List import scanl1
from Data.List import scanr
from Data.List import scanr1


#=============================================================================#
### Infinite lists

from Data.List import iterate
from Data.List import repeat
from Data.List import replicate
from Data.List import cycle


#=============================================================================#
## Sublists

from Data.List import take
from Data.List import drop
from Data.List import splitAt
from Data.List import takeWhile
from Data.List import dropWhile
from Data.List import span
from Data.List import break_


#=============================================================================#
## Searching lists

from Data.List import elem
from Data.List import notElem
from Data.List import lookup


#=============================================================================#
## Zipping and unzipping lists

from Data.List import zip
from Data.List import zip3
from Data.List import zipWith
from Data.List import zipWith3
from Data.List import unzip
from Data.List import unzip3


#=============================================================================#
## Functions on strings

from Data.List import lines
from Data.List import words
from Data.List import unlines
from Data.List import unwords
