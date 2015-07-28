from ..lang import Read
from ..lang import Show
from ..lang import L
from ..lang import H
from ..lang import sig
from ..lang import t
from ..lang import data
from ..lang import d
from ..lang import caseof
from ..lang import m
from ..lang import p
from ..lang import deriving
from ..lang import instance
from ..lang import typify

from Eq import Eq
from Ord import Ord
from Functor import Functor
from ..Control.Applicative import Applicative
from ..Control.Monad import Monad


# data Maybe a = Nothing | Just a deriving(Show, Eq, Ord)
Maybe, Nothing, Just =\
    data.Maybe("a") == d.Nothing | d.Just("a") & deriving(Read, Show, Eq, Ord)

instance(Functor, Maybe).where(
    fmap = lambda f, x: ~(caseof(x)
                            | m(Just(m.a)) >> Just(f(p.a))
                            | m(Nothing)   >> Nothing)
)

instance(Applicative, Maybe).where(
    pure = Just
)

instance(Monad, Maybe).where(
    bind = lambda x, f: ~(caseof(x)
                            | m(Just(m.a)) >> f(p.a)
                            | m(Nothing)   >> Nothing)
)


def in_maybe(fn):
    """
    Decorator for monadic error handling.

    If the decorated function raises an exception, return Nothing. Otherwise,
    take the result and wrap it in a Just.
    """
    def closure_in_maybe(*args, **kwargs):
        try:
            return Just(fn(*args, **kwargs))
        except:
            return Nothing
    return typify(fn, hkt=lambda x: t(Maybe, x))(closure_in_maybe)


@sig(H/ "b" >> (H/ "a" >> "b") >> t(Maybe, "a") >> "b")
def maybe(default, f, maybe_a):
    """
    maybe :: b -> (a -> b) -> Maybe a -> b

    The maybe function takes a default value, a function, and a Maybe value. If
    the Maybe value is Nothing, the function returns the default value.
    Otherwise, it applies the function to the value inside the Just and returns
    the result.
    """
    return default if maybe_a == Nothing else f(maybe_a[0])


@sig(H/ t(Maybe, "a") >> bool)
def isJust(a):
    return not isNothing(a)


@sig(H/ t(Maybe, "a")  >> bool)
def isNothing(a):
    return ~(caseof(a)
                | m(Nothing)   >> True
                | m(Just(m.x)) >> False)


@sig(H/ t(Maybe, "a") >> "a")
def fromJust(x):
    if isJust(x):
        return x[0]
    raise ValueError("Cannot call fromJust on Nothing.")


@sig(H/ ["a"] >> t(Maybe, "a"))
def listToMaybe(a):
    return ~(caseof(a)
                | m(m.a ^ m.b) >> Just(p.a)
                | m(m.a)       >> Nothing)


@sig(H/ t(Maybe, "a") >> ["a"])
def maybeToList(a):
    """
    maybeToList :: Maybe a -> [a]

    The maybeToList function returns an empty list when given Nothing or a
    singleton list when not given Nothing.
    """
    return ~(caseof(a)
                | m(Nothing)   >> L[[]]
                | m(Just(m.x)) >> L[[p.x]])


@sig(H/ [t(Maybe, "a")] >> ["a"])
def catMaybes(a):
    """
    catMaybes :: [Maybe a] -> [a]

    The catMaybes function takes a list of Maybes and returns a list of all the
    Just values.
    """
    return L[(fromJust(item) for item in a if isJust(item))]


@sig(H/ (H/ "a" >> t(Maybe, "b")) >> ["a"] >> ["b"])
def mapMaybe(f, la):
    """
    mapMaybe :: (a -> Maybe b) -> [a] -> [b]

    The mapMaybe function is a version of map which can throw out elements. In
    particular, the functional argument returns something of type Maybe b. If
    this is Nothing, no element is added on to the result list. If it is Just
    b, then b is included in the result list.
    """
    return L[(fromJust(b) for b in (f(a) for a in la) if isJust(b))]
