from ..lang import Read
from ..lang import Show
from ..lang import sig
from ..lang import H
from ..lang import t
from ..lang import d
from ..lang import caseof
from ..lang import m
from ..lang import p
from ..lang import data
from ..lang import deriving
from ..lang import instance
from ..lang import L
from ..lang import typify

from Eq import Eq
from Ord import Ord
from Functor import Functor
from ..Control.Applicative import Applicative
from ..Control.Monad import Monad


# data Either a b = Left b | Right a deriving(Read, Show, Eq, Ord)
Either, Left, Right =\
data.Either("a", "b") == d.Left("a") | d.Right("b") \
                       & deriving(Read, Show, Eq, Ord)


instance(Functor, Either).where(
    fmap = lambda f, v: ~(caseof(v)
                            | m(Left(m.e))  >> Left(p.e)
                            | m(Right(m.ra)) >> Right(f(p.ra)))
)

instance(Applicative, Either).where(
    pure = Right
)

instance(Monad, Either).where(
    bind = lambda v, f: ~(caseof(v)
                            | m(Left(m.e))  >> Left(p.e)
                            | m(Right(m.a)) >> f(p.a))
)


def in_either(fn):
    """
    Decorator for monadic error handling.
    If the decorated function raises an exception, return the exception inside
    Left. Otherwise, take the result and wrap it in Right.
    """
    def closure_in_either(*args, **kwargs):
        try:
            return Right(fn(*args, **kwargs))
        except Exception as e:
            return Left(e)
    return typify(fn, hkt=lambda x: t(Either, "aa", x))(closure_in_either)


@sig(H/ (H/ "a" >> "c") >> (H/ "b" >> "c") >> t(Either, "a", "b") >> "c")
def either(fa, fb, e):
    """
    either :: (a -> c) -> (b -> c) -> Either a b -> c

    Case analysis for the Either type. If the value is Left(a), apply the first
    function to a; if it is Right(b), apply the second function to b.
    """
    return ~(caseof(e)
                | m(Left(m.a))  >> fa(p.a)
                | m(Right(m.b)) >> fb(p.b))


@sig(H/ [t(Either, "a", "b")] >> ["a"])
def lefts(xs):
    """
    lefts :: [Either a b] -> [a]

    Extracts from a List of Either all the Left elements. All the Left elements
    are extracted in order.
    """
    return L[(x[0] for x in xs if isLeft(x))]


@sig(H/ [t(Either, "a", "b")] >> ["b"])
def rights(xs):
    """
    rights :: [Either a b] -> [b]

    Extracts from a list of Either all the Right elements. All the Right
    elements are extracted in order.
    """
    return L[(x[0] for x in xs if isRight(x))]


@sig(H/ t(Either, "a", "b") >> bool)
def isLeft(x):
    """
    isLeft :: Either a b -> bool

    Return True if the given value is a Left-value, False otherwise.
    """
    return ~(caseof(x)
                | m(Right(m.x)) >> False
                | m(Left(m.x))  >> True)


@sig(H/ t(Either, "a", "b") >> bool)
def isRight(x):
    """
    isRight :: Either a b -> bool

    Return True if the given value is a Right-value, False otherwise.
    """
    return not isLeft(x)


@sig(H/ [t(Either, "a", "b")] >> (["a"], ["b"]))
def partitionEithers(xs):
    """
    partitionEithers :: [Either a b] -> ([a], [b])

    Partitions a List of Either into two lists. All the Left elements are
    extracted, in order, to the first component of the output. Similarly the
    Right elements are extracted to the second component of the output.
    """
    return (lefts(xs), rights(xs))
