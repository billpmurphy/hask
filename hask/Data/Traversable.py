from ..lang import build_instance
from ..lang import sig
from ..lang import H
from ..lang import t
from ..Control.Applicative import Applicative
from ..Control.Monad import Monad
from Foldable import Foldable
from Functor import Functor


class Traversable(Foldable, Functor):
    """
    Functors representing data structures that can be traversed from left to
    right.

    Dependencies:
        Foldable, Functor

    Attributes:
        traverse, sequenceA, mapM, sequence

    Minimal complete definition:
        traverse
    """
    @classmethod
    def make_instance(typeclass, cls, traverse, sequenceA=None, mapM=None,
                      sequence=None):
        attrs = {"traverse":traverse, "sequenceA":sequenceA, "mapM":mapM,
                 "sequence":sequence}
        build_instance(Traversable, cls, attrs)
        return


@sig(H[(Applicative, "f"), (Traversable, "t")]/
        (H/ "a" >> t("f", "b")) >> t("t", "a") >> t("f", t("t", "b")))
def traverse(f, t):
    """
    traverse :: (Traversable t, Applicative f) => (a -> f b) -> t a -> f (t b)

    Map each element of a structure to an action, evaluate these these actions
    from left to right, and collect the results. actions from left to right,
    and collect the results. For a version that ignores the results see
    traverse_.
    """
    return Traversable[t].traverse(f, t)


@sig(H[(Applicative, "f"), (Traversable, "t")]/
        t("t", t("f", "a")) >> t("f", t("t", "a")))
def sequenceA(t):
    """
    sequenceA :: (Traversable t, Applicative f) => t (f a) -> f (t a)

    Evaluate each action in the structure from left to right, and and collect
    the results. For a version that ignores the results see sequenceA_.
    """
    return Traversable[t].sequenceA(t)


@sig(H[(Monad, "m"), (Traversable, "t")]/
        (H/ "a" >> t("m", "b")) >> t("t", "a") >> t("m", t("t", "b")))
def mapM(f, m):
    """
    mapM :: (Traversable t, Monad m) => (a -> m b) -> t a -> m (t b)

    Map each element of a structure to a monadic action, evaluate these actions
    from left to right, and collect the results. For a version that ignores the
    results see mapM_.
    """
    return Traversable[t].mapM(f, t)


@sig(H[(Monad, "m"), (Traversable, "t")]/
        t("t", t("m", "a")) >> t("m", t("t", "a")))
def sequence(t):
    """
    sequence :: (Traversable t, Monad m) => t (m a) -> m (t a)

    Evaluate each monadic action in the structure from left to right, and
    collect the results. For a version that ignores the results see sequence_.
    """
    return Traversable[t].sequence(t)


#=============================================================================#
# Utility functions


@sig(H[(Applicative, "f"), (Traversable, "t")]/
        t("t", "a") >> (H/ "a" >> t("f", "b")) >> t("f", t("t", "b")))
def for1(t, f):
    """
    for1 :: (Traversable t, Applicative f) => t a -> (a -> f b) -> f (t b)

    for1 is traverse with its arguments flipped. For a version that ignores the
    results see for1_.
    """
    return traverse(f, t)


@sig(H[(Monad, "m"), (Traversable, "t")]/
        t("t", "a") >> (H/ "a" >> t("m", "b")) >> t("m", t("t", "b")))
def forM(t, f):
    """
    forM :: (Traversable t, Monad m) => t a -> (a -> m b) -> m (t b)

    forM is mapM with its arguments flipped. For a version that ignores the
    results see forM_.
    """
    return mapM(f, t)


@sig(H[(Traversable, "t")]/ (H/ "a" >> "b" >> ("a", "c")) >> "a" >> t("t", "b")
        >> ("a", t("t", "c")))
def mapAccumL(f, a, tb):
    """
    mapAccumL :: Traversable t => (a -> b -> (a, c)) -> a -> t b -> (a, t c)

    The mapAccumL function behaves like a combination of fmap and foldl; it
    applies a function to each element of a structure, passing an accumulating
    parameter from left to right, and returning a final value of this
    accumulator together with the new structure.
    """
    raise NotImplementedError()


@sig(H[(Traversable, "t")]/ (H/ "a" >> "b" >> ("a", "c")) >> "a" >> t("t", "b")
        >> ("a", t("t", "c")))
def mapAccumR(f, a, tb):
    """
    mapAccumR :: Traversable t => (a -> b -> (a, c)) -> a -> t b -> (a, t c)

    The mapAccumR function behaves like a combination of fmap and foldr; it
    applies a function to each element of a structure, passing an accumulating
    parameter from right to left, and returning a final value of this
    accumulator together with the new structure.
    """
    raise NotImplementedError()
