import functools
import operator

from ..lang import sig
from ..lang import H
from ..lang import t
from ..lang import Typeclass
from ..lang import build_instance
from ..lang import List
from ..lang import Ord

import List
from ..Control.Applicative import Applicative
from ..Control.Monad import Monad
from Eq import Eq
from Num import Num
from Maybe import Maybe
from Ord import Ordering


class Foldable(Typeclass):
    """
    Data structures that can be folded.

    Attributes:
        foldr, foldr1, foldl, foldl_, foldl1, foldl1_, toList, null, length,
        elem, maximum, minimum, sum, product

    Minimal complete definition:
        foldr
    """
    @classmethod
    def make_instance(typeclass, cls, foldr, foldr1=None, foldl=None,
            foldl_=None, foldl1=None, toList=None, null=None, length=None,
            elem=None, maximum=None, minumum=None, sum=None, product=None):

        attrs = {"foldr":foldr, "foldr1":foldr1, "foldl":foldl,
                "foldl_":foldl_, "foldl1":foldl1, "foldl1_":foldl1_,
                "toList":toList, "null":null, "length":length, "elem":elem,
                "maximum":maximum, "minimum":minimum, "sum":sum,
                "product":product}
        build_instance(Foldable, cls, attrs)
        return


@sig(H[(Foldable, "t")]/ (H/ "a" >> "b" >> "b") >> "b" >> t("t", "a") >> "b")
def foldr(f, z, t):
    """
    foldr :: Foldable t => (a -> b -> b) -> b -> t a -> b

    Right-associative fold of a structure.
    """
    return Foldable[t].foldr(f, z, t)


@sig(H[(Foldable, "t")]/ (H/ "a" >> "a" >> "a") >> t("t", "a") >> "a")
def foldr1(f, t):
    """
    foldr1 :: Foldable t => (a -> a -> a) -> t a -> a

    A variant of foldr that has no base case, and thus may only be applied to
    non-empty structures.
    """
    return Foldable[t].foldr(f, t)


@sig(H[(Foldable, "t")]/ (H/ "a" >> "a" >> "b") >> "b" >> t("t", "a") >> "b")
def foldl(f, z, t):
    """
    foldl :: Foldable t => (b -> a -> b) -> b -> t a -> b

    Left-associative fold of a structure.
    """
    return Foldable[t].foldl(f, z, t)


@sig(H[(Foldable, "t")]/ (H/ "a" >> "a" >> "b") >> "b" >> t("t", "a") >> "b")
def foldl_(f, z, t):
    """
    foldl' :: Foldable t => (b -> a -> b) -> b -> t a -> b

    Left-associative fold of a structure. but with strict application of the
    operator.
    """
    return Foldable[t].foldl_(f, z, t)


@sig(H[(Foldable, "t")]/ (H/ "a" >> "a" >> "a") >> t("t", "a") >> "a")
def foldl1(f, t):
    """
    foldl1 :: Foldable t => (a -> a -> a) -> t a -> a

    A variant of foldl that has no base case, and thus may only be applied to
    non-empty structures.
    """
    Foldable[t].foldl1(f, t)


@sig(H[(Foldable, "t")]/ t("t", "a") >> ["a"])
def toList(t):
    """
    toList :: Foldable t => t a -> [a]

    List of elements of a structure, from left to right.
    """
    return Foldable[t].toList(t)


@sig(H[(Foldable, "t")]/ t("t", "a") >> bool)
def null(t):
    """
    null :: Foldable t => t a -> Bool
    Source

    Test whether the structure is empty.
    """
    return Foldable[t].null(t)


@sig(H[(Foldable, "t")]/ t("t", "a") >> int)
def length(t):
    """
    length :: Foldable t => t a -> int

    Returns the size/length of a finite structure as an int.
    """
    return Foldable[t].length(t)


@sig(H[(Foldable, "t"), (Eq, "a")]/ t("t", "a") >> "a")
def elem(a, t):
    """
    elem :: (Foldable t, Eq a) => a -> t a -> bool

    Does the element occur in the structure?
    """
    return Foldable[t].elem(t)


@sig(H[(Foldable, "t"), (Ord, "a")]/ t("t", "a") >> "a")
def maximum(t):
    """
    maximum :: (Foldable t, forall a. Ord a) => t a -> a

    The largest element of a non-empty structure.
    """
    return Foldable[t].maximum(t)


@sig(H[(Foldable, "t"), (Ord, "a")]/ t("t", "a") >> "a")
def minimum(t):
    """
    minimum :: (Foldable t, forall a. Ord a) => t a -> a

    The least element of a non-empty structure.
    """
    return Foldable[t].minimum(t)


@sig(H[(Foldable, "t"), (Num, "a")]/ t("t", "a") >> "a")
def sum(t):
    """
    sum :: (Foldable t, Num a) => t a -> a

    The sum function computes the sum of the numbers of a structure.
    """
    return Foldable[t].sum(t)


@sig(H[(Foldable, "t"), (Num, "a")]/ t("t", "a") >> "a")
def product(t):
    """
    product :: (Foldablet, Num a) => t a -> a

    The product function computes the product of the numbers of a structure.
    """
    return Foldable[t].product(t)


#=============================================================================#
# Special biased folds


@sig(H[(Foldable, "t"), (Monad, "m")]/ (H/ "a" >> "b" >> t("m", "b")) >>
    "b" >> t("t", "a") >> t("m", "b"))
def foldlM(f, b, ta):
    """
    foldrM :: (Foldable t, Monad m) => (a -> b -> m b) -> b -> t a -> m b

    Monadic fold over the elements of a structure, associating to the right,
    i.e. from right to left.
    """
    raise NotImplementedError()


@sig(H[(Foldable, "t"), (Monad, "m")]/ (H/ "b" >> "a" >> t("m", "b")) >>
    "b" >> t("t", "a") >> t("m", "b"))
def foldrM(f, b, ta):
    """
    foldlM :: (Foldable t, Monad m) => (b -> a -> m b) -> b -> t a -> m b

    Monadic fold over the elements of a structure, associating to the left,
    i.e. from left to right.
    """
    raise NotImplementedError()


#=============================================================================#
# Applicative actions


@sig(H[(Foldable, "t"), (Applicative, "f")]/ (H/ "a" >> t("f", "b")) >>
        t("f", "a") >> t("f", None))
def traverse_(f, t):
    """
    traverse_ :: (Foldable t, Applicative f) => (a -> f b) -> t a -> f ()

    Map each element of a structure to an action, evaluate these actions from
    left to right, and ignore the results. For a version that doesn't ignore
    the results see traverse.
    """
    raise NotImplementedError()


@sig(H[(Foldable, "t"), (Applicative, "f")]/ t("f", "a") >>
        (H/ "a" >> t("f", "b")) >> t("f", None))
def for_(t, f):
    """
    for_ :: (Foldable t, Applicative f) => t a -> (a -> f b) -> f ()

    for_ is traverse_ with its arguments flipped. For a version that doesn't
    ignore the results see for.
    """
    return traverse(f, t)


@sig(H[(Foldable, "t"), (Applicative, "f")]/ t("t", t("m", "a")) >>
        t("f", None))
def sequenceA_(t):
    """
    sequenceA_ :: (Foldable t, Applicative f) => t (f a) -> f ()

    Evaluate each action in the structure from left to right, and ignore the
    results. For a version that doesn't ignore the results see sequenceA.
    """
    raise NotImplementedError()


#=============================================================================#
# Monadic actions


@sig(H[(Foldable, "t"), (Monad, "m")]/ (H/ "a" >> t("m", "b")) >>
        t("m", "a") >> t("m", None))
def mapM_(f, t):
    """
    mapM_ :: (Foldable t, Monad m) => (a -> m b) -> t a -> m ()

    Map each element of a structure to a monadic action, evaluate these actions
    from left to right, and ignore the results. For a version that doesn't
    ignore the results see mapM.

    As of base 4.8.0.0, mapM_ is just traverse_, specialized to Monad.
    """
    return traverse_(f, t)


@sig(H[(Foldable, "t"), (Monad, "m")]/ t("m", "a") >>
        (H/ "a" >> t("m", "b")) >> t("m", None))
def forM_(t, f):
    """
    forM_ :: (Foldable t, Monad m) => t a -> (a -> m b) -> m ()

    forM_ is mapM_ with its arguments flipped. For a version that doesn't
    ignore the results see forM.

    As of base 4.8.0.0, forM_ is just for_, specialized to Monad.
    """
    return mapM_(f, t)


@sig(H[(Foldable, "t"), (Monad, "m")]/ t("t", t("m", "a")) >> t("m", None))
def sequence_(t):
    """
    sequence_ :: (Foldable t, Monad m) => t (m a) -> m ()

    Evaluate each monadic action in the structure from left to right, and
    ignore the results. For a version that doesn't ignore the results see
    sequence.

    As of base 4.8.0.0, sequence_ is just sequenceA_, specialized to Monad.
    """
    return sequenceA_(t)


#=============================================================================#
# Specialized folds


@sig(H[(Foldable, "t")]/ t("t", ["a"]) >> ["a"])
def concat(t):
    """
    concat :: Foldable t => t [a] -> [a]

    The concatenation of all the elements of a container of lists.
    """
    return List.concat(toList(t))


@sig(H[(Foldable, "t")]/ (H/ "a" >> ["b"]) >> t("t", "a") >> ["b"])
def concatMap(f, t):
    """
    concatMap :: Foldable t => (a -> [b]) -> t a -> [b]

    Map a function over all the elements of a container and concatenate the
    resulting lists.
    """
    return List.concatMap(f, toList(t))


@sig(H[(Foldable, "t")]/ t("t", bool) >> bool)
def and_(t):
    """
    and :: Foldable t => t bool -> bool

    and returns the conjunction of a container of Bools. For the result to be
    True, the container must be finite; False, however, results from a False
    value finitely far from the left end.
    """
    return List.and_(toList(t))


@sig(H[(Foldable, "t")]/ t("t", bool) >> bool)
def or_(t):
    """
    or :: Foldable t => t bool -> bool

    or returns the disjunction of a container of Bools. For the result to be
    False, the container must be finite; True, however, results from a True
    value finitely far from the left end.
    """
    return List.or_(toList(t))


@sig(H[(Foldable, "t")]/ (H/ "a" >> bool) >> t("t", "a") >> bool)
def any_(f, t):
    """
    any :: Foldable t => (a -> bool) -> t a -> bool

    Determines whether any element of the structure satisfies the predicate.
    """
    return List.any_(toList(t))


@sig(H[(Foldable, "t")]/ (H/ "a" >> bool) >> t("t", "a") >> bool)
def all_(f, t):
    """
    all :: Foldable t => (a -> bool) -> t a -> bool

    Determines whether all elements of the structure satisfy the predicate.
    """
    return List.all_(toList(t))


@sig(H[(Foldable, "t")]/ (H/ "a" >> "a" >> Ordering) >> t("t", "a") >> "a")
def maximumBy_(f, t):
    """
    maximumBy :: Foldable t => (a -> a -> Ordering) -> t a -> a

    The largest element of a non-empty structure with respect to the given
    comparison function.
    """
    return List.maximumBy(toList(t))


@sig(H[(Foldable, "t")]/ (H/ "a" >> "a" >> Ordering) >> t("t", "a") >> "a")
def minimumBy_(f, t):
    """
    minimumBy :: Foldable t => (a -> a -> Ordering) -> t a -> a

    The least element of a non-empty structure with respect to the given
    comparison function.
    """
    return List.minimumBy(toList(t))


#=============================================================================#
# Searches


@sig(H[(Foldable, "t"), (Eq, "a")]/ "a" >> t("t", "a") >> bool)
def notElem(a, t):
    """
    notElem :: (Foldable t, Eq a) => a -> t a -> bool

    notElem is the negation of elem.
    """
    return not elem(a, t)


@sig(H[(Foldable, "t")]/ (H/ "a" >> bool) >> t("t", "a") >> t(Maybe, "a"))
def find(f, t):
    """
    find :: Foldable t => (a -> bool) -> t a -> Maybe a

    The find function takes a predicate and a structure and returns the
    leftmost element of the structure matching the predicate, or Nothing if
    there is no such element.
    """
    return List.find(f, toList(t))
