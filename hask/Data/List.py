import itertools
import functools
import operator

from ..lang import H
from ..lang import sig
from ..lang import t
from ..lang import L
from ..lang import __
from ..lang import caseof
from ..lang import m
from ..lang import p

from Eq import Eq
from Ord import Ord
from Ord import Ordering
from Num import Num
from Num import Integral
from Maybe import Maybe
from Maybe import Just
from Maybe import Nothing

#=============================================================================#
# Basic functions


@sig(H/ ["a"] >> "a")
def head(xs):
    """
    head :: [a] -> a

    Extract the first element of a list, which must be non-empty.
    """
    return xs[0]


@sig(H/ ["a"] >> "a")
def last(xs):
    """
    last :: [a] -> a

    Extract the last element of a list, which must be finite and non-empty.
    """
    return xs[-1]


@sig(H/ ["a"] >> ["a"])
def tail(xs):
    """
    tail :: [a] -> [a]

    Extract the elements after the head of a list, which must be non-empty.
    """
    if null(xs):
        raise IndexError("empty list")
    return xs[1:]


@sig(H/ ["a"] >> ["a"])
def init(xs):
    """
    init :: [a] -> [a]

    Return all the elements of a list except the last one. The list must be
    non-empty.
    """
    if null(xs):
        raise IndexError("empty list")
    return xs[:-1]


@sig(H/ ["a"] >> t(Maybe, ("a", ["a"])))
def uncons(xs):
    """
    uncons :: [a] -> Maybe (a, [a])

    Decompose a list into its head and tail. If the list is empty, returns
    Nothing. If the list is non-empty, returns Just((x, xs)), where x is the
    head of the list and xs its tail.
    """
    return Just((head(xs), tail(xs))) if not null(xs) else Nothing


@sig(H/ ["a"] >> bool)
def null(xs):
    """
    null :: [a] -> bool

    Test whether the structure is empty.
    """
    return ~(caseof(xs)
                | m(m.y ^ m.ys) >> False
                | m(m.ys)       >> True)


@sig(H/ ["a"] >> int )
def length(xs):
    """
    length :: [a] -> int

    Returns the size/length of a finite structure as an Int. The default
    implementation is optimized for structures that are similar to cons-lists,
    because there is no general way to do better.
    """
    return len(xs)


#=============================================================================#
# List transformations


@sig(H/ (H/ "a" >> "b") >> ["a"] >> ["b"])
def map(f, xs):
    """
    map :: (a -> b) -> [a] -> [b]

    map(f, xs) is the list obtained by applying f to each element of xs
    """
    return L[itertools.imap(f, xs)]


@sig(H/ ["a"] >> ["a"] )
def reverse(xs):
    """
    reverse :: [a] -> [a]

    reverse(xs) returns the elements of xs in reverse order. xs must be finite.
    """
    return L[(x for x in xs[::-1])]


@sig(H/ "a" >> ["a"] >> ["a"] )
def intersperse(x, xs):
    """
    intersperse :: a -> [a] -> [a]

    The intersperse function takes an element and a list and `intersperses'
    that element between the elements of the list.
    """
    def __intersperse(x, xs):
        for y in init(xs):
            yield y
            yield x
        yield last(xs)

    if null(xs):
        return xs
    return L[__intersperse(x, xs)]


@sig(H/ ["a"] >> [["a"]] >> ["a"] )
def intercalate(xs, xss):
    """
    intercalate :: [a] -> [[a]] -> [a]

    intercalate(xs,xss) is equivalent to concat(intersperse(xs,xss)). It
    inserts the list xs in between the lists in xss and concatenates the
    result.
    """
    return concat(intersperse(xs, xss))


@sig(H/ [["a"]] >> [["a"]] )
def transpose(xs):
    """
    transpose :: [[a]] -> [[a]]

    The transpose function transposes the rows and columns of its argument.
    """
    return L[(L[x] for x in itertools.izip(*xs))]


@sig(H/ ["a"] >> [["a"]] )
def subsequences(xs):
    """
    subsequences :: [a] -> [[a]]

    The subsequences function returns the list of all subsequences of the
    argument.
    """
    ret = L[[L[[]]]]
    for r, _ in enumerate(xs):
        ret += L[(L[x] for x in itertools.combinations(xs, r+1))]
    return ret


@sig(H/ ["a"] >> [["a"]] )
def permutations(xs):
    """
    permutations :: [a] -> [[a]]

    The permutations function returns the list of all permutations of the
    argument.
    """
    if null(xs):
        return L[[]]
    return L[(L[x] for x in itertools.permutations(xs))]


#=============================================================================#
# Reducing lists (folds)


@sig(H/ (H/ "b" >> "a" >> "b") >> "a" >> ["a"] >> "b")
def foldl(f, z, xs):
    """
    foldl :: (b -> a -> b) -> b -> [a] -> b

    foldl, applied to a binary operator, a starting value (typically the
    left-identity of the operator), and a list, reduces the list using the
    binary operator, from left to right. The list must be finite.
    """
    return reduce(f, xs, z)


@sig(H/ (H/ "b" >> "a" >> "b") >> "a" >> ["a"] >> "b")
def foldl_(f, z, xs):
    """
    foldl_ :: (b -> a -> b) -> b -> [a] -> b

    A strict version of foldl.
    """
    return foldl(f, z, xs)


@sig(H/ (H/ "a" >> "a" >> "a") >> ["a"] >> "a")
def foldl1(f, xs):
    """
    foldl1 :: (a -> a -> a) -> [a] -> a

    foldl1 is a variant of foldl that has no starting value argument, and thus
    must be applied to non-empty lists.
    """
    return foldl(f, xs[0], xs[1:])


@sig(H/ (H/ "a" >> "a" >> "a") >> ["a"] >> "a")
def foldl1_(f, xs):
    """
    foldl1' :: (a -> a -> a) -> [a] -> a

    A strict version of foldl1
    """
    return foldl1(f, xs[0], xs[1:])


@sig(H/ (H/ "a" >> "b" >> "b") >> "a" >> ["a"] >> "b")
def foldr(f, z, xs):
    """
    foldr :: (a -> b -> b) -> b -> [a] -> b

    foldr, applied to a binary operator, a starting value (typically the
    right-identity of the operator), and a list, reduces the list using the
    binary operator, from right to left
    """
    return ~(caseof(xs)
                | m(L[[]])     >> z
                | m(m.a ^ m.b) >> f(p.a, foldr(f, z, p.b)))


@sig(H/ (H/ "a" >> "a" >> "a") >> ["a"] >> "a")
def foldr1(f, xs):
    """
    foldr1 :: (a -> a -> a) -> [a] -> a

    foldr1 is a variant of foldr that has no starting value argument, and thus
    must be applied to non-empty lists.
    """
    return foldr(f, xs[0], xs[1:])


#=============================================================================#
## Special folds


@sig(H/ [["a"]] >> ["a"] )
def concat(xss):
    """
    concat :: [[a]] -> [a]

    Concatenate a list of lists.
    """
    def __concat(xss):
        for xs in xss:
            for x in xs:
                yield x
    return L[__concat(xss)]


@sig(H/ (H/ "a" >> ["b"]) >> ["a"] >> ["b"])
def concatMap(f, xs):
    """
    concatMap :: (a -> [b]) -> [a] -> [b]

    Map a function over a list and concatenate the results.
    """
    return concat(map(f, xs))


@sig(H/ [bool] >> bool)
def and_(xs):
    """
    and_ :: [Bool] -> Bool

    and returns the conjunction of a Boolean list. For the result to be True,
    the list must be finite; False, however, results from a False value at a
    finite index of a finite or infinite list.
    """
    return False not in xs


@sig(H/ [bool] >> bool)
def or_(xs):
    """
    or_ :: [Bool] -> Bool

    or returns the disjunction of a Boolean list. For the result to be False,
    the list must be finite; True, however, results from a True value at a
    finite index of a finite or infinite list.
    """
    return True in xs


@sig(H/ (H/ "a" >> bool) >> ["a"] >> bool)
def any(p, xs):
    """
    any :: (a -> Bool) -> [a] -> Bool

    Applied to a predicate and a list, any determines if any element of the
    list satisfies the predicate. For the result to be False, the list must be
    finite; True, however, results from a True value for the predicate applied
    to an element at a finite index of a finite or infinite list.
    """
    return True in ((p(x) for x in xs))


@sig(H/ (H/ "a" >> bool) >> ["a"] >> bool)
def all(p, xs):
    """
    all :: (a -> Bool) -> [a] -> Bool

    Applied to a predicate and a list, all determines if all elements of the
    list satisfy the predicate. For the result to be True, the list must be
    finite; False, however, results from a False value for the predicate
    applied to an element at a finite index of a finite or infinite list.
    """
    return False not in ((p(x) for x in xs))


@sig(H[(Num, "a")]/ ["a"] >> "a")
def sum(xs):
    """
    sum :: Num a => [a] -> a

    The sum function computes the sum of a finite list of numbers.
    """
    return functools.reduce(operator.add, xs, 0)


@sig(H[(Num, "a")]/ ["a"] >> "a")
def product(xs):
    """
    product :: Num a => [a] -> a

    The product function computes the product of a finite list of numbers.
    """
    return functools.reduce(operator.mul, xs, 1)


@sig(H[(Ord, "a")]/ ["a"] >> "a")
def minimum(xs):
    """
    minimum :: Ord a => [a] -> a

    minimum returns the minimum value from a list, which must be non-empty,
    finite, and of an ordered type. It is a special case of minimumBy, which
    allows the programmer to supply their own comparison function.
    """
    return min(xs)


@sig(H[(Ord, "a")]/ ["a"] >> "a")
def maximum(xs):
    """
    maximum :: Ord a => [a] -> a

    maximum returns the maximum value from a list, which must be non-empty,
    finite, and of an ordered type. It is a special case of maximumBy, which
    allows the programmer to supply their own comparison function.
    """
    return max(xs)


#=============================================================================#
# Building lists
## Scans

@sig(H/ (H/ "b" >> "a" >> "b") >> "b" >> ["a"] >> ["b"])
def scanl(f, z, xs):
    """
    scanl :: (b -> a -> b) -> b -> [a] -> [b]

    scanl is similar to foldl, but returns a list of successive reduced values
    from the left
    """
    raise NotImplementedError()


@sig(H/ (H/ "a" >> "a" >> "a") >> ["a"] >> ["a"])
def scanl1(f, xs):
    """
    scanl1 :: (a -> a -> a) -> [a] -> [a]

    scanl1 is a variant of scanl that has no starting value argument
    """
    raise NotImplementedError()


@sig(H/ (H/ "a" >> "a" >> "b") >> "b" >> ["a"] >> ["b"])
def scanr(f, z, xs):
    """
    scanr :: (a -> b -> b) -> b -> [a] -> [b]

    scanr is the right-to-left dual of scanl.
    """
    raise NotImplementedError()


@sig(H/ (H/ "a" >> "a" >> "a") >> ["a"] >> ["a"])
def scanr1(f, xs):
    """
    scanr1 :: (a -> a -> a) -> [a] -> [a]

    scanr1 is a variant of scanr that has no starting value argument.
    """
    raise NotImplementedError()


#=============================================================================#
## Accumulating maps

@sig(H/ (H/ "a" >> "x" >> ("a", "y")) >> "a" >> ["x"] >> ("a", ["y"]))
def mapAccumL(xs):
    """
    mapAccumL :: (a -> x -> (a, y)) -> a -> [x] -> (a, [y])

    The mapAccumL function behaves like a combination of map and foldl; it
    applies a function to each element of a list, passing an accumulating
    parameter from left to right, and returning a final value of this
    accumulator together with the new list.
    """
    raise NotImplementedError()


@sig(H/ (H/ "a" >> "x" >> ("a", "y")) >> "a" >> ["x"] >> ("a", ["y"]))
def mapAccumR(xs):
    """
    mapAccumR :: (acc -> x -> (acc, y)) -> acc -> [x] -> (acc, [y])

    The mapAccumR function behaves like a combination of map and foldr; it
    applies a function to each element of a list, passing an accumulating
    parameter from right to left, and returning a final value of this
    accumulator together with the new list.
    """
    raise NotImplementedError()


#=============================================================================#
## Infinite lists

@sig(H/ (H/ "a" >> "a") >> "a" >> ["a"])
def iterate(f, x):
    """
    iterate :: (a -> a) -> a -> [a]

    iterate(f, x) returns an infinite List of repeated applications of f to x:
    iterate(f, x) == [x, f(x), f(f(x)), ...]
    """
    def __iterate(f, x):
        while True:
            yield x
            x = f(x)
    return L[__iterate(f, x)]


@sig(H/ "a" >> ["a"])
def repeat(x):
    """
    repeat :: a -> [a]

    repeat(x) is an infinite list, with x the value of every element.
    """
    def __repeat(x):
        while True:
            yield x
    return L[__repeat(x)]


@sig(H/ int >> "a" >> ["a"])
def replicate(n, x):
    """
    replicate :: Int -> a -> [a]

    replicate(n, x) is a list of length n with x the value of every element.
    """
    def __replicate(n, x):
        for _ in range(n):
            yield x
    return L[__replicate(n, x)]


@sig(H/ ["a"] >> ["a"])
def cycle(x):
    """
    cycle :: [a] -> [a]

    cycle ties a finite list into a circular one, or equivalently, the infinite
    repetition of the original list. It is the identity on infinite lists.
    """
    def __cycle(x):
        while True:
            for i in x:
                yield i
    return L[__cycle(x)]


#=============================================================================#
## Unfolding


@sig(H/ (H/ "b" >> t(Maybe, ("a", "b"))) >> "b" >> ["a"])
def unfoldr(f, x):
    """
    unfoldr :: (b -> Maybe (a, b)) -> b -> [a]

    The unfoldr function is a `dual' to foldr: while foldr reduces a list to a
    summary value, unfoldr builds a list from a seed value. The function takes
    the element and returns Nothing if it is done producing the list or returns
    Just (a,b), in which case, a is prepended to the list and b is used as the
    next element in a recursive call
    """
    y = f(x)
    if y == Nothing:
        return L[[]]
    return y[0][0] ^ unfoldr(f, y[0][1])


#=============================================================================#
# Sublists
## Extracting sublists

@sig(H/ int >> ["a"] >> ["a"])
def take(n, xs):
    """
    take :: Int -> [a] -> [a]

    take(n), applied to a list xs, returns the prefix of xs of length n, or xs
    itself if n > length xs
    """
    return xs[:n]


@sig(H/ int >> ["a"] >> ["a"])
def drop(n, xs):
    """
    drop :: Int -> [a] -> [a]

    drop(n, xs) returns the suffix of xs after the first n elements, or [] if n >
    length xs
    """
    return xs[n:]


@sig(H/ int >> ["a"] >> (["a"], ["a"]))
def splitAt(n, xs):
    """
    splitAt :: Int -> [a] -> ([a], [a])

    splitAt(n, xs) returns a tuple where first element is xs prefix of length n
    and second element is the remainder of the list
    """
    return (xs[:n], xs[n:])


@sig(H/ (H/ "a" >> bool) >> ["a"] >> ["a"])
def takeWhile(p, xs):
    """
    takeWhile :: (a -> Bool) -> [a] -> [a]

    takeWhile, applied to a predicate p and a list xs, returns the longest
    prefix (possibly empty) of xs of elements that satisfy p
    """
    return L[itertools.takewhile(p, xs)]


@sig(H/ (H/ "a" >> bool) >> ["a"] >> ["a"])
def dropWhile(p, xs):
    """
    dropWhile :: (a -> Bool) -> [a] -> [a]

    dropWhile(p, xs) returns the suffix remaining after takeWhile(p, xs)
    """
    return L[itertools.dropwhile(p, xs)]


@sig(H/ (H/ "a" >> bool) >> ["a"] >> ["a"])
def dropWhileEnd(p, xs):
    """
    dropWhileEnd :: (a -> Bool) -> [a] -> [a]

    The dropWhileEnd function drops the largest suffix of a list in which the
    given predicate holds for all elements.
    """
    raise NotImplementedError()


@sig(H/ (H/ "a" >> bool)  >> ["a"] >> (["a"], ["a"]))
def span(p, xs):
    """
    span :: (a -> Bool) -> [a] -> ([a], [a])

    span, applied to a predicate p and a list xs, returns a tuple where first
    element is longest prefix (possibly empty) of xs of elements that satisfy p
    and second element is the remainder of the list
    """
    front = takeWhile(p, xs)
    rest = xs[len(front):]
    return front, rest


@sig(H/ (H/ "a" >> bool)  >> ["a"] >> (["a"], ["a"]))
def break_(p, xs):
    """
    break :: (a -> Bool) -> [a] -> ([a], [a])

    break, applied to a predicate p and a list xs, returns a tuple where first
    element is longest prefix (possibly empty) of xs of elements that do not
    satisfy p and second element is the remainder of the list
    """
    inv = (lambda x: not p(x)) ** (H/ "a" >> bool)
    return span(inv, xs)


@sig(H[(Eq, "a")]/ ["a"] >> ["a"] >> t(Maybe, ["a"]))
def stripPrefix(xs, ys):
    """
    stripPrefix :: Eq a => [a] -> [a] -> Maybe [a]

    The stripPrefix function drops the given prefix from a list. It returns
    Nothing if the list did not start with the prefix given, or Just the list
    after the prefix, if it does.
    """
    if isPrefixOf(xs, ys):
        return Just(ys[len(xs)])
    return Nothing


@sig(H[(Eq, "a")]/ ["a"] >> [["a"]])
def group(xs):
    """
    group :: Eq a => [a] -> [[a]]

    The group function takes a list and returns a list of lists such that the
    concatenation of the result is equal to the argument. Moreover, each
    sublist in the result contains only equal elements.
    It is a special case of groupBy, which allows the programmer to supply
    their own equality test.
    """
    return groupBy(xs, (__==__))


@sig(H/ ["a"] >> [["a"]])
def inits(xs):
    """
    inits :: [a] -> [[a]]

    The inits function returns all initial segments of the argument, shortest
    first.
    """
    if null(xs):
        return L[[xs]]
    return L[[L[[]]]] + L[(xs[:n+1] for n,_ in enumerate(xs))]


@sig(H/ ["a"] >> [["a"]])
def tails(xs):
    """
    tails :: [a] -> [[a]]

    The tails function returns all final segments of the argument, longest
    first.
    """
    if null(xs):
        return L[[L[[]]]]
    return L[(xs[n:] for n,_ in enumerate(xs))] + L[[L[[]]]]


#=============================================================================#
## Predicates


@sig(H[(Eq, "a")]/ ["a"] >> ["a"] >> bool)
def isPrefixOf(xs, ys):
    """
    isPrefixOf :: Eq a => [a] -> [a] -> Bool

    The isPrefixOf function takes two lists and returns True iff the first list
    is a prefix of the second.
    """
    return xs == ys[:len(xs)]


@sig(H[(Eq, "a")]/ ["a"] >> ["a"] >> bool)
def isSuffixOf(xs, ys):
    """
    isSuffixOf :: Eq a => [a] -> [a] -> Bool

    The isSuffixOf function takes two lists and returns True iff the first list
    is a suffix of the second. The second list must be finite.
    """
    return xs == ys[-len(xs):]


@sig(H[(Eq, "a")]/ ["a"] >> ["a"] >> bool)
def isInfixOf(xs, ys):
    """
    isInfixOf :: Eq a => [a] -> [a] -> Bool

    The isInfixOf function takes two lists and returns True iff the first list
    is contained, wholly and intact, anywhere within the second.
    """
    return any(isPrefixOf(xs), tails(ys))


@sig(H[(Eq, "a")]/ ["a"] >> ["a"] >> bool)
def isSubsequenceOf(x, y):
    """
    isSubsequenceOf :: Eq a => [a] -> [a] -> Bool

    The isSubsequenceOf function takes two lists and returns True if the first
    list is a subsequence of the second list.

    isSubsequenceOf(x, y) is equivalent to elem(x, subsequences(y))
    """
    return elem(x, subsequences(y))


#=============================================================================#
# Searching lists
## Searching by equality


@sig(H[(Eq, "a")]/ "a" >> ["a"] >> bool)
def elem(x, xs):
    """
    elem :: Eq a => a -> [a] -> Bool

    elem is the list membership predicate, elem(x, xs). For the result to be
    False, the list must be finite; True, however, results from an element
    equal to x found at a finite index of a finite or infinite list.
    """
    return x in xs


@sig(H[(Eq, "a")]/ "a" >> ["a"] >> bool)
def notElem(x, xs):
    """
    notElem :: Eq a => a -> [a] -> Bool

    notElem is the negation of elem.
    """
    return not elem(x, xs)


@sig(H[(Eq, "a")]/ "a" >> [("a", "b")] >> t(Maybe, "b"))
def lookup(key, assocs):
    """
    lookup :: Eq a => a -> [(a, b)] -> Maybe b

    lookup(key, assocs) looks up a key in an association list.
    """
    for k, value in assocs:
        if k == key:
            return Just(value)
    return Nothing


#=============================================================================#
## Searching with a predicate


@sig(H/ (H/ "a" >> bool) >> ["a"] >> t(Maybe, "a"))
def find(p, xs):
    """
    find :: (a -> Bool) -> [a] -> Maybe a

    The find function takes a predicate and a structure and returns the
    leftmost element of the structure matching the predicate, or Nothing if
    there is no such element.
    """
    for x in xs:
        if p(x):
            return Just(x)
    return Nothing


@sig(H/ (H/ "a" >> bool) >> ["a"] >> ["a"])
def filter(f, xs):
    """
    filter :: (a -> Bool) -> [a] -> [a]

    filter, applied to a predicate and a list, returns the list of those
    elements that satisfy the predicate
    """
    return L[itertools.ifilter(f, xs)]


@sig(H/ (H/ "a" >> bool) >> ["a"] >> (["a"], ["a"]))
def partition(f, xs):
    """
    partition :: (a -> Bool) -> [a] -> ([a], [a])

    The partition function takes a predicate a list and returns the pair of
    lists of elements which do and do not satisfy the predicate.
    """
    yes, no = [], []
    for item in xs:
        if f(item):
            yes.append(item)
        else:
            no.append(item)
    return L[yes], L[no]


#=============================================================================#
# Indexing lists


@sig(H[(Eq, "a")]/ "a" >> ["a"] >> t(Maybe, int))
def elemIndex(x, xs):
    """
    elemIndex :: Eq a => a -> [a] -> Maybe Int

    The elemIndex function returns the index of the first element in the given
    list which is equal (by ==) to the query element, or Nothing if there is no
    such element.
    """
    for i, a in enumerate(xs):
        if a == x:
            return Just(i)
    return Nothing


@sig(H[(Eq, "a")]/ "a" >> ["a"] >> [int])
def elemIndices(x, xs):
    """
    elemIndices :: Eq a => a -> [a] -> [Int]

    The elemIndices function extends elemIndex, by returning the indices of all
    elements equal to the query element, in ascending order.
    """
    return L[(i for i, a in enumerate(xs) if a == x)]


@sig(H/ (H/ "a" >> bool) >> ["a"] >> t(Maybe, int))
def findIndex(f, xs):
    """
    findIndex :: (a -> Bool) -> [a] -> Maybe Int

    The findIndex function takes a predicate and a list and returns the index
    of the first element in the list satisfying the predicate, or Nothing if
    there is no such element.
    """
    for i, x in enumerate(xs):
        if f(x):
            return Just(i)
    return Nothing


@sig(H/ (H/ "a" >> bool) >> ["a"] >> [int])
def findIndicies(f, xs):
    """
    findIndices :: (a -> Bool) -> [a] -> [Int]

    The findIndices function extends findIndex, by returning the indices of all
    elements satisfying the predicate, in ascending order.
    """
    return L[(i for i, x in enumerate(xs) if f(x))]


#=============================================================================#
# Zipping and unzipping lists


@sig(H/ ["a"] >> ["b"] >> [("a", "b")])
def zip(xs, ys):
    """
    zip :: [a] -> [b] -> [(a, b)]

    zip takes two lists and returns a list of corresponding pairs. If one input
    list is short, excess elements of the longer list are discarded.
    """
    return L[itertools.izip(xs, ys)]


@sig(H/ ["a"] >> ["b"] >> ["c"] >> [("a", "b", "c")])
def zip3(a, b, c):
    """
    zip3 :: [a] -> [b] -> [c] -> [(a, b, c)]

    zip3 takes three lists and returns a list of triples, analogous to zip.
    """
    return L[itertools.izip(a, b, c)]


@sig(H/ ["a"] >> ["b"] >> ["c"] >> ["d"] >> [("a", "b", "c", "d")])
def zip4(a, b, c, d):
    """
    zip4 :: [a] -> [b] -> [c] -> [d] -> [(a, b, c, d)]

    The zip4 function takes four lists and returns a list of quadruples,
    analogous to zip.
    """
    return L[itertools.izip(a, b, c, d)]


@sig(H/ ["a"] >> ["b"] >> ["c"] >> ["d"] >> ["e"] >>
        [("a", "b", "c", "d", "e")])
def zip5(a, b, c, d, e):
    """
    zip5 :: [a] -> [b] -> [c] -> [d] -> [e] -> [(a, b, c, d, e)]

    The zip5 function takes five lists and returns a list of five-tuples,
    analogous to zip.
    """
    return L[itertools.izip(a, b, c, d, e)]


@sig(H/ ["a"] >> ["b"] >> ["c"] >> ["d"] >> ["e"] >> ["f"] >>
        [("a", "b", "c", "d", "e", "f")])
def zip6(a, b, c, d, e, f):
    """
    zip6 :: [a] -> [b] -> [c] -> [d] -> [e] -> [f] -> [(a, b, c, d, e, f)]

    The zip6 function takes six lists and returns a list of six-tuples,
    analogous to zip.
    """
    return L[itertools.izip(a, b, c, d, e, f)]


@sig(H/ ["a"] >> ["b"] >> ["c"] >> ["d"] >> ["e"] >> ["f"] >> ["g"] >>
        [("a", "b", "c", "d", "e", "f", "g")])
def zip7(a, b, c, d, e, f, g):
    """
    zip7 :: [a] -> [b] -> [c] -> [d] -> [e] -> [f] -> [g] -> [(a, b, c, d, e, f, g)]

    The zip7 function takes seven lists and returns a list of seven-tuples,
    analogous to zip.
    """
    return L[itertools.izip(a, b, c, d, e, f, g)]


@sig(H/ (H/ "a" >> "b" >> "c") >> ["a"] >> ["b"] >> ["c"])
def zipWith(fn, xs, ys):
    """
    zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]

    zipWith generalises zip by zipping with the function given as the first
    argument, instead of a tupling function. For example, zipWith (+) is
    applied to two lists to produce the list of corresponding sums.
    """
    return L[(fn(*s) for s in zip(xs, ys))]


@sig(H/ (H/ "a" >> "b" >> "c" >> "d") >> ["a"] >> ["b"] >> ["c"] >> ["d"])
def zipWith3(fn, a, b, c):
    """
    zipWith3 :: (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]

    The zipWith3 function takes a function which combines three elements, as
    well as three lists and returns a list of their point-wise combination,
    analogous to zipWith.
    """
    return L[(fn(*s) for s in zip3(a, b, c))]


@sig(H/ (H/ "a" >> "b" >> "c" >> "d" >> "e") >>
        ["a"] >> ["b"] >> ["c"] >> ["d"] >> ["e"])
def zipWith4(fn, a, b, c, d):
    """
    zipWith4 :: (a -> b -> c -> d -> e) -> [a] -> [b] -> [c] -> [d] -> [e]

    The zipWith4 function takes a function which combines four elements, as
    well as four lists and returns a list of their point-wise combination,
    analogous to zipWith.
    """
    return L[(fn(*s) for s in zip4(a, b, c, d))]


@sig(H/ (H/ "a" >> "b" >> "c" >> "d" >> "e" >> "f") >>
        ["a"] >> ["b"] >> ["c"] >> ["d"] >> ["e"] >> ["f"])
def zipWith5(fn, a, b, c, d, e):
    """
    zipWith5 :: (a -> b -> c -> d -> e -> f) -> [a] -> [b] -> [c] -> [d] -> [e]
                -> [f]

    The zipWith5 function takes a function which combines five elements, as
    well as five lists and returns a list of their point-wise combination,
    analogous to zipWith.
    """
    return L[(fn(*s) for s in zip5(a, b, c, d, e))]


@sig(H/ (H/ "a" >> "b" >> "c" >> "d" >> "e" >> "f" >> "g") >>
        ["a"] >> ["b"] >> ["c"] >> ["d"] >> ["e"] >> ["f"] >> ["g"])
def zipWith6(fn, a, b, c, d, e, f):
    """
    zipWith6 :: (a -> b -> c -> d -> e -> f -> g) -> [a] -> [b] -> [c] -> [d]
                -> [e] -> [f] -> [g]

    The zipWith6 function takes a function which combines six elements, as well
    as six lists and returns a list of their point-wise combination, analogous
    to zipWith.
    """
    return L[(fn(*s) for s in zip6(a, b, c, d, e, f))]


@sig(H/ (H/ "a" >> "b" >> "c" >> "d" >> "e" >> "f" >> "g" >> "h") >>
        ["a"] >> ["b"] >> ["c"] >> ["d"] >> ["e"] >> ["f"] >> ["g"] >> ["h"])
def zipWith7(fn, a, b, c, d, e, f):
    """
    zipWith7 :: (a -> b -> c -> d -> e -> f -> g -> h) -> [a] -> [b] -> [c] ->
                [d] -> [e] -> [f] -> [g] -> [h]

    The zipWith7 function takes a function which combines seven elements, as
    well as seven lists and returns a list of their point-wise combination,
    analogous to zipWith.
    """
    return L[(fn(*s) for s in zip7(a, b, c, d, e, f))]


@sig(H/ [("a", "b")] >> (["a"], ["b"]))
def unzip(xs):
    """
    unzip :: [(a, b)] -> ([a], [b])

    unzip transforms a list of pairs into a list of first components and a list
    of second components.
    """
    a = L[(i[0] for i in xs)]
    b = L[(i[1] for i in xs)]
    return a, b


@sig(H/ [("a", "b", "c")] >> (["a"], ["b"], ["c"]))
def unzip3(xs):
    """
    unzip3 :: [(a, b, c)] -> ([a], [b], [c])

    The unzip3 function takes a list of triples and returns three lists,
    analogous to unzip.
    """
    a = L[(i[0] for i in xs)]
    b = L[(i[1] for i in xs)]
    c = L[(i[2] for i in xs)]
    return a, b, c


@sig(H/ [("a", "b", "c", "d")] >> (["a"], ["b"], ["c"], ["d"]))
def unzip4(xs):
    """
    unzip4 :: [(a, b, c, d)] -> ([a], [b], [c], [d])

    The unzip4 function takes a list of quadruples and returns four lists,
    analogous to unzip.
    """
    a = L[(i[0] for i in xs)]
    b = L[(i[1] for i in xs)]
    c = L[(i[2] for i in xs)]
    d = L[(i[3] for i in xs)]
    return a, b, c, d


@sig(H/ [("a", "b", "c", "d", "e")] >> (["a"], ["b"], ["c"], ["d"], ["e"]))
def unzip5(xs):
    """
    unzip5 :: [(a, b, c, d, e)] -> ([a], [b], [c], [d], [e])

    The unzip5 function takes a list of five-tuples and returns five lists,
    analogous to unzip.
    """
    a = L[(i[0] for i in xs)]
    b = L[(i[1] for i in xs)]
    c = L[(i[2] for i in xs)]
    d = L[(i[3] for i in xs)]
    e = L[(i[4] for i in xs)]
    return a, b, c, d, e


@sig(H/ [("a", "b", "c", "d", "e", "f")]
        >> (["a"], ["b"], ["c"], ["d"], ["e"], ["f"]))
def unzip6(xs):
    """
    unzip6 :: [(a, b, c, d, e, f)] -> ([a], [b], [c], [d], [e], [f])

    The unzip6 function takes a list of six-tuples and returns six lists,
    analogous to unzip.
    """
    a = L[(i[0] for i in xs)]
    b = L[(i[1] for i in xs)]
    c = L[(i[2] for i in xs)]
    d = L[(i[3] for i in xs)]
    e = L[(i[4] for i in xs)]
    f = L[(i[5] for i in xs)]
    return a, b, c, d, e, f


@sig(H/ [("a", "b", "c", "d", "e", "f", "g")]
        >> (["a"], ["b"], ["c"], ["d"], ["e"], ["f"], ["g"]))
def unzip7(xs):
    """
    unzip7 :: [(a, b, c, d, e, f, g)] -> ([a], [b], [c], [d], [e], [f], [g])

    The unzip7 function takes a list of seven-tuples and returns seven lists,
    analogous to unzip.
    """
    a = L[(i[0] for i in xs)]
    b = L[(i[1] for i in xs)]
    c = L[(i[2] for i in xs)]
    d = L[(i[3] for i in xs)]
    e = L[(i[4] for i in xs)]
    f = L[(i[5] for i in xs)]
    g = L[(i[6] for i in xs)]
    return a, b, c, d, e, f, g


#=============================================================================#
# Special lists
## Functions on strings


from String import lines
from String import words
from String import unlines
from String import unwords


#=============================================================================#
## "Set" operations

@sig(H[(Eq, "a")]/ ["a"] >> ["a"])
def nub(xs):
    """
    nub :: Eq a => [a] -> [a]

    The nub function removes duplicate elements from a list. In particular, it
    keeps only the first occurrence of each element. (The name nub means
    `essence'.) It is a special case of nubBy, which allows the programmer to
    supply their own equality test.
    """
    return L[(i for i in set(xs))]


@sig(H[(Eq, "a")]/ "a" >> ["a"] >> ["a"])
def delete(x, xs):
    """
    delete :: Eq a => a -> [a] -> [a]

    delete(x) removes the first occurrence of x from its list argument.

    It is a special case of deleteBy, which allows the programmer to supply
    their own equality test.
    """
    raise NotImplementedError()


@sig(H[(Eq, "a")]/ ["a"] >> ["a"] >> ["a"])
def diff(xs, ys):
    """
    diff :: :: Eq a => [a] -> [a] -> [a]

    List difference.
    """
    raise NotImplementedError()


@sig(H[(Eq, "a")]/ ["a"] >> ["a"] >> ["a"])
def union(xs, ys):
    """
    union :: Eq a => [a] -> [a] -> [a]

    The union function returns the list union of the two lists.

    Duplicates, and elements of the first list, are removed from the the second
    list, but if the first list contains duplicates, so will the result. It is
    a special case of unionBy, which allows the programmer to supply their own
    equality test.
    """
    raise NotImplementedError()


@sig(H[(Eq, "a")]/ ["a"] >> ["a"] >> ["a"])
def intersect(xs, ys):
    """
    intersect :: Eq a => [a] -> [a] -> [a]

    The intersect function takes the list intersection of two lists.  It is a
    special case of intersectBy, which allows the programmer to supply their
    own equality test. If the element is found in both the first and the second
    list, the element from the first list will be used.
    """
    raise NotImplementedError()


#=============================================================================#
## Ordered lists


@sig(H[(Ord, "a")]/ ["a"] >> ["a"])
def sort(xs):
    """
    sort :: Ord a => [a] -> [a]

    The sort function implements a stable sorting algorithm. It is a special
    case of sortBy, which allows the programmer to supply their own comparison
    function.

    Note: Current implementation is not lazy
    """
    return L[sorted(xs)]


@sig(H[(Ord, "b")]/ (H/ "a" >> "b") >> ["a"] >> ["a"])
def sortOn(f, xs):
    """
    sortOn :: Ord b => (a -> b) -> [a] -> [a]

    Sort a list by comparing the results of a key function applied to each
    element.

    Note: Current implementation is not lazy
    """
    raise NotImplementedError()


@sig(H[(Ord, "a")]/ "a" >> ["a"] >> ["a"])
def insert(x, xs):
    """
    insert :: Ord a => a -> [a] -> [a]

    The insert function takes an element and a list and inserts the element
    into the list at the first position where it is less than or equal to the
    next element. In particular, if the list is sorted before the call, the
    result will also be sorted.
    """
    def __insert(x, xs):
        for i in xs:
            if i > x:
                yield x
            yield i
    return L[__insert(x, xs)]


#=============================================================================#
# Generalized functions
## The "By" operations
### User-supplied equality (replacing an Eq context)


@sig(H/ (H/ "a" >> "a" >> bool) >> ["a"] >> ["a"])
def nubBy(f, xs):
    """
    nubBy :: (a -> a -> Bool) -> [a] -> [a]

    The nubBy function behaves just like nub, except it uses a user-supplied
    equality predicate instead of the overloaded == function.
    """
    raise NotImplementedError()


@sig(H/ (H/ "a" >> "a" >> bool) >> "a" >> ["a"] >> ["a"])
def deleteBy(f, xs):
    """
    deleteBy :: (a -> a -> Bool) -> a -> [a] -> [a]

    The deleteBy function behaves like delete, but takes a user-supplied
    equality predicate.
    """
    raise NotImplementedError()


@sig(H/ (H/ "a" >> "a" >> bool) >> ["a"] >> ["a"] >> ["a"])
def deleteFirstBy(f, xs, ys):
    """
    deleteFirstsBy :: (a -> a -> Bool) -> [a] -> [a] -> [a]

    The deleteFirstsBy function takes a predicate and two lists and returns the
    first list with the first occurrence of each element of the second list
    removed.
    """
    raise NotImplementedError()


@sig(H/ (H/ "a" >> "a" >> bool) >> ["a"] >> ["a"] >> ["a"])
def unionBy(f, xs, ys):
    """
    unionBy :: (a -> a -> Bool) -> [a] -> [a] -> [a]

    The unionBy function is the non-overloaded version of union.
    """
    raise NotImplementedError()


@sig(H/ (H/ "a" >> "a" >> bool) >> ["a"] >> ["a"] >> ["a"])
def intersectBy(f, xs, ys):
    """
    intersectBy :: (a -> a -> Bool) -> [a] -> [a] -> [a]

    The intersectBy function is the non-overloaded version of intersect.
    """
    raise NotImplementedError()


@sig(H/ (H/ "a" >> "a" >> bool) >> ["a"] >> [["a"]])
def groupBy(f, xs):
    """
    groupBy :: (a -> a -> Bool) -> [a] -> [[a]]

    The groupBy function is the non-overloaded version of group.
    """
    return L[(L[i[1]] for i in itertools.groupby(xs, keyfunc=f))]


#=============================================================================#
### User-supplied comparison (replacing an Ord context)


@sig(H/ (H/ "a" >> "a" >> Ordering) >> ["a"] >> ["a"])
def sortBy(f, xs):
    """
    sortBy :: (a -> a -> Ordering) -> [a] -> [a]

    The sortBy function is the non-overloaded version of sort.
    """
    raise NotImplementedError()


@sig(H/ (H/ "a" >> "a" >> Ordering) >> "a" >> ["a"] >> ["a"])
def insertBy(f, xs):
    """
    insertBy :: (a -> a -> Ordering) -> a -> [a] -> [a]

    The non-overloaded version of insert.
    """
    raise NotImplementedError()


@sig(H/ (H/ "a" >> "a" >> Ordering) >> ["a"] >> "a")
def maximumBy(f, xs):
    """
    maximumBy :: (a -> a -> Ordering) -> [a] -> a

    The maximumBy function takes a comparison function and a list and returns
    the greatest element of the list by the comparison function. The list must
    be finite and non-empty.
    """
    return max(xs, key=f)


@sig(H/ (H/ "a" >> "a" >> Ordering) >> ["a"] >> "a")
def minimumBy(f, xs):
    """
    minimumBy :: (a -> a -> Ordering) -> [a] -> a

    The minimumBy function takes a comparison function and a list and returns
    the least element of the list by the comparison function. The list must be
    finite and non-empty.
    """
    return min(xs, key=f)


#=============================================================================#
## The "generic" operators

@sig(H[(Num, "i")]/ ["a"] >> "i")
def genericLength(xs):
    """
    genericLength :: Num i => [a] -> i

    The genericLength function is an overloaded version of length. In
    particular, instead of returning an Int, it returns any type which is an
    instance of Num. It is, however, less efficient than length.
    """
    raise NotImplementedError()


@sig(H[Integral, "i"]/ "i" >> ["a"] >> ["a"])
def genericTake(n, xs):
    """
    genericTake :: Integral i => i -> [a] -> [a]

    The genericTake function is an overloaded version of take, which accepts
    any Integral value as the number of elements to take.
    """
    raise NotImplementedError()


@sig(H[Integral, "i"]/ "i" >> ["a"] >> ["a"])
def genericDrop(n, xs):
    """
    genericDrop :: Integral i => i -> [a] -> [a]

    The genericDrop function is an overloaded version of drop, which accepts
    any Integral value as the number of elements to drop.
    """
    raise NotImplementedError()


@sig(H[Integral, "i"]/ "i" >> ["a"] >> (["a"], ["a"]))
def genericSplitAt(n, xs):
    """
    genericSplitAt :: Integral i => i -> [a] -> ([a], [a])

    The genericSplitAt function is an overloaded version of splitAt, which
    accepts any Integral value as the position at which to split.
    """
    raise NotImplementedError()


@sig(H[Integral, "i"]/ ["a"] >> "i" >> ["a"])
def genericIndex(xs, i):
    """
    genericIndex :: Integral i => [a] -> i -> a

    The genericIndex function is an overloaded version of !!, which accepts any
    Integral value as the index.
    """
    raise NotImplementedError()


@sig(H[Integral, "i"]/ "i" >> ["a"] >> ["a"])
def genericReplicate(i, a):
    """
    genericReplicate :: Integral i => i -> a -> [a]

    The genericReplicate function is an overloaded version of replicate, which
    accepts any Integral value as the number of repetitions to make.
    """
    raise NotImplementedError()
