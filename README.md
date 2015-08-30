# Hask

[![Build Status](https://travis-ci.org/billpmurphy/hask.svg)](https://travis-ci.org/billpmurphy/hask)
[![Coverage Status](https://coveralls.io/repos/billpmurphy/hask/badge.svg?branch=master&service=github)](https://coveralls.io/github/billpmurphy/hask?branch=master)


Hask is a pure-Python, zero-dependencies library that mimics most of the core
language tools from Haskell, including:

* Full Hindley-Milner type system (with typeclasses) that will typecheck any
  function decorated with a Hask type signature
* Easy creation of new algebraic data types and new typeclasses, with
  Haskell-like syntax
* Pattern matching with `case` expressions
* Automagical function currying/partial application and function composition
* Efficient, immutable, lazily evaluated `List` type with Haskell-style list
  comprehensions
* All your favorite syntax and control flow tools, including operator sections,
  monadic error handling, guards, and more
* Python port of (some of) the standard libraries from Haskell's `base`,
  including:
    * Algebraic datatypes from the Haskell `Prelude`, including `Maybe` and
      `Either`
    * Typeclasses from the Haskell `base` libraries, including `Functor`,
      `Applicative`, `Monad`, `Enum`, `Num`, and all the rest
    * Standard library functions from `base`, including all functions from
      `Prelude`, `Data.List`, `Data.Maybe`, and more


Features not yet implemented, but coming soon:

* Python 3 compatibility
* Better support for polymorphic return values/type defaulting
* Better support for lazy evaluation (beyond just the `List` type and pattern matching)
* More of the Haskell standard library (`Control.*` libraries, QuickCheck, and more)
* Monadic, lazy I/O

**Note that all of this is still very much pre-alpha, and some things may be buggy!**

## Installation

1) `git clone https://github.com/billpmurphy/hask`

2) `python setup.py install`

To run the tests: `python tests.py`.


## Why did you make this?

I wanted to cram as much of Haskell into Python as possible while still being
100% compatible with the rest of Python, just to see if any useful ideas came
out of the result. Also, it was fun!

Contributions, forks, and extensions to this experiment are always welcome!
Feel free to submit a pull request, open an issue, or email me. In the spirit
of this project, abusing the Python language as much as possible is encouraged.


## Features

Hask is a grab-bag of features that add up to one big pseudo-Haskell functional
programming library. The rest of this README lays out the basics.

I recommend playing around in the REPL while going through the examples. You

To import all the language features: `from hask import *`
To import the Prelude: `from hask import Prelude`
To import a `base` library, e.g. `Data.List`: `from hask import Data.List`


### The List type and list comprehensions


Hask provides the `List` type, a lazy and statically-typed list, similar to
Haskell's standard list type.

To create a new `List`, just put the elements inside `L[` and `]` brackets, or
wrap an existing iterable inside `L[ ]`.

```python
>>> L[1, 2, 3]
L[1, 2, 3]

>>> my_list = ["a", "b", "c"]
>>> L[my_list]
L['a', 'b', 'c']

>>> L[(x**2 for x in range(1, 11))]
L[1 ... ]
```

To add elements to the front of a List, use `^`, the cons operator.  To combine
two lists, use `+`, the concatenation operator.

```python
>>> 1 ^ L[2, 3]
L[1, 2, 3]

>>> "goodnight" ^ ("sweet" ^ ("prince" ^ L[[]]))
L["goodnight", "sweet", "prince"]

>>> "a" ^ L[1.0, 10.3]  # type error

>>> L[1, 2] + L[3, 4]
L[1, 2, 3, 4]
```

Lists are always evaluated lazily, and will only evaluate list elements as
needed, so you can use infinite Lists or put never-ending generators inside of
a `List`. (Of course, you can still blow up the interpreter if you try to
evaluate the entirety of an infinite List, e.g. by trying to find the length of
the List with `len`.)

One way to create infinite lists is via list comprehensions. As in Haskell,
there are four basic type of list comprehensions:


```python
# list from 1 to infinity, counting by ones
L[1, ...]

# list from 1 to infinity, counting by twos
L[1, 3, ...]

# list from 1 to 20 (inclusive), counting by ones
L[1, ..., 20]

# list from 1 to 20 (inclusive), counting by fours
L[1, 5, ..., 20]
```

List comprehensions can be used on ints, longs, floats, one-character strings,
or any other instance of the `Enum` typeclass (more on this later).

Hask provides all of the Haskell functions for List manipulation (`take`,
`drop`, `takeWhile`, etc.), or you can also use Python-style indexing.


```python
>>> L[1, ...]
L[1 ...]


>>> from hask.Data.List import take
>>> take(5, L["a", "b", ...])
L['a', 'b', 'c', 'd', 'e']


>>> L[1,...][5:10]
L[6, 7, 8, 9, 10]


>>> from hask.Data.List import map
>>> from hask.Data.Char import chr
>>> letters = map(chr, L[97, ...])
>>> letters[:9]
L['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i']


>>> len(L[1, 3, ...])  # uh oh
```

Otherwise, you can use `List` just like you would use a regular Python list.

```python
for i in L[0, ...]:
    print i


>>> 55 in L[1, 3, ...]
True
```

### Algebraic Data Types

Hask allows you to define [algebraic
datatypes](https://wiki.haskell.org/Algebraic_data_type), which are immutable
objects with a fixed number of typed, unnamed fields.

Here is the definition for the infamous `Maybe` type:

```python
from hask import data, d, deriving
from hask import Read, Show, Eq, Ord

Maybe, Nothing, Just =\
    data.Maybe("a") == d.Nothing | d.Just("a") & deriving(Read, Show, Eq, Ord)
```

Let's break this down a bit. The syntax for defining a new [type
constructor](https://wiki.haskell.org/Constructor#Type_constructor) is:

```python
data.TypeName("type param", "type param 2" ... "type param n")
```

This defines a new algebraic datatype with type parameters.

To define [data
constructors](https://wiki.haskell.org/Constructor#Data_constructor) for this
type, use `d.` The name of the data constructor goes first, followed by its
fields. Multiple data constructors should be separted by `|`. If your data
constructor has no fields, you can omit the parens. For example:

```python
FooBar, Foo, Bar =\
    data.FooBar("a", "b") == d.Foo("a", "b", str) | d.Bar
```

To automagically derive typeclass instances for the type, add `&
deriving(...typeclasses...)` after the data constructor declarations.
Currently, the only typeclasses that can be derived are `Eq`, `Show`, `Read`,
`Ord`, and `Bounded`.

Putting it all together, here are the definitions of `Either` and `Ordering`:

```python
Either, Left, Right =\
    data.Either("a", "b") == d.Left("a") | d.Right("b") & deriving(Read, Show, Eq)


Ordering, LT, EQ, GT =\
    data.Ordering == d.LT | d.EQ | d.GT & deriving(Read, Show, Eq, Ord, Bounded)
```

You can now use the data constructors defined in a `data` statement to create
instances of these new types. If the data constructor takes no arguments, you
can use it just like a variable.

```python
>>> Just(10)
Just(10)

>>> Nothing
Nothing

>>> Just(Just(10))
Just(Just(10))

>>> Left(1)
Left(1)

>>> Foo(1, 2, "hello")
Foo(1, 2, 'hello')
```

You can view the type of an object with `_t` (equivalent to `:t` in ghci).

```python
>>> from hask import _t

>>> _t(1)
int

>>> _t(Just("soylent green"))
(Maybe str)

>>> _t(Right(("a", 1)))
(Either a (str, int))

>>> _t(Just)
(a -> Maybe a)

>>> _t(L[1, 2, 3, 4])
[int]
```


### The type system and typed functions

So what's up with those types? Hask operates its own shadow [Hindley-Milner
type system](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system)
on top of Python's type system; `_t` shows the Hask type of a particular
object.

In Hask, typed functions take the form of `TypedFunc` objects, which are typed
wrappers around Python functions. There are two ways to create `TypedFunc`
objects:

1) Use the `sig` decorator to decorate the function with the type signature

```python
@sig(H/ "a" >> "b" >> "a")
def const(x, y):
    return x
```

2) Use the `**` operator (similar to `::` in Haskell) to provide the type.
Useful for turning functions or lambdas into `TypedFunc` objects in the REPL,
or wrapping already-defined Python functions.

```python
def const(x, y):
    return x

const = const ** (H/ "a" >> "b" >> "a")
```

`TypedFunc` objects have several special properties.  First, they are type
checked--when arguments are supplied, the type inference engine will check
whether their types match the type signature, and raise a `TypeError` if there
is a discrepancy.

```python
>>> f = (lambda x, y: x + y) ** (H/ int >> int >> int)

>>> f(2, 3)
5

>>> f(9, 1.0)  # type error
```

Second, `TypedFunc` objects can be [partially
applied](https://wiki.haskell.org/Partial_application):

```python
>>> g = (lambda a, b, c: a / (b + c)) ** (H/ int >> int >> int >> int)

>>> g(10, 2, 3)
2

>>> part_g = g(12)

>>> part_g(2, 2)
3

>>> g(20, 1)(4)
4
```

`TypedFunc` objects also have two special infix operators, the `*` and `%`
operators. `*` is the compose operator (equivalent to `(.)` in Haskell), so
`f * g` is equivalent to `lambda x: f(g(x))`. `%` is just the apply operator,
which applies a `TypedFunc` to one argument (equivalent to `($)` in Haskell).
The convinience of this notation (when combined with partial application)
cannot be overstated--you can get rid of a ton of nested parenthesis this way.

```python
>>> from hask.Prelude import flip
>>> h = (lambda x, y: x / y) ** (H/ float >> float >> float)

>>> h(3.0) * h(6.0) * flip(h, 2.0) % 36.0
9.0
```

The compose operation is also typed-checked, which makes it appealing to write
programs in [pointfree style](https://wiki.haskell.org/Pointfree), i.e,
chaining together lots of functions with composition and relying on the type
system to catch programming errors.

As you would expect, data constructors are also just `TypedFunc` objects:

```python
>>> Just * Just * Just * Just % 77
Just(Just(Just(Just(77))))
```

The type signature syntax is very simple, and consists of a few basic
primitives that can be combined to build any type signature:

| Primitive | Syntax/examples |
| --------- | --------------- |
| Type literal for Python builtin type or user-defined class | `int`, `float`, `set`, `list` |
| Type variable | `"a"`, `"b"`, `"zz"` |
| `List` of some type | `[int]`, `["a"]`, `[["a"]]` |
| Tuple type | `(int, int)`, `("a", "b", "c")`, `(int, ("a", "b"))` |
| ADT with type parameters | `t(Maybe, "a")`, `t(Either, "a", str)` |
| Unit type (`None`) | `None` |
| Untyped Python function | `func` |
| Typeclass constraint | `H[(Eq, "a"), (Show, "b")]/`, `H[(Functor, "f"), (Show, "f")]/` |

Some examples:

```python
# add two ints together
@sig(H/ int >> int >> int)
def add(x, y):
    return x + y


# reverse order of arguments to a function
@sig(H/ (H/ "a" >> "b" >> "c") >> "b" >> "a" >> "c")
def flip(f, b, a):
    return f(a, b)


# map a Python (untyped) function over a Python (untyped) set
@sig(H/ func >> set >> set)
def set_map(fn, lst):
    return set((fn(x) for x in lst))


# map a typed function over a List
@sig(H/ (H/ "a" >> "b") >> ["a"] >> ["b"])
def map(f, xs):
    return L[(f(x) for x in xs)]


# type signature with an Eq constraint
@sig(H[(Eq, "a")]/ "a" >> ["a"] >> bool)
def not_in(y, xs):
    return not any((x == y for x in xs))


# type signature with a type constructor (Maybe) that has type arguments
@sig(H/ int >> int >> t(Maybe, int))
def safe_div(x, y):
    return Nothing if y == 0 else Just(x/y)


# type signature for a function that returns nothing
@sig(H/ int >> None)
def launch_missiles(num_missiles):
    print "Launching {0} missiles! Bombs away!" % num_missiles
```

It is also possible to create type synonyms using `t`. For example, check out the definition of `Rational`:

```python
Ratio, R =\
        data.Ratio("a") == d.R("a", "a") & deriving(Eq)


Rational = t(Ratio, int)


@sig(H/ Rational >> Rational >> Rational)
def addRational(rat1, rat2):
    ...
```

### Pattern matching

Pattern matching is a more powerful control flow tool than the `if` statement,
and can be used to deconstruct iterables and ADTs and bind values to local
variables.

Pattern matching expressions follow this syntax:

```python
~(caseof(value_to_match)
    | m(pattern_1) >> return_value_1
    | m(pattern_2) >> return_value_2
    | m(pattern_3) >> return_value_3)
```

Here is a function that uses pattern matching to compute the fibonacci
sequence. Note that within a pattern match expression, `m.*` is used to bind
variables, and `p.*` is used to access them.

```python
def fib(x):
    return ~(caseof(x)
                | m(0)   >> 1
                | m(1)   >> 1
                | m(m.n) >> fib(p.n - 1) + fib(p.n - 2))

>>> fib(1)
1

>>> fib(6)
13
```

As the above example shows, you can combine pattern matching and recursive
functions without a hitch.

You can also deconstruct an iterable using `^` (the cons operator). The variable
before the `^` is bound to the first element of the iterable, and the variable
after the `^` is bound to the rest of the iterable. Here is a function that
adds the first two elements of any iterable, returning `Nothing` if there are
less than two elements:

```python
@sig(H[(Num, "a")]/ ["a"] >> t(Maybe, "a"))
def add_first_two(xs):
    return ~(caseof(xs)
                | m(m.x ^ (m.y ^ m.z)) >> Just(p.x + p.y)
                | m(m.x)               >> Nothing)


>>> add_first_two(L[1, 2, 3, 4, 5])
Just(3)

>>> add_first_two(L[9.0])
Nothing
```

Pattern matching is also very useful for deconstructing ADTs and assigning
their fields to temporary variables.

```python
def default_to_zero(x):
    return ~(caseof(x)
                | m(Just(m.x)) >> p.x
                | m(Nothing)   >> 0)


>>> default_to_zero(Just(27))
27


>>> default_to_zero(Nothing)
0
```

If you find pattern matching on ADTs too cumbersome, you can also use numeric
indexing on ADT fields. An `IndexError` will be thrown if you mess something
up.

```python
>>> Just(20.0)[0]
20.0

>>> Left("words words words words")[0]
'words words words words'

>>> Nothing[0]  # IndexError
```


### Typeclasses and typeclass instances


[Typeclasses](https://en.wikipedia.org/wiki/Type_class) allow you to add
additional functionality to your ADTs. Hask implements all of the major
typeclasses from Haskell (see the Appendix for a full list) and provides syntax
for creating new typeclass instances.

As an example, let's add a [`Monad`](https://wiki.haskell.org/Monad) instance
for the `Maybe` type.  First, however, `Maybe` needs
[`Functor`](https://wiki.haskell.org/Functor) and
[`Applicative`](https://wiki.haskell.org/Applicative_functor) instances.


```python
def maybe_fmap(fn, x):
    """Apply a function to the value inside of a (Maybe a) value"""
    return ~(caseof(x)
                | m(Nothing)   >> Nothing
                | m(Just(m.x)) >> Just(fn(p.x)))


instance(Functor, Maybe).where(
    fmap = maybe_fmap
)
```

`Maybe` is now an instance of `Functor`. This allows us to call `fmap`
and map any function of type `a -> b` into a value of type `Maybe a`.

```python
>>> times2 = (lambda x: x * 2) ** (H/ int >> int)
>>> toFloat = float ** (H/ int >> float)

>>> fmap(toFloat, Just(10))
Just(10.0)

>>> fmap(toFloat, fmap(times2, Just(25)))
Just(50.0)
```

Lots of nested calls to `fmap` get unwieldy very fast. Fortunately, any
instance of `Functor` can be used with the infix `fmap` operator, `*`. This is
equivalent to `<$>` in Haskell. Rewriting our example from above:

```python
>>> (toFloat * times2) * Just(25)
Just(50.0)

>>> (toFloat * times2) * Nothing
Nothing
```

Note that this example uses `*` as both the function compose operator and as
`fmap`, to lift functions into a `Maybe` value. If this seems confusing,
remember that `fmap` for functions is just function composition!


Now that `Maybe` is an instance of `Functor`, we can make it an instance of
`Applicative` and then an instance of `Monad` by defining the appropriate
function implementations. To implement `Applicative`, we just need to provide
`pure`. To implement `Monad`, we need to provide `bind`.


```python
from hask import Applicative, Monad

instance(Applicative, Maybe).where(
    pure = Just
)

instance(Monad, Maybe).where(
    bind = lambda x, f: ~(caseof(x)
                            | m(Just(m.a)) >> f(p.a)
                            | m(Nothing)   >> Nothing)
)
```

The `bind` function also has an infix form, which is `>>` in Hask.

```python
@sig(H/ int >> int >> t(Maybe, int))
def safe_div(x, y):
    return Nothing if y == 0 else Just(x/y)


>>> from hask.Prelude import flip
>>> divBy = flip(safe_div)


>>> Just(9) >> divBy(3)
Just(3)


>>> Just(12) >> divBy(2) >> divBy(2) >> divBy(3)
Just(1)


>>> Just(12) >> divBy(0) >> divBy(6)
Nothing
```

As in Haskell, `List` is also a monad, and `bind` for the `List` type is just
`concatMap`.

```python
>>> from hask.Data.List import replicate
>>> L[1, 2] >> replicate(2) >> replicate(2)
L[1, 1, 1, 1, 2, 2, 2, 2]
```

You can also define typeclass instances for classes that are not ADTs:

```python
class Person(object):
    def __init__(self, name, age):
        self.name = name
        self.age = age


instance(Eq, Person).where(
    eq = lambda p1, p2: p1.name == p2.name and p1.age == p2.age
)

>>> Person("Philip Wadler", 59) == Person("Simon Peyton Jones", 57)
False
```

If you want instances of the `Show`, `Eq`, `Read`, `Ord`, and `Bounded`
typeclasses for your ADTs, it is adviseable to use `deriving` to automagically
generate instances rather than defining them manually.


Defining your own typeclasses is pretty easy--take a look at `help(Typeclass)`
and look at the typeclasses defined in `Data.Functor` and `Data.Num` to
see how it's done.


### Operator sections

Hask also supports operator sections (e.g. `(1+)` in Haskell). Sections are
just `TypedFunc` objects, so they are automagically curried and typechecked.

```python
>>> from hask import __

>>> f = (__ - 20) * (2 ** __) * (__ + 3)
>>> f(10)
8172

>>> ((90/__) * (10+__)) * Just(20)
Just(3)

>>> from hask.Data.List import takeWhile
>>> takeWhile(__<5, L[1, ...])
L[1, 2, 3, 4]

>>> (__+__)('Hello ', 'world')
'Hello world'

>>> (__**__)(2)(10)
1024

>>> from hask.Data.List import zipWith, take
>>> take(5) % zipWith(__ * __, L[1, ...], L[1, ...])
L[1, 4, 9, 16, 25]
```

As you can see, this much easier than using `lambda` and adding a type
signature with the `(lambda x: ...) ** (H/ ...)` syntax.

In addition, the types of the `TypedFuncs` created by sections are always
polymorphic, to allow for any operator overloading.

Note that if you are using IPython, Hask's `__` will conflict with IPython's
special double underscore variable. To avoid conflicts, you can use `from hask
import __ as _s` in IPython.


### Guards

If you don't need the full power of pattern matching and just want a neater
switch statement, you can use guards. The syntax for guards is almost identical
to the syntax for pattern matching.

```python
~(guard(expr_to_test)
    | c(test_1) >> return_value_1
    | c(test_2) >> return_value_2
    | otherwise >> return_value_3
)
```

As in Haskell, `otherwise` will always evaluate to `True` and can be used as a
catch-all in guard expressions. If no match is found (and an `otherwise` clause
is not present), a `NoGuardMatchException` will be raised.

Guards will also play nicely with sections:

```python
>>> from hask import guard, c, otherwise

>>> porridge_tempurature = 80

>>> ~(guard(porridge_tempurature)
...     | c(__ < 20)  >> "Porridge is too cold!"
...     | c(__ < 90)  >> "Porridge is just right!"
...     | c(__ < 150) >> "Porridge is too hot!"
...     | otherwise   >> "Porridge has gone thermonuclear"
... )
'Porridge is just right!'
```

If you need a more complex conditional, you can always use lambdas, regular
Python functions, or any other callable in your guard condition.

```python
def examine_password_security(password):
    analysis = ~(guard(password)
        | c(lambda x: len(x) > 20) >> "Wow, that's one secure password"
        | c(lambda x: len(x) < 5)  >> "You made Bruce Schneier cry"
        | c(__ == "12345")         >> "Same combination as my luggage!"
        | otherwise                >> "Hope it's not 'password'"
    )
    return analysis


>>> nuclear_launch_code = "12345"

>>> examine_password_security(nuclear_launch_code)
'Same combination as my luggage!'
```

### Monadic error handling (of Python functions)

If you want to use `Maybe` and `Either` to handle errors raised by Python
functions defined outside Hask, you can use the decorators `in_maybe` and
`in_either` to create functions that call the original function and return the
result wrapped inside a `Maybe` or `Either` value.

If a function wrapped in `in_maybe` raises an exception, the wrapped function
will return `Nothing`. Otherwise, the result will be returned wrapped in a
`Just`.

```python
def eat_cheese(cheese):
    if cheese <= 0:
        raise ValueError("Out of cheese error")
    return cheese - 1

maybe_eat = in_maybe(eat_cheese)

>>> maybe_eat(1)
Just(0)

>>> maybe_eat(0)
Nothing
```

Note that this is equivalent to lifting the original function into the Maybe
monad. That is, its type has changed from `func` to `a -> Maybe b`.  This
makes it easier to use the convineient monad error handling style commonly seen
in Haskell with existing Python functions.

Continuing with this silly example, let's try to eat three pieces of cheese,
returning `Nothing` if the attempt was unsuccessful:

```python
>>> cheese = 10
>>> cheese_left = Just(cheese) >> maybe_eat >> maybe_eat >> maybe_eat
>>> cheese_left
Just(7)

>>> cheese = 1
>>> cheese_left = Just(cheese) >> maybe_eat >> maybe_eat >> maybe_eat
>>> cheese_left
Nothing
```

Notice that we have taken a regular Python function that throws Exceptions, and
are now handling it in a type-safe, monadic way.

The `in_either` function works just like `in_maybe`. If an Exception is thrown,
the wrapped function will return the exception wrapped in `Left`. Otherwise,
the result will be returned wrapped in `Right`.

```python
either_eat = in_either(eat_cheese)

>>> either_eat(Right(10))
Right(9)

>>> either_eat(Right(0))
Left(ValueError('Out of cheese error',))
```

Chained cheese-eating in the `Either` monad is left as an exercise for
the reader.

You can also use `in_maybe` or `in_either` as decorators:

```python
@in_maybe
def some_function(x, y):
    ...
```


### Standard libraries

All of your favorite functions from `Prelude`, `Data.List`, `Data.Maybe`,
`Data.Either`, `Data.Monoid`, and more are implemented too. Everything is
pretty well documented, so if you're not sure about some function or typeclass,
use `help` liberally. See the Appendix below for a full list of modules. Some
highlights:

```python
>>> from hask.Data.Maybe import mapMaybe
>>> mapMaybe(safe_div(12)) % L[0, 1, 3, 0, 6]
L[12, 4, 2]


>>> from hask.Data.List import isInfixOf
>>> isInfixOf(L[2, 8], L[1, 4, 6, 2, 8, 3, 7])
True


>>> from hask.Control.Monad import join
>>> join(Just(Just(1)))
Just(1)
```

Hask also provies `TypeFunc` wrappers for everything in `__builtins__` for ease
of compatibity. (Eventually, Hask will have typed wrappers for most of the
Python standard library.)

```python
>>> from hask.Prelude import flip
>>> from hask.Data.Tuple import snd
>>> from hask.Python.builtins import divmod, hex

>>> hexMod = hex * snd * flip(divmod, 16)
>>> hexMod(24)
'0x8'
```

### Internals

If you want to poke around behind the curtain, here are some useful starting
points:

* `typeof(obj)` returns an object's type in Hask's type system
* `has_instance(some_type, typeclass)` tests for typeclass membership
* `nt_to_tuple` converts instances of `namedtuple` (including Hask ADTs) into
  regular tuples
* `typify` converts a Python function into a `TypedFunc` object







## Appendix

**Table 1.** Overview of Hask typeclasses.

| Typeclass | Superclasses | Required functions | Optional functions | Magic Methods |
| --------- | ------------ | ------------------ | ------------------ | ------------- |
| `Show` | | `show` | | `str` |
| `Read` | | `read` | | |
| `Eq` | | `eq` | `ne` | `==`, `!=` | |
| `Ord` | `Eq` | `lt` | `gt`, `le`, `ge` | `<`, `<`, `=<`, `=>` | |
| `Enum` | | `toEnum`, `fromEnum` | `pred`, `succ`, `enumTo`, `enumFromTo`, `enumFromThen`, `enumFromThenTo` | |
| `Bounded` | | `minBound`, `maxBound` | | |
| `Functor` | | `fmap` | | `*` |
| `Applicative` | `Functor` | `pure` | | |
| `Monad` | `Applicative` | `bind` | | `>>` |
| `Monoid` | | `mappend`, `mempty` |  `mconcat` | `+` |
| `Foldable` | | `foldr` | `foldr_`, `foldl`, `foldl_`, `foldr1`, `foldl1`, `toList`, `null`, `length`, `elem`, `maximum`, `minimum`, `sum`, `product` | `len`, `iter` |
| `Traversable` | `Foldable`, `Functor` | `traverse` | `sequenceA`, `mapM`, `sequence` | |
| `Num` | `Show`, `Eq` | `add`, `mul`, `abs`, `signum`, `fromInteger`, `negate` | `sub` | `+`, `-`, `*` |
| `Real` | `Num`, `Ord` | `toRational` | |
| `Integral` | `Real`, `Enum` | `quotRem`, `divMod`, `toInteger` | `quot`, `rem`, `div`, `mod` | `/`, `%` |
| `Fractional` | `Num` | `fromRational`, `div` | `recip` | `/` |
| `Floating` | `Fractional` | `exp`, `sqrt`, `log`, `pow`, `logBase`, `sin`, `tan`, `cos`, `asin`, `atan`, `acos`, `sinh`, `tanh`, `cosh`, `asinh`, `atanh`, `acosh` | |
| `RealFrac` | `Real`, `Fractional` | `properFraction`, `truncate`, `round`, `ceiling`, `floor` |
| `RealFloat` | `Floating`, `RealFrac` | `floatRange`, `isNaN`, `isInfinite`, `isNegativeZero`, `atan2` |


**Table 2.** Hask library structure.

| Module | Dependencies | Exported functions |
| ------ | ------------ | ------------------ |
| `hask` | `hask.lang`, `hask.Data.Char`, `hask.Data.Either`, `hask.Data.Eq`, `hask.Data.Foldable`, `hask.Data.Functor`, `hask.Data.List`, `hask.Data.Maybe`, `hask.Data.Monoid`, `hask.Data.Num`, `hask.Data.Ord`, `hask.Data.Ratio`, `hask.Data.String`, `hask.Data.Traversable`, `hask.Data.Tuple`, `hask.Control.Applicative`, `hask.Control.Monad`, `hask.Python.builtins` | `instance`, `__`, `guard`, `c`, `otherwise`, `NoGuardMatchException`, `L`, `data`, `d`, `deriving`, `sig`, `H`, `t`, `func`, `TypeSignatureError`, `caseof`, `p`, `m`, `IncompletePatternError`, `_t`, `_i`, `_q`, `typeof`, `has_instance`, `Typeclass`, `Hask`, `Read`, `Show`, `Eq`, `Ord`, `Enum`, `Bounded`, `Num`, `Real`, `Integral`, `Fractional`, `Floating`, `RealFrac`, `RealFloat`, `Functor`, `Applicative`, `Monad`, `Traversable`, `Foldable`, `Maybe`, `Just`, `Nothing`, `in_maybe`, `Either`, `Left`, `Right`, `in_either`, `Ordering`, `LT`, `EQ`, `GT` |
| `hask.Prelude` | `hask.lang` | `hask.Data.Either`, `hask.Data.Eq`, `hask.Data.Foldable`, `hask.Data.Functor`, `hask.Data.List`, `hask.Data.Maybe`, `hask.Data.Num`, `hask.Data.Ord`, `hask.Data.Traversable`, `hask.Data.Tuple`, `hask.Control.Applicative`, `hask.Control.Monad` | `Maybe`, `Just`, `Nothing`, `in_maybe`, `maybe`, `Either`, `Left`, `Right`, `in_either`, `either`, `Ordering`, `LT`, `EQ`, `GT`, `fst`, `snd`, `curry`, `uncurry`, `Read`, `Show`, `show`, `Eq`, `Ord`, `max`, `min`, `compare`, `Enum`, `fromEnum`, `succ`, `pred`, `enumFromThen`, `enumFrom`, `enumFromThenTo`, `enumFromTo`, `Bounded`, `Functor`, `fmap`, `Applicative`, `Monad`, `Foldable`, `Traversable`, `Num`, `abs`, `negate`, `signum`, `Fractional`, `recip`, `Integral`, `toRatio`, `Ratio`, `R`, `Rational`, `Floating`, `exp`, `sqrt`, `log`, `pow`, `logBase`, `sin`, `tan`, `cos`, `asin`, `atan`, `acos`, `sinh`, `tanh`, `cosh`, `asinh`, `atanh`, `acosh`, `Real`, `toRational`, `RealFrac`, `properFraction`, `truncate`, `round`, `ceiling`, `floor`, `RealFloat`, `isNaN`, `isInfinite`, `isNegativeZero`, `atan2`, `subtract`, `even`, `odd`, `gcd`, `lcm`, `Functor`, `Applicative`, `Monad`, `sequence`, `sequence_`, `mapM`, `mapM_`, `id`, `const`, `flip`, `until`, `asTypeOf`, `error`, `undefined`, `map`, `filter`, `head`, `last`, `tail`, `init`, `null`, `reverse`, `length`, `foldl`, `foldl1`, `foldr`, `foldr1`, `and_`, `or_`, `any`, `all`, `sum`, `product`, `concat`, `concatMap`, `maximum`, `minimum`, `scanl`, `scanl1`, `scanr`, `scanr1`, `iterate`, `repeat`, `replicate`, `cycle`, `take`, `drop`, `splitAt`, `takeWhile`, `dropWhile`, `span`, `break_`, `elem`, `notElem`, `lookup`, `zip`, `zip3`, `zipWith`, `zipWith3`, `unzip`, `unzip3`, `lines`, `words`, `unlines`, `unwords` |
| `hask.Data.Maybe` | `hask.lang`, `hask.Data.Eq`, `hask.Data.Ord`, `hask.Data.Functor`, `hask.Control.Applicative`, `hask.Control.Monad` | `Maybe` (`Nothing`, `Just`), `in_maybe`, `maybe`, `isJust`, `isNothing`, `fromJust`, `listToMaybe`, `maybeToList`, `catMaybes`, `mapMaybe` |
| `hask.Data.Either` | `hask.lang`, `hask.Data.Eq`, `hask.Data.Ord`, `hask.Data.Functor`, `hask.Control.Applicative`, `hask.Control.Monad` | `Either` (`Left`, `Right`), `in_either`, `either`, `lefts`, `rights`, `isLeft`, `isRight`, `partitionEithers` |
| `hask.Data.List` | `hask.lang`, `hask.Data.Foldable`, `hask.Data.Eq`, `hask.Data.Ord`, `hask.Data.Num`, `hask.Data.Maybe` | `head`, `last`, `tail`, `init`, `uncons`, `null`, `length`, `map`, `reverse`, `intersperse`, `intercalate`, `transpose`, `subsequences`, `permutations`, `foldl`, `foldl_`, `foldl1`, `foldl1_`, `foldr`, `foldr1`, `concat`, `concatMap`, `and_`, `or_`, `any`, `all`, `sum`, `product`, `minimum`, `maximum`, `scanl`, `scanl1`, `scanr`, `scanr1`, `mapAccumL`, `mapAccumR`, `iterate`, `repeat`, `replicate`, `cycle`, `unfoldr`, `take`, `drop`, `splitAt`, `takeWhile`, `dropWhile`, `dropWhileEnd`, `span`, `break_`, `stripPrefix`, `group`, `inits`, `tails`, `isPrefixOf`, `isSuffixOf`, `isInfixOf`, `isSubsequenceOf`, `elem`, `notElem`, `lookup`, `find`, `filter`, `partition`, `elemIndex`, `elemIndices`, `findIndex`, `findIndicies`, `zip`, `zip3`, `zip4`, `zip5`, `zip6`, `zip7`, `zipWith`, `zipWith3`, `zipWith4`, `zipWith5`, `zipWith6`, `zipWith7`, `unzip`, `unzip3`, `unzip4`, `unzip5`, `unzip6`, `unzip7`, `lines`, `words`, `unlines`, `unwords`, `nub`, `delete`, `diff`, `union`, `intersect`, `sort`, `sortOn`, `insert`, `nubBy`, `deleteBy`, `deleteFirstBy`, `unionBy`, `intersectBy`, `groupBy`, `sortBy`, `insertBy`, `maximumBy`, `minimumBy`, `genericLength`, `genericTake`, `genericDrop`, `genericSplitAt`, `genericIndex`, `genericReplicate` |
| `hask.Data.String` | `hask.lang` | `words`, `unwords`, `lines`, `unlines` |
| `hask.Data.Tuple` | `hask.lang` | `fst`, `snd`, `swap`, `curry`, `uncurry` |
| `hask.Data.Char` | `hask.lang` | `isControl`, `isSpace`, `isLower`, `isUpper`, `isAlpha`, `isAlphaNum`, `isPrint`, `isDigit`, `isOctDigit`, `isHexDigit`, `isLetter`, `isMark`, `isNumber`, `isPunctuation`, `isSymbol`, `isSeparator`, `isAscii`, `isLatin1`, `isAsciiUpper`, `toLower`, `toUpper`, `toTitle`, `digitToInt`, `intToDigit`, `chr`, `ord` |
| `hask.Data.Eq` | `hask.lang` | `Eq` (`==`, `!=`)
| `hask.Data.Ord` | `hask.lang`, `hask.Data.Eq` | `Ord` (`>`, `<`, `>=`, `<=`), `Ordering` (`LT`, `EQ`, `GT`), `max`, `min`, `compare`, `comparing` |
| `hask.Data.Functor` | `hask.lang` | `Functor` (`fmap`, `*`),  |
| `hask.Data.Foldable` | `hask.lang` | `Foldable` (`foldr`, `foldr_`, `foldl`, `foldl_`, `foldr1`, `foldl1`, `toList`, `null`, `length`, `elem`, `maximum`, `minimum`, `sum`, `product`), `foldlM`, `foldrM`, `traverse_`, `for_`, `sequenceA_`, `mapM_`, `forM_`, `sequence_`, `concat`, `concatMap` , `and_`, `or_`, `all_`, `maximumBy_`, `minimumBy`, `notElem`, `find` |
| `hask.Data.Traversable` | `hask.lang`, `hask.Data.Foldable`, `hask.Data.Functor` | `Traversable` (`traverse`, `sequenceA`, `mapM`, `sequence`), `for1`, `forM`, `mapAccumL`, `mapAccumR` |
| `hask.Data.Monoid` | `hask.lang` | `Monoid` (`mappend`, `mempty`, `mconcat`) |
| `hask.Data.Ratio` | `hask.lang`, `hask.Data.Num` | `Integral`, `Ratio` (`R`), `Rational`, `toRatio`, `toRational`, `numerator`, `denominator` |
| `hask.Data.Num` | `hask.lang`, `hask.Data.Eq`, `hask.Data.Ord` | `Num` (`+`, `*`, `abs`, `signum`, `fromInteger`, `negate`, `-`), `Fractional` (`fromRational`, `/`, `recip`), `Floating` (`exp`, `sqrt`, `log`, `pow`, `logBase`, `sin`, `tan`, `cos`, `asin`, `atan`, `acos`, `sinh`, `tanh`, `cosh`, `asinh`, `atanh`, `acosh`), `Real` (`toRational`), `Integral` (`quotRem`, `quot`, `rem`, `div`, `mod`), `toRatio`, `RealFrac` (`properFraction`, `truncate`, `round`, `ceiling`, `floor`), `RealFloat` (`isNan`, `isInfinite`, `isNegativeZero`, `atan2`) |
| `hask.Control.Applicative` | `hask.lang`, `hask.Data.Functor` | `Applicative` |
| `hask.Control.Monad` | `hask.lang`, `hask.Control.Applicative`, `hask.Data.Functor` | `Monad` (`bind`, `>>`), `join`, `liftM` |
| `hask.Python.builtins` | `hask.lang` | `callable`, `cmp`, `delattr`, `divmod`, `frozenset`, `getattr`, `hasattr`, `hash`, `hex`, `isinstance`, `issubclass`, `len`, `oct`, `repr`, `setattr`, `sorted`, `unichr` |
| `hask.lang` | | `Show` (`show`), `Read`, `Eq`, `Ord`, `Enum` (`fromEnum`, `succ`, `pred`, `enumFrom`, `enumFromTo`, `enumFromThen`, `enumFromThenTo`), `Bounded`, `typeof`, `is_builtin`, `has_instance`, `nt_to_tuple`, `build_instance`, `Typeclass`, `Hask`, `TypedFunc`, `TypeSignatureError`, `undefined`, `caseof`, `m`, `p`, `IncompletePattnerError`, `data`, `d`, `deriving`, `H`, `sig`, `t`, `func`, `typify`, `NoGuardMatchException`, `guard`, `c`, `otherwise`, `instance`, `__`, `_t`, `_q`, `_i`, `List`, `L` |
