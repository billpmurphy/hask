import inspect
import operator
import string
import sys
from collections import deque, defaultdict

from type_system import typeof
from type_system import Typeclass
from type_system import TypedFunc
from type_system import TypeSignature
from type_system import TypeSignatureHKT
from type_system import ADT
from type_system import build_ADT
from type_system import build_sig
from type_system import make_fn_type
from type_system import PatternMatchBind
from type_system import PatternMatchListBind
from type_system import pattern_match
from type_system import Undefined
from type_system import PyFunc


#=============================================================================#
# Base class for syntactic constructs


__magic_methods__ = ["__%s__" % s for s in set((
    "len", "getitem", "setitem", "delitem", "iter", "reversed", "contains",
    "missing", "delattr", "call", "enter", "exit", "eq", "ne", "gt", "lt",
    "ge", "le", "pos", "neg", "abs", "invert", "round", "floor", "ceil",
    "trunc", "add", "sub", "mul", "div", "truediv", "floordiv", "mod",
    "divmod", "pow", "lshift", "rshift", "or", "and", "xor", "radd", "rsub",
    "rmul", "rdiv", "rtruediv", "rfloordiv", "rmod", "rdivmod", "rpow",
    "rlshift", "rrshift", "ror", "rand", "rxor", "isub", "imul", "ifloordiv",
    "idiv", "imod", "idivmod", "irpow", "ilshift", "irshift", "ior", "iand",
    "ixor", "nonzero"))]


def replace_magic_methods(cls, fn):
    """
    Replace the magic method of a class with some function or method.

    Args:
        cls: The class to modify
        fn: The function to replace cls's magic methods with
    """
    for attr in __magic_methods__:
        setattr(cls, attr, fn)
    return


class Syntax(object):
    """
    Base class for new syntactic constructs. All of the new "syntax" elements
    of Hask inherit from this class.

    By default, a piece of syntax will raise a syntax error with a standard
    error message if the syntax object is used with a Python builtin operator.

    Subclasses may override these methods to define what syntax is valid for
    those objects.
    """
    def __init__(self, err_msg):
        self.__syntax_err_msg = err_msg
        self.invalid_syntax = SyntaxError(self.__syntax_err_msg)

    def __raise(self):
        raise self.invalid_syntax

    __syntaxerr__ = lambda s, *a: s.__raise()


replace_magic_methods(Syntax, Syntax.__syntaxerr__)


#=============================================================================#
# Typeclass instance declaration


class instance(Syntax):
    """
    Special syntax for defining typeclass instances.

    Example usage:

    instance(Functor, Maybe).where(
        fmap = ...
    )
    """
    def __init__(self, typecls, cls):
        if not (inspect.isclass(typecls) and issubclass(typecls, Typeclass)):
            raise TypeError("%s is not a typeclass" % typecls)
        self.typeclass = typecls
        self.cls = cls
        return

    def where(self, **kwargs):
        self.typeclass.make_instance(self.cls, **kwargs)
        return


#=============================================================================#
# Type signatures


class __constraints__(Syntax):
    """
    H/ creates a new function type signature.

    Examples:
    (H/ int >> int >> int)
    (H/ (H/ "a" >> "b" >> "c") >> "b" >> "a" >> "c")
    (H/ func >> set >> set)
    (H/ (H/ "a" >> "b") >> ["a"] >> ["b"])
    (H[(Eq, "a")]/ "a" >> ["a"] >> bool)
    (H/ int >> int >> t(Maybe, int))
    (H/ int >> None)

    See help(sig) for more information on type signature decorators.
    """
    def __init__(self, constraints=()):
        self.constraints = defaultdict(lambda: [])
        if len(constraints) > 0:
            # multiple typeclass constraints
            if isinstance(constraints[0], tuple):
                for con in constraints:
                    self.__add_constraint(con)
            # only one typeclass constraint
            else:
                self.__add_constraint(constraints)
        super(__constraints__, self).__init__("Syntax error in type signature")
        return

    def __add_constraint(self, con):
        if len(con) != 2 or not isinstance(con, tuple):
            raise SyntaxError("Invalid typeclass constraint: %s" % str(con))

        if not isinstance(con[1], str):
            raise SyntaxError("%s is not a type variable" % con[1])

        if not (inspect.isclass(con[0]) and issubclass(con[0], Typeclass)):
            raise SyntaxError("%s is not a typeclass" % con[0])

        self.constraints[con[1]].append(con[0])
        return

    def __getitem__(self, constraints):
        return __constraints__(constraints)

    def __div__(self, arg):
        return __signature__((), self.constraints).__rshift__(arg)

    def __truediv__(self, arg):
        return self.__div__(arg)


class __signature__(Syntax):
    """
    Class that represents a (complete or incomplete) type signature.
    """
    def __init__(self, args, constraints):
        self.sig = TypeSignature(args, constraints)
        super(__signature__, self).__init__("Syntax error in type signature")
        return

    def __rshift__(self, arg):
        arg = arg.sig if isinstance(arg, __signature__) else arg
        return __signature__(self.sig.args + (arg,), self.sig.constraints)

    def __rpow__(self, fn):
        return sig(self)(fn)


H = __constraints__()
func = PyFunc


class sig(Syntax):
    """
    Decorator to convert a Python function into a statically typed function
    (TypedFunc object).

    TypedFuncs are automagically curried, and polymorphic type arguments will
    be inferred by the type system.

    Usage:

    @sig(H/ int >> int >> int )
    def add(x, y):
        return x + y

    @sig(H[(Show, "a")]/ >> "a" >> str)
    def to_str(x):
        return str(x)
    """
    def __init__(self, signature):
        super(self.__class__, self).__init__("Syntax error in type signature")

        if not isinstance(signature, __signature__):
            msg = "Signature expected in sig(); found %s" % signature
            raise SyntaxError(msg)

        elif len(signature.sig.args) < 2:
            raise SyntaxError("Not enough type arguments in signature")

        self.sig = signature.sig
        return

    def __call__(self, fn):
        fn_args = build_sig(self.sig)
        fn_type = make_fn_type(fn_args)
        return TypedFunc(fn, fn_args, fn_type)


def t(type_constructor, *params):
    if inspect.isclass(type_constructor) and \
       issubclass(type_constructor, ADT) and \
       len(type_constructor.__params__) != len(params):
            raise TypeError("Incorrect number of type parameters to %s" %
                            type_constructor.__name__)

    params = [p.sig if isinstance(p, __signature__) else p for p in params]
    return TypeSignatureHKT(type_constructor, params)


def typify(fn, hkt=None):
    """
    Convert an untyped Python function to a TypeFunc.

    Args:
        fn: The function to wrap
        hkt: A higher-kinded type wrapped in a closure (e.g., lambda x:
             t(Maybe, x))

    Returns:
        A TypedFunc object with a polymorphic type (e.g. a -> b -> c, etc) with
        the same number of arguments as fn. If hkt is supplied, the return type
        will be the supplied HKT parameterized by a type variable.

    Example usage:

    @typify(hkt=lambda x: t(Maybe, x))
    def add(x, y):
        return x + y
    """
    args = [chr(i) for i in range(97, 98 + fn.func_code.co_argcount)]
    if hkt is not None:
        args[-1] = hkt(args[-1])
    return sig(__signature__(args, []))


#=============================================================================#
# Undefined values

class __undefined__(Undefined):
    """
    Undefined value with special syntactic powers. Whenever you try to use one
    if its magic methods, it returns undefined. Used to prevent overzealous
    evaluation in pattern matching.

    Its type unifies with any other type.
    """
    pass

replace_magic_methods(__undefined__, lambda *a: __undefined__())
undefined = __undefined__()


#=============================================================================#
# Pattern matching

# Constructs for pattern matching.
# Note that the approach implemented here uses lots of global state and is
# pretty much the opposite of "functional" or "thread-safe."

class IncompletePatternError(Exception):
    pass


class MatchStackFrame(object):
    """One stack frame for pattern matching bound variable stack"""
    def __init__(self, value):
        self.value = value
        self.cache = {}
        self.matched = False


class MatchStack(object):
    """Stack for storing locally bound variables from matches"""
    __stack__ = deque()

    @classmethod
    def push(cls, value):
        """Push a new frame onto the stack, representing a new case expr"""
        cls.__stack__.append(MatchStackFrame(value))
        return

    @classmethod
    def pop(cls):
        """Pop the current frame off the stack"""
        cls.__stack__.pop()
        return

    @classmethod
    def get_frame(cls):
        """Access the current frame"""
        return cls.__stack__[-1]

    @classmethod
    def get_name(cls, name):
        """Lookup a variable name in the current frame"""
        if cls.get_frame().matched:
            return undefined
        return cls.get_frame().cache.get(name, undefined)


class __var_bind__(Syntax):
    """
    m.* binds a local variable while pattern matching.
    For example usage, see help(caseof).
    """
    def __getattr__(self, name):
        return __pattern_bind__(name)

    def __call__(self, pattern):
        is_match, env = pattern_match(MatchStack.get_frame().value, pattern)
        if is_match and not MatchStack.get_frame().matched:
            MatchStack.get_frame().cache = env
        return __match_test__(is_match)


class __var_access__(Syntax):
    """
    p.* accesses a local variable bound during pattern matching.
    For example usage, see help(caseof).
    """
    def __getattr__(self, name):
        return MatchStack.get_name(name)


m = __var_bind__("Syntax error in pattern match")
p = __var_access__("Syntax error in pattern match")


class __pattern_bind_list__(Syntax, PatternMatchListBind):
    """
    Class that represents a pattern designed to match an iterable, consisting
    of a head (one element) and a tail (zero to many elements).
    """
    def __init__(self, head, tail):
        self.head = [head]
        self.tail = tail
        super(__pattern_bind_list__, self).__init__("Syntax error in match")

    def __rxor__(self, head):
        self.head.insert(0, head)
        return self


class __pattern_bind__(Syntax, PatternMatchBind):
    """
    Class that represents a pattern designed to match any value and bind it to
    a name.
    """
    def __init__(self, name):
        self.name = name
        super(__pattern_bind__, self).__init__("Syntax error in match")

    def __rxor__(self, cell):
        return __pattern_bind_list__(cell, self)

    def __xor__(self, other):
        if isinstance(other, __pattern_bind_list__):
            return other.__rxor__(self)

        elif isinstance(other, __pattern_bind__):
            return __pattern_bind_list__(self, other)

        raise self.invalid_syntax
        return


class __match_line__(Syntax):
    """
    This class represents one line of a caseof expression, i.e.:
    m( ... ) >> return_value
    """
    def __init__(self, is_match, return_value):
        self.is_match = is_match
        self.return_value = return_value
        return


class __match_test__(Syntax):
    """
    This class represents the pattern part of one caseof line, i.e.:
    m( ... )
    """
    def __init__(self, is_match):
        self.is_match = is_match
        return

    def __rshift__(self, value):
        MatchStack.get_frame().cache = {}
        return __match_line__(self.is_match, value)


class __unmatched_case__(Syntax):
    """
    This class represents a caseof expression in mid-evaluation, when zero or
    more lines have been tested, but before a match has been found.
    """
    def __or__(self, line):
        if line.is_match:
            MatchStack.get_frame().matched = True
            return __matched_case__(line.return_value)
        return self

    def __invert__(self):
        value = MatchStack.get_frame().value
        MatchStack.pop()
        raise IncompletePatternError(value)


class __matched_case__(Syntax):
    """
    This class represents a caseof expression in mid-evaluation, when one or
    more lines have been tested and after a match has been found.
    """
    def __init__(self, return_value):
        self.value = return_value
        return

    def __or__(self, line):
        return self

    def __invert__(self):
        MatchStack.pop()
        return self.value


class caseof(__unmatched_case__):
    """
    Pattern matching can be used to deconstruct lists and ADTs, and is a very
    useful control flow tool.

    Usage:

    ~(caseof(value_to_match)
        | m(pattern_1) >> return_value_1
        | m(pattern_2) >> return_value_2
        | m(pattern_3) >> return_value_3)

    Example usage:

    def fib(x):
        return ~(caseof(x)
                    | m(0)   >> 1
                    | m(1)   >> 1
                    | m(m.n) >> fib(p.n - 1) + fib(p.n - 2))
    """
    def __init__(self, value):
        if isinstance(value, Undefined):
            return
        MatchStack.push(value)
        return


#=============================================================================#
# ADT creation syntax ("data" expressions)


## "data"/type constructor half of the expression

class __data__(Syntax):
    """
    `data` is part of Hask's special syntax for defining ADTs.

    Example usage:

    Maybe, Nothing, Just =\
    data.Maybe("a") == d.Nothing | d.Just("a") & deriving(Read, Show, Eq, Ord)
    """
    def __init__(self):
        super(__data__, self).__init__("Syntax error in `data`")

    def __getattr__(self, value):
        if not value[0] in string.uppercase:
            raise SyntaxError("Type constructor name must be capitalized")
        return __new_tcon_enum__(value)


class __new_tcon__(Syntax):
    """
    Base class for Syntax classes related to creating new type constructors.
    """
    def __init__(self, name, args=()):
        self.name = name
        self.args = args
        super(__new_tcon__, self).__init__("Syntax error in `data`")

    def __eq__(self, d):
        # one data constructor, zero or more derived typeclasses
        if isinstance(d, __new_dcon__):
            return build_ADT(self.name, self.args, [(d.name, d.args)], d.classes)

        # one or more data constructors, zero or more derived typeclasses
        elif isinstance(d, __new_dcons_deriving__):
            return build_ADT(self.name, self.args, d.dcons, d.classes)

        raise self.invalid_syntax


class __new_tcon_enum__(__new_tcon__):
    """
    This class represents a `data` statement in mid evaluation; it represents
    the part of the expression that builds the type constructor, before type
    parameters have been added.

    Examples:

    data.Either
    data.Ordering
    """
    def __call__(self, *typeargs):
        if len(typeargs) < 1:
            msg = "Missing type args in statement: `data.%s()`" % self.name
            raise SyntaxError(msg)

        # make sure all type params are strings
        if not all((type(arg) == str for arg in typeargs)):
            raise SyntaxError("Type parameters must be strings")

        # make sure all type params are letters only
        is_letters = lambda xs: all((x in string.lowercase for x in xs))
        if not all((is_letters(arg) for arg in typeargs)):
            raise SyntaxError("Type parameters must be lowercase letters")

        # all type parameters must have unique names
        if len(typeargs) != len(set(typeargs)):
            raise SyntaxError("Type parameters are not unique")

        return __new_tcon_hkt__(self.name, typeargs)


class __new_tcon_hkt__(__new_tcon__):
    """
    This class represents a `data` statement in mid evaluation; it represents
    the part of the expression that builds the type constructor, after type
    parameters have been added.

    Examples:

    data.Maybe("a")
    data.Either("a", "b")
    """
    pass


## "d"/data constructor half of the expression


class __d__(Syntax):
    """
    `d` is part of hask's special syntax for defining algebraic data types.

    See help(data) for more information.
    """
    def __init__(self):
        super(__d__, self).__init__("Syntax error in `d`")

    def __getattr__(self, value):
        if not value[0] in string.uppercase:
            raise SyntaxError("Data constructor name must be capitalized")
        return __new_dcon_enum__(value)


class __new_dcon__(Syntax):
    """
    Base class for Syntax objects that handle data constructor creation syntax
    within a `data` statment (`d.*`).
    """
    def __init__(self, dcon_name, args=(), classes=()):
        self.name = dcon_name
        self.args = args
        self.classes = classes
        super(__new_dcon__, self).__init__("Syntax error in `d`")
        return


class __new_dcon_params__(__new_dcon__):
    """
    This class represents a `data` statement in mid evaluation; it represents
    the part of the expression that builds a data constructor, after type
    parameters have been added.

    Examples:

    d.Just("a")
    d.Foo(int, "a", "b", str)
    """
    def __and__(self, derive_exp):
        if not isinstance(derive_exp, deriving):
            raise self.invalid_syntax
        return __new_dcon_deriving__(self.name, self.args, derive_exp.classes)

    def __or__(self, dcon):
        if isinstance(dcon, __new_dcon__):
            constructors = ((self.name, self.args), (dcon.name, dcon.args))

            if isinstance(dcon, __new_dcon_deriving__):
                return __new_dcons_deriving__(constructors, dcon.classes)
            return __new_dcons__(constructors)

        raise self.invalid_syntax


class __new_dcon_deriving__(__new_dcon__):
    """
    This class represents a `data` statement in mid evaluation; it represents
    the part of the expression that builds a data constructor (with or without type
    parameters) and adds derived typeclasses.

    Examples:

    d.Just("a") & deriving(Show, Eq, Ord)
    d.Bar & deriving(Eq)
    """
    pass


class __new_dcon_enum__(__new_dcon_params__):
    """
    This class represents a `data` statement in mid evaluation; it represents
    the part of the expression that builds a data constructor, after type
    parameters have been added.

    Examples:

    d.Just
    d.Foo
    """
    def __call__(self, *typeargs):
        return __new_dcon_params__(self.name, typeargs)


class __new_dcons_deriving__(Syntax):
    """
    This class represents a `data` statement in mid evaluation; it represents
    the part of the expression that builds data constructors (with or without type
    parameters) and adds derived typeclasses.

    Examples:

    d.Nothing | d.Just("a") & deriving(Show, Eq, Ord)
    d.Foo(int, "a", "b", str) | d.Bar & deriving(Eq)
    """
    def __init__(self, data_consts, classes=()):
        self.dcons = data_consts
        self.classes = classes
        super(__new_dcons_deriving__, self).__init__("Syntax error in `d`")
        return


class __new_dcons__(__new_dcons_deriving__):
    """
    This class represents a `data` statement in mid evaluation; it represents
    the part of the expression that builds data constructors (with or without type
    parameters), with no derived typeclasses.

    Examples:

    d.Foo(int, "a", "b", str) | d.Bar
    """

    def __init__(self, data_consts):
        super(__new_dcons__, self).__init__(data_consts)
        return

    def __or__(self, new_dcon):
        if isinstance(new_dcon, __new_dcon__):
            constructor = ((new_dcon.name, new_dcon.args),)

            if isinstance(new_dcon, __new_dcon_deriving__):
                return __new_dcons_deriving__(self.dcons + constructor,
                                              new_dcon.classes)
            return __new_dcons__(self.dcons + constructor)
        raise self.invalid_syntax


data = __data__()
d = __d__()


class deriving(Syntax):
    """
    `deriving` is part of hask's special syntax for defining algebraic data
    types.

    See help(data) for more information.
    """
    def __init__(self, *tclasses):
        for tclass in tclasses:
            if not issubclass(tclass, Typeclass):
                raise TypeError("Cannot derive non-typeclass %s" % tclass)
        self.classes = tclasses
        super(deriving, self).__init__("Syntax error in `deriving`")
        return


#=============================================================================#
# Operator sections


class __section__(Syntax):
    """
    __ is Hask's special syntax for operator sections.

    Example usage:
    >>> (__+1)(5)
    6

    >>> (6/__) * (__-1) % 4
    2

    >>> (__*__)(2, 10)
    1024

    Operators supported:
    + - * / // ** >> << | & ^ == != > >= < <=
    """
    def __init__(self, syntax_err_msg):
        super(__section__, self).__init__(syntax_err_msg)
        return

    @staticmethod
    def __make_section(fn):
        """
        Create an operator section from a binary operator.
        """
        def section_wrapper(self, y):
            # double section, e.g. (__+__)
            if isinstance(y, __section__):
                @sig(H/ "a" >> "b" >> "c")
                def double_section(a, b):
                    return fn(a, b)
                return double_section

            # single section, e.g. (__+1) or (1+__)
            @sig(H/ "a" >> "b")
            def section(a):
                return fn(a, y)
            return section
        return section_wrapper

    # left section, e.g. (__+1)
    __wrap = __make_section.__func__

    # right section, e.g. (1+__)
    __flip = lambda f: lambda x, y: f(y, x)

    __add__ = __wrap(operator.add)
    __sub__ = __wrap(operator.sub)
    __mul__ = __wrap(operator.mul)
    __truediv__ = __wrap(operator.truediv)
    __floordiv__ = __wrap(operator.floordiv)
    __mod__ = __wrap(operator.mod)
    __divmod__ = __wrap(divmod)
    __pow__ = __wrap(operator.pow)
    __lshift__ = __wrap(operator.lshift)
    __rshift__ = __wrap(operator.rshift)
    __or__ =  __wrap(operator.or_)
    __and__ = __wrap(operator.and_)
    __xor__ = __wrap(operator.xor)

    __eq__ = __wrap(operator.eq)
    __ne__ = __wrap(operator.ne)
    __gt__ = __wrap(operator.gt)
    __lt__ = __wrap(operator.lt)
    __ge__ = __wrap(operator.ge)
    __le__ = __wrap(operator.le)

    __radd__ = __wrap(__flip(operator.add))
    __rsub__ = __wrap(__flip(operator.sub))
    __rmul__ = __wrap(__flip(operator.mul))
    __rtruediv__ = __wrap(__flip(operator.truediv))
    __rfloordiv__ = __wrap(__flip(operator.floordiv))
    __rmod__ = __wrap(__flip(operator.mod))
    __rdivmod__ = __wrap(__flip(divmod))
    __rpow__ = __wrap(__flip(operator.pow))
    __rlshift__ = __wrap(__flip(operator.lshift))
    __rrshift__ = __wrap(__flip(operator.rshift))
    __ror__ = __wrap(__flip(operator.or_))
    __rand__ = __wrap(__flip(operator.and_))
    __rxor__ = __wrap(__flip(operator.xor))

    if sys.version[0] == '2':
        __div__ = __wrap(operator.div)
        __rdiv__ = __wrap(__flip(operator.div))


__ = __section__("Error in section")


#=============================================================================#
# Guards! Guards!

# Unlike pattern matching, this approach is completely stateless and
# thread-safe. However, it has the pretty undesireable property that it cannot
# be used with recursive functions.


class NoGuardMatchException(Exception):
    pass


class __guard_test__(Syntax):
    """
    c creates a new condition that can be used in a guard
    expression.

    otherwise is a guard condition that always evaluates to True.

    Usage:

    ~(guard(<expr to test>)
        | c(<test_fn_1>) >> <return_value_1>
        | c(<test_fn_2>) >> <return_value_2>
        | otherwise      >> <return_value_3>
    )

    See help(guard) for more details.
    """
    def __init__(self, fn):
        if not callable(fn):
            raise ValueError("Guard condition must be callable")
        self.__test = fn
        super(__guard_test__, self).__init__("Syntax error in guard condition")

    def __rshift__(self, value):
        if isinstance(value, __guard_test__) or \
           isinstance(value, __guard_conditional__) or \
           isinstance(value, __guard_base__):
            raise self.invalid_syntax
        return __guard_conditional__(self.__test, value)


class __guard_conditional__(Syntax):
    """
    Object that represents one line of a guard expression, consisting of:
        1) a condition (a test function wrapped in c and a value to be returned
           if that condition is satisfied).
        2) a return value, which will be returned if the condition evaluates
           to True
    See help(guard) for more details.
    """
    def __init__(self, fn, return_value):
        self.check = fn
        self.return_value = return_value
        msg = "Syntax error in guard condition"
        super(__guard_conditional__, self).__init__(msg)


class __guard_base__(Syntax):
    """
    Superclass for the classes __unmatched_guard__ and __matched_guard__ below,
    which represent the internal state of a guard expression as it is being
    evaluated.

    See help(guard) for more details.
    """
    def __init__(self, value):
        self.value = value
        super(__guard_base__, self).__init__("Syntax error in guard")


class __unmatched_guard__(__guard_base__):
    """
    Object that represents the state of a guard expression in mid-evaluation,
    before one of the conditions in the expression has been satisfied.

    See help(guard) for more details.
    """
    def __or__(self, cond):
        # Consume the next line of the guard expression

        if isinstance(cond, __guard_test__):
            raise SyntaxError("Guard expression is missing return value")

        elif not isinstance(cond, __guard_conditional__):
            raise SyntaxError("Guard condition expected, got %s" % cond)

        # If the condition is satisfied, change the evaluation state to
        # __matched_guard__, setting the return value to the value provided on
        # the current line
        elif cond.check(self.value):
            return __matched_guard__(cond.return_value)

        # If the condition is not satisfied, continue on with the next line,
        # still in __unmatched_guard__ state with the return value not set
        return __unmatched_guard__(self.value)

    def __invert__(self):
        raise NoGuardMatchException("No match found in guard(%s)" % self.value)


class __matched_guard__(__guard_base__):
    """
    Object that represents the state of a guard expression in mid-evaluation,
    after one of the conditions in the expression has been satisfied.

    See help(guard) for more details.
    """
    def __or__(self, cond):
        # Consume the next line of the guard expression
        # Since a condition has already been satisfied, we can ignore the rest
        # of the lines in the guard expression
        if isinstance(cond, __guard_conditional__):
            return self
        raise self.invalid_syntax

    def __invert__(self):
        return self.value


class guard(__unmatched_guard__):
    """
    Special syntax for guard expression.

    Usage:

    ~(guard(<expr to test>)
        | c(<test_fn_1>) >> <return_value_1>
        | c(<test_fn_2>) >> <return_value_2>
        | otherwise      >> <return_value_3>
    )

    Examples:

    ~(guard(8)
         | c(lambda x: x < 5) >> "less than 5"
         | c(lambda x: x < 9) >> "less than 9"
         | otherwise          >> "unsure"
    )

    # Using guards with sections. See help(__) for information on sections.
    ~(guard(20)
        | c(__ > 10)  >> 20
        | c(__ == 10) >> 10
        | c(__ > 5)   >> 5
        | otherwise   >> 0)

    Args:
        value: the value being tested in the guard expression

    Returns:
        the return value corresponding to the first matching condition

    Raises:
        NoGuardMatchException (if no match is found)

    """
    def __invert__(self):
        raise self.invalid_syntax


c = __guard_test__
otherwise = c(lambda _: True)


#=============================================================================#
# REPL tools (:q, :t, :i)


def _q(status=None):
    """
    Shorthand for sys.exit() or exit() with no arguments. Equivalent to :q in
    Haskell. Should only be used in the REPL.

    Usage:

    >>> _q()
    """
    if status is None:
        exit()
    exit(status)
    return


def _t(obj):
    """
    Returns a string representing the type of an object, including
    higher-kinded types and ADTs. Equivalent to `:t` in Haskell. Meant to be
    used in the REPL, but might also be useful for debugging.

    Args:
        obj: the object to inspect

    Returns:
        A string representation of the type

    Usage:

    >>> _t(1)
    int

    >>> _t(Just("hello world"))
    Maybe str
    """
    return str(typeof(obj))


def _i(obj):
    """
    Show information about an object. Equivalent to `:i` in Haskell or
    help(obj) in Python. Should only be used in the REPL.

    Args:
        obj: the object to inspect

    Usage:

    >>> _i(Just("hello world"))

    >>> _i(Either)
    """
    help(obj)
