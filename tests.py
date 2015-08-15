import math
import sys
import unittest

from hask import H, sig, t, func, TypeSignatureError
from hask import p, m, caseof, IncompletePatternError
from hask import has_instance
from hask import guard, c, otherwise, NoGuardMatchException
from hask import __
from hask import data, d, deriving, instance
from hask import L
from hask import Ordering, LT, EQ, GT
from hask import Maybe, Just, Nothing, in_maybe
from hask import Either, Left, Right, in_either
from hask import Typeclass
from hask import Read, Show, Eq, Ord, Bounded, Num
from hask import Functor, Applicative, Monad
from hask import Foldable, Traversable

# internals
from hask.lang.type_system import make_fn_type
from hask.lang.type_system import build_sig_arg
from hask.lang.type_system import build_sig
from hask.lang.type_system import build_ADT
from hask.lang.type_system import typeof
from hask.lang.type_system import pattern_match
from hask.lang.type_system import PatternMatchBind

from hask.lang.hindley_milner import Var
from hask.lang.hindley_milner import App
from hask.lang.hindley_milner import Lam
from hask.lang.hindley_milner import Let
from hask.lang.hindley_milner import TypeVariable
from hask.lang.hindley_milner import TypeOperator
from hask.lang.hindley_milner import Function
from hask.lang.hindley_milner import Tuple
from hask.lang.hindley_milner import analyze
from hask.lang.hindley_milner import unify

from hask.lang.lazylist import List

te = TypeError
se = SyntaxError
ve = ValueError


class TestHindleyMilner(unittest.TestCase):
    """Test the internals of the Hindley-Milner type inference engine"""

    def inference(self, expr):
        """Type inference succeeded using our toy environment"""
        self.assertIsNotNone(analyze(expr, self.env))
        return

    def not_inference(self, expr):
        """Type inference failed using our toy environment"""
        with self.assertRaises(te):
            analyze(expr, self.env)
        return

    def unified(self, t1, t2):
        """Two types are able to be unified"""
        self.assertIsNone(unify(t1, t2))
        return

    def typecheck(self, expr, expr_type):
        """Typecheck succeeded using our toy environment"""
        self.assertIsNone(unify(analyze(expr, self.env), expr_type))
        return

    def not_typecheck(self, expr, expr_type):
        """Typecheck failed, but inference succeeded using our toy environment
        """
        self.inference(expr)
        with self.assertRaises(te):
            self.typecheck(expr, expr_type)
        return

    def setUp(self):
        """Create some basic types and polymorphic typevars, a toy environment,
           and some AST nodes
        """
        self.var1 = TypeVariable()
        self.var2 = TypeVariable()
        self.var3 = TypeVariable()
        self.var4 = TypeVariable()
        self.Pair = TypeOperator("*", (self.var1, self.var2))
        self.Bool = TypeOperator("bool", [])
        self.Integer = TypeOperator("int", [])
        self.NoneT = TypeOperator("None", [])

        # toy environment
        self.env = {"pair": Function(self.var1,
                                     Function(self.var2, self.Pair)),
                    "True": self.Bool,
                    "None": self.NoneT,
                    "id": Function(self.var4, self.var4),
                    "cond": Function(self.Bool, Function(self.var3,
                                     Function(self.var3, self.var3))),
                    "zero": Function(self.Integer, self.Bool),
                    "pred": Function(self.Integer, self.Integer),
                    "times": Function(self.Integer,
                                      Function(self.Integer, self.Integer)),
                    "4": self.Integer,
                    "1": self.Integer}

        # some expressions to play around with
        self.compose = Lam("f", Lam("g", Lam("arg",
                            App(Var("g"), App(Var("f"), Var("arg"))))))
        self.pair = App(App(Var("pair"),
                         App(Var("f"), Var("1"))),
                         App(Var("f"), Var("True")))

    def test_type_inference(self):
        """Basic type inference in our toy environment"""

        # (* True) ==> TypeError
        self.not_inference(App(Var("times"), Var("True")))

        # (* True) ==> TypeError (undefined symbol a)
        self.not_inference(App(Var("times"), Var("a")))

        # monomorphism restriction
        # \x -> ((x 4), (x True)) ==> TypeError
        self.not_inference(
            Lam("x",
                App(
                    App(Var("pair"),
                        App(Var("x"), Var("4"))),
                    App(Var("x"), Var("True")))))

        # \x -> ((f 4), (f True)) ==> TypeError (undefined symbol f)
        self.not_inference(
            App(
                App(Var("pair"), App(Var("f"), Var("4"))),
                App(Var("f"), Var("True"))))

        # \f -> (f f) ==> TypeError (recursive unification)
        self.not_inference(Lam("f", App(Var("f"), Var("f"))))

    def test_type_checking(self):
        """Basic type checking in our toy environment"""

        # 1 :: Integer
        self.typecheck(Var("1"), self.Integer)

        # 1 :: Bool ==> TypeError
        self.not_typecheck(Var("1"), self.Bool)

        # (\x -> x) :: (a -> a)
        v = TypeVariable()
        self.typecheck(
                Lam("n", Var("n")),
                Function(v, v))

        # type(id) == type(\x -> x)
        self.typecheck(
                Lam("n", Var("n")),
                self.env["id"])

        # (\x -> x) :: (a -> b)
        self.typecheck(
                Lam("n", Var("n")),
                Function(TypeVariable(), TypeVariable()))

        # (id 1) :: Integer
        self.typecheck(App(Var("id"), Var("1")), self.Integer)

        # (id 1) :: Bool ==> TypeError
        self.not_typecheck(App(Var("id"), Var("1")), self.Bool)

        # pred :: (Integer -> Integer)
        self.typecheck(Var("pred"), Function(self.Integer, self.Integer))

        # (pred 4) :: Integer
        self.typecheck(
            App(Var("pred"), Var("1")),
            self.Integer)

        # ((pair 1) 4) :: (a, b)
        self.typecheck(
            App(App(Var("pair"), Var("1")), Var("4")),
            TypeOperator("*", [TypeVariable(), TypeVariable()]))


        # (*) :: (Integer -> Integer -> Integer)
        self.typecheck(
            Var("times"),
            Function(self.Integer, Function(self.Integer, self.Integer)))

        # (* 4) :: (Integer -> Integer)
        self.typecheck(
            App(Var("times"), Var("4")),
            Function(self.Integer, self.Integer))

        # (* 4) :: (Bool -> Integer) ==> TypeError
        self.not_typecheck(
            App(Var("times"), Var("4")),
            Function(self.Bool, self.Integer))

        # (* 4) :: (Integer -> a) ==> TypeError
        self.not_typecheck(
            App(Var("times"), Var("4")),
            Function(self.Integer, TypeVariable))

        # ((* 1) 4) :: Integer
        self.typecheck(
            App(App(Var("times"), Var("1")), Var("4")),
            self.Integer)

        # ((* 1) 4) :: Bool ==> TypeError
        self.not_typecheck(
            App(App(Var("times"), Var("1")), Var("4")),
            self.Bool)

        # let g = (\f -> 5) in (g g) :: Integer
        self.typecheck(
            Let("g",
                Lam("f", Var("4")),
                App(Var("g"), Var("g"))),
            self.Integer)

        # (.) :: (a -> b) -> (b -> c) -> (a -> c)
        a, b, c = TypeVariable(), TypeVariable(), TypeVariable()
        self.typecheck(
                self.compose,
                Function(Function(a, b),
                         Function(Function(b, c), Function(a, c))))

        # composing `id` with `id` == `id`
        # ((. id) id) :: (a -> a)
        d = TypeVariable()
        self.typecheck(
            App(App(self.compose, Var("id")), Var("id")),
            Function(d, d))

        # composing `id` with `times 4`
        # ((. id) (* 2)) :: (int -> int)
        self.typecheck(
            App(App(self.compose, Var("id")),
                                  App(Var("times"), Var("4"))),
            Function(self.Integer, self.Integer))

        # composing `times 4` with `id`
        # ((. (* 2)) id) :: (int -> int)
        self.typecheck(
            App(App(self.compose, App(Var("times"), Var("4"))),
                                  Var("id")),
            Function(self.Integer, self.Integer))

        # basic closure
        #((\x -> (\y -> ((* x) y))) 1) :: (Integer -> Integer)
        self.typecheck(
                App(
                    Lam("x", Lam("y",
                        App(App(Var("times"), Var("x")), Var("y")))),
                    Var("1")),
                Function(self.Integer, self.Integer))

        # lambdas have lexical scope
        # (((\x -> (\x -> x)) True) None) :: NoneT
        self.typecheck(
                App(App(
                    Lam("x", Lam("x", Var("x"))),
                    Var("True")), Var("None")),
                self.NoneT)

        # basic let expression
        # let a = times in ((a 1) 4) :: Integer
        self.typecheck(
                Let("a", Var("times"), App(App(Var("a"), Var("1")), Var("4"))),
                self.Integer)

        # let has lexical scope
        # let a = 1 in (let a = None in a) :: NoneT
        self.typecheck(
                Let("a", Var("1"), Let("a", Var("None"), Var("a"))),
                self.NoneT)

        # let polymorphism
        # let f = (\x -> x) in ((f 4), (f True)) :: (Integer, Bool)
        self.typecheck(
            Let("f", Lam("x", Var("x")), self.pair),
            TypeOperator("*", [self.Integer, self.Bool]))

        # recursive let
        # (factorial 4) :: Integer
        self.typecheck(
            Let("factorial", # letrec factorial =
                Lam("n",    # fn n =>
                    App(
                        App(   # cond (zero n) 1
                            App(Var("cond"),     # cond (zero n)
                                App(Var("zero"), Var("n"))),
                            Var("1")),
                        App(    # times n
                            App(Var("times"), Var("n")),
                            App(Var("factorial"),
                                App(Var("pred"), Var("n")))
                        )
                    )
                ),      # in
                App(Var("factorial"), Var("4"))),
            self.Integer)

    def test_build_sig_item(self):
        """Test type signature building internals - make sure that types are
           translated in a reasonable way"""

        class example(object):
            pass

        # type variables
        self.assertTrue(isinstance(build_sig_arg("a", {}, {}), TypeVariable))
        self.assertTrue(isinstance(build_sig_arg("abc", {}, {}), TypeVariable))

        # builtin/non-ADT types
        self.unified(build_sig_arg(str, {}, {}), TypeOperator(str, []))
        self.unified(build_sig_arg(int, {}, {}), TypeOperator(int, []))
        self.unified(build_sig_arg(float, {}, {}), TypeOperator(float, []))
        self.unified(build_sig_arg(list, {}, {}), TypeOperator(list, []))
        self.unified(build_sig_arg(set, {}, {}), TypeOperator(set, []))
        self.unified(build_sig_arg(example, {}, {}), TypeOperator(example, []))

        # unit type (None)
        self.unified(build_sig_arg(None, {}, {}), TypeOperator(None, []))

        # tuple
        self.unified(
                build_sig_arg((int, int), {}, {}),
                Tuple([TypeOperator(int, []), TypeOperator(int, [])]))
        self.unified(
                build_sig_arg((None, (None, int)), {}, {}),
                Tuple([TypeOperator(None, []),
                       Tuple([TypeOperator(None, []), TypeOperator(int, [])])]))
        a = TypeVariable()
        self.unified(
                build_sig_arg(("a", "a", "a"), {}, {}),
                Tuple([a, a, a]))

        # list
        self.unified(typeof(L[[]]), build_sig_arg(["a"], {}, {}))
        self.unified(typeof(L[1, 1]), build_sig_arg([int], {}, {}))
        self.unified(typeof(L[[L[1, 1]]]), build_sig_arg([[int]], {}, {}))

        # adts
        self.unified(typeof(Nothing), build_sig_arg(t(Maybe, "a"), {}, {}))
        self.unified(typeof(Just(1)), build_sig_arg(t(Maybe, int), {}, {}))
        self.unified(
                typeof(Just(Just(Nothing))),
                build_sig_arg(t(Maybe, t(Maybe, t(Maybe, "a"))), {}, {}))
        self.unified(
                typeof(Right("error")),
                build_sig_arg(t(Either, str, "a"), {}, {}))
        self.unified(
                typeof(Left(2.0)),
                build_sig_arg(t(Either, "a", int), {}, {}))
        self.unified(
                typeof(Just(__+1)),
                build_sig_arg(t(Maybe, "a"), {}, {}))
        self.unified(
                typeof(Just(__+1)),
                build_sig_arg(t(Maybe, (H/ "a" >> "b")), {}, {}))

    def test_signature_build(self):
        """Make sure type signatures are built correctly"""
        # int -> int
        self.unified(
                make_fn_type(build_sig((H/ int >> int).sig)),
                Function(TypeOperator(int, []), TypeOperator(int, [])))

        # a -> a
        a = TypeVariable()
        self.unified(
                make_fn_type(build_sig((H/ "a" >> "a").sig)),
                Function(a, a))

        # a -> b
        a, b  = TypeVariable(), TypeVariable()
        self.unified(
                make_fn_type(build_sig((H/ "a" >> "b").sig)),
                Function(a, b))

        # (int -> int) -> int -> int
        self.unified(
                make_fn_type(build_sig((H/ (H/ int >> int) >> int >> int).sig)),
                Function(
                    Function(TypeOperator(int, []), TypeOperator(int, [])),
                    Function(TypeOperator(int, []), TypeOperator(int, []))))

    def test_typecheck_builtins(self):
        """Make sure builtin types typecheck correctly"""

        # 1 :: int
        self.unified(typeof(1), TypeOperator(int, []))

        # "a" :: str
        self.unified(typeof("a"), TypeOperator(str, []))

        # Nothing :: Maybe a
        self.unified(
                typeof(Nothing),
                TypeOperator(Maybe, [TypeVariable()]))

        # Just(1) :: Maybe int
        self.unified(
                typeof(Just(1)),
                TypeOperator(Maybe, [TypeOperator(int, [])]))

        # Just(Just(Nothing)) :: Maybe (Maybe (Maybe a))
        self.unified(
                typeof(Just(Just(Nothing))),
                TypeOperator(Maybe,
                    [TypeOperator(Maybe,
                        [TypeOperator(Maybe, [TypeVariable()])])]))

        # Right("error") :: Either a str
        self.unified(
                typeof(Right("error")),
                TypeOperator(Either, [TypeVariable(),
                    TypeOperator(str, [])]))

        # Left(2.0) :: Either float a
        self.unified(
                typeof(Left(2.0)),
                TypeOperator(Either,
                    [TypeOperator(float, []), TypeVariable()]))


class TestTypeSystem(unittest.TestCase):

    def test_TypedFunc_builtin(self):
        """TypedFunc with builtin types"""

        f = (lambda x: x + 2) ** (H/ int >> int)
        g = (lambda x: x - 5) ** (H/ int >> int)
        h = (lambda x: x * 2) ** (H/ int >> int)
        i = (lambda x: str(x)) ** (H/ int >> str)
        j = (lambda x: x[0]) ** (H/ list >> float)

        # basic type checking
        self.assertEqual(2, f(g(5)))
        self.assertEqual(2, (f * g)(5))
        self.assertEqual(2, f * g % 5)
        self.assertEqual(8, f * f * f % 2)
        self.assertEqual(f(h(g(5))), (f * h * g)(5))
        self.assertEqual((i * h * f)(9), "22")
        self.assertEqual(1., j % [1., 2.])
        with self.assertRaises(te): f(4.0)
        with self.assertRaises(te): f("4")
        with self.assertRaises(te): f(1, 2)

    def test_TypedFunc_var(self):
        @sig(H/ "a" >> "b" >> "a" >> "b")
        def superconst(a, b, c):
            return b

        self.assertEqual(1, superconst([], 1, [1, 2]))
        self.assertEqual(None, superconst([], None, [1, 2]))
        with self.assertRaises(te): superconst(1, "a", 1.)

    def test_TypedFunc_tuple(self):
        @sig(H/ (int, "a", str) >> str)
        def pprint(tup):
            return str(tup[0]) + tup[2]

        self.assertEqual("1a", pprint((1, 9., "a")))
        with self.assertRaises(te): pprint((1, 2, 3))
        with self.assertRaises(te): pprint(("1", 2, "3"))
        with self.assertRaises(te): pprint((1, 2, 3, 4))
        with self.assertRaises(te): pprint((1, 2))

        @sig(H/ ("a", "b") >> ("b", "a"))
        def swap(tup):
            return (tup[1], tup[0])

        self.assertEqual(swap((1, 2)), (2, 1))
        self.assertEqual(swap((1., 2)), (2, 1.))
        with self.assertRaises(te): swap((1, 2, 3))

    def test_TypedFunc_list(self):
        @sig(H/ [int] >> int)
        def sum1(l):
            return sum(l)

        self.assertEqual(sum1 % L[1, 2, 3], 6)
        with self.assertRaises(te): sum1 % L[1., 2., 3.]

        @sig(H/ [["a"]] >> ["a"])
        def flatten(xss):
            return L[(x for xs in xss for x in xs)]

        self.assertEqual(flatten(L[L["a", "b"], L["c", "d"]]),
                         L["a", "b", "c", "d"])
        with self.assertRaises(te): flatten(L["a", "b"])

    def test_TypedFunc_None(self):
        @sig(H/ None >> None)
        def n_to_n(n):
            return

        self.assertIsNone(None, n_to_n % None)
        self.assertIsNone(None, n_to_n * n_to_n % None)
        with self.assertRaises(te): n_to_n(1)

    def test_TypedFunc_func(self):
        """PyFunc signature type"""

        @sig(H/ func >> func)
        def id_wrap(f):
            return lambda x: f(x)

        lam_test = lambda x: x + "!"

        def f_test(x):
            return x ** 2

        class example(object):
            def meth_test(self, x):
                return (x, x)

            @staticmethod
            def stat_test(x):
                return [x]

        self.assertEqual(id_wrap(lam_test)("woot"), "woot!")
        self.assertEqual(id_wrap(f_test)(2), 4)
        self.assertEqual(id_wrap(example().meth_test)(2), (2, 2))
        self.assertEqual(id_wrap(example.stat_test)(2), [2])

        self.assertEqual((id_wrap * id_wrap % (lambda x: x+1))(9), 10)
        with self.assertRaises(te): id_wrap(1)

        @sig(H/ func >> func >> int >> int)
        def composei(f, g, x):
            return f(g(x))

        self.assertEqual(composei(lambda x: x + 2)(lambda x: x * 3)(6), 20)

    def test_TypedFunc_class(self):
        @sig(H[(Eq, "a")]/ "a" >> "a")
        def eq_id(a):
            return a

        self.assertEqual(1, eq_id(1))

    def test_match(self):
        match_only = lambda v, p: pattern_match(v, p)[0]
        pb = PatternMatchBind

        # literal matches
        self.assertTrue(match_only(1, 1))
        self.assertTrue(match_only((1, "a"), (1, "a")))
        self.assertTrue(match_only(Nothing, Nothing))
        self.assertTrue(match_only(Just(1), Just(1)))
        self.assertFalse(match_only(2, 1))
        self.assertFalse(match_only(("a", 1), (1, "a")))
        self.assertFalse(match_only(("a", "b"), ["a", "b"]))
        self.assertFalse(match_only(Nothing, Just(Nothing)))
        self.assertFalse(match_only(Just(2), Just(1)))
        self.assertFalse(match_only(Right(2), Just(2)))
        self.assertFalse(match_only(Right(2), Left(2)))

        # matches with wildcard (i.e, discarded variable bind)
        self.assertTrue(match_only(1, pb("_")))
        self.assertTrue(match_only(Nothing, pb("_")))
        self.assertTrue(match_only(Just("whatever"), Just(pb("_"))))
        self.assertTrue(match_only(Right(Just(5)), Right(Just(pb("_")))))
        self.assertTrue(match_only(("a", "b", "c"), ("a", pb("_"), "c")))
        self.assertFalse(match_only(("a", "b", "c"), ("1", pb("_"), "c")))
        self.assertFalse(match_only(("a", "b", "d"), ("a", pb("_"), "c")))

        # matches with variable binding
        self.assertEqual((True, {"a":1}), pattern_match(1, pb("a")))
        self.assertEqual((True, {"a":1, "b":2}),
                pattern_match((1, 2), (pb("a"), pb("b"))))
        self.assertEqual((True, {"a":8}),
                pattern_match(Just(8), Just(pb("a"))))
        self.assertEqual((True, {"a":"a"}),
                pattern_match(Right(Just("a")), Right(Just(pb("a")))))
        self.assertEqual((False, {"a":1}),
                pattern_match((2, 1), (3, pb("a"))))
        self.assertEqual((True, {"a":1, "b":2, "_":"a"}),
                pattern_match((1, "a", 2), (pb("a"), pb("_"), pb("b"))))

        with self.assertRaises(se):
            pattern_match((1, 2), (pb("c"), pb("a")), {"c":1})
        with self.assertRaises(se):
            pattern_match((1, 2), (pb("c"), pb("a")), {"a":1})


class TestADTInternals_Enum(unittest.TestCase):

    def setUp(self):
        """
        Dummy type constructors and data constructors for an ADT with all
        enum data constructors
        """
        ds =  [("E1", []), ("E2", []), ("E3", [])]
        self.Type_Const, self.E1, self.E2, self.E3 =\
                build_ADT("Type_Const", [], ds, [])

    def test_adt(self):
        self.assertEqual(list(self.Type_Const.__constructors__),
                         [self.E1, self.E2, self.E3])
        self.assertTrue(isinstance(self.E1, self.Type_Const))
        self.assertTrue(isinstance(self.E2, self.Type_Const))
        self.assertTrue(isinstance(self.E3, self.Type_Const))

    def test_derive_eq_data(self):
        with self.assertRaises(te): self.E1 == self.E1
        with self.assertRaises(te): self.E1 != self.E1

        Eq.derive_instance(self.Type_Const)

        self.assertTrue(self.E1 == self.E1)
        self.assertTrue(self.E2 == self.E2)
        self.assertTrue(self.E3 == self.E3)

    def test_derive_show_data(self):
        self.assertNotEquals("E1", str(self.E1))

        Show.derive_instance(self.Type_Const)

        self.assertEqual("E1", str(self.E1))
        self.assertEqual("E2", str(self.E2))
        self.assertEqual("E3", str(self.E3))

    def test_derive_ord_data(self):
        with self.assertRaises(te): self.E1 > self.E1
        with self.assertRaises(te): self.E1 >= self.E1
        with self.assertRaises(te): self.E1 < self.E1
        with self.assertRaises(te): self.E1 <= self.E1

        Eq.derive_instance(self.Type_Const)
        Ord.derive_instance(self.Type_Const)

        self.assertTrue(self.E1 < self.E2)
        self.assertTrue(self.E1 <= self.E2)
        self.assertFalse(self.E1 > self.E2)
        self.assertFalse(self.E1 >= self.E2)

    def test_derive_bounded_data(self):
        Bounded.derive_instance(self.Type_Const)


class TestADTInternals_Builtin(unittest.TestCase):

    def setUp(self):
        """
        Dummy type constructors and data constructors for an ADT with all
        builtin (non-polymorphic) fields
        """
        ds =  [("M1", [int]), ("M2", [int, str]), ("M3", [int, int, int])]
        self.Type_Const, self.M1, self.M2, self.M3 =\
                build_ADT("Type_Const", [], ds, [])

    def test_adt(self):
        self.assertTrue(isinstance(self.M1(1), self.Type_Const))
        self.assertTrue(isinstance(self.M2(1, "abc"), self.Type_Const))
        self.assertTrue(isinstance(self.M2(1)("abc"), self.Type_Const))
        self.assertTrue(isinstance(self.M3(1, 2, 3), self.Type_Const))
        self.assertTrue(isinstance(self.M3(1)(2, 3), self.Type_Const))

        with self.assertRaises(te): self.M1(1.0)
        with self.assertRaises(te): self.M3(1, 2, "3")

    def test_derive_eq_data(self):
        with self.assertRaises(te): self.M1(1) == self.M1(1)
        with self.assertRaises(te): self.M1(1) != self.M1(1)

        Eq.derive_instance(self.Type_Const)

        self.assertTrue(self.M1(1) == self.M1(1))
        self.assertTrue(self.M2(1, "b") == self.M2(1, "b"))
        self.assertTrue(self.M3(1, 2, 3) == self.M3(1, 2, 3))
        self.assertFalse(self.M1(1) != self.M1(1))
        self.assertFalse(self.M2(1, "b") != self.M2(1, "b"))
        self.assertFalse(self.M3(1, 2, 3) != self.M3(1, 2, 3))
        self.assertFalse(self.M1(1) == self.M1(2))
        self.assertFalse(self.M2(1, "b") == self.M2(4, "b"))
        self.assertFalse(self.M2(1, "b") == self.M2(1, "a"))
        self.assertFalse(self.M3(1, 2, 3) == self.M3(1, 9, 3))

    def test_derive_show_data(self):
        self.assertNotEquals("M1(1)", str(self.M1(1)))

        Show.derive_instance(self.Type_Const)
        self.assertEqual("M1(1)", str(self.M1(1)))
        self.assertEqual("M2(1, \'a\')", str(self.M2(1, "a")))
        self.assertEqual("M3(1, 2, 3)", str(self.M3(1, 2, 3)))

    def test_derive_ord_data(self):
        with self.assertRaises(te): self.M1(1) > self.M1(1)
        with self.assertRaises(te): self.M1(1) >= self.M1(1)
        with self.assertRaises(te): self.M1(1) < self.M1(1)
        with self.assertRaises(te): self.M1(1) <= self.M1(1)

        Eq.derive_instance(self.Type_Const)
        Ord.derive_instance(self.Type_Const)

        self.assertTrue(self.M1(1) < self.M1(2))
        self.assertTrue(self.M1(1) <= self.M1(2))
        self.assertTrue(self.M1(2) <= self.M1(2))
        self.assertFalse(self.M1(3) < self.M1(2))
        self.assertFalse(self.M1(3) <= self.M1(2))
        self.assertTrue(self.M1(2) > self.M1(1))
        self.assertTrue(self.M1(2) >= self.M1(1))
        self.assertTrue(self.M1(2) >= self.M1(2))
        self.assertFalse(self.M1(1) > self.M1(2))
        self.assertFalse(self.M1(1) >= self.M1(2))

    def test_derive_bounded_data(self):
        with self.assertRaises(te):
            Bounded.derive_instance(self.Type_Const)


class TestADTInternals_Poly(unittest.TestCase):
    def setUp(self):
        """
        Dummy type constructors and data constructors for an ADT with
        polymorphic fields
        """
        ds =  [("M1", ["a"]), ("M2", ["a", "b"]), ("M3", ["a", "c", "c"])]
        self.Type_Const, self.M1, self.M2, self.M3 =\
                build_ADT("Type_Const", ["a", "b", "c"], ds, [])

    def test_adt(self):
        self.assertTrue(isinstance(self.M1(1), self.Type_Const))
        self.assertTrue(isinstance(self.M2(1, "abc"), self.Type_Const))
        self.assertTrue(isinstance(self.M2(1)("abc"), self.Type_Const))
        self.assertTrue(isinstance(self.M3(1, 2, 3), self.Type_Const))
        self.assertTrue(isinstance(self.M3(1)(2, 3), self.Type_Const))
        with self.assertRaises(te): self.M3(1, "a", 2)

    def test_derive_eq_data(self):
        with self.assertRaises(te): self.M1(1) == self.M1(1)
        with self.assertRaises(te): self.M1(1) == self.M2(1, "b")
        with self.assertRaises(te): self.M1(1) != self.M1(1)
        with self.assertRaises(te): self.M1(1) != self.M2(1, "b")

        Eq.derive_instance(self.Type_Const)

        self.assertEqual(self.M1(1), self.M1(1))
        self.assertEqual(self.M2(1, "a"), self.M2(1, "a"))
        self.assertNotEqual(self.M1("a"), self.M1("b"))
        self.assertNotEqual(self.M1("a"), self.M2("a", "b"))
        self.assertEqual(self.M3(1, "b", "b"), self.M3(1, "b", "b"))
        with self.assertRaises(te): self.M1(1) == self.M1("a")
        with self.assertRaises(te): self.M3(1, 2, 2) == self.M3(1, "a", "b")

    def test_derive_show_data(self):
        self.assertNotEqual("M1(1)", str(self.M1(1)))
        self.assertNotEqual("M2(1, 2)", str(self.M2(1, 2)))

        Show.derive_instance(self.Type_Const)

        self.assertEqual("M1(1)", str(self.M1(1)))
        self.assertEqual("M2(1, 2)", str(self.M2(1, 2)))

    def test_derive_ord_data(self):
        with self.assertRaises(te): self.M1(1) > self.M1(1)
        with self.assertRaises(te): self.M1(1) < self.M2(1, "b")
        with self.assertRaises(te): self.M1(1) >= self.M1(1)
        with self.assertRaises(te): self.M1(1) <= self.M2(1, "b")

        Eq.derive_instance(self.Type_Const)
        Ord.derive_instance(self.Type_Const)

        self.assertTrue(self.M1(1) < self.M2(100, "a"))
        self.assertTrue(self.M1(1) <= self.M2(100, "a"))
        self.assertFalse(self.M1(1) > self.M2(100, "a"))
        self.assertFalse(self.M1(1) >= self.M2(100, "a"))
        self.assertTrue(self.M3(1, "a", "b") < self.M3(1, "a", "c"))
        self.assertTrue(self.M3(1, "a", "b") <= self.M3(1, "a", "c"))
        self.assertFalse(self.M1(1) > self.M2(100, "a"))
        self.assertFalse(self.M1(1) >= self.M2(100, "a"))
        with self.assertRaises(te): self.M1(1) > self.M1("a")
        with self.assertRaises(te): self.M3(1, 2, 2) > self.M3(1, "a", "b")


class TestADTSyntax(unittest.TestCase):

    def test_data(self):
        # these are not syntactically valid
        with self.assertRaises(se): data.n
        with self.assertRaises(se): data.n("a")
        with self.assertRaises(se): data.N("!")
        with self.assertRaises(se): data.N("A")
        with self.assertRaises(se): data.N("a", "a")
        with self.assertRaises(se): data.N(1, "b")
        with self.assertRaises(se): data.N("a")("b")
        with self.assertRaises(se): data.N()
        with self.assertRaises(se): data.N == d
        with self.assertRaises(se): data.N == 1

        # these should all work fine
        self.assertIsNotNone(data.N)
        self.assertIsNotNone(data.N1)
        self.assertIsNotNone(data.N("a"))
        self.assertIsNotNone(data.N("azzz"))
        self.assertIsNotNone(data.N("a", "b"))

    def test_d(self):
        # these are not syntactically valid
        with self.assertRaises(se): d.a
        with self.assertRaises(se): d.A | deriving(Eq)
        with self.assertRaises(se): d.A | d
        with self.assertRaises(se): d.A | d.B | d
        with self.assertRaises(se): d.A | "a"
        with self.assertRaises(te): deriving("a")
        with self.assertRaises(se): deriving(Eq, Show) | d.B
        with self.assertRaises(se): deriving(Eq, Show) & d.B
        with self.assertRaises(se): d.A("a", "b") & deriving
        with self.assertRaises(se): d.A("a", "b") & Show
        with self.assertRaises(te): deriving(1, 2)

        # these should all work fine
        self.assertIsNotNone(d.A)
        self.assertIsNotNone(d.A("a"))
        self.assertIsNotNone(d.A("a", "b", "c"))
        self.assertIsNotNone(d.A("a") | d.B("b"))
        self.assertIsNotNone(d.A("a") | d.B)
        self.assertIsNotNone(d.B | d.A("a"))
        self.assertIsNotNone(d.B | d.A)
        self.assertIsNotNone(d.A("a") | d.B("b") | d.C("a"))
        self.assertIsNotNone(d.A("a", "b") & deriving(Eq, Show))
        self.assertIsNotNone(d.A("a") | d.B("b") & deriving(Eq, Show))

    def test_adts(self):
        """Assorted ADT tests that don't fit anywhere else"""
        T, M1, M2, M3 =\
        data.T("a", "b") == d.M1("a") | d.M2("b") | d.M3 & deriving(Eq)

        self.assertEqual(M1(20), M1(20))
        self.assertEqual(M2(20), M2(20))
        self.assertNotEqual(M1(20), M1(21))
        self.assertNotEqual(M2(20), M2(21))
        self.assertNotEqual(M1(2), M2(2))
        self.assertNotEqual(M1(2), M2("a"))
        self.assertNotEqual(M1(2), M3)
        self.assertEqual(M3, M3)
        self.assertFalse(M3 != M3)
        with self.assertRaises(te): M1("a") == M1(3.0)

        A, B, C =\
        data.A == d.B(str, str) | d.C(str) & deriving(Show, Eq)
        self.assertTrue(has_instance(A, Show))
        self.assertTrue(has_instance(A, Eq))
        self.assertEqual("B('a', 'b')", str(B("a", "b")))
        self.assertEqual("C('a')", str(C("a")))
        self.assertEqual(B("a", "b"), B("a", "b"))
        self.assertEqual(C("a"), C("a"))
        self.assertNotEqual(B("a", "b"), B("a", "c"))
        self.assertNotEqual(C("b"), C("c"))
        self.assertNotEqual(C("b"), B("b", "c"))
        with self.assertRaises(te): M1("a") == C("a")

        # make sure everything works with only 1 constructor
        A, B =\
        data.A == d.B(str, str) & deriving(Show, Eq)
        self.assertTrue(has_instance(A, Show))
        self.assertTrue(has_instance(A, Eq))
        self.assertEqual("B('a', 'b')", str(B("a", "b")))
        self.assertEqual(B("a", "b"), B("a", "b"))
        self.assertNotEqual(B("a", "b"), B("a", "c"))

        # make sure everything works with a bunch of constructors
        X, X1, X2, X3, X4, X5, X6 =\
        data.X == d.X1 | d.X2 | d.X3 | d.X4 | d.X5 | d.X6 & deriving(Eq, Ord)
        self.assertTrue(X1 != X2 and X2 != X3 and X3 != X4 and X4 != X5 and \
                X4 != X5 and X5 != X6)
        self.assertTrue(X1 < X2 < X3 < X4 < X5 < X6)
        with self.assertRaises(te): X1 < A("a", "a")
        with self.assertRaises(te): data.X == d.A | d.B & deriving(Show, 1)


class TestBuiltins(unittest.TestCase):

    def test_show(self):
        from hask.Prelude import show
        self.assertEqual('1', show(1))
        self.assertEqual("'a'", show("a"))
        self.assertEqual("[1, 2]", show([1, 2]))
        self.assertEqual("{'a': 1}", show({"a": 1}))

    def test_enum(self):
        from hask.Prelude import fromEnum, succ, pred
        self.assertEqual(1, fromEnum(1))
        self.assertEqual("b", succ("a"))
        self.assertEqual("a", pred("b"))
        self.assertEqual(2, succ(1))
        self.assertEqual(1, pred(2))
        self.assertEqual(0, pred(pred(2)))
        self.assertEqual(-1, pred(pred(pred(2))))
        self.assertEqual(4, succ(succ(succ(1))))

    def test_numerics(self):
        self.assertTrue(has_instance(int, Num))
        self.assertTrue(has_instance(long, Num))
        self.assertTrue(has_instance(float, Num))
        self.assertTrue(has_instance(complex, Num))


class TestSyntax(unittest.TestCase):

    def test_syntax(self):
        from hask.lang.syntax import Syntax
        s = Syntax("err")
        with self.assertRaises(se): len(s)
        with self.assertRaises(se): s[0]
        with self.assertRaises(se): s[1]
        with self.assertRaises(se): del s["foo"]
        with self.assertRaises(se): iter(s)
        with self.assertRaises(se): reversed(s)
        with self.assertRaises(se): 1 in s
        with self.assertRaises(se): 1 not in s
        with self.assertRaises(se): s("f")
        with self.assertRaises(se):
            with s as b: pass
        with self.assertRaises(se): s > 0
        with self.assertRaises(se): s < 0
        with self.assertRaises(se): s >= 0
        with self.assertRaises(se): s <= 0
        with self.assertRaises(se): s == 0
        with self.assertRaises(se): s != 0
        with self.assertRaises(se): abs(s)
        with self.assertRaises(se): ~s
        with self.assertRaises(se): +s
        with self.assertRaises(se): -s
        with self.assertRaises(se): s + 1
        with self.assertRaises(se): s - 1
        with self.assertRaises(se): s * 1
        with self.assertRaises(se): s ** 1
        with self.assertRaises(se): s / 1
        with self.assertRaises(se): s % 1
        with self.assertRaises(se): divmod(s, 1)
        with self.assertRaises(se): s << 1
        with self.assertRaises(se): s >> 1
        with self.assertRaises(se): s & 1
        with self.assertRaises(se): s | 1
        with self.assertRaises(se): s ^ 1
        with self.assertRaises(se): 1 + s
        with self.assertRaises(se): 1 - s
        with self.assertRaises(se): 1 * s
        with self.assertRaises(se): 1 ** s
        with self.assertRaises(se): 1 / s
        with self.assertRaises(se): 1 % s
        with self.assertRaises(se): 1 << s
        with self.assertRaises(se): 1 >> s
        with self.assertRaises(se): 1 & s
        with self.assertRaises(se): 1 | s
        with self.assertRaises(se): 1 ^ s
        with self.assertRaises(se): s += 1
        with self.assertRaises(se): s -= 1
        with self.assertRaises(se): s *= 1
        with self.assertRaises(se): s **= 1
        with self.assertRaises(se): s /= 1
        with self.assertRaises(se): s %= 1
        with self.assertRaises(se): s <<= 1
        with self.assertRaises(se): s >>= 1
        with self.assertRaises(se): s &= 1
        with self.assertRaises(se): s |= 1
        with self.assertRaises(se): s ^= 1

    def test_section(self):
        """Operator sections (e.g. `(1+__)` )"""

        # basic sections
        self.assertEqual(4, (__ + 1)(3))
        self.assertEqual(4, (1 + __)(3))
        self.assertEqual(3, (__ - 5)(8))
        self.assertEqual(3, (8 - __)(5))
        self.assertEqual(8, (__ * 2)(4))
        self.assertEqual(8, (2 * __)(4))
        self.assertEqual(1, (__ % 4)(5))
        self.assertEqual(1, (5 % __)(4))

        self.assertTrue((__ < 4)(3))
        self.assertTrue((5 < __)(9))
        self.assertTrue((__ > 4)(5))
        self.assertTrue((5 > __)(4))
        self.assertTrue((__ == 4)(4))
        self.assertTrue((5 == __)(5))
        self.assertTrue((__ != 4)(3))
        self.assertTrue((5 != __)(8))
        self.assertTrue((__ >= 4)(5))
        self.assertTrue((5 >= __)(5))
        self.assertTrue((__ <= 4)(4))
        self.assertTrue((5 <= __)(8))
        self.assertFalse((__ < 4)(4))
        self.assertFalse((5 < __)(2))
        self.assertFalse((__ > 4)(3))
        self.assertFalse((5 > __)(5))
        self.assertFalse((__ == 4)(9))
        self.assertFalse((5 == __)(8))
        self.assertFalse((__ != 4)(4))
        self.assertFalse((5 != __)(5))
        self.assertFalse((__ >= 4)(1))
        self.assertFalse((5 >= __)(6))
        self.assertFalse((__ <= 4)(6))
        self.assertFalse((5 <= __)(4))

        # double sections
        self.assertEqual(3, (__+__)(1, 2))
        self.assertEqual(1, (__-__)(2, 1))
        self.assertEqual(4, (__*__)(1, 4))
        self.assertEqual(3, (__/__)(12, 4))
        self.assertEqual(3, (__+__)(1)(2))
        self.assertEqual(1, (__-__)(2)(1))
        self.assertEqual(4, (__*__)(1)(4))
        self.assertEqual(3, (__/__)(12)(4))

        # sections composed with `fmap`
        self.assertEqual(12, ((__*4) * (__+2) * (1+__))(0))
        self.assertEqual(2, (__+1) * (__/2) * (2-__) % 0)
        self.assertEqual(4, (__ + 1) * (__ * 3) % 1)

    def test_guard(self):
        me = NoGuardMatchException

        self.assertTrue(~(guard(1)
            | c(lambda x: x == 1) >> True
            | otherwise           >> False))
        self.assertFalse(~(guard(2)
            | c(lambda y: y == 1) >> True
            | otherwise           >> False))
        self.assertFalse(~(guard(2)
            | otherwise >> False))
        self.assertFalse(~(guard(2)
            | otherwise           >> False
            | c(lambda x: x == 2) >> True))
        self.assertEqual("foo", ~(guard(1)
            | c(lambda x: x > 1)  >> "bar"
            | c(lambda x: x < 1)  >> "baz"
            | c(lambda x: x == 1) >> "foo"
            | otherwise           >> "Err"))

        with self.assertRaises(ve): ~(guard(2) | c(1) >> 1)
        with self.assertRaises(me): ~(guard(1) | c(lambda x: x == 2) >> 1)

        # syntax checks
        with self.assertRaises(se): c(lambda x: x == 10) + c(lambda _: 1)
        with self.assertRaises(se): c(lambda x: x == 10) - c(lambda _: 1)
        with self.assertRaises(se): c(lambda x: x == 10) * c(lambda _: 1)
        with self.assertRaises(se): c(lambda x: x == 10) / c(lambda _: 1)
        with self.assertRaises(se): c(lambda x: x == 10) % c(lambda _: 1)
        with self.assertRaises(se): c(lambda x: x == 10) ** c(lambda _: 1)
        with self.assertRaises(se): c(lambda x: x == 10) << c(lambda _: 1)
        with self.assertRaises(se): c(lambda x: x == 10) & c(lambda _: 1)
        with self.assertRaises(se): c(lambda x: x == 10) ^ c(lambda _: 1)

        with self.assertRaises(se): c(lambda x: x == 10) >> c(lambda _: 1)
        with self.assertRaises(se): c(lambda x: x == 10) >> 2 >> 2
        with self.assertRaises(se): c(lambda x: x > 1) | c(lambda x: x < 1)
        with self.assertRaises(se): otherwise >> c(lambda _: 1)
        with self.assertRaises(se): otherwise | c(lambda x: x < 1)
        with self.assertRaises(se): otherwise >> c(lambda _: 1)
        with self.assertRaises(se): otherwise | c(lambda x: x < 1)
        with self.assertRaises(se):
            ~(guard(2) | c(lambda x: x == 2) >> 1 | c(lambda y: y == 2))
        with self.assertRaises(se): c(lambda x: x == 10) >> "1" >> "2"
        with self.assertRaises(se): "1" >> c(lambda x: x == 10)
        with self.assertRaises(se): guard(1) | c(lambda x: x > 1)
        with self.assertRaises(se): guard(1) | (lambda x: x > 1)
        with self.assertRaises(se): ~guard(1) | (lambda x: x > 1)
        with self.assertRaises(se): ~guard(1)
        with self.assertRaises(se): otherwise >> "1" >> "2"
        with self.assertRaises(se): "1" >> otherwise

    def test_caseof(self):

        # literal matching
        self.assertEqual(1,
                ~(caseof("a")
                    | m("a") >> 1))
        self.assertEqual(1,
                ~(caseof(2.0)
                    | m(2.0) >> ~(caseof("a")
                                    | m("b") >> 3
                                    | m("a") >> 1)
                    | m(2.0) >> 2))
        self.assertEqual("x",
                ~(caseof(Just("x"))
                    | m(Nothing)   >> False
                    | m(Just("x")) >> "x"))
        self.assertEqual(1,
                ~(caseof([1, 2])
                    | m((1, 2)) >> 2
                    | m([1, 2]) >> 1))
        self.assertEqual(True,
                ~(caseof(GT)
                    | m(LT) >> False
                    | m(EQ) >> False
                    | m(GT) >> True))
        self.assertEqual(2,
                ~(caseof((1, 2, 3))
                    | m((1, 2))    >> 1
                    | m((1, 2, 3)) >> 2))

        with self.assertRaises(IncompletePatternError):
            ~(caseof(1) | m(2) >> 2)

        # matches with wildcard
        self.assertEqual(1,
                ~(caseof(1)
                    | m(m._) >> 1
                    | m(1) >> 2))
        self.assertEqual(True,
                ~(caseof(GT)
                    | m(LT) >> False
                    | m(EQ) >> False
                    | m(m._) >> True))
        self.assertEqual(False,
                ~(caseof(GT)
                    | m(LT) >> False
                    | m(m._)  >> False
                    | m(GT) >> True))
        self.assertEqual(2,
                ~(caseof((1, 2, 3))
                    | m((2, 1, 3)) >> 1
                    | m((1, m._, 3)) >> 2
                    | m((1, 2, 3)) >> 3))

        # variable bind
        self.assertEqual(("b", "a"),
                ~(caseof(("a", "b"))
                    | m((m.x, m.y)) >> (p.y, p.x)
                    | m(m._)          >> None))
        self.assertEqual(1,
                ~(caseof(Just(1))
                    | m(Just(m.x)) >> p.x
                    | m(Nothing)   >> 0))
        self.assertEqual(Just(0),
                ~(caseof(Nothing)
                    | m(Just(m.x)) >> Just(p.x + 1)
                    | m(Nothing)   >> Just(0)))
        self.assertEqual(1,
                ~(caseof(2)
                    | m((m.a, m.a)) >> p.a
                    | m(2)          >> 1))
        self.assertEqual(1,
                ~(caseof(Just(10))
                    | m(Just(m.a)) >> ~(caseof(1)
                                            | m(m.a) >> p.a
                                            | m(m._) >> False)
                    | m(Nothing)   >> 11))

        # cons matches
        self.assertEqual([3],
                ~(caseof([1, 2, 3])
                    | m(1 ^ (2 ^ m.x)) >> p.x
                    | m(m.x)           >> False))
        self.assertEqual([3, 2, 1],
                ~(caseof([3, 2, 1])
                    | m(m.a ^ (2 ^ m.c)) >> [p.a, 2, p.c[0]]
                    | m(m.x)             >> False))
        self.assertEqual([3, 2, [1, 0]],
                ~(caseof([3, 2, 1, 0])
                    | m(m.a ^ (m.b ^ m.c)) >> [p.a, p.b, p.c]
                    | m(m.x)               >> False))
        self.assertEqual(L[3, 2, 1],
                ~(caseof(L[3, 2, 1, 0])
                    | m(m.a ^ (m.b ^ m.c)) >> L[p.a, p.b, p.c[0]]
                    | m(m.x)               >> False))
        self.assertEqual(1,
                ~(caseof(L[1, ...])
                    | m(m.a ^ m.b) >> p.a
                    | m(m.a)       >> False))
        self.assertTrue(~(caseof(L[[]])
                            | m(m.a ^ m.b) >> False
                            | m(m.a)       >> True))

        with self.assertRaises(se):
            ~(caseof((1, 2))
                | m((m.a, m.a)) >> p.a
                | m(1)          >> 1)
        with self.assertRaises(se):
            ~(caseof([1, 2, 3, 4])
                | m(m.a ^ m.b ^ m.c) >> True
                | m(m.x)             >> False)
        with self.assertRaises(se):
            ~(caseof(L[1, 2, 2])
                | m(m.a ^ 1) >> False
                | m(m.a)     >> True)


    def test_type_sig(self):
        tse = TypeSignatureError
        x = lambda x: x
        with self.assertRaises(tse): x ** (H/ int >> 1)
        with self.assertRaises(tse): x ** (H/ int >> [int, int])
        with self.assertRaises(tse): x ** (H/ int >> [])
        with self.assertRaises(tse): x ** (H/ int >> "AAA")

        with self.assertRaises(te): t(Maybe, "a", "b")
        with self.assertRaises(te): t(Either, "a")
        with self.assertRaises(te): t(Ordering, "a")

        with self.assertRaises(se): sig(sig(H/ int >> int))
        with self.assertRaises(se): sig(H)

        with self.assertRaises(se): H[Eq, "a", "b"]
        with self.assertRaises(se): H[(Eq, Eq)]
        with self.assertRaises(se): H[("a", Eq)]
        with self.assertRaises(se): H[("a", "a")]
        with self.assertRaises(se): H[(Eq, "a", "b")]
        with self.assertRaises(se): H[(Eq, 1)]
        with self.assertRaises(se): H[(Maybe, 1)]
        with self.assertRaises(se): sig(H/ "a")(1)


class TestTypeclass(unittest.TestCase):

    def test_typeclasses(self):
        A, B =\
                data.A == d.B & deriving(Show, Eq)
        self.assertTrue(has_instance(A, Show))
        self.assertTrue(has_instance(A, Eq))
        self.assertFalse(has_instance(A, Ord))
        with self.assertRaises(te): Ord[B]
        with self.assertRaises(te):
            A, B = data.A == d.B & deriving(Show, Ord)

        class example(object):
            def __str__(self):
                return "example()"

        instance(Show, example).where(show=example.__str__)
        with self.assertRaises(te): instance(1, example)
        with self.assertRaises(te): instance(example, str)

        from hask.Prelude import show
        self.assertEqual("example()", show(example()))



class TestOrdering(unittest.TestCase):

    def test_ordering(self):
        from hask.Data.Ord import Ordering, LT, EQ, GT
        self.assertTrue(has_instance(Ordering, Read))
        self.assertTrue(has_instance(Ordering, Show))
        self.assertTrue(has_instance(Ordering, Eq))
        self.assertTrue(has_instance(Ordering, Ord))
        self.assertTrue(has_instance(Ordering, Bounded))

        from hask.Prelude import show
        self.assertEqual("LT", show(LT))
        self.assertEqual("EQ", show(EQ))
        self.assertEqual("GT", show(GT))

        self.assertTrue(EQ == EQ and not EQ != EQ)
        self.assertTrue(LT == LT and not LT != LT)
        self.assertTrue(GT == GT and not GT != GT)
        self.assertFalse(LT == EQ)
        self.assertFalse(LT == GT)
        self.assertFalse(EQ == GT)
        self.assertTrue(LT < EQ < GT)
        self.assertTrue(LT <= EQ < GT)
        self.assertTrue(LT < EQ <= GT)
        self.assertTrue(LT <= EQ <= GT)
        self.assertFalse(LT > EQ or EQ > GT)
        self.assertFalse(LT >= EQ or EQ > GT)
        self.assertFalse(LT > EQ or EQ >= GT)
        self.assertFalse(LT >= EQ or EQ >= GT)

        with self.assertRaises(te): EQ + EQ


class TestMaybe(unittest.TestCase):

    def test_instances(self):
        self.assertTrue(has_instance(Maybe, Read))
        self.assertTrue(has_instance(Maybe, Show))
        self.assertTrue(has_instance(Maybe, Eq))
        self.assertTrue(has_instance(Maybe, Functor))
        self.assertTrue(has_instance(Maybe, Applicative))
        self.assertTrue(has_instance(Maybe, Monad))

        self.assertFalse(has_instance(Maybe, Typeclass))
        self.assertFalse(has_instance(Maybe, Num))
        self.assertFalse(has_instance(Maybe, Foldable))
        self.assertFalse(has_instance(Maybe, Traversable))

    def test_show(self):
        from hask.Prelude import show
        self.assertEqual("Just(3)", str(Just(3)))
        self.assertEqual("Just(3)", show(Just(3)))
        self.assertEqual("Just('a')", str(Just("a")))
        self.assertEqual("Just('a')", show(Just("a")))
        self.assertEqual("Just(Just(3))", str(Just(Just(3))))
        self.assertEqual("Just(Just(3))", show(Just(Just(3))))
        self.assertEqual("Nothing", str(Nothing))
        self.assertEqual("Nothing", show(Nothing))

    def test_eq(self):
        self.assertEqual(Nothing, Nothing)
        self.assertEqual(Just(3), Just(3))
        self.assertEqual(Just("3"), Just("3"))
        self.assertNotEqual(Just(1), Just(3))
        self.assertNotEqual(Just(3), Nothing)
        self.assertNotEqual(Nothing, Just(0))
        self.assertTrue(Just(1) == Just(1))
        self.assertFalse(Just(1) == Just(2))
        self.assertTrue(Nothing == Nothing or Nothing != Nothing)
        self.assertTrue(Just(1) == Just(1) or Just(1) != Just(1))
        self.assertFalse(Nothing == Nothing and Nothing != Nothing)
        self.assertFalse(Just(1) == Just(1) and Just(1) != Just(1))
        with self.assertRaises(te): Just(1) == Just("1")
        with self.assertRaises(te): Just(1) == Just(1.0)
        with self.assertRaises(te): Nothing == None
        with self.assertRaises(te): Nothing == 1
        with self.assertRaises(te): Just(1) == 1

    def test_ord(self):
        self.assertTrue(Nothing < Just(0))
        self.assertTrue(Nothing < Just("a"))
        self.assertTrue(Nothing < Just(-float("inf")))
        self.assertTrue(Nothing <= Just(0))
        self.assertTrue(Nothing <= Just("a"))
        self.assertTrue(Nothing <= Just(-float("inf")))
        self.assertTrue(Nothing >= Nothing and Nothing <= Nothing)
        self.assertFalse(Nothing > Just(0))
        self.assertFalse(Nothing > Just("a"))
        self.assertFalse(Nothing > Just(-float("inf")))
        self.assertFalse(Nothing >= Just(0))
        self.assertFalse(Nothing >= Just("a"))
        self.assertFalse(Nothing >= Just(-float("inf")))
        self.assertFalse(Nothing > Nothing or Nothing < Nothing)

        self.assertTrue(Just(1) > Just(0))
        self.assertTrue(Just(Just(1)) > Just(Nothing))
        self.assertTrue(Just(Just(Nothing)) > Just(Nothing))
        self.assertTrue(Just(1) >= Just(0))
        self.assertTrue(Just(1) >= Just(1))
        self.assertTrue(Just(Just(1)) >= Just(Nothing))
        self.assertTrue(Just(Just(Nothing)) >= Just(Nothing))
        self.assertTrue(Just(Just(Nothing)) >= Just(Just(Nothing)))
        self.assertFalse(Just(0) > Just(1))
        self.assertFalse(Just(0) > Just(0))
        self.assertFalse(Just(Nothing) > Just(Just(1)))
        self.assertFalse(Just(Nothing) > Just(Just(Nothing)))
        self.assertFalse(Just(0) >= Just(1))
        self.assertFalse(Just(Nothing) >= Just(Just(1)))
        self.assertFalse(Just(Nothing) >= Just(Just(Nothing)))

        self.assertTrue(Just(0) < Just(1))
        self.assertTrue(Just(Nothing) < Just(Just(1)))
        self.assertTrue(Just(Nothing) < Just(Just(Nothing)))
        self.assertTrue(Just(0) <= Just(1))
        self.assertTrue(Just(Nothing) <= Just(Just(1)))
        self.assertTrue(Just(Nothing) <= Just(Just(Nothing)))
        self.assertFalse(Just(1) < Just(0))
        self.assertFalse(Just(1) < Just(1))
        self.assertFalse(Just(Just(1)) < Just(Nothing))
        self.assertFalse(Just(Just(Nothing)) < Just(Nothing))
        self.assertFalse(Just(1) <= Just(0))
        self.assertTrue(Just(1) <= Just(1))
        self.assertFalse(Just(Just(1)) <= Just(Nothing))
        self.assertFalse(Just(Just(Nothing)) <= Just(Nothing))
        self.assertTrue(Just(Just(Nothing)) <= Just(Just(Nothing)))

        with self.assertRaises(te): Just(1) > Just(1.0)
        with self.assertRaises(te): Just(1) >= Just(1.0)
        with self.assertRaises(te): Just(1) < Just(1.0)
        with self.assertRaises(te): Just(1) <= Just(1.0)
        with self.assertRaises(te): Just(1) > Just(Just(1))
        with self.assertRaises(te): Just(1) >= Just(Just(1))
        with self.assertRaises(te): Just(1) < Just(Just(1))
        with self.assertRaises(te): Just(1) <= Just(Just(1))

    def test_functor(self):
        from hask.Prelude import id, fmap
        plus1 = (lambda x: x + 1) ** (H/ int >> int)
        toStr = str ** (H/ int >> str)

        self.assertEqual(Just(Just(2)), fmap(Just, Just(2)))
        self.assertEqual(Just(3), plus1 * Just(2))
        self.assertEqual(Just("1"), toStr * Just(1))
        self.assertEqual(Just("3"), (toStr * plus1) * Just(2))

        # functor laws
        self.assertEqual(fmap(id, Just(4)), Just(4))
        self.assertEqual(fmap(id, Nothing), Nothing)
        self.assertEqual(id * Just(4), Just(4))
        self.assertEqual(id * Nothing, Nothing)
        self.assertEqual(fmap(toStr, fmap(plus1, Just(2))),
                         fmap(toStr * plus1, Just(2)))
        self.assertEqual((toStr * (plus1 * Just(2))),
                         (toStr * plus1) * Just(2))

    def test_monad(self):
        f = (lambda x: Just(str(x))) ** (H/ int >> t(Maybe, str))
        g = (lambda x: Just(x * 10)) ** (H/ int >> t(Maybe, int))
        self.assertEqual(Just("1"), Just(1) >> f)
        self.assertEqual(Just(10), Just(1) >> g)
        self.assertEqual(Just(1000), Just(1) >> g >> g >> g)

        @sig(H[(Num, "a")]/ "a" >> "a" >> t(Maybe, "a"))
        def safediv(x, y):
            return Just(x/y) if y != 0 else Nothing

        from hask.Prelude import flip
        s = flip(safediv)
        self.assertEqual(Just(3), Just(9) >> s(3))
        self.assertEqual(Just(1), Just(9) >> s(3) >> s(3))
        self.assertEqual(Nothing, Just(9) >> s(0) >> s(3))
        self.assertEqual(Nothing, Nothing >> s(3) >> s(3))

        # monad laws
        s_composed = (lambda x: s(3, x) >> s(3)) ** (H/ int >> t(Maybe, int))
        self.assertEqual(Just(2), Just(2) >> Just)
        self.assertEqual(Nothing, Nothing >> Just)
        self.assertEqual(Just(4) >> s(2), s(2, 4))
        self.assertEqual(Just(1), (Just(9) >> s(3)) >> s(3))
        self.assertEqual(Just(1), Just(9) >> s_composed)
        self.assertEqual(Nothing, (Nothing >> s(3)) >> s(3))
        self.assertEqual(Nothing, Nothing >> s_composed)

        from hask.Control.Monad import join, liftM
        self.assertEqual(join(Just(Just(1))), Just(1))
        self.assertEqual(join(Just(Nothing)), Nothing)
        self.assertEqual(liftM(__+1, Just(1)), Just(2))
        self.assertEqual(liftM(__+1, Nothing), Nothing)

    def test_functions(self):
        from hask.Data.Maybe import maybe, isJust, isNothing, fromJust
        from hask.Data.Maybe import listToMaybe, maybeToList, catMaybes
        from hask.Data.Maybe import mapMaybe

        self.assertTrue(isJust(Just(1)))
        self.assertTrue(isJust(Just(Nothing)))
        self.assertFalse(isJust(Nothing))
        self.assertFalse(isNothing(Just(1)))
        self.assertFalse(isNothing(Just(Nothing)))
        self.assertTrue(isNothing(Nothing))
        self.assertEqual(fromJust(Just("bird")), "bird")
        self.assertEqual(fromJust(Just(Nothing)), Nothing)
        with self.assertRaises(ve): fromJust(Nothing)

        self.assertEqual(2, maybe(0, (__+1), Just(1)))
        self.assertEqual(0, maybe(0, (__+1)) % Nothing)
        self.assertEqual(Nothing, listToMaybe(L[[]]))
        self.assertEqual(Just("a"), listToMaybe(L[["a"]]))
        self.assertEqual(Just("a"), listToMaybe(L["a", "b"]))
        self.assertEqual(Just(1), listToMaybe(L[1, ...]))
        self.assertEqual(L[[]], maybeToList(Nothing))
        self.assertEqual(L[[1]], maybeToList(Just(1)))
        self.assertEqual(L[[]], catMaybes(L[[]]))
        self.assertEqual(L[[]], catMaybes(L[Nothing, Nothing]))
        self.assertEqual(L[1, 2], catMaybes(L[Just(1), Just(2)]))
        self.assertEqual(L[1, 2], catMaybes(L[Just(1), Nothing, Just(2)]))

        from hask.Prelude import const
        self.assertEqual(L[[]], mapMaybe(const(Nothing), L[1, 2]))
        self.assertEqual(L[1, 2], mapMaybe(Just, L[1, 2]))
        self.assertEqual(L[[]], mapMaybe(Just, L[[]]))

        f = (lambda x: Just(x) if x > 3 else Nothing) \
            ** (H/ int >> t(Maybe, int))
        self.assertEqual(L[4, 5], mapMaybe(f, L[1, ..., 5]))
        self.assertEqual(L[[]], mapMaybe(f, L[1, ..., 3]))


class TestEither(unittest.TestCase):

    def test_instances(self):
        self.assertTrue(has_instance(Either, Read))
        self.assertTrue(has_instance(Either, Show))
        self.assertTrue(has_instance(Either, Eq))
        self.assertTrue(has_instance(Either, Functor))
        self.assertTrue(has_instance(Either, Applicative))
        self.assertTrue(has_instance(Either, Monad))

        self.assertFalse(has_instance(Either, Typeclass))
        self.assertFalse(has_instance(Either, Num))
        self.assertFalse(has_instance(Either, Foldable))
        self.assertFalse(has_instance(Either, Traversable))

    def test_show(self):
        from hask.Prelude import show
        self.assertEqual("Left(1)", str(Left(1)))
        self.assertEqual("Left('1')", str(Left("1")))
        self.assertEqual("Right(1)", str(Right(1)))
        self.assertEqual("Right('1')", str(Right("1")))
        self.assertEqual("Right(Left('1'))", str(Right(Left("1"))))
        self.assertEqual("Left(1)", show(Left(1)))
        self.assertEqual("Left('1')", show(Left("1")))
        self.assertEqual("Right(1)", show(Right(1)))
        self.assertEqual("Right('1')", show(Right("1")))
        self.assertEqual("Right(Left('1'))", show(Right(Left("1"))))

    def test_eq(self):
        self.assertTrue(Left(1) == Left(1))
        self.assertTrue(Right(1) == Right(1))
        self.assertFalse(Left(1) == Left(2))
        self.assertFalse(Right(1) == Right(2))
        self.assertFalse(Left(1) == Right(1))
        self.assertFalse(Left("a") == Right(1))
        self.assertFalse(Left(1) != Left(1))
        self.assertFalse(Right(1) != Right(1))
        self.assertTrue(Left(1) != Left(2))
        self.assertTrue(Right(1) != Right(2))
        self.assertTrue(Left(1) != Right(1))
        self.assertTrue(Left("a") != Right(1))

    def test_ord(self):
        self.assertTrue(Left(20) < Right(0))
        self.assertTrue(Left(20) < Right("a"))
        self.assertTrue(Left(2) < Left(3))
        self.assertTrue(Right(2) < Right(3))
        self.assertTrue(Left(20) <= Right(0))
        self.assertTrue(Left(20) <= Right("a"))
        self.assertTrue(Left(2) <= Left(3))
        self.assertTrue(Right(2) <= Right(3))
        self.assertFalse(Right(0) < Left(20))
        self.assertFalse(Right("a") < Left(20))
        self.assertFalse(Left(3) < Left(2))
        self.assertFalse(Right(3) < Right(2))
        self.assertFalse(Right(2) <= Left(20))
        self.assertFalse(Right("a") <= Left(20))
        self.assertFalse(Left(3) <= Left(2))
        self.assertFalse(Right(3) <= Right(2))

        self.assertTrue(Right(0) > Left(20))
        self.assertTrue(Right("a") > Left(20))
        self.assertTrue(Left(3) > Left(2))
        self.assertTrue(Right(3) > Right(2))
        self.assertTrue(Right(2) >= Left(20))
        self.assertTrue(Right("a") >= Left(20))
        self.assertTrue(Left(3) >= Left(2))
        self.assertTrue(Right(3) >= Right(2))
        self.assertFalse(Left(20) > Right(0))
        self.assertFalse(Left(20) > Right("a"))
        self.assertFalse(Left(2) > Left(3))
        self.assertFalse(Right(2) > Right(3))
        self.assertFalse(Left(20) >= Right(0))
        self.assertFalse(Left(20) >= Right("a"))
        self.assertFalse(Left(2) >= Left(3))
        self.assertFalse(Right(2) >= Right(3))

        self.assertFalse(Right(3) > Right(3))
        self.assertFalse(Left(3) > Left(3))
        self.assertFalse(Right(3) < Right(3))
        self.assertFalse(Left(3) < Left(3))
        self.assertTrue(Left(2.0) <= Left(2.0))
        self.assertTrue(Right(2) <= Right(2))
        self.assertTrue(Left(2.0) >= Left(2.0))
        self.assertTrue(Right(2) >= Right(2))

    def test_functor(self):
        from hask.Prelude import id, flip, fmap, const
        self.assertEqual(Left(7), fmap(__+1, Left(7)))
        self.assertEqual(Left("a"), fmap(__+1, Left("a")))
        self.assertEqual(Right(8), fmap(__+1, Right(7)))
        with self.assertRaises(te): fmap(__+1, Right("a"))
        self.assertEqual(Right(Left(1)), fmap(const(Left(1)), Right("a")))
        self.assertEqual(Left("a"), fmap(const(Left(1)), Left("a")))

        f = (lambda x: x + "!") ** (H/ str >> str)
        g = (lambda x: x + "?") ** (H/ str >> str)
        self.assertEqual(Right("b?!"), (f * g) * Right("b"))
        self.assertEqual(Right("b?!"), f * g * Right("b"))
        self.assertEqual(Left("b"), (f * g) * Left("b"))
        self.assertEqual(Left("b"), f * g * Left("b"))

        # functor laws
        self.assertEqual(Left(7), fmap(id, Left(7)))
        self.assertEqual(Right(7), fmap(id, Right(7)))
        self.assertEqual(Right("a?!"), fmap(f * g, Right("a")))
        self.assertEqual(Left("a"), fmap(f * g, Left("a")))
        self.assertEqual(Right("a?!"), fmap(f, fmap(g, Right("a"))))
        self.assertEqual(Left("a"), fmap(f, fmap(g, Left("a"))))

    def test_monad(self):
        from hask.Prelude import flip
        from hask.Control.Monad import bind, join

        @sig(H/ int >> int >> t(Either, str, int))
        def sub_whole(x, y):
            return Right(x-y) if (x-y) >= 0 else Left("err")

        sub = flip(sub_whole)

        self.assertEqual(Right(2), Right(4) >> sub(2))
        self.assertEqual(Right(0), Right(4) >> sub(2) >> sub(2))
        self.assertEqual(Left("err"), Right(4) >> sub(10))
        self.assertEqual(Left("0"), Left("0") >> sub_whole(1))

        # monad laws
        sub_composed = (lambda x: sub_whole(4, x) >> sub(2)) ** \
                (H/ int >> t(Either, "a", int))
        self.assertEqual(Right(7), Right(7) >> Right)
        self.assertEqual(Left(7), Left(7) >> Right)
        self.assertEqual(Right(1), (Right(5) >> sub(1)) >> sub(3))
        self.assertEqual(Left("e"), (Left("e") >> sub(1)) >> sub(3))
        self.assertEqual(Left("err"), (Right(5) >> sub(10)) >> sub(3))
        self.assertEqual(Right(0), Right(2) >> sub_composed)
        self.assertEqual(Left("e"), Left("e") >> sub_composed)

        self.assertEqual(Right(2), bind(Right(4), sub(2)))

        self.assertEqual(join(Right(Right(1))), Right(1))
        self.assertEqual(join(Right(Left(1))), Left(1))

    def test_functions(self):
        from hask.Data.Either import either
        from hask.Data.Either import isRight
        from hask.Data.Either import isLeft
        from hask.Data.Either import lefts
        from hask.Data.Either import rights
        from hask.Data.Either import partitionEithers

        f = (lambda x: x + " world") ** (H/ str >> str)
        g = (lambda x: str(x * 10)) ** (H/ int >> str)

        self.assertEqual('20', either(f, g, Right(2)))
        self.assertEqual("hello world", either(f, g, Left("hello")))
        self.assertTrue(isLeft(Left(1)))
        self.assertTrue(isRight(Right("a")))
        self.assertFalse(isLeft(Right("a")))
        self.assertFalse(isRight(Left(1)))

        self.assertEqual(L[1, 3],
                rights(L[Right(1), Left(2), Right(3), Left(4)]))
        self.assertEqual(L[[]], rights(L[[]]))
        self.assertEqual(L[2, 4],
                lefts(L[Right(1), Left(2), Right(3), Left(4)]))
        self.assertEqual(L[[]], lefts(L[[]]))
        self.assertEqual((L[2, 4], L[1, 3]),
                partitionEithers(L[Right(1), Left(2), Right(3), Left(4)]))
        self.assertEqual((L[2, 4], L[[]]),
                partitionEithers(L[Left(2), Left(4)]))
        self.assertEqual((L[[]], L[1, 3]),
                partitionEithers(L[Right(1), Right(3)]))
        self.assertEqual((L[[]], L[[]]),
                partitionEithers(L[[]]))


class TestList(unittest.TestCase):

    def test_instances(self):
        self.assertTrue(has_instance(List, Show))
        self.assertTrue(has_instance(List, Eq))
        self.assertTrue(has_instance(List, Ord))
        self.assertTrue(has_instance(List, Functor))
        self.assertTrue(has_instance(List, Applicative))
        self.assertTrue(has_instance(List, Monad))
        self.assertTrue(has_instance(List, Foldable))
        #self.assertTrue(has_instance(List, Traversable))

        self.assertFalse(has_instance(List, Typeclass))
        self.assertFalse(has_instance(List, Num))

    def test_eq(self):
        self.assertEqual(L[[]], L[[]])
        self.assertEqual(L[[1, 2]], L[[1, 2]])
        self.assertEqual(L[1, 2], L[1, 2])
        self.assertEqual(L[1, 2], L[[1, 2]])
        self.assertEqual(L[range(10)], L[range(10)])
        self.assertEqual(L[range(5)], L[0, 1, 2, 3, 4])
        self.assertEqual(L[range(10)], L[xrange(10)])
        self.assertEqual(L[xrange(10)], L[xrange(10)])
        self.assertEqual(L[xrange(5)], L[0, 1, 2, 3, 4])
        self.assertEqual(L[(i for i in range(5))], L[(i for i in range(5))])
        self.assertEqual(L[(i for i in range(5))], L[0, 1, 2, 3, 4])
        self.assertEqual(L[(i for i in [])], L[[]])
        self.assertEqual(L[1, ..., 20], L[1, ..., 20])
        self.assertEqual(L[1, 4, ..., 20], L[1, 4, ..., 20])
        self.assertNotEqual(L[1, 2], L[[]])
        self.assertNotEqual(L[1, 2], L[[1]])
        self.assertNotEqual(L[1, 2], L[1, 2, 3])
        self.assertNotEqual(L[1, 2], L[2, 2])
        with self.assertRaises(te): L["a", "b"] == L[1, 2]

        # with infinite lists
        self.assertNotEqual(L[1, ...], L[0,...])
        self.assertNotEqual(L[1, 3, ...], L[1, 4, ...])
        self.assertNotEqual(L[1, 4], L[1, 4, ...])
        with self.assertRaises(te): L["a", "b"] == L[1, ...]

    def test_ord(self):
        self.assertTrue(L[[]] < L[2, 1])
        self.assertTrue(L[1, 2] < L[2, 1])
        self.assertTrue(L[1, 2] < L[2, 1, 3])
        self.assertTrue(L[1, 2] < L[2, ...])
        self.assertFalse(L[2, 1] < L[[]])
        self.assertFalse(L[2, 1] < L[1, 2])
        self.assertFalse(L[2, 1] < L[1, 1, 1])
        self.assertFalse(L[2, 1] < L[1, ...])
        self.assertTrue(L[[]] <= L[2, 1])
        self.assertTrue(L[1, 2] <= L[2, 1])
        self.assertTrue(L[1, 2] <= L[2, 1, 3])
        self.assertTrue(L[1, 2] <= L[2, ...])
        self.assertFalse(L[2, 1] <= L[[]])
        self.assertFalse(L[2, 1] <= L[1, 2])
        self.assertFalse(L[2, 1] <= L[1, 1, 1])
        self.assertFalse(L[2, 1] <= L[1, ...])

        self.assertFalse(L[[]] > L[2, 1])
        self.assertFalse(L[1, 2] > L[2, 1])
        self.assertFalse(L[1, 2] > L[2, 1, 3])
        self.assertFalse(L[1, 2] > L[2, ...])
        self.assertTrue(L[2, 1] > L[[]])
        self.assertTrue(L[2, 1] > L[1, 2])
        self.assertTrue(L[2, 1] > L[1, 1, 1])
        self.assertTrue(L[2, 1] > L[1, ...])
        self.assertFalse(L[[]] >= L[2, 1])
        self.assertFalse(L[1, 2] >= L[2, 1])
        self.assertFalse(L[1, 2] >= L[2, 1, 3])
        self.assertFalse(L[1, 2] >= L[2, ...])
        self.assertTrue(L[2, 1] >= L[[]])
        self.assertTrue(L[2, 1] >= L[1, 2])
        self.assertTrue(L[2, 1] >= L[1, 1, 1])
        self.assertTrue(L[2, 1] >= L[1, ...])

        self.assertFalse(L[1, 2] < L[1, 2])
        self.assertFalse(L[1, 2] > L[1, 2])
        self.assertTrue(L[1, 2] <= L[1, 2])
        self.assertTrue(L[1, 2] <= L[1, 2])

        self.assertTrue(L[1, 2] + L[3, ...] > L[1, 2, 3] + L[2, ...])
        self.assertTrue(L[1, 2] + L[3, ...] >= L[1, 2, 3] + L[2, ...])
        self.assertTrue(L[1, 2, 3] + L[1, ...] < L[1, 2] + L[3, ...])
        self.assertTrue(L[1, 2, 3] + L[1, ...] <= L[1, 2] + L[3, ...])
        self.assertFalse(L[1, 2] + L[3, ...] < L[1, 2, 3] + L[2, ...])
        self.assertFalse(L[1, 2] + L[3, ...] <= L[1, 2, 3] + L[2, ...])
        self.assertFalse(L[1, 2, 3] + L[1, ...] > L[1, 2] + L[3, ...])
        self.assertFalse(L[1, 2, 3] + L[1, ...] >= L[1, 2] + L[3, ...])

        self.assertTrue(L[1, 2, 3] + L[4, ...] > L[1, 2])
        self.assertTrue(L[1, 2, 3] + L[4, ...] >= L[1, 2])
        self.assertTrue(L[1, 2] < L[1, 2, 3] + L[4, ...])
        self.assertTrue(L[1, 2] <= L[1, 2, 3] + L[4, ...])
        self.assertFalse(L[1, 2] > L[1, 2, 3] + L[4, ...])
        self.assertFalse(L[1, 2] >= L[1, 2, 3] + L[4, ...])
        self.assertFalse(L[1, 2, 3] + L[4, ...] < L[1, 2])
        self.assertFalse(L[1, 2, 3] + L[4, ...] <= L[1, 2])

        with self.assertRaises(te): L[1, 2] > L[1.0, 2.0]
        with self.assertRaises(te): L[1, 2] > L[1.0, 2.0, ...]
        with self.assertRaises(te): L[1, 2] < L[1.0, 2.0]
        with self.assertRaises(te): L[1, 2] < L[1.0, 2.0, ...]
        with self.assertRaises(te): L[1, 2] >= L[1.0, 2.0]
        with self.assertRaises(te): L[1, 2] >= L[1.0, 2.0, ...]
        with self.assertRaises(te): L[1, 2] <= L[1.0, 2.0]
        with self.assertRaises(te): L[1, 2] <= L[1.0, 2.0, ...]

    def test_show(self):
        from hask.Prelude import show
        self.assertEqual("L[[]]", show(L[[]]))
        self.assertEqual("L[[2.0]]", show(L[[2.0]]))
        self.assertEqual("L['a', 'a']", show(L[['a', 'a']]))
        self.assertEqual("L[['a']]", show(L[['a']]))
        self.assertEqual("L[1, 2]", show(L[1, 2]))
        self.assertEqual("L[1, 2]", show(L[[1, 2]]))
        self.assertEqual("L[1, 2, 3]", show(L[1, 2, 3]))
        self.assertEqual("L[1, 2, 3]", show(L[1, 2, 3][:]))

    def test_cons(self):
        self.assertEqual(L[[1]], 1 ^ L[[]])
        self.assertEqual(L[1, 2, 3], 1 ^ (2 ^ L[[3]]))
        self.assertEqual(L[0, 1, 2], (0 ^ L[1, ...])[:3])
        self.assertEqual(L[True, False, True], True ^ (False ^ L[[True]]))
        with self.assertRaises(te): "a" ^ L[2, 4]
        with self.assertRaises(te): True ^ L[2, 4]
        with self.assertRaises(te): "a" ^ L[(i for i in range(20))]
        with self.assertRaises(te): L[1, "a"]

    def test_extend(self):
        self.assertEqual(L[1, 2, 3, 4], L[[1, 2]] + L[[3, 4]])
        self.assertEqual(L[1, 2, 3, 4, 5], L[1, 2] + L[3, 4] + L[[5]])
        self.assertEqual(L[1, 2, 3, 4, 5], L[1, 2] + L[[]] + L[3, 4, 5])
        self.assertEqual(L[1, ..., 10], (L[1, ...] + L[0, ...])[:10])
        with self.assertRaises(te): L[1.0, 2.0] + L[3, 4]
        with self.assertRaises(te): L[1.0, 2.0] + [3, 4]
        with self.assertRaises(te): L[(i for i in "abc")] + L[1, 2]

    def test_indexing(self):
        ie = IndexError

        # regular indexing
        self.assertEqual(3, L[range(10)][3])
        self.assertEqual(3, L[range(4)][-1])
        self.assertEqual(3, L[(i for i in range(10))][3])
        self.assertEqual(3, L[(i for i in range(4))][-1])
        self.assertEqual(2, L[[0, 1, 2, 3]][2])
        self.assertEqual(2, L[[0, 1, 2, 3]][-2])
        self.assertEqual(1, L[(0, 1, 2, 3)][1])
        self.assertEqual(1, L[(0, 1, 2, 3)][-3])
        with self.assertRaises(ie): L[((0, 1, 2))][3]
        with self.assertRaises(ie): L[((0, 1, 2))][-4]
        with self.assertRaises(ie): L[((i for i in range(3)))][3]
        with self.assertRaises(ie): L[((i for i in range(3)))][-4]

        # slice indexing
        self.assertEqual(L[1, 2, 3], L[1, 2, 3, 4][:3])
        self.assertEqual(L[1, 2, 3], L[1, 2, 3][:3])
        self.assertEqual(L[1, 2, 3], L[1, 2, 3][:4])
        self.assertEqual(L[[]], L[1, 2, 3][:-4])
        self.assertEqual(L[2, 3], L[1, 2, 3, 4][1:3])
        self.assertEqual(L[2, 3, 4], L[1, 2, 3, 4][1:4])
        self.assertEqual(L[[2]], L[1, 2, 3][1:-1])
        self.assertEqual(L[[]], L[1, 2, 3][1:-4])
        self.assertEqual(L[2, 3, 4], L[1, 2, 3, 4][1:])
        self.assertEqual(L[[]], L[1, 2, 3, 4][4:])
        self.assertEqual(L[[]], L[1, 2, 3, 4][9:])
        self.assertEqual(L[3, 2, 1], L[1, 2, 3][::-1])
        self.assertEqual(L[2, 1], L[1, 2, 3][1::-1])
        self.assertEqual(L[[]], L[1, 2, 3][:4:-1])
        self.assertEqual(L[[3]], L[1, 2, 3][:1:-1])

    def test_list_comp(self):
        # numeric lists
        self.assertEqual(10, len(L[0, ...][:10]))
        self.assertEqual(L[0, ...][:10], L[range(10)])
        self.assertEqual(L[-10, ...][:10], L[range(-10, 0)])
        self.assertEqual(11, len(L[-5, ..., 5]))
        self.assertEqual(L[-5, ..., 5], L[range(-5, 6)])
        self.assertEqual(L[-5, -4, ..., 5], L[range(-5, 6)])
        self.assertEqual(L[-5, -3, ..., 5], L[range(-5, 6, 2)])
        self.assertEqual(L[1, 3, 5, 7], L[1, 3, ...][:4])
        self.assertEqual(L[3, 5, 7], L[1, 3, ...][1:4])
        self.assertEqual(L[5, 7], L[1, 3, ...][2:4])
        self.assertEqual(L[[]], L[1, 3, ...][4:4])
        self.assertEqual(L[[]], L[1, 3, ...][5:4])
        self.assertEqual(L[1, 3, 5, 7], L[1, 3, ..., 7])
        self.assertEqual(L[1, 3, 5, 7], L[1, 3, ..., 8])
        self.assertEqual(L[2, 3], L[1,...][1:][:2])
        self.assertEqual(L[2, 7, ..., 4], L[[2]])
        self.assertEqual(L[[2]], L[2, 3, ..., 2])
        self.assertEqual(L[2, 3], L[2, 3, ..., 3])

        # decreasing lists
        self.assertEqual(L[5, 4, ...][:10], L[range(5, -5, -1)])
        self.assertEqual(L[5, 3, ...][:10], L[range(5, -15, -2)])
        self.assertEqual(L[5, ..., 1], L[5, 4, 3, 2, 1])
        self.assertEqual(L[5, 3, ..., -5], L[5, 3, 1, -1, -3, -5])
        self.assertEqual(L[[]], L[2, 3, ..., 1])
        self.assertEqual(L[[]], L[2, 2, ..., 1])

        # character lists
        self.assertEqual(10, len(L["a", ...][:10]))
        self.assertEqual("abcdefghij", "".join(L["a", ...][:10]))
        self.assertEqual(11, len(L["a", ..., "k"]))

        with self.assertRaises(se): L[1, 2, 3, ...]
        with self.assertRaises(se): L[..., 2]
        with self.assertRaises(se): L[1, ..., 10, 11]

    def test_contains(self):
        self.assertTrue(1 in L[2, 3, 1])
        self.assertFalse(1 not in L[2, 3, 1])
        self.assertTrue(4 not in L[2, 3, 1])
        self.assertFalse(4 in L[2, 3, 1])
        self.assertTrue(55 in L[1,...])
        self.assertFalse(4 in L[1, 3, ..., 19])
        self.assertTrue(4 not in L[1, 3, ..., 19])

        with self.assertRaises(te): "b" in L[1, ...]
        self.assertEqual(1, L["a", "b", "a"].count("b"))
        self.assertEqual(2, L["a", "b", "a"].count("a"))
        self.assertEqual(0, L["a", "b", "a"].count("d"))
        with self.assertRaises(te): L["a", "b", "c"].count(1)
        self.assertEqual(1, L["a", "b", "a"].index("b"))
        self.assertEqual(0, L["a", "b", "a"].index("a"))
        with self.assertRaises(ve): L["a", "b", "c"].index("d")
        with self.assertRaises(te): L["a", "b", "c"].index(1)

    def test_functor(self):
        from hask.Prelude import id, map, fmap
        f = (lambda x: x ** 2 - 1) ** (H/ int >> int)
        g = (lambda y: y / 4 + 9) ** (H/ int >> int)

        self.assertEqual(L[0, 3, 8, 15], fmap(f, L[1, ..., 4]))
        self.assertEqual(L[0, 3, 8, 15], fmap(f, L[1, ...])[:4])
        self.assertEqual(L[0, 3, 8, 15], f * L[1, ..., 4])
        self.assertEqual(L[0, 3, 8, 15], (f * L[1, ...])[:4])

        # functor laws
        self.assertEqual(L[range(10)], fmap(id, L[range(10)]))
        self.assertEqual(L[range(10)], fmap(id, L[0, ...][:10]))
        self.assertEqual(fmap(f * g, L[range(20)]),
                         fmap(f, fmap(g, L[range(20)])))
        self.assertEqual(fmap(f * g, L[7, ...])[:20],
                         fmap(f, fmap(g, L[7, ...]))[:20])

    def test_monad(self):
        @sig(H/ "a" >> ["a"])
        def double(x):
            return L[x, x]

        self.assertEqual(L[[]], L[[]] >> double)
        self.assertEqual(L[1, 1], L[[1]] >> double)
        self.assertEqual(L[1, 1, 2, 2], L[1, 2] >> double)
        self.assertEqual(L[1, 1, 1, 1, 2, 2, 2, 2],
                         L[1, 2] >> double >> double)

        @sig(H/ "a" >> ["a"])
        def single(x):
            return L[[x]]

        composed_double = (lambda x: double(x) >> double) ** (H/ "a" >> ["a"])

        # monad laws
        self.assertEqual(L[[]], L[[]] >> single)
        self.assertEqual(L[[1]], L[[1]] >> single)
        self.assertEqual(L[1, ..., 20], L[1, ..., 20] >> single)
        self.assertEqual(L[1, 1, 1, 1, 2, 2, 2, 2],
                         (L[1, 2] >> double) >> double)
        self.assertEqual(L[1, 1, 1, 1, 2, 2, 2, 2],
                         L[1, 2] >> (composed_double))

    def test_len(self):
        self.assertEqual(0, len(L[[]]))
        self.assertEqual(0, len(L[None]))
        self.assertEqual(1, len(L[None,]))
        self.assertEqual(3, len(L[1, 2, 3]))
        self.assertEqual(20, len(L[0, ..., 19]))


class TestDataList(unittest.TestCase):

    def test_basic_functions(self):
        from hask.Data.List import head, last, tail, init, uncons, null, length

        self.assertEqual(4, head(L[4, 2]))
        self.assertEqual(1, head(L[1, ...]))
        with self.assertRaises(IndexError): head(L[[]])

        self.assertEqual(1, last(L[[1]]))
        self.assertEqual(4, last(L[1, 5, 3, 6, 4]))
        with self.assertRaises(IndexError): last(L[[]])

        self.assertEqual(L[[]], tail(L[[1]]))
        self.assertEqual(L[2, 3], tail(L[1, 2, 3]))
        with self.assertRaises(IndexError): tail(L[[]])

        self.assertEqual(L[[]], init(L[[1]]))
        self.assertEqual(L[1, 2], init(L[1, 2, 3]))
        with self.assertRaises(IndexError): init(L[[]])

        self.assertEqual(Nothing, uncons(L[[]]))
        self.assertEqual(Just % (1, L[[]]), uncons(L[[1]]))
        self.assertEqual(Just % (1, L[2, 3]), uncons(L[1, 2, 3]))

        self.assertTrue(null(L[[]]))
        self.assertFalse(null(L[[1]]))
        self.assertFalse(null(L[1, ...]))

        self.assertEqual(20, length(L[0, ..., 19]))
        self.assertEqual(0, length(L[[]]))

    def test_list_transformations(self):
        from hask.Data.List import map, reverse, intersperse, intercalate
        from hask.Data.List import transpose, subsequences, permutations

        self.assertEqual(L[1, 2, 1], intersperse(2, L[1, 1]))
        self.assertEqual(L[[]], intersperse(2, L[[]]))

        self.assertEqual(L[[L[[]]]], subsequences(L[[]]))
        self.assertEqual(L[ L[[]], L[[1]], L[[2]], L[1, 2]],
                         subsequences(L[1, 2]))

        self.assertEqual(L[L[1, 2], L[2, 1]], permutations(L[1, 2]))
        self.assertEqual(L[[]], permutations(L[[]]))

    def test_reducing_lists(self):
        from hask.Data.List import foldl, foldl_, foldl_, foldr, foldr1, concat
        from hask.Data.List import concatMap, and_, or_, any, all, sum, product
        from hask.Data.List import maximum, minimum

        from hask.Data.List import repeat, take

        self.assertEqual(L[1, ..., 6], concat(L[L[1, 2, 3], L[4, 5, 6]]))
        self.assertEqual(L[[]], concat(L[[]]))
        self.assertEqual(L[1, 1, 1, 1], take(4) * concat * repeat % L[[1]])

        self.assertTrue(or_(L[True, True]))
        self.assertTrue(or_(L[True, False]))
        self.assertFalse(or_(L[[]]))
        self.assertTrue(or_(repeat(True)))

        self.assertTrue(and_(L[True, True]))
        self.assertFalse(and_(L[True, False]))
        self.assertTrue(and_(L[[]]))
        self.assertFalse(and_(repeat(False)))

        self.assertTrue(any(__>5, L[0, ..., 6]))
        self.assertFalse(any(__>6, L[0, ..., 6]))
        self.assertFalse(any(__>6, L[[]]))
        self.assertTrue(any(__>0, L[0, ...]))

        self.assertTrue(all(__>6, L[7, ..., 15]))
        self.assertFalse(all(__>6, L[0, ..., 5]))
        self.assertTrue(all(__>6, L[[]]))
        self.assertFalse(all(__<0, L[0, ...]))

        self.assertEqual(55, sum(L[1, ..., 10]))
        self.assertEqual(0, sum(L[[]]))

        self.assertEqual(3628800, product(L[1, ..., 10]))
        self.assertEqual(1, product(L[[]]))

        self.assertEqual(10, maximum(L[0, ..., 10]))
        with self.assertRaises(ve): maximum(L[[]])

        self.assertEqual(0, minimum(L[0, ..., 10]))
        with self.assertRaises(ve): minimum(L[[]])

    def test_building_lists(self):
        from hask.Data.List import scanl, scanl1, scanr, scanr1, mapAccumL
        from hask.Data.List import mapAccumR, iterate, repeat, replicate, cycle
        from hask.Data.List import unfoldr

        plus_one = (lambda x: x + 1) ** (H/ int >> int)
        self.assertEquals(iterate(plus_one, 0)[:10], L[range(10)])
        self.assertEquals(iterate(__+1, 0)[:10], L[range(10)])

        uf = (lambda x: Nothing if x > 5 else Just((x+1, x+1))) ** \
                (H/ int >> t(Maybe, (int, int)))
        self.assertEquals(L[[]], unfoldr(uf, 6))
        self.assertEquals(L[1, ..., 6], unfoldr(uf, 0))

    def test_sublists(self):
        from hask.Data.List import take, drop, splitAt, takeWhile, dropWhile
        from hask.Data.List import dropWhileEnd, span, break_, stripPrefix
        from hask.Data.List import group, inits, tails, isPrefixOf, isSuffixOf
        from hask.Data.List import isInfixOf, isSubsequenceOf

        self.assertEqual(L[1, 2], take(2, L[1, 2, 3]))
        self.assertEqual(L[1, 2, 3], take(3, L[1, 2, 3]))
        self.assertEqual(L[1, 2, 3], take(3, L[1, ...]))
        self.assertEqual(L[[]], take(0, L[1, ...]))

        self.assertEqual(L[2, 3], drop(1, L[1, 2, 3]))
        self.assertEqual(L[[]], drop(3, L[1, 2, 3]))
        self.assertEqual(L[1, 2, 3], drop(0, L[1, 2, 3]))
        self.assertEqual(4, drop(3, L[1, ...])[0])

        self.assertEqual((L[1, 2, 3], L[4, 5]), splitAt(3, L[1, ..., 5]))
        self.assertEqual((L[[]], L[[]]), splitAt(0, L[[]]))
        self.assertEqual((L[[]], L[1, 2]), splitAt(0, L[1, 2]))
        self.assertEqual((L[[]], L[[]]), splitAt(10, L[[]]))
        self.assertEqual((L[1, 2], L[[]]), splitAt(10, L[1, 2]))
        self.assertEqual(L[1, ..., 10], splitAt(10, L[1, ...])[0])

        self.assertEqual(L[1, ..., 4], takeWhile(__<5, L[1, ...]))
        self.assertEqual(L[[]], takeWhile(__>5, L[1, ...]))
        self.assertEqual(L[[]], takeWhile(__|True, L[[]]))

        self.assertEqual(L[ L[[]], L[[1]], L[1, 2], L[1, 2, 3]],
                         inits(L[1, 2, 3]))
        self.assertEqual(L[[L[[]]]], inits(L[[]]))

        self.assertEqual(L[ L[1, 2, 3], L[2, 3], L[[3]], L[[]] ],
                         tails(L[1, 2, 3]))
        self.assertEqual(L[[L[[]]]], tails(L[[]]))

        self.assertTrue(isPrefixOf(L["a", "b"], L["a", "b", "c"]))
        self.assertTrue(isPrefixOf(L["a", "b"], L["a", ...]))
        self.assertFalse(isPrefixOf(L["a", "b"], L["d", "a", "b", "c"]))

        self.assertTrue(isSuffixOf(L["b", "c"], L["a", "b", "c"]))
        self.assertFalse(isSuffixOf(L["a", "b"], L["d", "a", "b", "c"]))

        self.assertTrue(isInfixOf(L[1, 2], L[2, 3, 1, 2, 4]))
        self.assertTrue(isInfixOf(L[1, 2], L[1, ...]))
        self.assertFalse(isInfixOf(L[8, 1], L[2, 3, 1, 2, 4]))
        self.assertFalse(isInfixOf(L[1, 2], L[2, 3, 1, 4]))

    def test_searching_lists(self):
        from hask.Data.List import elem, notElem, lookup, find, filter
        from hask.Data.List import partition

        self.assertTrue(elem(1, L[1, ...]))
        self.assertFalse(elem(2, L[1, 3, 4, 5]))
        self.assertFalse(notElem(1, L[1, ...]))
        self.assertTrue(notElem(2, L[1, 3, 4, 5]))

    def test_indexing_lists(self):
        from hask.Data.List import elemIndex, elemIndices, findIndex
        from hask.Data.List import findIndicies

    def test_zipping_lists(self):
        from hask.Data.List import zip, zip3, zip4, zip5, zip6, zip7, zipWith
        from hask.Data.List import zipWith3, zipWith4, zipWith5, zipWith6
        from hask.Data.List import zipWith7, unzip, unzip3, unzip4, unzip5
        from hask.Data.List import unzip5, unzip6

        self.assertEqual(L[(1, "a"), (2, "b")], zip(L[1, 2], L["a", "b"]))
        self.assertEqual(L[(1, "a"), (2, "b")], zip(L[1, 2, 3], L["a", "b"]))
        self.assertEqual(L[(1, "a"), (2, "b")], zip(L[1, 2], L["a", "b", "c"]))
        self.assertEqual(L[[]], zip(L[[]], L[[]]))

        self.assertEqual(L[1, 1, 1], zipWith(__-__, L[1, 2, 3], L[0, 1, 2]))
        self.assertEqual(L[1, 1, 1], zipWith(__-__, L[1, 2, 3, 4], L[0, 1, 2]))
        self.assertEqual(L[1, 1, 1], zipWith(__-__, L[1, 2, 3], L[0, 1, 2, 3]))
        self.assertEqual(L[[]], zipWith(__-__, L[[]], L[[]]))

        self.assertEqual((L["a", "b"], L[2, 4]), unzip(L[("a", 2), ("b", 4)]))
        self.assertEqual((L[[]], L[[]]), unzip(L[[]]))

    def test_set_operations(self):
        from hask.Data.List import nub, delete, diff, union, intersect

        self.assertEqual(L[[]], nub(L[[]]))
        self.assertEqual(L[[1]], nub(L[[1]]))
        self.assertEqual(L[[1]], nub(L[[1, 1]]))

    def test_ordered_lists(self):
        from hask.Data.List import sort, sortOn, insert

        self.assertEqual(L[[]], sort(L[[]]))
        self.assertEqual(L[1, 2, 3], sort(L[1, 2, 3]))
        self.assertEqual(L[1, 2, 3], sort(L[2, 3, 1]))
        self.assertEqual(L[1, 1, 2, 3], sort(L[2, 1, 3, 1]))

    def test_generalized_functions(self):
        from hask.Data.List import nubBy, deleteBy, deleteFirstBy, unionBy
        from hask.Data.List import intersectBy, groupBy, sortBy, insertBy
        from hask.Data.List import maximumBy, minimumBy, genericLength
        from hask.Data.List import genericTake, genericDrop, genericSplitAt
        from hask.Data.List import genericIndex, genericReplicate


class TestPrelude(unittest.TestCase):

    def test_imports(self):
        """
        Prelude imports from Data.* modules; ensure things get loaded correctly
        """
        from hask.Prelude import fst, snd, curry, uncurry
        from hask.Prelude import lines, words, unlines, unwords
        from hask.Prelude import Maybe, Just, Nothing, maybe
        from hask.Prelude import Either, Left, Right, either
        from hask.Prelude import Ordering, LT, EQ, GT, max, min, compare
        from hask.Prelude import Num, abs, negate, subtract
        from hask.Prelude import Fractional, recip
        from hask.Prelude import Integral, toRatio, Ratio, R, Rational
        from hask.Prelude import Floating, exp, sqrt, log, pow, logBase, sin
        from hask.Prelude import tan, cos, asin, atan, acos, sinh, tanh, cosh
        from hask.Prelude import asinh, atanh, acosh
        from hask.Prelude import Real, toRational
        from hask.Prelude import RealFrac, properFraction, truncate, round
        from hask.Prelude import ceiling, floor
        from hask.Prelude import RealFloat, isNaN, isInfinite, isNegativeZero
        from hask.Prelude import atan2

        # Data.List, Data.Foldable
        from hask.Prelude import map, filter, head, last, tail, init, null
        from hask.Prelude import length, reverse, foldl, foldl1, foldr
        from hask.Prelude import foldr1, and_, or_, any, all, sum, product
        from hask.Prelude import concat, concatMap, maximum, minimum, scanl
        from hask.Prelude import scanl1, scanr, scanr1, iterate, repeat
        from hask.Prelude import replicate, cycle, take, drop, splitAt
        from hask.Prelude import takeWhile, dropWhile, span, break_, elem
        from hask.Prelude import notElem, lookup, zip, zip3, unzip, unzip3
        from hask.Prelude import zipWith, zipWith3

    def test_functions(self):
        from hask.Prelude import subtract, even, odd, gcd, lcm, id, const, flip
        from hask.Prelude import until, asTypeOf, error

        self.assertEqual(5, subtract(2, 7))
        self.assertEqual(-5, subtract(7, 2))
        self.assertTrue(even(20) and even(-20))
        self.assertFalse(even(21) and even(-21))
        self.assertTrue(odd(21) and odd(-21))
        self.assertFalse(odd(20) and odd(-20))
        self.assertEqual(4, gcd(8, 12))
        self.assertEqual(4, gcd(8, 12))
        self.assertEqual(2, gcd(-4, 6))
        self.assertEqual(8, gcd(8, 0))
        self.assertEqual(8, gcd(0, 8))
        self.assertEqual(0, gcd(0, 0))
        self.assertEqual(12, lcm(6, 4))
        self.assertEqual(3, lcm(3, 3))
        self.assertEqual(9, lcm(9, 3))
        self.assertEqual(2, lcm(1, 2))
        self.assertEqual(0, lcm(0, 8))
        self.assertEqual(0, lcm(8, 0))
        self.assertEqual(0, lcm(0, 0))

        self.assertEqual("a", id("a"))
        self.assertEqual("a", id * id * id % "a")
        self.assertEqual(1, const(1, 2))
        self.assertEqual(1, const(1) * const(3) % "a")
        self.assertEqual(1, flip(__-__, 2, 3))
        self.assertEqual(1, flip(const, 2, 1))
        self.assertEqual(2, flip(flip(const))(2, 1))

        self.assertEqual(1, until(__>0, __+1, -20))
        self.assertEqual(-20, until(__<0, __+1, -20))
        self.assertEqual("a", asTypeOf("a", "a"))
        self.assertEqual(1, asTypeOf(1, 1))

        # error
        with self.assertRaises(Exception): error("")
        msg = "OUT OF CHEESE ERROR"
        try:
            error(msg)
        except Exception as e:
            self.assertEqual(msg, e.message)


class TestDataString(unittest.TestCase):

    def test_string(self):
        from hask.Data.String import lines, words, unlines, unwords
        self.assertEqual(lines("a\nb \n\nc"), L[["a", "b ", "", "c"]])
        self.assertEqual(lines(""), L[[]])
        self.assertEqual(unlines(L[["a", "b ", "", "c"]]), "a\nb \n\nc")
        self.assertEqual(unlines(L[[]]), "")
        self.assertEqual(words(" 1 2  4"), L[["", "1", "2", "", "4"]])
        self.assertEqual(words(""), L[[]])
        self.assertEqual(unwords(L[["", "1", "2", "", "4"]]), " 1 2  4")
        self.assertEqual(unwords(L[[]]), "")


class TestDataChar(unittest.TestCase):

    def test_char(self):
        from hask.Data.Char import ord, chr

        self.assertEqual("a", chr(97))
        with self.assertRaises(te): ord(97)
        with self.assertRaises(te): chr("a")
        with self.assertRaises(te): chr * chr
        for i in range(256):
            self.assertEqual(i, ord * chr % i)


class TestDataNum(unittest.TestCase):

    def test_Num(self):
        from hask.Data.Num import negate, signum, abs
        self.assertEqual(negate(5), -5)
        self.assertEqual(negate(-5), 5)
        self.assertEqual(signum(5), 1)
        self.assertEqual(signum(-5), -1)
        self.assertEqual(signum(0), 0)
        self.assertEqual(abs(5), 5)
        self.assertEqual(abs(-5), 5)

    def test_RealFloat(self):
        from hask.Data.Num import isNaN, isInfinite, isNegativeZero, atan2
        self.assertTrue(isNaN(float("nan")) and not isNaN(1.0))
        self.assertTrue(isInfinite(float("-inf")) and not isInfinite(1.0))
        self.assertTrue(isNegativeZero(-0.0) and not isNegativeZero(0.0))
        self.assertEqual(round(atan2(0.0, 0.0), 5), round(0.0, 5))
        self.assertEqual(round(atan2(0.0, -0.0), 5), round(math.pi, 5))

class TestDataTuple(unittest.TestCase):

    def test_tuple(self):
        from hask.Data.Tuple import fst, snd, curry, uncurry, swap

        self.assertEqual(1, fst((1, 2)))
        self.assertEqual(("a", "b"), fst((("a", "b"), ("c", "d"))))
        self.assertEqual("a", fst(fst((("a", "b"), ("c", "d")))))

        self.assertEqual(2, snd((1, 2)))
        self.assertEqual(("c", "d"), snd((("a", "b"), ("c", "d"))))
        self.assertEqual("b", snd * fst % (("a", "b"), ("c", "d")))
        self.assertEqual("c", fst * snd % (("a", "b"), ("c", "d")))

        self.assertEqual(swap(swap((1, 2))), (1, 2))
        self.assertEqual(swap((1, "a")), ("a", 1))

        @sig(H/ (str, str) >> str)
        def uncurried_fn(tup):
            return tup[0] + tup[1]

        @sig(H/ list >> list >> list)
        def curried_fn(x, y):
            return x + y

        self.assertEqual(uncurry(curried_fn, ([1, 2], [3, 4])), [1, 2, 3, 4])
        self.assertEqual(curry(uncurried_fn, "a", "b"), "ab")
        self.assertEqual(uncurry(curry(uncurried_fn), ("a","b")), "ab")
        self.assertEqual(curry(uncurry(curried_fn), ["a"], ["b"]), ["a","b"])


class TestDataOrd(unittest.TestCase):

    def test_ord(self):
        from hask.Data.Ord import max, min, compare, comparing
        self.assertEqual(max(1, 2), 2)
        self.assertEqual(min(1, 2), 1)
        self.assertEqual(compare(1)(2), LT)

        from hask.Data.Tuple import fst, snd
        self.assertEqual(comparing(fst, (1, 2), (3, 0)), LT)
        self.assertEqual(comparing(snd, (1, 2), (3, 0)), GT)


class TestDataRatio(unittest.TestCase):

    def test_ratio(self):
        from hask.Data.Ratio import R, numerator, denominator
        self.assertEqual(1, numerator % R(1, 2))
        self.assertEqual(2, denominator % R(1, 2))


class TestPython(unittest.TestCase):

    def test_builtins(self):
        from hask.Python.builtins import callable, cmp, delattr, divmod
        from hask.Python.builtins import getattr, hasattr, hash
        from hask.Python.builtins import hex, isinstance, issubclass, len, oct
        from hask.Python.builtins import repr, setattr, sorted

        class Example(object):
            a = 1

        self.assertTrue(callable(__+1))
        self.assertEqual(1, cmp(10) % 9)
        self.assertEqual(divmod(5)(2), (2, 1))

        with self.assertRaises(te): cmp(1, "a")
        with self.assertRaises(te): oct(1.0)
        with self.assertRaises(te): hex(1.0)
        with self.assertRaises(te): hasattr(list)(len)
        with self.assertRaises(te): getattr(list)(len)
        with self.assertRaises(te): setattr(list)(len)
        with self.assertRaises(te): delattr(list)(len)


class Test_README_Examples(unittest.TestCase):
    """Make sure the README examples are all working"""

    def test_list(self):
        self.assertEqual([1, 2, 3], list(L[1, 2, 3]))
        my_list = ["a", "b", "c"]
        self.assertEqual(L["a", "b", "c"], L[my_list])
        self.assertEqual(L[(x**2 for x in range(1, 11))],
            L[1, 4, 9, 16, 25, 36, 49, 64, 81, 100])

        self.assertEqual(L[1, 2, 3], 1 ^ L[2, 3])
        self.assertEqual("goodnight" ^ ("sweet" ^ ("prince" ^ L[[]])),
            L["goodnight", "sweet", "prince"])
        with self.assertRaises(te): "a" ^ L[1.0, 10.3]
        self.assertEqual(L[1, 2] + L[3, 4], L[1, 2, 3, 4])

        from hask.Data.List import take
        self.assertEqual(take(5, L["a", "b", ...]),
                         L['a', 'b', 'c', 'd', 'e'])

        self.assertEqual(L[1,...][5:10],
                         L[6, 7, 8, 9, 10])

        from hask.Data.List import map
        from hask.Data.Char import chr
        letters = map(chr, L[97, ...])
        self.assertEqual(letters[:9],
                          L['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i'])

        self.assertTrue(55 in L[1, 3, ...])

    def test_ADT(self):
        FooBar, Foo, Bar =\
        data.FooBar("a", "b") == d.Foo("a", "b", str) | d.Bar
        self.assertIsNotNone(Foo(1, 2, "s"))

    def test_sig(self):
        @sig(H/ "a" >> "b" >> "a")
        def const(x, y):
            return x
        self.assertEqual(const(1, 2), 1)

        def const(x, y):
            return x
        const = const ** (H/ "a" >> "b" >> "a")
        self.assertEqual(const(1, 2), 1)

        f = (lambda x, y: x + y) ** (H/ int >> int >> int)
        self.assertEqual(5, f(2, 3))
        with self.assertRaises(te): f(9, 1.0)

        g = (lambda a, b, c: a / (b + c)) ** (H/ int >> int >> int >> int)
        self.assertEqual(g(10, 2, 3), 2)
        part_g = g(12)
        self.assertEqual(part_g(2, 2), 3)
        self.assertEqual(g(20, 1)(4), 4)
        self.assertEqual(Just * Just * Just * Just % 77, Just(Just(Just(Just(77)))))

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
            return

        Ratio, R =\
                data.Ratio("a") == d.R("a", "a") & deriving(Eq)

        Rational = t(Ratio, int)


        @sig(H/ Rational >> Rational >> Rational)
        def addRational(rat1, rat2):
            pass

        from hask.Prelude import flip
        h = (lambda x, y: x / y) ** (H/ float >> float >> float)
        self.assertEqual(h(3.0) * h(6.0) * flip(h, 2.0) % 36.0, 9.0)

    def test_match(self):
        @sig(H/ int >> int)
        def fib(x):
            return ~(caseof(x)
                        | m(0)   >> 1
                        | m(1)   >> 1
                        | m(m.n) >> fib(p.n - 2) + fib(p.n - 1)
                    )

        self.assertEqual(1, fib(0))
        self.assertEqual(1, fib(1))
        self.assertEqual(13, fib(6))

        def default_to_zero(x):
            return ~(caseof(x)
                        | m(Just(m.x)) >> p.x
                        | m(Nothing)   >> 0)

        self.assertEqual(default_to_zero(Just(27)), 27)
        self.assertEqual(default_to_zero(Nothing), 0)
        self.assertEqual(Just(20.0)[0], 20.0)
        self.assertEqual(Left("words words words words")[0], "words words words words")
        with self.assertRaises(IndexError): Nothing[0]

    def test_typeclasses(self):
        from hask.Prelude import fmap
        M, N, J = data.M("a") == d.N | d.J("a") & deriving(Show, Eq, Ord)

        def maybe_fmap(fn, maybe_value):
            return ~(caseof(maybe_value)
                        | m(N)      >> N
                        | m(J(m.x)) >> J(fn(p.x))
                    )

        instance(Functor, M).where(
            fmap = maybe_fmap
        )

        times2 = (lambda x: x * 2) ** (H/ int >> int)
        toFloat = float ** (H/ int >> float)

        self.assertEqual(fmap(toFloat, J(10)), J(10.0))
        self.assertEqual(fmap(toFloat, fmap(times2, J(25))), J(50.0))
        self.assertEqual((toFloat * times2) * J(25), J(50.0))
        self.assertEqual((toFloat * times2) * N, N)

        instance(Applicative, M).where(
            pure = J
        )

        instance(Monad, M).where(
            bind = lambda x, f: ~(caseof(x)
                                    | m(J(m.a)) >> f(p.a)
                                    | m(N)   >> N)
        )

        @sig(H/ int >> int >> t(M, int))
        def safe_div(x, y):
            return N if y == 0 else J(x/y)

        from hask.Prelude import flip
        divBy = flip(safe_div)
        self.assertEqual(J(9) >> divBy(3), J(3))

        self.assertEqual(Just(12) >> divBy(2) >> divBy(2) >> divBy(3), J(1))
        self.assertEqual(J(12) >> divBy(0) >> divBy(6), N)

        from hask.Data.List import replicate
        self.assertEqual(L[1, 2] >> replicate(2) >> replicate(2),
                L[1, 1, 1, 1, 2, 2, 2, 2])

        class Person(object):
            def __init__(self, name, age):
                self.name = name
                self.age = age

        instance(Eq, Person).where(
            eq = lambda p1, p2: p1.name == p2.name and p1.age == p2.age
        )

        self.assertFalse(Person("Philip Wadler", 59) == Person("Simon Peyton Jones", 57))

    def test_sections(self):
        f = (__ - 20) * (2 ** __) * (__ + 3)
        self.assertEqual(8172, f(10))
        self.assertEqual("Hello world", (__+__)('Hello ', 'world'))
        self.assertEqual(1024, (__**__)(2)(10))

    def test_guard(self):
        porridge_tempurature = 80
        self.assertEqual(
                ~(guard(porridge_tempurature)
                    | c(__ < 20)  >> "Porridge is too cold!"
                    | c(__ < 90)  >> "Porridge is just right!"
                    | c(__ < 150) >> "Porridge is too hot!"
                    | otherwise   >> "Porridge has gone thermonuclear"
                ),
                'Porridge is just right!')

        def examine_password_security(password):
            analysis = ~(guard(password)
                | c(lambda x: len(x) > 20) >> "Wow, that's one secure password"
                | c(lambda x: len(x) < 5)  >> "You made Bruce Schneier cry"
                | c(__ == "12345")         >> "Same combination as my luggage!"
                | otherwise                >> "Hope it's not `password`"
            )
            return analysis

        nuclear_launch_code = "12345"
        self.assertEqual(
                examine_password_security(nuclear_launch_code),
                'Same combination as my luggage!')

    def test_decorators(self):
        def eat_cheese(cheese):
            if cheese <= 0:
                raise ValueError("Out of cheese error")
            return cheese - 1

        maybe_eat = in_maybe(eat_cheese)
        self.assertEqual(maybe_eat(1), Just(0))
        self.assertEqual(maybe_eat(0), Nothing)
        self.assertEqual(Just(6), Just(7) >> maybe_eat)
        self.assertEqual(Just(7),
                         Just(10) >> maybe_eat >> maybe_eat >> maybe_eat)
        self.assertEqual(Nothing,
                         Just(1) >> maybe_eat >> maybe_eat >> maybe_eat)

        either_eat = in_either(eat_cheese)
        self.assertEqual(either_eat(10), Right(9))
        self.assertTrue(isinstance(either_eat(0)[0], ValueError))

    def test_examples(self):
        @sig(H/ int >> int >> t(Maybe, int))
        def safe_div(x, y):
            return Nothing if y == 0 else Just(x/y)

        from hask.Data.Maybe import mapMaybe
        self.assertEqual(mapMaybe(safe_div(12)) % L[0, 1, 3, 0, 6],
                         L[12, 4, 2])

        from hask.Data.List import isInfixOf
        self.assertTrue(isInfixOf(L[2, 8], L[1, 4, 6, 2, 8, 3, 7]))

        from hask.Control.Monad import join
        self.assertEqual(join(Just(Just(1))), Just(1))

        from hask.Prelude import flip
        from hask.Data.Tuple import snd
        from hask.Python.builtins import divmod, hex

        hexMod = hex * snd * flip(divmod, 16)
        self.assertEqual(hexMod(24), '0x8')


if __name__ == '__main__':
    unittest.main()
