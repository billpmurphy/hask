import operator
import sys

from type_system import Typeclass
from type_system import is_builtin
from type_system import nt_to_tuple
from type_system import build_instance

from syntax import instance
from syntax import sig
from syntax import H


#=============================================================================#
# Basic typeclasses


class Show(Typeclass):
    """
    Conversion of values to readable strings.

    Attributes:
        __str__, show

    Minimal complete definition:
        show

    """
    @classmethod
    def make_instance(typeclass, cls, show):
        __show__ = show ** (H/ "a" >> str)
        show = lambda self: __show__(self)

        build_instance(Show, cls, {"show": show})
        if not is_builtin(cls):
            cls.__repr__ = show
            cls.__str__ = show
        return

    @classmethod
    def derive_instance(typeclass, cls):
        def show(self):
            if len(self.__class__._fields) == 0:
                return self.__class__.__name__

            nt_tup = nt_to_tuple(self)
            if len(nt_tup) == 1:
                tuple_str = "(%s)" % Show[nt_tup[0]].show(nt_tup[0])
            else:
                tuple_str = Show[nt_tup].show(nt_tup)

            return "{0}{1}".format(self.__class__.__name__, tuple_str)
        Show.make_instance(cls, show=show)
        return


@sig(H/ "a" >> str)
def show(obj):
    """
    show :: a -> str

    Convert a value to a readable string.
    """
    return Show[obj].show(obj)


class Eq(Typeclass):
    """
    The Eq class defines equality (==) and inequality (!=).

    Attributes:
        __eq__
        __ne__

    Minimal complete definition:
        eq
    """
    @classmethod
    def make_instance(typeclass, cls, eq, ne=None):
        def default_ne(self, other):
            return not eq(self, other)

        __eq__ = eq ** (H/ "a" >> "a" >> bool)
        __ne__ = (default_ne if ne is None else ne) ** (H/ "a" >> "a" >> bool)
        eq = lambda self, other: __eq__(self, other)
        ne = lambda self, other: __ne__(self, other)

        build_instance(Eq, cls, {"eq": eq, "ne": ne})
        if not is_builtin(cls):
            cls.__eq__ = eq
            cls.__ne__ = ne
        return

    @classmethod
    def derive_instance(typeclass, cls):
        def __eq__(self, other):
            return self.__class__ == other.__class__ and \
                nt_to_tuple(self) == nt_to_tuple(other)

        def __ne__(self, other):
            return self.__class__ != other.__class__ or  \
                nt_to_tuple(self) != nt_to_tuple(other)

        Eq.make_instance(cls, eq=__eq__, ne=__ne__)
        return


class Ord(Eq):
    """
    The Ord class is used for totally ordered datatypes.

    Instances of Ord can be derived for any user-defined datatype whose
    constituent types are in Ord. The declared order of the constructors in the
    data declaration determines the ordering in derived Ord instances. The
    Ordering datatype allows a single comparison to determine the precise
    ordering of two objects.

    Dependencies:
        Eq

    Attributes:
        __lt__, __le__, __gt__, __ge__

    Minimal complete definition:
        lt
    """
    @classmethod
    def make_instance(typeclass, cls, lt, le=None, gt=None, ge=None):
        def_le = lambda s, o: s.__lt__(o) or s.__eq__(o)
        def_gt = lambda s, o: not s.__lt__(o) and not s.__eq__(o)
        def_ge = lambda s, o: not s.__lt__(o) or s.__eq__(o)

        __lt__ = lt ** (H/ "a" >> "a" >> bool)
        __le__ = (def_le if le is None else le) ** (H/ "a" >> "a" >> bool)
        __gt__ = (def_gt if gt is None else gt) ** (H/ "a" >> "a" >> bool)
        __ge__ = (def_ge if ge is None else ge) ** (H/ "a" >> "a" >> bool)

        lt = lambda self, other: __lt__(self, other)
        le = lambda self, other: __le__(self, other)
        gt = lambda self, other: __gt__(self, other)
        ge = lambda self, other: __ge__(self, other)

        attrs = {"lt":lt, "le":le, "gt":gt, "ge":ge}
        build_instance(Ord, cls, attrs)
        if not is_builtin(cls):
            cls.__lt__ = lt
            cls.__le__ = le
            cls.__gt__ = gt
            cls.__ge__ = ge
        return

    @classmethod
    def derive_instance(typeclass, cls):
        def zip_cmp(self, other, fn):
            """
            Compare the data constructor and all of the fields of two ADTs.
            """
            if self.__ADT_slot__ == other.__ADT_slot__:
                if len(nt_to_tuple(self)) == 0:
                    return fn((), ())
                return fn(nt_to_tuple(self), nt_to_tuple(other))
            return fn(self.__ADT_slot__, other.__ADT_slot__)

        lt = lambda s, o: zip_cmp(s, o, operator.lt)
        le = lambda s, o: zip_cmp(s, o, operator.le)
        gt = lambda s, o: zip_cmp(s, o, operator.gt)
        ge = lambda s, o: zip_cmp(s, o, operator.ge)

        Ord.make_instance(cls, lt=lt, le=le, gt=gt, ge=ge)
        return


#=============================================================================#
# Classes not yet functional, because they have polymorphic return types


class Bounded(Typeclass):
    """
    The Bounded class is used to name the upper and lower limits of a type. Ord
    is not a superclass of Bounded since types that are not totally ordered may
    also have upper and lower bounds.

    The Bounded class may be derived for any enumeration type; minBound is the
    first constructor listed in the data declaration and maxBound is the last.
    Bounded may also be derived for single-constructor datatypes whose
    constituent types are in Bounded.

    Attributes:
        minBound, maxBound

    Minimal complete definition:
        minBound, maxBound
    """
    @classmethod
    def make_instance(typeclass, cls, minBound, maxBound):
        attrs = {"minBound":minBound, "maxBound":maxBound}
        build_instance(Bounded, cls, attrs)
        return

    @classmethod
    def derive_instance(typeclass, cls):
        # All data constructors must be enums
        for data_con in cls.__constructors__:
            if not isinstance(data_con, cls):
                raise TypeError("Cannot derive Bounded; %s is not an enum" %
                                 data_con.__name__)

        maxBound = lambda s: cls.__constructors__[0]
        minBound = lambda s: cls.__constructors__[-1]
        Bounded.make_instance(cls, minBound=minBound, maxBound=maxBound)
        return


class Read(Typeclass):
    """
    Parsing of Strings, producing values.

    Attributes:
        read

    Minimal complete definition:
        read
    """
    @classmethod
    def make_instance(typeclass, cls, read):
        build_instance(Read, cls, {"read":read})
        return

    @classmethod
    def derive_instance(typeclass, cls):
        Read.make_instance(cls, read=eval)
        return


#=============================================================================#
# Instances for builtin types


instance(Show, str).where(show=str.__repr__)
instance(Show, int).where(show=int.__str__)
instance(Show, float).where(show=tuple.__str__)
instance(Show, complex).where(show=complex.__str__)
instance(Show, bool).where(show=bool.__str__)
instance(Show, list).where(show=list.__str__)
instance(Show, tuple).where(show=tuple.__str__)
instance(Show, set).where(show=set.__str__)
instance(Show, dict).where(show=dict.__str__)
instance(Show, frozenset).where(show=frozenset.__str__)
instance(Show, slice).where(show=slice.__str__)

instance(Eq, str).where(eq=str.__eq__, ne=str.__ne__)
instance(Eq, int).where(eq=int.__eq__, ne=int.__ne__)
instance(Eq, float).where(eq=float.__eq__, ne=float.__ne__)
instance(Eq, complex).where(eq=complex.__eq__, ne=complex.__ne__)
instance(Eq, bool).where(eq=bool.__eq__, ne=bool.__ne__)
instance(Eq, list).where(eq=list.__eq__, ne=list.__ne__)
instance(Eq, tuple).where(eq=tuple.__eq__, ne=tuple.__ne__)
instance(Eq, set).where(eq=set.__eq__, ne=set.__ne__)
instance(Eq, dict).where(eq=dict.__eq__, ne=dict.__ne__)
instance(Eq, frozenset).where(eq=frozenset.__eq__, ne=frozenset.__ne__)
instance(Eq, slice).where(eq=slice.__eq__, ne=slice.__ne__)
instance(Eq, type).where(eq=type.__eq__, ne=type.__ne__)

instance(Ord, str).where(lt=str.__lt__, le=str.__le__,
                         gt=str.__gt__, ge=str.__ge__)
instance(Ord, int).where(lt=int.__lt__, le=int.__le__,
                         gt=int.__gt__, ge=int.__ge__)
instance(Ord, float).where(lt=float.__lt__, le=float.__le__,
                           gt=float.__gt__, ge=float.__ge__)
instance(Ord, complex).where(lt=complex.__lt__, le=complex.__le__,
                             gt=complex.__gt__, ge=complex.__ge__)
instance(Ord, bool).where(lt=bool.__lt__, le=bool.__le__,
                          gt=bool.__gt__, ge=bool.__ge__)
instance(Ord, list).where(lt=list.__lt__, le=list.__le__,
                          gt=list.__gt__, ge=list.__ge__)
instance(Ord, tuple).where(lt=tuple.__lt__, le=tuple.__le__,
                           gt=tuple.__gt__, ge=tuple.__ge__)
instance(Ord, set).where(lt=set.__lt__, le=set.__le__,
                          gt=set.__gt__, ge=set.__ge__)
instance(Ord, dict).where(lt=dict.__lt__, le=dict.__le__,
                          gt=dict.__gt__, ge=dict.__ge__)
instance(Ord, frozenset).where(lt=frozenset.__lt__, le=frozenset.__le__,
                               gt=frozenset.__gt__, ge=frozenset.__ge__)

if sys.version[0] == '2':

    instance(Show, long).where(show=long.__str__)
    instance(Show, unicode).where(show=unicode.__str__)

    instance(Eq, long).where(eq=long.__eq__, ne=long.__ne__)
    instance(Eq, unicode).where(eq=unicode.__eq__, ne=unicode.__ne__)

    instance(Ord, long).where(lt=long.__lt__, le=long.__le__,
                            gt=long.__gt__, ge=long.__ge__)
    instance(Ord, unicode).where(lt=unicode.__lt__, le=unicode.__le__,
                                gt=unicode.__gt__, ge=unicode.__ge__)
