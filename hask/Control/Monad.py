import itertools

from ..lang import sig
from ..lang import H
from ..lang import t
from ..lang import L
from ..lang import build_instance
from ..lang import is_builtin
from ..lang import List
from ..lang import instance
from ..Data.Functor import fmap
from Applicative import Applicative


class Monad(Applicative):
    """
    The Monad class defines the basic operations over a monad, a concept from a
    branch of mathematics known as category theory. From the perspective of a
    Haskell programmer, however, it is best to think of a monad as an abstract
    datatype of actions.

    Dependencies:
        Functor, Applicative

    Attributes:
        bind, __rshift__

    Minimal complete definition:
        bind
    """
    @classmethod
    def make_instance(typeclass, cls, bind):
        bind = bind ** (H[(Monad, "m")]/ t("m", "a") >> (H/ "a" >> t("m", "b"))
                >> t("m", "b"))
        if not is_builtin(cls):
            def bind_wrap(s, o):
                return Monad[s].bind(s, o)
            cls.__rshift__ = bind_wrap
        build_instance(Monad, cls, {"bind":bind})
        return


@sig(H[(Monad, "m")]/ t("m", "a") >> (H/ "a" >> t("m", "b")) >> t("m", "b"))
def bind(m, fn):
    """
    bind :: Monad m => m a -> (a -> m b) -> m b

    Monadic bind.
    """
    return Monad[m].bind(m, fn)


@sig(H[(Monad, "m")]/ t("m", t("m", "a")) >> t("m", "a"))
def join(m):
    """
    join :: Monad m => m (m a) -> m a

    The join function is the conventional monad join operator. It is used to
    remove one level of monadic structure, projecting its bound argument into
    the outer level.
    """
    __id = (lambda x: x) ** (H/ "a" >> "a")
    return bind(m, __id)


@sig(H[(Monad, "m")]/ (H/ "a" >> "r") >> t("m", "a") >> t("m", "r"))
def liftM(fn, m):
    """
    liftM :: Monad m => (a1 -> r) -> m a1 -> m r

    Promote a function to a monad.
    """
    return fmap(fn, m)


instance(Monad, List).where(
    bind = lambda x, fn: L[itertools.chain.from_iterable(fmap(fn, x))]
)
