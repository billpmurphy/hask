import itertools
from ..lang import TypedFunc
from ..lang import Typeclass
from ..lang import is_builtin
from ..lang import build_instance
from ..lang import List
from ..lang import L
from ..lang import H
from ..lang import sig
from ..lang import t
from ..lang import instance


class Functor(Typeclass):
    """
    The Functor class is used for types that can be mapped over. Instances of
    Functor should satisfy the following laws:

    fmap(id)  ==  id
    fmap(f * g)  ==  fmap(f * (fmap g))

    Attributes:
        fmap, __rmul__

    Minimal complete definition:
        fmap
    """
    @classmethod
    def make_instance(typeclass, cls, fmap):
        fmap = fmap ** \
            (H[(Functor, "f")]/ (H/ "a" >> "b") >> t("f", "a") >> t("f", "b"))
        if not is_builtin(cls):
            cls.__rmul__ = lambda x, f: fmap(f, x)
        build_instance(Functor, cls, {"fmap":fmap})
        return


@sig(H[(Functor, "f")]/ (H/ "a" >> "b") >> t("f", "a") >> t("f", "b"))
def fmap(f, x):
    return Functor[x].fmap(f, x)


instance(Functor, List).where(
    fmap = lambda fn, lst: L[itertools.imap(fn, iter(lst))]
)

instance(Functor, TypedFunc).where(
    fmap = TypedFunc.__mul__
)
