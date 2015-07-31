from ..lang import H


#=============================================================================#
# Typed wrappers for builtin Python functions.
# This makes it easier to chain lots of things together in function composition
# without having to manually add type signatures to Python builtins.


callable = callable ** (H/ "a" >> bool)
cmp = cmp ** (H/ "a" >> "a" >> int)
delattr = delattr ** (H/ "a" >> str >> None)
divmod = divmod ** (H/ "a" >> "b" >> ("c", "c"))
getattr = getattr ** (H/ "a" >> str >> "b")
hasattr = hasattr ** (H/ "a" >> str >> bool)
hash = hash ** (H/ "a" >> int)
hex = hex ** (H/ int >> str)
isinstance = isinstance ** (H/ "a" >> "b" >> bool)
issubclass = issubclass ** (H/ "a" >> "b" >> bool)
len = len ** (H/ "a" >> int)
oct = oct ** (H/ int >> str)
repr = repr ** (H/ "a" >> str)
setattr = setattr ** (H/ "a" >> str >> "b" >> None)
sorted = sorted ** (H/ "a" >> list)
unichr = unichr ** (H/ int >> unicode)
