from ..lang import H
from ..lang import sig


#=============================================================================#
# Character classification


@sig(H/ str >> bool)
def isControl(s):
    """
    isControl :: str -> bool

    Selects control characters, which are the non-printing characters of the
    Latin-1 subset of Unicode.
    """
    raise NotImplementedError


@sig(H/ str >> bool)
def isSpace(s):
    """
    isSpace :: str -> bool

    Returns True for any Unicode space character, and the control characters
    \t, \n, \r, \f, \v.
    """
    return s in " \t\n\r\f\v"


@sig(H/ str >> bool)
def isLower(s):
    """
    isLower :: str -> bool

    Selects lower-case alphabetic Unicode characters (letters).
    """
    return s.lower() == s


@sig(H/ str >> bool)
def isUpper(s):
    """
    isUpper :: str -> bool

    Selects upper-case or title-case alphabetic Unicode characters (letters).
    Title case is used by a small number of letter ligatures like the
    single-character form of Lj.
    """
    return s.upper() == s


@sig(H/ str >> bool)
def isAlpha(s):
    """
    isAlpha :: str -> bool

    Selects alphabetic Unicode characters (lower-case, upper-case and
    title-case letters, plus letters of caseless scripts and modifiers
    letters). This function is equivalent to isLetter.
    """
    raise NotImplementedError


@sig(H/ str >> bool)
def isAlphaNum(s):
    """
    isAlphaNum :: str -> bool

    Selects alphabetic or numeric digit Unicode characters.

    Note that numeric digits outside the ASCII range are selected by this
    function but not by isDigit. Such digits may be part of identifiers but are
    not used by the printer and reader to represent numbers.
    """
    raise NotImplementedError


@sig(H/ str >> bool)
def isPrint(s):
    """
    isPrint :: str -> bool

    Selects printable Unicode characters (letters, numbers, marks, punctuation,
    symbols and spaces).
    """
    raise NotImplementedError


@sig(H/ str >> bool)
def isDigit(s):
    """
    isDigit :: str -> bool

    Selects ASCII digits, i.e. '0'..'9'.
    """
    return s in "0123456789"


@sig(H/ str >> bool)
def isOctDigit(s):
    """
    isOctDigit :: str -> bool

    Selects ASCII octal digits, i.e. '0'..'7'.
    """
    return s in "01234567"


@sig(H/ str >> bool)
def isHexDigit(s):
    """
    isHexDigit :: str -> bool

    Selects ASCII hexadecimal digits, i.e. '0'..'9', 'a'..'f', 'A'..'F'.
    """
    return s in "0123456789abcdefABCDEF"


@sig(H/ str >> bool)
def isLetter(s):
    """
    isLetter :: str -> bool

    Selects alphabetic Unicode characters (lower-case, upper-case and
    title-case letters, plus letters of caseless scripts and modifiers
    letters). This function is equivalent to isAlpha.
    """
    return isAlpha(s)


@sig(H/ str >> bool)
def isMark(s):
    """
    isMark :: str -> bool

    Selects Unicode mark characters, e.g. accents and the like, which combine
    with preceding letters.
    """
    raise NotImplementedError


@sig(H/ str >> bool)
def isNumber(s):
    """
    isNumber :: str -> bool

    Selects Unicode numeric characters, including digits from various scripts,
    Roman numerals, etc.
    """
    raise NotImplementedError


@sig(H/ str >> bool)
def isPunctuation(s):
    """
    isPunctuation :: str -> bool

    Selects Unicode punctuation characters, including various kinds of
    connectors, brackets and quotes.
    """
    raise NotImplementedError


@sig(H/ str >> bool)
def isSymbol(s):
    """
    isSymbol :: str -> bool

    Selects Unicode symbol characters, including mathematical and currency
    symbols.
    """
    raise NotImplementedError


@sig(H/ str >> bool)
def isSeparator(s):
    """
    isSeparator :: str -> bool

    Selects Unicode space and separator characters.
    """
    raise NotImplementedError


#=============================================================================#
# Subranges


@sig(H/ str >> bool)
def isAscii(s):
    """
    isAscii :: str -> bool

    Selects the first 128 characters of the Unicode character set,
    corresponding to the ASCII character set.
    """
    return ord(s) < 128


@sig(H/ str >> bool)
def isLatin1(s):
    """
    isLatin1 :: str -> bool

    Selects the first 256 characters of the Unicode character set,
    corresponding to the ISO 8859-1 (Latin-1) character set.
    """
    return ord(s) < 256


@sig(H/ str >> bool)
def isAsciiUpper(s):
    """
    isAsciiUpper :: str -> bool

    Selects ASCII upper-case letters, i.e. characters satisfying both isAscii
    and isUpper.
    """
    return isAscii(s) and isUpper(s)


@sig(H/ str >> bool)
def isAsciiLower(s):
    """
    isAsciiLower :: str -> bool

    Selects ASCII lower-case letters, i.e. characters satisfying both isAscii
    and isLower.
    """
    return isAscii(s) and isLower(s)


#=============================================================================#
# Case conversion


@sig(H/ str >> str)
def toUpper(s):
    """
    toUpper :: str -> str

    Convert a letter to the corresponding upper-case letter, if any. Any other
    character is returned unchanged.
    """
    return s.upper()


@sig(H/ str >> str)
def toLower(s):
    """
    toLower :: str -> str

    Convert a letter to the corresponding lower-case letter, if any. Any other
    character is returned unchanged.
    """
    return s.lower()


@sig(H/ str >> str)
def toTitle(s):
    """
    toTitle :: str -> str

    Convert a letter to the corresponding title-case or upper-case letter, if
    any. (Title case differs from upper case only for a small number of
    ligature letters.) Any other character is returned unchanged.
    """
    return toUpper(s)


#=============================================================================#
# Single digit characters


@sig(H/ str >> int)
def digitToInt(s):
    """
    digitToInt :: str -> int

    Convert a single digit Char to the corresponding Int. This function fails
    unless its argument satisfies isHexDigit, but recognises both upper and
    lower-case hexadecimal digits (i.e. '0'..'9', 'a'..'f', 'A'..'F').
    """
    if s not in "0123456789abcdefABCDEF":
        raise ValueError("not a digit %s" % s)
    return "0123456789abcdef".index(s.lower())


@sig(H/ int >> str)
def intToDigit(s):
    """
    intToDigit :: int -> str

    Convert an Int in the range 0..15 to the corresponding single digit Char.
    This function fails on other inputs, and generates lower-case hexadecimal
    digits.
    """
    if s > 15 or s < 0:
        raise ValueError("not a digit %s" % s)
    return str(s) if s < 10 else "abcdef"[s-10]


#=============================================================================#
# Numeric representations

chr = chr ** (H/ int >> str)
ord = ord ** (H/ str >> int)
