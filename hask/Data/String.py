from ..lang import H
from ..lang import sig
from ..lang import L


@sig(H/ str >> [str])
def lines(string):
    """
    lines :: String -> [String]

    lines breaks a string up into a list of strings at newline characters.
    The resulting strings do not contain newlines.
    """
    return L[[]] if not string else L[string.split("\n")]


@sig(H/ str >> [str])
def words(string):
    """
    words :: String -> [String]

    words breaks a string up into a list of words, which were delimited by
    white space.
    """
    return L[[]] if string == "" else L[string.split(" ")]


@sig(H/ [str] >> str)
def unlines(strings):
    """
    lines :: [String] -> String

    unlines is an inverse operation to lines. It joins lines, after appending a
    terminating newline to each.
    """
    return "\n".join(strings)


@sig(H/ [str] >> str)
def unwords(strings):
    """
    unwords :: [String] -> String

    unwords is an inverse operation to words. It joins words with separating
    spaces.
    """
    return " ".join(strings)
