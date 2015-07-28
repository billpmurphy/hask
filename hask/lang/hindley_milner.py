# Implementation of Hindley-Milner type inference system for Python, based on
# by Robert Smallshire's implementation for OWL BASIC.
#
# Robert's original version can be found here:
# http://smallshire.org.uk/sufficientlysmall/2010/04/11/a-hindley-milner-type-inference-implementation-in-python/
#
# Changes from Robert's version:
# 1) Simplified type language somewhat (Let and Letrec are merged, as are Var
#    and Ident)
# 2) Type system expanded to handle polymorphic higher-kinded types (however,
#    in its current state it does not do this correctly due to the way that
#    typeclasses were bolted on; this will be fixed in future versions)
# 3) Interface tweaked a bit to work better with Python types, including
#    pretty-printing of type names and some useful subclasses of TypeOperator
# 4) Type unification also unifies typeclass constraints


#=============================================================================#
# Class definitions for the AST nodes which comprise the type language for
# which types will be inferred


class Lam(object):
    """Lambda abstraction"""

    def __init__(self, v, body):
        self.v = v
        self.body = body

    def __str__(self):
        return "(\{v} -> {body})".format(v=self.v, body=self.body)


class Var(object):
    """Variable/Identifier"""

    def __init__(self, name):
        self.name = name

    def __str__(self):
        return str(self.name)


class App(object):
    """Function application"""

    def __init__(self, fn, arg):
        self.fn = fn
        self.arg = arg

    def __str__(self):
        return "({fn} {arg})".format(fn=self.fn, arg=self.arg)


class Let(object):
    """Let binding (always recursive)"""

    def __init__(self, v, defn, body):
        self.v = v
        self.defn = defn
        self.body = body

    def __str__(self):
        exp = "(let {v} = {defn} in {body})"
        return exp.format(v=self.v, defn=self.defn, body=self.body)


#=============================================================================#
# Types and type constructors


def show_type(type_name):
    """
    Pretty-print a Python type or internal type name.

    Args:
        type_name: a Python type, or a string representing a type name

    Returns: a string representation of the type
    """
    if isinstance(type_name, str):
        return type_name

    elif isinstance(type_name, type):
        return type_name.__name__

    return str(type_name)


class TypeVariable(object):
    """
    A type variable standing for an arbitrary type. All type variables have
    a unique id, but names are only assigned lazily, when required.

    Note that this approach is *not* thread-safe.
    """

    next_variable_id = 0
    next_var_name = 'a'

    def __init__(self, constraints=()):
        self.id = TypeVariable.next_variable_id
        TypeVariable.next_variable_id += 1
        self.instance = None
        self.__name = None
        self.constraints = constraints

    def __getName(self):
        """
        Names are allocated to TypeVariables lazily, so that only TypeVariables
        converted to strings are given names.
        """
        if self.__name is None:
            self.__name = TypeVariable.next_var_name
            TypeVariable.next_var_name = chr(ord(TypeVariable.next_var_name)
                                             + 1)
        return self.__name

    name = property(__getName)

    def __str__(self):
        if self.instance is not None:
            return str(self.instance)
        return self.name

    def __repr__(self):
        return "TypeVariable(id = {0})".format(self.id)


class TypeOperator(object):
    """An n-ary type constructor which builds a new type from old"""

    def __init__(self, name, types):
        self.name = name
        self.types = types

    def __str__(self):
        num_types = len(self.types)
        if num_types == 0:
            return show_type(self.name)
        return "({0} {1})".format(show_type(self.name),
                                  ' '.join(map(show_type, self.types)))


class Function(TypeOperator):
    """A binary type constructor which builds function types"""

    def __init__(self, from_type, to_type):
        super(self.__class__, self).__init__("->", [from_type, to_type])

    def __str__(self):
        return "({1} {0} {2})".format(show_type(self.name),
                                      *map(show_type, self.types))


class Tuple(TypeOperator):
    """N-ary constructor which builds tuple types"""

    def __init__(self, types):
        super(self.__class__, self).__init__(tuple, types)

    def __str__(self):
        return "({0})".format(", ".join(map(show_type, self.types)))


class ListType(TypeOperator):
    """Unary constructor which builds list types"""

    def __init__(self, list_type):
        super(self.__class__, self).__init__("[]", [list_type])

    def __str__(self):
        return "[{0}]".format(show_type(self.types[0]))


#=============================================================================#
# Type inference machinery


def analyze(node, env, non_generic=None):
    """
    Computes the type of the expression given by node.

    The type of the node is computed in the context of the supplied type
    environment, env. Data types can be introduced into the language simply by
    having a predefined set of identifiers in the initial environment. This way
    there is no need to change the syntax or, more importantly, the
    type-checking program when extending the language.

    Args:
        node: The root of the abstract syntax tree.
        env: The type environment is a mapping of expression identifier names
            to type assignments.
            to type assignments.
        non_generic: A set of non-generic variables, or None

    Returns:
        The computed type of the expression.

    Raises:
        TypeError: The type of the expression could not be inferred, for
                   example if it is not possible to unify two types such as
                   Integer and Bool or if the abstract syntax tree rooted at
                   node could not be parsed
    """

    if non_generic is None:
        non_generic = set()

    if isinstance(node, Var):
        return getType(node.name, env, non_generic)
    elif isinstance(node, App):
        fun_type = analyze(node.fn, env, non_generic)
        arg_type = analyze(node.arg, env, non_generic)
        result_type = TypeVariable()
        unify(Function(arg_type, result_type), fun_type)
        return result_type
    elif isinstance(node, Lam):
        arg_type = TypeVariable()
        new_env = env.copy()
        new_env[node.v] = arg_type
        new_non_generic = non_generic.copy()
        new_non_generic.add(arg_type)
        result_type = analyze(node.body, new_env, new_non_generic)
        return Function(arg_type, result_type)
    elif isinstance(node, Let):
        new_type = TypeVariable()
        new_env = env.copy()
        new_env[node.v] = new_type
        new_non_generic = non_generic.copy()
        new_non_generic.add(new_type)
        defn_type = analyze(node.defn, new_env, new_non_generic)
        unify(new_type, defn_type)
        return analyze(node.body, new_env, non_generic)
    assert 0, "Unhandled syntax node {0}".format(node)


def getType(name, env, non_generic):
    """Get the type of identifier name from the type environment env.

    Args:
        name: The identifier name
        env: The type environment mapping from identifier names to types
        non_generic: A set of non-generic TypeVariables

    Raises:
        ParseError: Raised if name is an undefined symbol in the type
            environment.
    """
    if name in env:
        return fresh(env[name], non_generic)
    raise TypeError("Undefined symbol {0}".format(name))


def fresh(t, non_generic):
    """Makes a copy of a type expression.

    The type t is copied. The the generic variables are duplicated and the
    non_generic variables are shared.

    Args:
        t: A type to be copied.
        non_generic: A set of non-generic TypeVariables
    """
    mappings = {}  # A mapping of TypeVariables to TypeVariables

    def freshrec(tp):
        p = prune(tp)
        if isinstance(p, TypeVariable):
            if isGeneric(p, non_generic):
                if p not in mappings:
                    mappings[p] = TypeVariable()
                return mappings[p]
            else:
                return p
        elif isinstance(p, TypeOperator):
            return TypeOperator(p.name, [freshrec(x) for x in p.types])

    return freshrec(t)


def unify_var(v1, t2):
    """
    Unify the two type variable v1 and the type t2. Makes their types the same
    and unifies typeclass constraints.
    Note: Must be called with v1 and t2 pre-pruned

    Args:
        v1: The type variable to be made equivalent
        t2: The second type to be be equivalent

    Returns:
        None

    Raises:
        TypeError: Raised if the types cannot be unified.
    """
    if v1 != t2:
        if isinstance(t2, TypeVariable):
            # unify typeclass constraints
            union = tuple(set(v1.constraints + t2.constraints))
            v1.constraints = union
            t2.constraints = union

        if occursInType(v1, t2):
            raise TypeError("recursive unification")
        v1.instance = t2
    return


def unify(t1, t2):
    """
    Unify the two types t1 and t2. Makes the types t1 and t2 the same.

    Note that the current method of unifying higher-kinded types does not
    properly handle kind, i.e. it will happily unify `f a` and `g b c`.
    This is due to the way that typeclasses are implemented, and will be fixed
    in future versions.

    Args:
        t1: The first type to be made equivalent
        t2: The second type to be be equivalent

    Returns:
        None

    Raises:
        TypeError: Raised if the types cannot be unified.
    """
    a = prune(t1)
    b = prune(t2)
    if isinstance(a, TypeVariable):
        unify_var(a, b)
    elif isinstance(a, TypeOperator) and isinstance(b, TypeVariable):
        unify_var(b, a)
    elif isinstance(a, TypeOperator) and isinstance(b, TypeOperator):
        # Unify polymorphic higher-kinded type
        if isinstance(a.name, TypeVariable) and len(a.types) > 0:
            a.name = b.name
            a.types = b.types
            unify(a, b)
        elif isinstance(b.name, TypeVariable):
            unify(b, a)

        # Unify concrete higher-kinded type
        elif (a.name != b.name or len(a.types) != len(b.types)):
            raise TypeError("Type mismatch: {0} != {1}".format(str(a), str(b)))
        for p, q in zip(a.types, b.types):
            unify(p, q)
    else:
        raise TypeError("Not unified")
    return


def prune(t):
    """
    Returns the currently defining instance of t.
    As a side effect, collapses the list of type instances. The function prune
    is used whenever a type expression has to be inspected: it will always
    return a type expression which is either an uninstantiated type variable or
    a type operator; i.e. it will skip instantiated variables, and will
    actually prune them from expressions to remove long chains of instantiated
    variables.

    Args:
        t: The type to be pruned

    Returns:
        An uninstantiated TypeVariable or a TypeOperator
    """
    if isinstance(t, TypeVariable):
        if t.instance is not None:
            t.instance = prune(t.instance)
            return t.instance
    return t


def isGeneric(v, non_generic):
    """
    Checks whether a given variable occurs in a list of non-generic variables

    Note that a variables in such a list may be instantiated to a type term,
    in which case the variables contained in the type term are considered
    non-generic.

    Note: Must be called with v pre-pruned

    Args:
        v: The TypeVariable to be tested for genericity
        non_generic: A set of non-generic TypeVariables

    Returns:
        "true" if v is a generic variable, otherwise False
    """
    return not occursIn(v, non_generic)


def occursInType(v, type2):
    """Checks whether a type variable occurs in a type expression.

    Note: Must be called with v pre-pruned

    Args:
        v:  The TypeVariable to be tested for
        type2: The type in which to search

    Returns:
        True if v occurs in type2, otherwise False
    """
    pruned_type2 = prune(type2)
    if pruned_type2 == v:
        return True
    elif isinstance(pruned_type2, TypeOperator):
        return occursIn(v, pruned_type2.types)
    return False


def occursIn(t, types):
    """
    Checks whether a types variable occurs in any other types.

    Args:
        v:  The TypeVariable to be tested for
        types: The sequence of types in which to search

    Returns:
        True if t occurs in any of types, otherwise False
    """
    return any(occursInType(t, t2) for t2 in types)
