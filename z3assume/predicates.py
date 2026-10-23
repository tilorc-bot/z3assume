"""The predicate vocabulary: what a query may ask, and how the derived
predicates are defined from the basis (SymPy's definitions, see
``docs/design.md``, "Predicates")."""

#: Unary predicates in scope.
PREDICATES = (
    "algebraic", "antihermitian", "commutative", "complex", "composite",
    "even", "extended_negative", "extended_nonnegative",
    "extended_nonpositive", "extended_nonzero", "extended_positive",
    "extended_real", "finite", "hermitian", "imaginary", "infinite",
    "integer", "irrational", "negative", "negative_infinite", "noninteger",
    "nonnegative", "nonpositive", "nonzero", "odd", "polar", "positive",
    "positive_infinite", "prime", "rational", "real", "transcendental",
    "zero",
)

#: Predicates with a Boolean of their own per term.
BASIS = (
    "algebraic", "complex", "composite", "even", "extended_negative",
    "extended_positive", "extended_real", "finite", "imaginary", "integer",
    "polar", "prime", "rational", "zero",
)

#: Every other predicate: (connective, ((basis predicate, polarity), ...)).
DEFINITIONS = {
    "real": ("and", (("extended_real", True), ("finite", True))),
    "hermitian": ("and", (("extended_real", True), ("finite", True))),
    "infinite": ("and", (("finite", False),)),
    "positive": ("and", (("extended_positive", True), ("finite", True))),
    "negative": ("and", (("extended_negative", True), ("finite", True))),
    "nonnegative": ("and", (("extended_real", True), ("finite", True), ("extended_negative", False))),
    "nonpositive": ("and", (("extended_real", True), ("finite", True), ("extended_positive", False))),
    "nonzero": ("and", (("extended_real", True), ("finite", True), ("zero", False))),
    "extended_nonnegative": ("and", (("extended_real", True), ("extended_negative", False))),
    "extended_nonpositive": ("and", (("extended_real", True), ("extended_positive", False))),
    "extended_nonzero": ("and", (("extended_real", True), ("zero", False))),
    "positive_infinite": ("and", (("extended_positive", True), ("finite", False))),
    "negative_infinite": ("and", (("extended_negative", True), ("finite", False))),
    "odd": ("and", (("integer", True), ("even", False))),
    "irrational": ("and", (("extended_real", True), ("finite", True), ("rational", False))),
    "noninteger": ("and", (("extended_real", True), ("integer", False))),
    "transcendental": ("and", (("complex", True), ("algebraic", False))),
    "antihermitian": ("or", (("zero", True), ("imaginary", True))),
    "commutative": ("and", ()),
}

assert set(BASIS) | set(DEFINITIONS) == set(PREDICATES)

#: Implications between the basis predicates that hold for every value
#: SymPy decides (the facts of SymPy's assumption system).  They only
#: matter for a term that may be ``nan``: for every other value they follow
#: from the numeric definitions.  Each rule is (premises, conclusions as a
#: disjunction), literals as (predicate, polarity).
RULES = (
    ((("integer", True),), (("rational", True),)),
    ((("rational", True),), (("extended_real", True),)),
    ((("rational", True),), (("algebraic", True),)),
    ((("algebraic", True),), (("complex", True),)),
    ((("complex", True),), (("finite", True),)),
    ((("extended_real", True), ("finite", True)), (("complex", True),)),
    ((("extended_real", True),),
     (("extended_negative", True), ("zero", True), ("extended_positive", True))),
    ((("extended_negative", True),), (("extended_real", True),)),
    ((("extended_positive", True),), (("extended_real", True),)),
    ((("zero", True),), (("extended_real", True),)),
    ((("extended_negative", True),), (("zero", False),)),
    ((("extended_negative", True),), (("extended_positive", False),)),
    ((("zero", True),), (("extended_positive", False),)),
    ((("zero", True),), (("even", True),)),
    ((("zero", True),), (("finite", True),)),
    ((("even", True),), (("integer", True),)),
    ((("prime", True),), (("integer", True),)),
    ((("prime", True),), (("extended_positive", True),)),
    ((("composite", True),), (("integer", True),)),
    ((("composite", True),), (("extended_positive", True),)),
    ((("composite", True),), (("prime", False),)),
    ((("even", True), ("extended_positive", True), ("prime", False)), (("composite", True),)),
    ((("imaginary", True),), (("complex", True),)),
    ((("imaginary", True),), (("extended_real", False),)),
)
