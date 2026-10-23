# Design: SymPy assumptions as z3 queries

z3assume answers `ask(P, A)` for SymPy propositions `P` and assumptions `A`
by translating both into one z3 problem and asking z3 whether it is
satisfiable. It is a rewrite of satassume: satassume is the reference for
*what* is asked (the API, the predicates, the conventions and the test
corpora), not for how. Everything satassume does by hand (its SAT solver,
the rule base, templates and rows, its LRA and EUF theories, the relation
glue, hooks and class theories) is z3's job here: z3's SAT/SMT core, its
linear and nonlinear real arithmetic, integer arithmetic and uninterpreted
functions. What z3assume adds is a translation, plus ground axioms where z3
has no native theory (rationality, algebraicity, primality, transcendental
functions).

The runtime dependencies are SymPy (the input language) and `z3-solver`.
z3assume reads SymPy expression trees (`func`, `args`, the exact value of a
number, the declared assumptions of a symbol) and never calls SymPy's `ask`,
`refine`, simplification or old-style `is_*` queries on compound
expressions.

## The truth standard

As in satassume (satassume#247): SymPy's automatic evaluation is never
ground truth. Every definite answer must follow from the encoding, and every
part of the encoding must be justified by a definition, a theorem or a
stated convention. Where an exact encoding is not known (floats,
transcendental functions, branch cuts), the encoding says less and the
answer is `None`; it never guesses. Concretely, every axiom z3assume gives
z3 must be a true statement about every value its terms can take (including
`0`, `oo`, `-oo`, `zoo` and `nan`); an axiom that holds only "usually" is a
bug.

## Values

A scalar SymPy expression denotes one value of

    D = C  ∪  {+oo, -oo}  ∪  {other infinities}  ∪  {nan}

where `C` is the complex numbers, `+oo`, `-oo` are the infinities of the
extended reals, the other infinities are `zoo` and the directed non-real
ones (`I*oo`), lumped together, and `nan` is "undefined". These are SymPy's
own number objects; the conventions of SymPy's arithmetic on them are taken
as definitions where they are total and unambiguous (`oo - oo = nan`,
`0*oo = nan`, `1/0 = zoo`, `1/oo = 0`, `x**0 = 1`), see the open questions.

For every term `t` (every subexpression the query reaches, keyed by the
SymPy object, so equal subexpressions share their variables) z3assume
creates:

- a kind: exactly one of the Booleans `fin_t`, `pinf_t`, `ninf_t`,
  `cinf_t`, `nan_t`;
- two reals `re_t`, `im_t`: the value when `fin_t`;
- an integer `k_t` and its parity witnesses `h_t`, `r_t`: when `t` is an
  integer, `re_t = k_t = 2*h_t + r_t` with `r_t` in `{0, 1}`. Integer
  reasoning goes through z3's integer sort: mixed real/integer nonlinear
  goals such as "an odd times an odd is odd" come back `unknown` when stated
  with `IsInt` over reals, and are decided at once over the integer
  witnesses;
- Booleans for the predicates z3 has no theory for: `rational_t`,
  `algebraic_t`, `prime_t`.

A free symbol is any value except `nan` (open question 1). A complex number
is a pair of reals: z3's nonlinear real arithmetic (nlsat) is complete for
the real-closed-field problems this gives, so `(a + b*I)*(c + d*I)` and
`|z|**2 = re**2 + im**2` are exact.

## Predicates

Each `Q` predicate is a formula over these variables. For a value that is
not `nan`:

- `finite`: `fin_t`; `infinite`: not `fin_t`; `complex`: `fin_t`.
- `extended_real`: `(fin_t and im_t = 0) or pinf_t or ninf_t`; `real`: the
  finite part of it.
- `zero`: `fin_t and re_t = 0 and im_t = 0`.
- `extended_positive`: `(fin_t and im_t = 0 and re_t > 0) or pinf_t`,
  likewise `extended_negative`; `positive`, `negative`, `nonzero`,
  `nonnegative`, `nonpositive` and the other `extended_` forms by SymPy's
  definitions (satassume's `DEFINITIONS`: `positive` is
  `extended_positive & finite`, `nonnegative` is
  `real & !extended_negative`, ...).
- `imaginary`: `fin_t and re_t = 0 and im_t != 0`.
- `integer`: `fin_t and im_t = 0 and re_t = k_t`; its negation says
  `not IsInt(re_t)` for a finite real. `even`: `integer and r_t = 0`;
  `odd`: `integer and r_t = 1`.
- `rational`, `algebraic`, `prime`: their Booleans, with the definitional
  axioms `integer -> rational -> algebraic -> complex`,
  `rational -> real`, `prime -> integer and k_t >= 2`, `k_t = 2 -> prime`
  for an integer, and `composite` is `integer and k_t >= 2 and not prime`.
  `irrational` is `real and not rational`, `transcendental` is
  `complex and not algebraic`.
- `commutative`: true for every term in scope; a term with a
  non-commutative part is out of scope.

For `nan` SymPy decides no predicate. z3assume leaves every predicate
Boolean of a `nan` term free, subject only to the implications between
predicates (the rule base), so nothing definite follows from a term that
may be `nan`. To make that possible the predicates are z3 Booleans
`P_t` with `not nan_t -> (P_t <-> definition)`.

## Terms

- `Integer`, `Rational`: exact values, with their integer, parity and
  primality facts (primality decided by trial division up to a size bound,
  else left open).
- `Symbol`: fresh variables; declared assumptions (`Symbol('x',
  positive=True)`) become facts, as satassume reads them.
- `Add`: when all arguments are finite, finite with `re` and `im` the sums;
  when the arguments are integers, `k_t` is the sum of their `k`. With an
  infinite argument: `+oo` plus finite or `+oo` arguments is `+oo` (likewise
  `-oo`); `+oo` and `-oo` together give `nan`; one other infinity among
  finite arguments gives an infinite non-real value; any `nan` gives `nan`;
  nothing is said about the remaining cases.
- `Mul`: the complex product when all arguments are finite (and the integer
  product of the `k`s for integer arguments); `0` times an infinity is
  `nan`; nonzero values with an infinity give an infinity, whose sign is the
  product of the signs when all are extended real.
- `Pow` with an integer exponent `n`: `n > 0` is the product; `n < 0` is the
  inverse of the product: `1/z` exact for finite nonzero `z`
  (`conj(z)/|z|**2`), `zoo` for `0`, `0` for an infinity.
- Field closure, as ground axioms per node (z3 has no theory of the
  rationals inside the reals): a sum, product or integer power of rational
  (algebraic) values is rational (algebraic); a sum with all terms but one
  rational and that one real irrational is irrational; likewise for a
  product with nonzero rational factors.

Later steps, each with its own ground axioms, stated with the theorem that
justifies it:

- `Pow` with a rational exponent: the principal square root `s` of `z` is
  exactly `s**2 = z and (re_s > 0 or (re_s = 0 and im_s >= 0))`; `q`-th
  roots exactly for a nonnegative real base.
- `Pow` with a symbolic exponent, `exp`, `log`, `sin`, `cos`, other
  functions: z3 uninterpreted functions of the argument's components, with
  sound axioms only (`exp(r) > 0` and `exp(r) >= 1 + r` for real `r`,
  `log` monotone with `log(1) = 0` on positive reals, `|sin r| <= 1`,
  `sin**2 + cos**2 = 1`, Lindemann-Weierstrass for transcendence, ...).
  Applied undefined functions `f(x)` become uninterpreted functions too, so
  congruence (`x = y -> f(x) = f(y)`) is z3's.
- `pi`, `E`, other named constants: an interval with rational endpoints and
  their proven number-theoretic facts (`pi`, `E` transcendental); open
  problems (is `EulerGamma` rational?) stay open.
- `Abs`, `re`, `im`, `conjugate`, `sign`: exact in the pair encoding.

## Relations

`Q.eq(a, b)` and `Eq(a, b)`: equal values (same kind, equal components;
two other infinities or a `nan` leave it free). `Q.lt(a, b)` and `a < b`:
both extended real and `a < b` in the extended order, as satassume's
relation atoms mean; `<=`, `>`, `>=`, `!=` follow satassume's spec
(`a <= b` is `extended_real(a) & extended_real(b) & ~lt(b, a)`).
These are linear or nonlinear real constraints and need no glue: the link
between the sign predicates and the relations is the shared variables.

## Answering

`And`, `Or`, `Not`, `Implies`, `Equivalent`, `Xor` and `ITE` become z3
connectives. Then, with one z3 solver per query and the shared axioms of
every term the query reaches:

1. Constant propositions (no free symbols) are first answered without the
   assumptions, as satassume does: a definite answer is returned and never
   raises; a `None` falls through to step 2.
2. Check `A & ~P`. If unsat, check `A & P`: sat gives `True`; unsat means
   `A` is inconsistent and `ask` raises `ValueError` like satassume.
3. Otherwise (sat), check `A & P`: unsat gives `False`, anything else
   `None`.
4. `unknown` from z3 (resource limit, incompleteness) at a step gives
   `None`; when `A` cannot be shown consistent the answer is `None`, never
   a definite value under a possibly inconsistent set.

Unsupported input (matrix predicates, unregistered custom predicates,
terms outside the encoding) is opaque: a predicate it applies becomes a
free Boolean and a term a free value, so it can only weaken an answer. A
proposition about an out-of-scope thing is `None` (satassume's
`out_of_scope` categories are kept).

Answers are deterministic: each check runs under z3's `rlimit` (a count of
z3's internal steps, not wall time), the random seeds are fixed, and the
assertions are built in a fixed order (the SymPy argument order, never a
`set` iteration or a hash order). A memo of answers keyed by `(P, A)` is
kept, as satassume does; it cannot change an answer.

satassume answers under the part of `A` connected to `P` unless the whole
of `A` is inconsistent. z3assume gives z3 the whole of `A`: by monotonicity
the answer is the same or more definite, and it raises exactly when `A` is
inconsistent (as far as z3 can show). A relevance split may come back as an
optimization, never as a change of answers.

## Out of scope at first

Floats (open question 2); `polar`; matrices and matrix predicates;
non-commutative symbols; custom predicates and satassume's extension API
(`register`); `refine`; and, until their step, rational and symbolic
powers, transcendental and special functions, named constants, relations.
The first slice is the eleven predicates `real`, `rational`, `integer`,
`positive`, `negative`, `zero`, `nonzero`, `nonnegative`, `nonpositive`,
`even`, `odd` on polynomial and rational expressions.

## Open questions for Tilo

1. Can a symbol be `nan`? The design says no: `nan` comes only from the
   constant itself and from undefined operations (`oo - oo`). If symbols
   could be `nan`, `ask(Q.finite(x + 1), Q.finite(x))` would be `None`
   (satassume and SymPy say `True`).
2. Floats: satassume answers `Q.positive(0.5)` `True` and
   `Q.integer(2.0)`, `Q.rational(0.5)` `None`. An exact encoding of a Float
   as its binary value would make the last two `True`. The proposal: a Float
   is a real in a small interval around its value with its exact sign, and
   no rationality facts. Is that the convention you want?
3. Are SymPy's arithmetic conventions on its special numbers (`oo - oo =
   nan`, `0*oo = nan`, `1/0 = zoo`, `x**0 = 1` even for `x = nan`) the
   definitions z3assume should follow? Each could instead leave the result
   free (fewer definite answers, no convention).
4. Is the whole-set answer (more definite than satassume's relevance split,
   same raising) acceptable, or should z3assume reproduce satassume's
   answers exactly where they differ?
5. The comparison counts z3assume as wrong only where the two disagree on a
   definite answer. Should the comparison also run against SymPy's own
   `ask` (as satassume's `compare.py` does), with the same #247 standard?
