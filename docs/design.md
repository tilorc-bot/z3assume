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
own number objects. The arithmetic on them follows satassume's written
conventions: `1/0 = zoo` and `0**0 = 1` (satassume docs/design.md,
"Extended reals and `nan` in templates"), `oo - oo = 0*oo = nan`, and the
table of values at infinities, `nan` and poles in satassume's
docs/special-values.md (open PR satassume#293; rows V1-V3 are used here).
Where satassume states nothing, z3assume uses SymPy's total and unambiguous
conventions (`1/oo = 0`, `x**0 = 1`) as its own default, which Tilo may
change (open question 3).

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

A free symbol is any value except `nan`, as in satassume (its soundness
oracle never evaluates at a `nan` argument, and it answers
`ask(Q.finite(x + 1), Q.finite(x))` True). A complex number
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

For `nan`, satassume's convention (special-values row V1) is that `nan`
is no number: every predicate is False of it except `finite` and
`infinite`, which stay open (`polar` is not stated and stays open too).
So the predicates are z3 Booleans `P_t` with
`not nan_t -> (P_t <-> definition)` and `nan_t -> not P_t` for every basis
predicate but `finite` and `polar`. `commutative` is True of every term in
scope, `nan` included (satassume leaves it open of `nan`; a known
difference, harmless while non-commutative input is out of scope).

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
- Named constants (`NumberSymbol`): `pi`, `E`, `GoldenRatio`,
  `TribonacciConstant`, `EulerGamma`, `Catalan` are finite reals strictly
  inside the interval `(d, d + 10**-20)`, `d` the 20-decimal truncation of
  the published expansion (OEIS, cited per constant in `encode.py`), plus
  their proven facts: `pi`, `E` transcendental (Lindemann, Hermite);
  `GoldenRatio`, `TribonacciConstant` exact as the root of `x**2 - x - 1`,
  `x**3 - x**2 - x - 1` in the interval, algebraic and irrational (rational
  root test). Open problems stay open: nothing about the rationality or
  algebraicity of `EulerGamma` and `Catalan`.
- `Abs`, `re`, `im`, `conjugate`, `sign` of `z = a + b*I`: exact on the
  pair. `Abs(z) = r` with `r >= 0`, `r**2 = a**2 + b**2` (and `r = |a|`
  for real `z`), `re(z) = a`, `im(z) = b`, `conjugate(z) = a - b*I`,
  `sign(z) = 0` at `0`, else `z/r`. A `nan` argument gives `nan`
  (satassume special-values N1), every infinity has `Abs` `oo` (row F3);
  at `+-oo` the limits along `t*d` (row V2) give `re = +-oo`, `im = 0`,
  `conjugate = +-oo`, `sign = +-1`; at the other infinities `re`, `im`,
  `conjugate` and `sign` are free (`zoo` has no direction and no written
  convention). Number theory: for real `z` the value is `+-z`, so
  integer (with `|k|` and the parity of `k`), rational, algebraic agree
  with `z`'s (all predicates but `polar` for `re`, `conjugate` and a
  nonnegative `z` under `Abs`), and `sign` is the integer `-1`, `0` or `1`; for any
  finite algebraic `z` all five are algebraic (the algebraic numbers are a
  field closed under complex conjugation and square roots), and
  `conjugate(z)` is algebraic only for algebraic `z` (an involution).
  `arg` stays opaque (its values need `atan2`).
- Field closure, as ground axioms per node (z3 has no theory of the
  rationals inside the reals): a sum, product or integer power of rational
  (algebraic) values is rational (algebraic); a sum with all terms but one
  rational and that one real irrational is irrational, and one with all
  terms but one algebraic and that one transcendental is transcendental;
  likewise for a product with nonzero rational (algebraic) factors. The
  base of an algebraic integer power `b**n` (`b` finite, nonzero for
  `n < 0`) is algebraic: the algebraic numbers are algebraically closed.

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

## Relations

`Q.eq(a, b)` and `Eq(a, b)`: equal values (same kind, equal components;
two other infinities or a `nan` leave it free). `Q.lt(a, b)` and `a < b`:
both extended real and `a < b` in the extended order, as satassume's
relation atoms mean; `<=`, `>`, `>=`, `!=` follow satassume's spec
(`a <= b` is `extended_real(a) & extended_real(b) & ~lt(b, a)`).
These are linear or nonlinear real constraints and need no glue: the link
between the sign predicates and the relations is the shared variables.
Equal values satisfy the same predicates (congruence), so where an
equality holds with the same value on both sides (equal finite values, or
both `oo`, or both `-oo`), every basis atom of one side equals the same
atom of the other, except `polar`, which the value does not decide.

## Answering

`And`, `Or`, `Not`, `Implies`, `Equivalent`, `Xor` and `ITE` become z3
connectives. Then, with the shared axioms of every term the query reaches,
each check in a fresh z3 solver (after a `push`, z3 skips the
preprocessing that decides "an odd times an odd is odd"):

1. Constant propositions (no free symbols) are first answered without the
   assumptions, as satassume does: a definite answer is returned and never
   raises; a `None` falls through to step 2.
2. Check `A & ~P`. If unsat, check `A & P`: sat gives `True`; unsat means
   `A` is inconsistent and `ask` raises `ValueError` like satassume.
3. Otherwise (sat), check `A & P`: unsat gives `False`, anything else
   `None`.
4. `unknown` from z3 (resource limit, incompleteness) at both steps gives
   `None`; an `unknown` at one step and unsat at the other gives the
   definite answer of the unsat step.

The case that needs an argument is `A & ~P` unsat and `A & P` unknown.
z3assume answers `True` there. The argument: `A & ~P` unsat is a proof
that `A` entails `P`, and that is what `True` means; it holds whether or
not `A` is consistent. What can go wrong is only the raising: if `A` is in
fact inconsistent but z3 cannot show it, satassume would raise
`ValueError` where z3assume says `True`. The alternative (`None` unless `A`
is shown consistent) throws away a proved entailment to protect an error
signal, and makes the answer depend on how hard the consistency check is
rather than on the entailment. This is open question 6; Tilo may prefer
`None`.

Unsupported input (matrix predicates, unregistered custom predicates,
terms outside the encoding) is opaque: a predicate it applies becomes a
free Boolean and a term a free value, so it can only weaken an answer. A
proposition about an out-of-scope thing is `None` (satassume's
`out_of_scope` categories are kept).

Answers are meant to be deterministic: each check runs under z3's
`rlimit` (a count of z3's internal steps, not wall time), z3's random seeds
are its defaults and never changed, and the assertions are built in a fixed
order (the SymPy
argument order, never a `set` iteration or a hash order). A memo of
answers keyed by `(P, A)` is kept, as satassume does; it cannot change an
answer.

One exception: z3 does not check `rlimit` everywhere (a nonlinear sat
check was seen to overrun its rlimit by 68% and run for seconds), so each
check also has a wall-clock backstop of 10 s. A check stopped by the
backstop is `unknown`, so the answer is `None`, and whether a check near
the backstop finishes depends on the machine and its load: such answers
are not deterministic. The backstop is set far above the rlimit's usual
cost so that it fires only in these pathological cases; every firing is
counted (`last["timeout"]` in the module `z3assume.ask`), a `None` it
caused is not memoized, and the stream comparison (`tools/`) reports the
count, so a query that hits it is visible and can be fixed in the encoding
(by a smaller problem, not a larger limit).

satassume answers under the part of `A` connected to `P` unless the whole
of `A` is inconsistent. z3assume gives z3 the whole of `A`: by monotonicity
the answer is the same or more definite, and it raises exactly when `A` is
inconsistent (as far as z3 can show). A relevance split may come back as an
optimization, never as a change of answers.

## Out of scope at first

Floats (open question 2); `polar`; matrices and matrix predicates;
non-commutative symbols; custom predicates and satassume's extension API
(`register`); `refine`; and, until their step, rational and symbolic
powers, transcendental and special functions, relations.
The first slice is the eleven predicates `real`, `rational`, `integer`,
`positive`, `negative`, `zero`, `nonzero`, `nonnegative`, `nonpositive`,
`even`, `odd` on polynomial and rational expressions.

## Open questions for Tilo

Each question has a default, applied until Tilo answers (relayed by
architect-14, 23 Oct): where satassume's docs fix a convention, z3assume
adopts it and cites it; otherwise the default below stands, marked "Tilo
may change".

1. Can a symbol be `nan`? Default, adopted from satassume: no (see
   "Values"). If symbols could be `nan`, `ask(Q.finite(x + 1),
   Q.finite(x))` would be `None`.
2. Floats. satassume deliberately does not read Floats (its
   docs/theories.md and overview.md "Known gaps": SymPy compares
   `Float(0.1) > 1/10` exactly but decides `Eq` at the Float's precision,
   so no fixed reading agrees with SymPy everywhere), yet answers
   `Q.positive(0.5)` True. Default, Tilo may change: a Float is opaque for
   now; the next step makes it a real with its exact sign in an interval
   with rational endpoints around its value, with no rationality, integer
   or equality facts.
3. Special values. Default: satassume's conventions (`1/0 = zoo`,
   `0**0 = 1`, `nan` is no number, the special-values table of
   satassume#293); where satassume is silent, SymPy's total conventions
   (`1/oo = 0`, `x**0 = 1` even at `x = nan`), Tilo may change. Each could
   instead leave the result free (fewer definite answers, no convention).
4. Whole-set answers. Default (architect-14): answer under the whole of
   `A` (more definite than satassume's relevance split, same raising);
   comparisons report the difference as "more definite", not as a
   disagreement.
5. A third comparison column with SymPy's own `ask`, under the same #247
   standard. Default: only where it is cheap to compute; never as ground
   truth.
6. `A & ~P` unsat with `A & P` unknown: `True` (default, see "Answering",
   Tilo may change) or `None`.
7. `re`, `im`, `conjugate`, `sign` at the infinities. Default, Tilo may
   change: at `+oo` and `-oo` their limits along the real axis (`re = +-oo`,
   `im = 0`, `conjugate = +-oo`, `sign = +-1`; satassume's special-values
   table has no row for them); at `zoo` and the directed non-real
   infinities they are free. About 50 queries of the refine stream need a
   value at `zoo` (e.g. `Q.zero(sign(1/x))` under `Q.real(x)`).
