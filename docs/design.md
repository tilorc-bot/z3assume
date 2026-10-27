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
docs/special-values.md (open PR satassume#293; the rows used are cited
where they are used: V1-V3, N1, P1-P6, F1-F3, M3). Where satassume states
nothing, z3assume uses the table in SymPy's `Pow` docstring (`oo**-1 =
0`); where the two disagree (`nan**0`: N1 says `nan`, SymPy's table `1`)
the value is left free (decision 3). A sum, product or function value
is one point of `D`, never a limit: limits only argue which point a
function takes at a point (decisions 7 to 10), so `oo + I` is a point
(`+oo` for SymPy, an infinity of the other kind for satassume), and
`(x + I) - I = x` is no identity of `D`.

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
- a scaled integer witness `(d_t, n_t, cond_t)` for a term that is a
  rational linear combination of integers (issue #12): `d_t` a positive
  integer, `n_t` an integer expression over the `k` of other terms, and
  `cond_t` a condition under which the value is the finite real `n_t/d_t`.
  A Rational `p/q` is `(q, p, true)`; a sum combines the witnesses of its
  arguments over the lcm of their `d`; a product with at most one
  non-constant factor multiplies them; every other term is
  `(1, k_t, integer_t)`. For `d_t > 1` under `cond_t`, `n_t = d_t*q + r`
  with `0 <= r < d_t` (fresh integers), `integer_t` iff `r = 0`, and then
  `k_t = q`: `t` is an integer iff `d_t` divides `n_t`. z3 does not
  refute `not IsInt(x)` for an `x` that is an integer combination with
  rational coefficients (`k/2 - 1/2` with `k` odd: the strict bounds of
  `IsInt`'s floor stay real, and branch and bound runs into the rlimit),
  so under `cond_t` the non-integer fact is this one, over the integers;
  `not IsInt(re_t)` stays for when `cond_t` fails;
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
  `not IsInt(re_t)` for a finite real (`d_t` not dividing `n_t` under
  `cond_t` of a scaled witness, see "Values"). `even`: `integer and r_t = 0`;
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
  when the arguments are integers, `k_t` is the sum of their `k`, and
  when the sum and every argument but one are integers, so is that one (the
  integers are closed under subtraction; #23), except in a sum without
  free symbols (decision 13). With an
  infinite argument: `+oo` plus real or `+oo` arguments is `+oo` (likewise
  `-oo`); with a non-real finite argument it is `+oo` or an infinity of the
  other kind, as the conventions disagree (decision 3): SymPy evaluates
  `oo + I = oo`, satassume calls it "an infinity off the real axis"
  (templates/add.py, its test expects None for `Q.negative_infinite(ninf +
  I)`). The sum is one value of `D` (see "Values"), either of them, not
  a limit: `cosh(x + I)` under `Q.positive_infinite(x)` is `cosh(oo)` or
  `cosh` of a value of the other kind, so it stays open, while every value
  allowed has `im` in `{0, +-oo, nan}`; `+oo` and `-oo` together give
  `nan`; one other infinity among
  finite arguments gives an infinite non-real value; any `nan` gives `nan`;
  in the remaining cases (two infinities of the other kind, or one with
  `+-oo`) the sum is an infinity or `nan`, never a number: the sum is
  finite only when every argument is (#26). Argument: an infinity is a
  limit point of finite values of unbounded modulus; `w + v` with `|w|`
  unbounded and `v` bounded stays unbounded, and where two unbounded
  terms can cancel (`oo - oo`, `zoo + zoo`, `oo*I - oo*I`) the limit
  depends on the path, which is `nan` (satassume docs/design.md: "`oo +
  zoo`, `oo*I - oo*I` and `oo + nan` are `nan`, #187"). So `Q.zero(i -
  j)` is False under `Q.infinite(i)` and under `Q.ne(i, j)`.
- `Mul`: the complex product when all arguments are finite (and the integer
  product of the `k`s for integer arguments); `c*x` with a Rational
  `c = 1/q` or `-1/q` (`q > 1`) and a finite `x` makes `x = q*(c*x)` (or
  `-q*(c*x)`) an integer when `c*x` is one; `0` times an infinity is
  `nan`; nonzero values with an infinity give an infinity, whose sign is the
  product of the signs when all are extended real.
- `Pow` with an integer exponent `n`: `n > 0` is the product; `n < 0` is the
  inverse of the product: `1/z` exact for finite nonzero `z`
  (`conj(z)/|z|**2`), `zoo` for `0`, `0` for an infinity. An integer
  square or higher power of an integer is never prime (`0`, `1`, or two
  factors of modulus `>= 2`), and `1/b` is rational only for rational `b`.
- `Pow` with any other exponent `x` (rational literals as in `sqrt(z)`,
  symbols, Floats, `I`): SymPy's principal value `exp(x*log(b))` for
  finite `b != 0` and finite `x`, and satassume's special-values rows
  elsewhere: N1 (`nan` exponent, or `nan` base with `x != 0`, gives `nan`;
  `nan**x` at `x = 0` is free, N1 and SymPy's `nan**0 = 1` disagree), P2
  (`b**0 = 1`), P1 (`0**x = zoo` for real `x < 0`), P3, P4, P5 (`1**oo =
  nan`), P6, plus `b**1 = b` and `0**x = 0` for real `x > 0` (the limit,
  as SymPy evaluates it). `0**x` for non-real `x` is free (SymPy says
  `nan`, the limit would be `0` for `re x > 0`), and so are an infinite
  base to a non-real exponent and any base to `zoo` or `oo*I` (no row).
  For finite `b != 0` and finite `x` the value is the term
  `exp(x*log(b))`, built from unevaluated SymPy objects and encoded as
  `exp`, `log` and `Mul` are (no new axioms: finite, nonzero, `|b**x| =
  e**re(x*log b)`, real and positive for `b > 0` and real `x`, ...). A
  literal base `r*exp(I*pi*c0)` (a nonzero rational, `I`, `r*I`) uses
  `log(b) = log(r) + I*pi*c0`, so `b**x = exp(x*log r)*exp(I*pi*c0*x)`, the
  second factor split over the summands of `x` that have the factor `I`
  (`I**(3 + I) = exp(3*I*pi/2)*exp(-pi/2)`). A real negative base and a
  real `x` give `|b|**x*exp(I*pi*x)`, so the signs of the parts are those
  of `exp(I*pi*x)`. `exp(I*pi*c)` gained two facts: for a literal
  rational `c` the signs of `cos(pi*c)`, `sin(pi*c)` after reducing `c`
  mod 2 (period `2*pi*I`), and for real `c`, `cos(pi*c) = 0` iff
  `c - 1/2` is an integer (for `c = +-y/2`: iff `y` is odd). For an
  integer `x` (a symbol): a real `b != 0` gives a real power with the sign
  `(-1)**x` of a negative base, an imaginary `b = I*s` a real power for
  even and an imaginary one for odd `x`; integer bases give integers for
  `x >= 0` with the parity of the base (even only for `x >= 1`), no prime
  for `|b| >= 2`, `x >= 2`, and a non-integer `0 < |b**x| <= 1/2` for
  `x <= -1` (encoded as `-1 < t < 1`, `t != 0`); a rational base a rational power. Algebraic numbers: for a
  rational `x = p/q`, `(b**x)**q = b**p`, so `b**x` is algebraic iff `b`
  is (`b` finite, `b != 0` one way, `x != 0` the other);
  Gelfond-Schneider: `b**x` is transcendental for algebraic `b` not in
  `{0, 1}` and algebraic `x` not rational (every value, so the principal
  one: `2**sqrt(2)`, `2**I`, `I**I`). A literal positive rational `n/d` to
  a literal `p/q` is rational iff `n` and `d` are `q`-th powers, and then
  exact. Roots: `sqrt(z)` is exactly `s**2 = z` with `re s > 0` or
  `re s = 0 <= im s`; for real `b >= 0` the cube root is the real
  `s >= 0` with `s**3 = b`, and `b**(-1/2)`, `b**(-1/3)` (`b > 0`) the
  `s > 0` with `s**q*b = 1`. Not encoded: a non-integer real power of an
  imaginary base beyond the principal value, and every exact value that
  needs `cos`/`sin` of a rational multiple of `pi` (`(-1)**(1/3) = 1/2 +
  sqrt(3)*I/2`).
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
  `conjugate = +-oo`, `sign = +-1`; at the other kind (`zoo` and the
  directed non-real infinities, one kind in the encoding) only what holds
  for each of them (decision 7): `re` is `+-oo`, `0` or `nan`, `im` is
  `+-oo` or `nan`, `conjugate` is again of that kind, `sign` is `nan` or a
  non-real unit. Number theory: for real `z` the value is `+-z`, so
  integer (with `|k|` and the parity of `k`), rational, algebraic agree
  with `z`'s (all predicates but `polar` for `re`, `conjugate` and a
  nonnegative `z` under `Abs`), and `sign` is the integer `-1`, `0` or `1`; for any
  finite algebraic `z` all five are algebraic (the algebraic numbers are a
  field closed under complex conjugation and square roots), and
  `conjugate(z)` is algebraic only for algebraic `z` (an involution).
  `arg` stays opaque (its values need `atan2`).
- `Float` (decision 2): a Float with mpf `(s, man, exp, bc)` and
  precision `p` bits (`Float._prec`) has the binary value
  `v = (-1)**s * man * 2**exp`. It is a finite real `x` with the sign of
  `v` (`x = 0` exactly when the mpf is zero) and `v - u < x < v + u`,
  where `u = 2**(exp + bc - p)` is one unit in the last place of a
  `p`-bit number with `v`'s leading bit. Nothing else is stated: whether
  `x` is an integer follows only where the interval decides it
  (`Q.integer(0.5)` False, no integer in `(1/2 - 2**-53, 1/2 + 2**-53)`;
  `Q.even(1.0)` False, the interval's only integer is `1`; `Q.integer(1.0)`
  None), and rationality and algebraicity never do (every open interval
  holds rationals, algebraic irrationals and transcendentals). An
  `Eq`/`<` with a value inside the interval stays open; one outside it is
  decided.

  The reading, and why the interval is a sound enclosure of it: a Float
  stands for some real that rounds to it at its own precision. mpmath
  (SymPy's Float arithmetic) rounds `y` to `v` at `p` bits only if
  `|y - v| < u`, in every rounding mode: to nearest `|y - v| <= u/2`
  (`u/4` below a power of two, where the spacing halves), and a directed
  mode (floor, ceiling, toward or away from zero) leaves less than the
  spacing next to `v` on `y`'s side, at most `u`. Rounding keeps the sign,
  and only `0` rounds to the zero mpf (mpmath's exponents are unbounded:
  no underflow, no signed zero). Both of SymPy's own readings of a Float
  lie inside the interval: `v` itself (`Float(0.1) > 1/10` compares `v`
  exactly) and every number `Eq` calls equal to the Float (`Eq(0.1,
  1/10)` is True because `1/10` rounds to `v` at 53 bits). So a definite
  answer holds under either reading, and a value the Float may round
  stays open: `Q.eq(0.1, 1/10)`, `Q.lt(0.1, 1/10)` and `Q.gt(0.1, 1/10)`
  are None, `Q.ne(0.1, 1/5)` is True. The interval is two ulps wide where
  half an ulp would cover round-to-nearest, so the reading does not
  depend on the rounding mode that made the Float.

  What the reading does not cover, deliberately: a Float made by `evalf`
  or by SymPy's Float arithmetic is taken as the Float it is, not as the
  exact value it approximates (evalf does not promise one-ulp accuracy,
  and the query never sees what the Float came from). So
  `sum([Float(0.1)]*10, S.Zero)`, printed `1.00000000000000`, is the
  binary value `1 - 2**-53`, and `Q.integer` of it is False; and a Python
  float such as the subnormal `5e-324` gets the interval of its 53-bit
  Float, not the IEEE one. One Float object
  (one mpf at one precision: SymPy's `==`; the hash ignores the
  precision) is one value, so
  `f - f` is `0`; Floats of different precisions are different objects
  (`Float(0.5, 15) != Float(0.5, 30)` in SymPy) and so independent values,
  each in its own interval. A Float whose mantissa, exponent or ulp
  exponent needs more than 4096 bits keeps only its sign (the endpoints
  would be rationals of thousands of digits). `Float('inf')`, `Float('-inf')` and
  `Float('nan')` are SymPy's `oo`, `-oo` and `nan` objects, encoded as
  such. A Float exponent (`x**1.4`) is a real in its interval, as any
  Float term (`Pow` above).
- `exp` (also `E**z` unevaluated) and `log` (SymPy's principal branch
  `log|z| + I*arg(z)`, `-pi < arg <= pi`; `log(x, b)` is `log(x)/log(b)`
  in SymPy). Special values from satassume's table: `nan` gives `nan`
  (N1); `exp(oo) = oo`, `exp(-oo) = 0`, and for the other infinities one
  of `cinf`, `0`, `nan` (F1: `zoo -> nan`, `oo*d` gives `zoo`, `0` or
  `nan` by the sign of `re(d)`; the kind does not tell which); `log(0) =
  zoo`, `log(+-oo) = oo`, `log` of the other kind `oo` or `cinf` (F2 and
  its "Choices"). For finite arguments, every `exp` and `log` term gives
  an *exp pair* of reals `(u, v)` with `v = e**u`: `(re z, |exp z|)` for
  `exp(z)`, `(re log z, |z|)` for `log(z)`, `z != 0`, and `(1, E)` for the
  constant `E`. Each pair has `v > 0`, `v >= 1 + u` (the tangent at 0, or
  `log v <= v - 1`), `u < 0` iff `v < 1`, `u = 0` iff `v = 1`, and every
  two pairs of the query are ordered alike (`e**u` is strictly
  increasing): ground instances, quadratic in the number of terms. So
  `exp(0) = 1`, `log(1) = 0`, `exp(z) != 0`, the sign of `log(x)` is that
  of `x - 1`, and `log(exp(x)) = x` for real `x`. `exp(z)` with
  `z = a + b*I`: real `e**a` for `b = 0`; `|exp z|**2 = re**2 + im**2`;
  the signs of `cos b`, `sin b` on `[-pi, pi]` (linear in `b` and the
  `pi` term); for `z = I*pi*c` with real `c`, `(-1)**c` for an integer `c`
  and not real otherwise. `log(z)`: `arg` by the quadrant of `z` (`0`,
  `pi`, `+-pi/2` on the axes, the open half-planes and quadrants as
  intervals in `(-pi, pi)`). Hermite-Lindemann: `exp(w)` is
  transcendental for algebraic `w != 0`, and every logarithm of an
  algebraic `z` other than `0`, `1` is transcendental.
  `exp(log(w)) = w` (unevaluated) and `log(exp(x)) = x` for real `x`
  carry the predicates. At a rational point the value of `exp`
  (`log|r|`) lies in a rational enclosure of relative width about
  `10**-19`, computed in exact rational arithmetic with the error bound
  argued in `bounds.py` (Taylor series with a geometric tail for `exp`,
  the `atanh` series for `log`, outward rounding). Not encoded: "`exp(z)`
  real iff `im(z)/pi` is an integer" for an imaginary part not of the
  form `pi*c` (the integer witness made z3 time out), `exp_polar`,
  `log` with two arguments (unevaluated), and Gelfond-Schneider for
  `exp`/`log` terms (it is encoded for `Pow`, above).
- `sin`, `cos`, `tan`, `cot`, `sec`, `csc` and `sinh`, `cosh`, `tanh`,
  `coth`, `sech`, `csch`. Special values: `nan` gives `nan` (N1); the
  hyperbolic functions at `+-oo` are their limits, `cosh(+-oo) = oo`,
  `sinh(+-oo) = +-oo`, `tanh(+-oo) = coth(+-oo) = +-1`, `sech(+-oo) =
  csch(+-oo) = 0` (decision 10); any other infinite argument leaves the
  value free (satassume's table has no row for them and names `sin(oo)`
  as a point no row covers). For finite
  `z = a + b*I`, fresh reals `C, S = cos u, sin u` and `H, K = cosh v,
  sinh v`, shared by all functions of `z`, with `(u, v) = (a, b)` for the
  circular family and `(b, a)` for the hyperbolic one, give the values
  exactly: `cos z = C*H - I*S*K`, `sin z = S*H + I*C*K`, `cosh z = H*C +
  I*K*S`, `sinh z = K*C + I*H*S` (addition theorems). Their facts:
  `C**2 + S**2 = 1`; `H**2 - K**2 = 1`, `H >= 1`, `K` with the sign of `v`
  and `|K| >= |v|`; `H + K = e**v` as an exp pair (with `exp` and `log`);
  the signs of `C` and `S` for `u` in `[-pi, pi]` (linear in `u` and the
  `pi` term, as for `exp`); for `u = pi*c` (`z = pi*c`, or `I*pi*c` for the
  hyperbolic family) with real `c`: `S = 0` iff `c` is an integer, and then
  `C = (-1)**c`; at a rational point the rational enclosures of
  `bounds.py` (Taylor polynomial with Lagrange's remainder for `sin` and
  `cos`, no argument reduction; `cosh`, `sinh` from those of `e**r`).
  The other four are quotients (`tan = sin/cos`, `sec = 1/cos`, ...),
  written with the real denominator `|d|**2` (`|cos z|**2 = C**2 + K**2`,
  `|sin z|**2 = S**2 + K**2`; `tan z = (S*C + I*H*K)/(C**2 + K**2)`):
  `t*|d|**2 = n*conj(d)` where `d` is nonzero, and `zoo` where it is
  `0` (`1/0 = zoo`, and `zoo` times the nonzero numerator is `zoo`, row
  M3: `tan(pi/2) = cot(0) = zoo`; the special-values table has no row for
  the poles of these functions, so this is the `1/0 = zoo` convention of
  decision 3 applied to `sin/cos`). Hermite-Lindemann: for algebraic
  `z != 0` every one of the twelve is transcendental or `zoo` (`e**(I*z)`
  is transcendental and a root of a quadratic over the field generated by
  the value; the argument is in `encode.py`). Not encoded: periodicity
  and the zeros outside `[-pi, pi]` for an argument not of the form
  `pi*c` (an integer witness for `u/pi`, which made z3 time out for
  `exp`), the identity `cos**2 + sin**2 = 1` for a non-real argument
  (it follows from the components, but z3's nonlinear arithmetic does
  not find it), and algebraic values at rational multiples of `pi`
  (`sin(pi/7)`).
- `asin`, `acos`, `atan`, `acot`, `asinh`, `acosh`, `atanh`, `acoth`
  (SymPy's principal branches; `acot` has SymPy's range `(-pi/2, pi/2]`).
  Each is a logarithm of an algebraic expression in `x`, so every branch
  is a right inverse where it is finite: a finite value `w` has
  `f(w) = x`. From that: `w = 0` only at `x = f(0)` (`0`, or `1` for `acos`
  and `acosh`, never for `acot` and `acoth` as `cot(0) = coth(0) = zoo`),
  and `w = 0` there; for algebraic `x`, a finite `w != 0` is
  transcendental (Hermite-Lindemann, through the forward function); for
  real `x` in the range of `f` on R, `w` is the real inverse (its interval
  in terms of `pi`, the sign of `x` for the odd ones, `acos` decreasing
  through `pi/2` at 0), and for real `x` outside that range (`|x| > 1`
  for `asin`, `acos`, `atanh`; `x < 1` for `acosh`; `|x| < 1` for
  `acoth`) `w` is not real. `asin`, `acos`, `asinh`, `acosh` of a finite
  value are finite. `nan` gives `nan`; infinities leave the value free
  (`atan(oo) = pi/2` is a limit no row states). `asec`, `acsc`, `asech`,
  `acsch` stay opaque.
- `floor`, `ceiling`, `frac` (issue #18). SymPy's definition for a
  complex argument rounds each part (the `floor` and `ceiling`
  docstrings: "taking the floor of the real and imaginary parts
  separately"; satassume's `templates/integer_funcs.py` and
  `functions.py` say the same): for finite `z = a + b*I`, `floor(z) =
  floor(a) + floor(b)*I` with z3's `ToInt` (exactly the floor of a real,
  the integer `m` with `m <= a < m + 1`), `ceiling(a) = -floor(-a)`, and
  `frac(z) = z - floor(z)` (SymPy's stated definition for real `x`, and
  its rewrite `frac(x) -> x - floor(x)` for any `x`, with the documented
  complex floor; the docstring's complex example agrees, but an example is
  an evaluation, not the ground). The value of `floor` and
  `ceiling` is a Gaussian integer: algebraic, real exactly when the
  rounded imaginary part is 0, and then the integer `k`; `frac(z)` is
  algebraic iff `z` is, and for real `z` rational iff `z` is (`z -
  frac(z)` is a Gaussian integer). `nan` gives `nan` (N1); an infinity
  keeps its kind under `floor` and `ceiling` (decision 8); `frac` of an
  infinity is free.
- `gamma` and `factorial` (issue #21). `factorial(z) = gamma(z + 1)`
  (decision 9), with the sum `z + 1` an unevaluated term and, for finite
  `z`, `z + 1` an integer iff `z` is. For `gamma(w)`, theorems about
  Euler's function, each argued in `encode.py`: the poles are exactly the
  nonpositive integers and the value there is `zoo` (decision 9); at every
  other finite `w` the value is finite and nonzero (`1/gamma` is entire);
  real and positive for real `w > 0` (Euler's integral); real with the
  sign `(-1)**floor(w)` for a real non-integer `w < 0` (the recurrence down
  to `(0, 1)`), stated with a fresh integer `h`: `w` in `(2*h, 2*h + 1)`
  and positive, or in `(2*h - 1, 2*h)` and negative; `(n - 1)!` at a
  positive integer `n`: `1, 1, 2` for `n = 1, 2, 3`, even and `>= 6` from
  `n = 4` on. `gamma(oo) = oo` (the limit); `gamma(-oo)` and `gamma` of the
  other kind are free; `nan` gives `nan` (N1). Not encoded:
  `gamma(conjugate(w)) = conjugate(gamma(w))`, values at other points
  (`gamma(1/2) = sqrt(pi)`), rationality or transcendence off the
  integers, and `loggamma`, `RisingFactorial`, `FallingFactorial`,
  `binomial`, `factorial2`, `subfactorial`, the polygamma family (opaque;
  no query of the corpora has them).
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

- Other functions: z3 uninterpreted
  functions of the argument's components, or fresh reals as for the
  circular functions above, with sound axioms only.
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
An equality left open is the same open Boolean for both orders of its
sides, since equality is symmetric whatever it means there.

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
rather than on the entailment (decision 6).

Unsupported input (matrix predicates, unregistered custom predicates,
terms outside the encoding) is opaque: a predicate it applies becomes a
free Boolean and a term a free value, so it can only weaken an answer. A
proposition about an out-of-scope thing is `None` (satassume's
`out_of_scope` categories are kept).

Answers are meant to be deterministic: each check runs under z3's
`rlimit` (a count of z3's internal steps, not wall time), z3's random seeds
are its defaults and never changed, and the assertions are built in a fixed
order (the SymPy
argument order, never a `set` iteration or a hash order). Each query is
encoded in its own `z3.Context`: in a shared context, z3's term ids and
caches, and with them its search, would depend on the queries asked
before (issue #7; a gate2 query took 0.8 s alone and ran into the
backstop below after the queries before it). A memo of
answers keyed by `(P, A)` is kept, as satassume does; it cannot change an
answer.

One exception: z3 does not check `rlimit` everywhere (a nonlinear sat
check was seen to overrun its rlimit by 68% and run for seconds), and a
step is not a fixed amount of time: in the nonlinear solver one step can
cost a hundred times what it costs elsewhere (#31: one Groebner basis call
took 11 s and 550 MB inside a limit of 1,000,000 steps, and nlsat's
polynomial work runs at about 200,000 steps a second). So each
check also has a wall-clock backstop of 10 s. A check stopped by the
backstop is `unknown`, so the answer is `None`, and whether a check near
the backstop finishes depends on the machine and its load: such answers
are not deterministic. The backstop is set far above the rlimit's usual
cost so that it fires only in these pathological cases; every firing is
counted (`last["timeout"]` in the module `z3assume.ask`), a `None` it
caused is not memoized, and the stream comparison (`tools/`) reports the
count, so a query that hits it is visible and can be fixed in the encoding
(by a smaller problem, not a larger limit).

The rlimit of a check is 1,000,000 (`RLIMIT`, decision 12). When the default solver
runs out of it (not when the backstop fires), the check is tried once
more with the tactics `simplify`, `propagate-values`, `solve-eqs`, `smt`
and an rlimit of 250,000 (`FALLBACK`, `FALLBACK_RLIMIT`). These tactics
have no wall-clock timers of their own (`qfnia` has `try_for`, so it
is not used), so both runs are deterministic, and
either `unsat` is a proof: the fallback can only turn a `None` into an
answer the axioms entail (decision 11).

satassume answers under the part of `A` connected to `P` unless the whole
of `A` is inconsistent. z3assume gives z3 the whole of `A`: by monotonicity
the answer is the same or more definite, and it raises exactly when `A` is
inconsistent (as far as z3 can show). A relevance split may come back as an
optimization, never as a change of answers.

## Out of scope at first

`polar`; matrices and matrix predicates;
non-commutative symbols; custom predicates and satassume's extension API
(`register`); `refine`; and, until their step, transcendental functions
other than `exp`, `log`, the circular and hyperbolic functions and
powers, special functions, relations.
The first slice is the eleven predicates `real`, `rational`, `integer`,
`positive`, `negative`, `zero`, `nonzero`, `nonnegative`, `nonpositive`,
`even`, `odd` on polynomial and rational expressions.

## Decisions

These were open questions for Tilo. Tilo does not answer questions about
z3assume (architect-17, 23 Oct): its sessions decide, by what he has said
and done (satassume's written conventions, the #247 truth standard,
soundness before definiteness, the comparison corpora). z3assume-5
re-checked each against those and recorded the outcome below. Later design
questions are decided the same way, by the session that meets them, with a
one-line rationale added here.

1. Kept: a free symbol is any value except `nan` (see "Values").
   Rationale: `nan` means "undefined", not a value a variable can take;
   satassume's soundness oracle never evaluates at `nan` and its answers
   assume the same (e.g. `ask(Q.finite(x) | Q.infinite(x))` is True only
   under this reading).
2. Kept: a Float is a real with its exact sign, strictly within one ulp (at
   its precision) of its binary value, with no rationality, integer or
   equality facts beyond what that interval decides (see "Terms").
   Rationale: SymPy compares `Float(0.1) > 1/10` exactly but decides `Eq`
   at the Float's precision, so only a bounded unknown is sound under both
   readings (satassume docs/theories.md).
3. Kept, with one change: special values follow satassume's written
   conventions (`1/0 = zoo` and `0**0 = 1`, satassume docs/design.md; the
   rows of the special-values table, satassume#293, cited where used) and,
   where satassume is silent, the table in SymPy's `Pow` docstring
   (`oo**-1 = 0`). Where they disagree the value is free: `nan**0` (N1 and
   P2 say `nan`, SymPy's table `z**0 = 1`) was 1 for a literal exponent 0
   and is now free, as it already was for a symbolic exponent. Rationale:
   each value used is a written convention, not an evaluation result
   (#247); a value two written conventions disagree on has no argument, so
   it is left open (soundness before definiteness); z3assume relies on
   each table row's own argument, whether or not #293 is merged.
4. Kept: answers are given under the whole of `A`, not satassume's
   relevance split; raising on inconsistent assumptions is as in satassume.
   Rationale: `ask(P, A)` asks whether `A` entails `P`, so the whole set is
   the definition; comparisons count the extra answers as "more definite".
5. Changed: no comparison column with SymPy's own `ask`. Rationale: under
   #247 it would be one more opinion, not ground truth; the satassume
   comparison stays the oracle, and every disagreement is settled by a
   mathematical argument in docs/comparison.md.
6. Kept: `A & ~P` unsat with `A & P` unknown answers `True` (see
   "Answering"). Rationale: the unsat result is a proof that `A` entails
   `P`; only the raising on an inconsistent `A` that z3 cannot show is
   lost.
7. Changed (#24): `re`, `im`, `conjugate`, `sign` at `+oo` and `-oo` are
   their limits along the real axis (`re = +-oo`, `im = 0`, `conjugate =
   +-oo`, `sign = +-1`; special-values row V2). At the other kind the
   encoding states only what holds for every member: along `t*d` (row V2,
   `u = d/|d|` non-real) `re = t*re(d)` tends to `+-oo` or is `0`, `im`
   tends to `+-oo`, `conjugate = t*conj(d)` is of the same kind and `sign =
   u` is a non-real unit; at `zoo`, `re`, `im` and `sign` are `nan` and
   `conjugate` is `zoo`. Rationale: `conjugate(zoo) = zoo` is a limit
   (`|conj z| = |z|` grows without bound). `re`, `im` and `sign` have no
   limit at `zoo` (`re(c + s*I) = c` for every `c` as `s -> oo`), and the
   table writes `nan` for "no limit" where it has a row (F1: `exp(zoo)`,
   `exp(oo*d)` with `re(d) = 0`; P5); `re(zoo)` cannot be `+oo` or `-oo`
   anyway, since `zoo = -zoo` (M3) and `re(-z) = -re(z)`. This is a
   convention, in the table's spirit, not a theorem; the table itself has
   no row for these four functions at an infinity. Decision 8 still leaves
   `frac` of an infinity free (no query needs it). Earlier these were free;
   the change decides `Q.zero(sign(1/x))` under `Q.real(x)` (False).
8. New (#18): `floor` and `ceiling` of `+-oo` are `+-oo`, and of the
   other kind (`zoo`, `oo*I`, ...) that kind; `frac` of any infinity is
   free. Rationale: satassume's `templates/integer_funcs.py` states
   `floor(+-oo) == +-oo` and `floor(zoo) == zoo` (the special-values table
   has no row), and they are limits: `|floor(w) - w| < 2` for finite `w`,
   so along `t*d` (row V2) `floor(t*d)` tends to the infinity of direction
   `d`, and on the Riemann sphere to `zoo`. `frac` has no limit at
   `+-oo` (SymPy writes `AccumBounds(0, 1)`, a set) and nothing written
   gives `frac(zoo)` a value.
9. New (#21): `factorial(z) = gamma(z + 1)` for every `z`, and `gamma` at
   a nonpositive integer (so `factorial` at a negative integer) is `zoo`;
   `gamma(oo) = factorial(oo) = oo`; `gamma(-oo)` and `gamma` of the other
   kind of infinity are free. Rationale: SymPy defines `factorial` on the
   nonnegative integers with `n! = gamma(n + 1)` and "factorial of a
   negative integer is complex infinity" (its docstring), and satassume
   writes the whole convention down (templates/integer_funcs.py:
   `factorial(x) == gamma(x + 1)` off the integers, `factorial(oo) == oo`;
   templates/gamma_functions.py: `gamma(-n) == zoo`, `gamma(oo) == oo`);
   the special-values table has no row. The values are limits: at a pole
   `|gamma|` tends to infinity from every direction (the point `zoo` of
   the Riemann sphere, as `1/0 = zoo`), and `gamma(x) -> oo` along the
   real axis; at `-oo` the poles accumulate, so there is no limit.
10. New (#26): `cosh`, `sinh`, `tanh`, `coth`, `sech`, `csch` at `+oo`
   and `-oo` are their limits along the real axis: `cosh(+-oo) = oo`,
   `sinh(+-oo) = +-oo`, `tanh(+-oo) = coth(+-oo) = +-1`, `sech(+-oo) =
   csch(+-oo) = 0`; at `zoo` and the directed non-real infinities, and
   the circular functions at every infinity, the value stays free.
   Rationale: satassume writes this convention down
   (templates/hyperbolic.py: "the limit at a real infinity ..., no claim
   at a non-real infinite argument"; the special-values table has no
   row), and the limits exist: `cosh t, |sinh t| >= e**|t|/2 - 1/2`
   tend to `oo` with the sign of `t` for `sinh`; `tanh t = 1 - 2/(e**(2t)
   + 1)` tends to `+-1`, and so does `coth = 1/tanh`; `sech`, `csch`
   are reciprocals of values of unbounded modulus. Along `I*t` they are
   periodic (`cosh(I*t) = cos t`), so there is no limit at `oo*I`, nor at
   `zoo`. These are the decision 7-9 rule: a limit along the direction
   of the infinity, written down by satassume. (SymPy evaluates the same
   values, which is not the argument, #247.) It is also the value the
   formulas through `exp` give, except for `tanh` and `coth`, whose
   quotient `(e**t - e**-t)/(e**t + e**-t)` is `oo/oo` at `+oo`: the
   function is the limit, not the formula's expression at the point.
11. New (#29; the rlimit is 1,000,000 again since decision 12): rlimit
   2,000,000 per check, and a fallback (plain
   preprocessing and the smt core, rlimit 250,000) when the default
   solver runs out of it. Rationale: the default
   solver's nonlinear search depends on the order in which terms were
   created and on what ran before in the context, so one added axiom can
   move a check across its limit with no change in what is true. Two cases
   of the public wester suite were lost that way by #26 (its axiom "a sum
   is finite only when every summand is"), and both old answers are right.
   `sign(x**4 - x) = 1` under `0 <= x <= 1` is False because `x**4 <= x`
   there. `sign(k*x**n - k*y**n) = 1` under `x > y > 1/10`, `x < 10`,
   `k > 0` and `0 < n < 10` is True because `t -> t**n` increases on
   `(0, oo)` for `n > 0`. The first check takes 90,000 steps in a fresh
   context and over 4,000,000 in `ask`'s order; the fallback decides it
   in about 51,000. The second needs 1,130,000 steps (990,000
   before #26). The limits are steps, not seconds, so answers stay
   deterministic. The cost is measured in the #29 PR description.
12. New (#31): the rlimit is 1,000,000 again; the fallback of decision 11
   stays. Rationale: an undecided check runs to its limit, so the 2,000,000
   of decision 11 doubled the cost of every `None` answer, and because a
   step in the nonlinear solver can take far longer than elsewhere, it
   pushed many of them past the 10 s backstop: on the bench site's 553
   public queries, 42 took over 10 s at f2d67e8 against 19 with this
   limit (21 at fb92e31, before #27-#29), and the backstop's answers
   depend on the machine. Smaller problems were tried first and rejected:
   turning off z3's Groebner bases (the step that ran 11 s inside one
   rlimit) or its substitution of fixed values loses the Tribonacci
   identity of `tests/test_constants.py`, and any such parameter moves
   the search of other hard checks in both directions, while the limit
   moves them all one way. The cost is seven definite answers of the
   bench site's public suites (all right, now `None`, listed in
   docs/comparison.md) and the second case of decision 11, which needs
   1,130,000 steps (its test is an expected failure); the stream and
   gate2 answers do not change.
13. New (#33): the converse integer axiom of a sum (#23: an integer sum
   whose other summands are integers makes the last one an integer) is
   left out for a sum without free symbols. Rationale: its summands are
   numbers whose kinds their own axioms state (rationals, the algebraic
   closure, the named constants), so the axiom gave no answer of the
   corpora there, but it let z3's nonlinear core split on the integer
   witnesses of nested radicals, and one Groebner step then ran for
   seconds inside one rlimit: the repro of #33 took 5.1 s against 0.30 s
   pinned (the same 1,024,583 against 1,024,506 steps). Leaving an axiom
   out cannot make an answer wrong; the stream and gate2 answers do not
   change, and on the bench site's 553 public queries one more is
   decided (True) and none is lost.
