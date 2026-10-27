# Comparison with satassume

z3assume is compared with satassume (main at 9bafaa5) on two of satassume's
corpora, using the same SymPy on both sides (1.15.dev, the checkout
satassume's tools use):

- the refine stream (`stream.pkl`, 16,232 queries recorded from SymPy's
  `refine`), and
- gate2 (`gate2-frozen.jsonl`, 2,863 queries), replayed through satassume's
  `tools/gate2_stream.py`.

Per query: **agree** (same answer, both raising included), **more**
(satassume None, z3assume definite), **less** (satassume definite,
z3assume None), **CONTRADICT** (True against False) and **error-diff** (only
one side raises ValueError, or z3assume crashes). Each contradiction must be either a z3assume bug,
which gets fixed, or a satassume bug with a mathematical argument, which gets
filed on satassume.

## How to run

    PY=/path/to/venv/bin/python   # sympy 1.15.dev and z3-solver
    SYMPY=/path/to/sympy
    PYTHONHASHSEED=0 PYTHONPATH=SATASSUME:$SYMPY $PY SATASSUME/tools/stream_answers.py stream.pkl sat.json default
    PYTHONHASHSEED=0 PYTHONPATH=.:$SYMPY $PY tools/stream_answers.py stream.pkl z3.json --jobs 6
    PYTHONHASHSEED=0 PYTHONPATH=.:$SYMPY $PY tools/compare_answers.py stream.pkl sat.json z3.json stream

`tools/compare_answers.py` prints the table per predicate, the contradictions
and error-diffs, and the constructs found in the "less" queries.

## Results, 23 Oct 2026 (z3assume 0f84081, satassume 9bafaa5)

| corpus | n | agree | more | less | CONTRADICT | error-diff | z3 timeouts |
|---|---|---|---|---|---|---|---|
| stream | 16,232 | 15,042 | 49 | 1,137 | 0 | 4 | 0 |
| gate2 | 2,863 | 2,288 | 30 | 545 | 0 | 0 | 0 |

The tables per predicate are in the PR that added this file
(tilorc-bot/z3assume#2).

The four error-diffs (stream 6796, 6798, 6813 and 6815) are expected. Each
asks `Q.zero(pi)` or `Q.negative(pi)` under assumptions that contain
`Q.negative(x) & Q.positive(x)`, so the assumptions are inconsistent.
satassume decides a constant proposition first, without the assumptions,
and answers False. z3assume does not encode `pi` yet, so it gets None from
that first step and then raises on the inconsistent set. That is the
documented behaviour, and the four will agree once `pi` is encoded.

## Arguments for the newly definite answers

79 queries (49 stream, 30 gate2; 24 + 26 distinct `(prop, assum)` pairs) get
`None` from satassume and a definite answer from z3assume. Each one is
justified below by a definition, a theorem, or a convention written down in
z3assume's docs/design.md ("Values", "Predicates", "Terms", "Relations") or in
satassume's docs (theories.md "What relations mean", special-values row V1).
SymPy's own evaluation is used for none of them. No answer is wrong: every
class has a short proof, and no query is left unjustified.

All symbols are plain `Symbol`s with no declared assumptions (so any value
of D except `nan`, z3assume's and satassume's convention), except in gate2
2855, where `a`, `b`, `c` are declared `real=True` (finite reals).

| Class | stream / gate2 | Example | z3assume |
|---|---|---|---|
| N. `nan` is no number | 0 / 23 | `Q.integer(nan)`, `Q.nonzero(nan)`, `Q.hermitian(nan)` | False |
| P. Parity of `n` and `n + 1` | 24 / 0 | `Q.odd(k/2 + 1/2)` given `Q.odd(k) & Q.even(k/2 - 1/2)` | True |
| T. Parity of a rational multiple | 7 / 2 | `Q.odd(2*k/3)` given `Q.odd(k)`; `Q.even(2*x)` given `~Q.integer(x)` | False |
| Z. A zero factor | 9 / 0 | `Q.zero(x)` given `Q.negative(x*y)`; `Q.positive(x*y)` given `Q.zero(y)` | False |
| L. Integer bounds | 7 / 0 | `Q.negative(k + x - 1)` given `k, x` integers, `k >= 0`, `x > 0` | False |
| I. An interval with `pi` | 2 / 0 | `Q.integer(-t/(2*pi) + 1/2)` given `Q.positive(t) & Q.negative(t - pi)` | False |
| E. Sums of same-signed infinities | 0 / 4 | `Q.finite(x + y + z)` given `Q.finite(x)`, `y`, `z` both `-oo` | False |
| M. Monotonicity of multiplication | 0 / 1 | `a*c <= b*c` given `(a <= b) & (c > 0)`, `a, b, c` real | True |

**N.** satassume's special-values row V1, adopted in z3assume's design.md
("Predicates"): `nan` is no number, and every predicate except `finite`,
`infinite` (and `polar`) is False of it. All 23 queries ask one of
`integer, rational, algebraic, real, extended_real, complex, irrational,
imaginary, positive, negative, nonzero, zero, even, odd, prime, composite,
hermitian, antihermitian, transcendental` of `nan` under no assumptions.

**P.** Let `k` be odd and `m = (k - 1)/2`, an integer. Then
`k/2 - 1/2 = m` and `k/2 + 1/2 = m + 1`. For an integer, `m` even iff `m + 1`
odd. So `even(m)` gives `odd(k/2 + 1/2)` True and `even(k/2 + 1/2)` False,
and `odd(m)` the reverse.

**T.** By the definition of `even`/`odd` (integers with remainder 0/1).
`2k/3` with `k` odd: if `2k/3 = n` is an integer, `3n = 2k` is even, so `n`
is even; if not an integer it is not odd. Same for `x/3` with `x` even
(`3n = x` even forces `n` even). `2x` even means `2x = 2m` for an integer
`m`, so `x = m` is an integer, contradicting `~Q.integer(x)` (an infinite
`x` gives an infinite `2x`, not an integer).

**Z.** `negative` implies a finite nonzero real. If `x = 0` then `x*y` is
`0` (finite `y`) or `nan` (infinite `y`, convention `0*oo = nan`, design.md
"Values"/"Terms: Mul"); neither is negative, so `x`, `-x`, `y`, `-y` are not
zero. With `y = 0`, `x*y` is `0` or `nan`; `0` is not (extended) positive or
negative, and not `imaginary` (SymPy's definition: `I*b` with `b` real
nonzero; design.md: `im != 0`); `nan` is none of them by V1.

**L.** Integer `k >= 0`, `x >= 1`: `k + x - 1 >= 0` (not negative) and
`-k - x + 1 <= 0` (not positive). Integer `k <= -1`, `x >= 1`:
`k - x + 1 <= -1` and `-k + x - 1 >= 1`, both nonzero. Integers `k, x >= 1`:
`k + x - 1 >= 1`, so it is neither zero nor negative, and `-k - x + 1 <= -1`
is not positive. (Positive/negative assumptions also make `k`, `x` finite.)

**I.** `positive(t)` and `negative(t - pi)` give a real `t` with
`0 < t < pi`. `pi` is still opaque in z3assume, but the assumptions alone
make it real with `pi = t - (t - pi) > t > 0`; so `0 < t/(2*pi) < 1/2`. So `-t/(2*pi)` lies in
`(-1/2, 0)` and `-t/(2*pi) + 1/2` in `(0, 1/2)`: no integer in either.

**E.** Extended-real addition (design.md "Terms: Add"): `-oo` plus finite or
`-oo` terms is `-oo`, likewise `+oo`. With `x` finite and `y = -oo`, `z` is
`-oo` or (extended_negative) a finite negative or `-oo`; the sum is `-oo`,
not finite. Symmetrically for `+oo` and extended_positive.

**M.** `a, b, c` are declared real, so finite; `c > 0` and `a <= b` give
`(b - a)*c >= 0` in the ordered field R, i.e. `a*c <= b*c` (both sides
real, so the relation's extended-real conjuncts hold). Note: with plain
symbols this would be False-able (`a = 0`, `b = 1`, `c = oo`:
`0*oo = nan`); z3assume answers None there, correctly.

Indices per class (raw, duplicates included):

- N gate2: 392-404, 407-411, 2215-2218, 2226
- P stream: 132, 133, 142, 143, 166, 167, 175, 176, 657, 658, 667, 668,
  691, 692, 700, 701, 1136, 1137, 1205, 1206, 1428, 1429, 1459, 1460
- T stream: 3077, 3083, 3089, 3095, 3101, 3107, 13881; gate2: 1134, 1698
- Z stream: 10169, 10171, 10172, 10196, 12409-12413
- L stream: 14531, 14532, 14998, 15049, 15136, 15140, 15141
- I stream: 11829, 11834
- E gate2: 2792, 2795, 2803, 2806
- M gate2: 2855

Most of the "less" answers come from constructs the first slice treats as
opaque:

- **Stream:** `pi` (692 queries), non-integer Rationals mixed with them
  (404), `Abs`/`re`/`im`/`sign` (390) and `1/x` of such terms (248).
- **gate2:** symbolic powers such as `I**I` and `3**I` (145), trig at
  numbers such as `sin(7)` (116), `pi` (113), named constants (`E`,
  `GoldenRatio`), `exp`/`log` at numbers, and Floats.

These classes set the order in which coverage is widened.

## Later steps

Each widening step re-runs the comparison. Every answer it changes must
move to "agree", or to "more" with an argument given here.

| step | stream less | gate2 less | CONTRADICT | new "more" |
|---|---|---|---|---|
| first slice | 1,137 | 545 | 0 | 79 (above) |
| named constants (#3) | 593 | 405 | 0 | none |
| `Abs`, `re`, `im`, `conjugate`, `sign` (#5) | 269 | 390 | 0 | 16 distinct, stream only |
| `Eq` carries the predicates (#6) | 269 | 389 | 0 | none |
| symmetric `Eq` (#8) | 261 | 389 | 0 | none |
| Floats (#9) | 261 | 368 | 0 | 15 stream, 3 gate2 (all distinct) |
| one z3 context per query (#10) | 261 | 368 | 0 | none |
| `exp`, `log` (#11) | 228 | 313 | 0 | 2 stream (distinct) |
| trigonometric and hyperbolic (#13) | 197 | 200 | 0 | 9 stream, 7 gate2 (13 distinct) |
| powers (#14) | 157 | 8 | 0 | 7 gate2 (6 distinct) |
| rational coefficients over the integers (#16) | 107 | 8 | 0 | none |
| floor and ceiling (#18) | 60 | 7 | 0 | 3 stream (distinct) |
| gamma and factorial (#21) | 42 | 5 | 0 | none |
| `re`, `im`, `conjugate`, `sign` at the `zoo` kind (#24) | 18 | 5 | 0 | 21 stream (distinct) |
| sums with an infinity, hyperbolic limits (#26) | 1 | 5 | 0 | none |
| inverse functions off the real axis (#27) | 1 | 4 | 0 | none |
| rlimit 2,000,000 and a fallback check (#29) | 1 | 4 | 0 | 1 stream |
| the converse integer axiom for sums (#28) | 1 | 4 | 0 | none |
| rlimit 1,000,000 again (#31) | 1 | 4 | 0 | none |

The rational-coefficient step (#16, fixes #12) moves 50 stream queries (7 distinct,
`Q.integer(k/2 - 1/2)`, `k/2 + 1/2`, `k/2 + 3/2`, `-k/2 - 3/2`, `1/2 - k/2`
given `Q.odd(k)`) from "less" to "agree"; no answer changes otherwise.

Arguments for the 16 new answers of the `Abs` step:

- **`re` of a real in an interval with `pi`** (11 queries, False): for a
  real `x`, `re(x) = x`. With `0 < x <= pi/2`, `x/pi` lies in `(0, 1/2]` and
  so is not an integer. The `2*pi` and `-t/(2*pi) + 1/2` variants are the
  same argument.
- **`x**2` real in `[0, pi/2]`** (one query, True): `x = a + b*I` gives
  `x**2 = a**2 - b**2 + 2*a*b*I`. Real means `a*b = 0`, and nonnegative
  means `b = 0` (if `a = 0`, then `-b**2 >= 0`). `x` is finite because `x**2`
  is. So `im(x) = 0`, and `im(x)/pi = 0` is an integer.
- **An imaginary `x = b*I`** (4 queries): `-I*x = b = im(x)`, so the sign of
  `im(x)` decides `positive(-I*x)`, and the other way round.
- **`sign` of an odd integer is `1` or `-1`** (4 queries, True):
  `sign(n) + 2 > 0`, `-2 < sign(n)`, `-sign(n) < 2`.

Arguments for the 18 new answers of the Float step (the reading of a
Float is design.md "Terms: `Float`": a finite real with its exact sign,
strictly within one ulp at its precision of its binary value):

- **A Float bound makes a symbol finite** (14 stream queries 4911-4996,
  `real(x)` True, `infinite(x)` and `infinite(x/pi + 1/2)` False, given
  `Q.le(x, F)` with a Float `F` (`1.5707963267948966`, `4.712`, `1.571`)
  and `Q.ge(x, -pi/2)`, `Q.gt(x, -pi/2)` or `Q.ge(x, pi/2)`): a relation
  holds only between extended reals (design.md "Relations"); `x <= F` with
  `F` finite excludes `x = +oo`, `x >= -pi/2` excludes `-oo`, so `x` is a
  finite real, and so is `x/pi + 1/2` (`pi` finite, nonzero).
- **Below `pi/2`** (stream 4930, `integer(x/pi + 1/2)` False given
  `x <= 1.5707963267948966` and `x > -pi/2`): this Float has 60 bits; its
  binary value is `pi/2 - 1.96e-17` and its ulp `2**-59 < 1.8e-18`, so its
  interval lies below `pi/2 - 1.7e-17` (and `pi`'s interval is `10**-20`
  wide). So `-pi/2 < x < pi/2` and `x/pi + 1/2` lies in `(0, 1)`. (The
  decimal `1.5707963267948966` is itself below `pi/2 = 1.5707963267948966192...`.)
  With `Q.ge(x, -pi/2)` instead, `x = -pi/2` gives `0` and z3assume
  answers None.
- **`1.0` is not even, prime or composite** (gate2 246, 249, 250, False):
  the interval of `Float(1.0)` is `(1 - 2**-52, 1 + 2**-52)`; its only
  integer is `1`, which is odd and neither prime nor composite, and a
  non-integer is none of the three. (`Q.integer(1.0)` and `Q.odd(1.0)` stay
  None.)

The other Float answers that moved (gate2 240-269, `Q.positive(1.0)`,
`Q.integer(7.2123)`, ...) now agree with satassume. The one Float query
still "less" is `Q.negative(x**1.4)` (gate2 1625): a Float exponent is not
an integer power and stays opaque.

Of four runs of the stream for this step on a shared machine (load
average 13 to 19), two had one check stopped by the 10 s backstop, each
in a query without a Float (stream 9500 and 3617, 0.05 s and 0.25 s in the
`Eq` step's run); 3617 kept its answer (False) and 9500 its None. The last
run, the one in the table, had none.

Arguments for the 2 new answers of the `exp`/`log` step (design.md
"Terms: `exp`, `log`"; satassume None, z3assume False):

- **`exp(I*t)` for `0 < t < pi` is not real** (stream 11818
  `Q.positive(exp(I*t))`, 11819 `Q.negative(exp(I*t))`, both under
  `Q.positive(t) & Q.negative(t - pi)`): `t` is a finite real in
  `(0, pi)`, so `exp(I*t) = cos t + I*sin t` with `sin t > 0`. Its
  imaginary part is nonzero, so it is not real, hence neither positive
  nor negative.

The other 33 stream and 55 gate2 answers that moved now agree with
satassume: `exp` of a real is positive (`Q.positive(exp(x))` given
`Q.real(x)`), `exp(z) != 0` (`Q.zero(exp(I*t))` given `Q.real(t)`, and
`Q.zero(sign(exp(x)))`), `log` of a positive real is real, `arg` on the
axes (`Q.real(log(x))` given `Q.imaginary(x)`), `log(pi) > 0`, the special
values `log(0) = zoo` and `log` of an infinity infinite, Hermite-Lindemann
(`Q.rational(exp(7))`, `Q.algebraic(log(7))`, `Q.rational(log(x))` given
`Q.rational(x) & Q.nonzero(x - 1)`), the enclosure of `exp(2)`, and
`exp(I*pi*x)` for an even or odd `x`. The `exp`/`log` queries still "less"
need a symbolic power (`exp(x)**x`, step 5), `sqrt` (`log(sqrt(2))`), or
trig.

In the final run one check of stream 6776 (no `exp`/`log`; `Q.integer(t/pi
+ 1/2)` with `tan`) hit the 10 s backstop; the other check was unsat, so
the answer (False) did not change, and alone the query takes 3.9 s with no
timeout. Wall times (6 jobs, shared machine, load average 7 to 12): stream
133 s, gate2 23 s (the Float step's run: 191 s, 36 s). Run back to back
with main (551bdb9, before the Float step) on gate2: 27.7 s and 31.9 s for
main, 38.5 s and 36.7 s for this step. The z3 problem of a query without
`exp`, `log` or `E` is unchanged (checked on the slowest movers), yet the
time of such queries alone varies by up to 5x between runs under this
load, so this gap is not measured well; a pinned benchmark was not run.

Arguments for the 16 new answers of the trigonometric and hyperbolic
step (design.md "Terms: `sin`, `cos`, ..."; satassume None, z3assume
False unless stated):

- **`sin` on `(0, pi)`** (stream 3260 `Q.zero(sin(x))` under
  `Q.positive(x) & Q.le(x, pi/2)`, 5176 under `Q.ge(x, 1) & Q.le(x, 2)`,
  5214 under `Q.eq(x, pi/2)`): a relation holds only between extended
  reals, so `x` is a finite real in `(0, pi)` (`2 < pi`), where
  `sin x > 0`.
- **`tan` without a zero in the interval** (stream 4048, 4080, 5336,
  5340, 6754, `Q.zero(tan(x))` under `0 < x < pi/2`, `-pi/2 < x < 0`,
  `0 < x < pi`, `-pi < x < 0`): `x` is a finite real with `sin x != 0`
  (the sign of `sin` on `(-pi, 0)` and `(0, pi)`); `tan x` is either
  `sin x/cos x != 0` or, where `cos x = 0`, `zoo` (`1/0 = zoo`, row M3),
  and neither is zero.
- **`x*tan(t)` real for `-pi/2 < t < pi/2`** (stream 6771, True, under
  `Q.positive(x)`): `t` is a finite real with `cos t > 0`, so `tan t =
  sin t/cos t` is real, and so is its product with the real `x`.
- **`cosh(1)**2 - sinh(1)**2 - 1` and `cos(1)**2 + sin(1)**2 - 1` are 0**
  (gate2 1621, 1763, 1784, 1810, 1831, `Q.negative`/`Q.positive` of the
  first, 1661 `Q.nonzero` of the second): `cosh**2 - sinh**2 = 1` and
  `cos**2 + sin**2 = 1` at a real point; the value is the number 0.
- **`acos(x)` for `x >= 1` is not positive** (gate2 2169, under
  `Q.nonnegative(x - 1)`): `acos(1) = 0`, and for real `x > 1` `acos(x)`
  is not real, as `cos` maps the reals into `[-1, 1]` and `cos(acos x) =
  x` for every branch.

The other 31 stream and 113 gate2 answers that moved now agree with
satassume: Hermite-Lindemann for the twelve functions and the inverse
ones (`Q.rational(sin(7))`, `Q.algebraic(acos(x))` given
`Q.algebraic(x) & Q.nonzero(x - 1)`, `Q.rational(cot(x))` given
`Q.rational(x)` with `cot(0) = zoo`), `cosh x >= 1` and the reciprocals
never zero (`Q.zero(sech(x))` given `Q.complex(x)`), `sin`, `cos` of a
real real, the signs of `atan`, `asin`, `acos`, `acot` on the real axis,
and `sin(2) > 0`. Still "less": `cosh`, `coth` at `oo` (6 stream queries
under `Q.extended_nonnegative(x)`, `Q.ge(x, 0)`, ...: an infinite
argument is free, no row of satassume's table gives `cosh(oo)`), `sqrt`
(`Q.algebraic(sqrt(sin(7)))`, step 5), and `acot` of an imaginary
argument (gate2 2172, not encoded).

No check hit the 10 s backstop on either stream. Wall times (6 jobs,
shared machine, load average 4 to 7): stream 112 s, gate2 17 s; the
summed query times 669 s and 97 s, against 794 s and 136 s for the
`exp`/`log` step's run (load average 7 to 12), so the step costs no
measurable time on these streams. A first version encoded `tan = sin/cos`
as `t*cos = sin` with a complex denominator; it took 10 s on gate2 2005
(`Q.algebraic(tan(x))` given `Q.algebraic(x)`, None either way) and was
replaced by the real denominator `|cos z|**2`, 0.3 s alone. Probes with a
non-real argument of `tan` (`Q.algebraic(tan(x))` given `Q.complex(x)`)
still can take seconds, depending on what the z3 context saw before:
nonlinear model search, the answer None either way.

Arguments for the 7 new answers of the powers step (design.md "Terms:
`Pow` with any other exponent"; satassume None; all gate2):

- **`(3*I)**I` and `(1 + I)**I` are not real** (663, 669, False): the
  principal value is `exp(I*log(b))` with `log(3*I) = log 3 + I*pi/2` and
  `log(1 + I) = log(sqrt(2)) + I*pi/4`, so `b**I = exp(-pi/2)*exp(I*log 3)`
  and `exp(-pi/4)*exp(I*log(sqrt(2)))`. The imaginary parts are a positive
  real times `sin(log 3)` and `sin(log sqrt(2))`, and `0 < log(sqrt(2)) <
  log 3 < pi`, so both are nonzero.
- **`1**y` for rational `y`** (1272, 1364, `Q.rational(x**y)` True under
  `Q.rational(y) & Q.eq(x, 1)`): a rational `y` is finite, and for finite
  `y`, `1**y = exp(y*log 1) = exp(0) = 1`.
- **`x**1 = x`** (1760, `Q.prime(x**y)` True under `Q.prime(x) &
  Q.eq(y, 1)`; 1761, the same under `Q.integer(y) & 0 < y < 2`, so `y =
  1`): `exp(log x) = x` for finite `x != 0`, and a prime is one.
- **A prime to an integer power other than 1 is no prime** (1755, False
  under `Q.integer(x) & Q.prime(p) & Q.ne(x, 1)`): `x >= 2` gives `p*p**(x -
  1)` with both factors at least 2; `x = 0` gives 1; `x <= -1` gives
  `0 < p**x <= 1/2`, no integer.

The other 40 stream and 192 gate2 answers that moved now agree with
satassume: `sqrt(2)` (irrational, algebraic, positive), `I**I`,
`(-1)**I`, `I**(3 + I)`, `3**I`, `2**I` (Gelfond-Schneider for the
transcendence, the principal value for the rest), `(-1)**k` and `I**k`
for integer `k`, signs and parities of `x**k` for integer `k`, `0**y`,
`b**0`, `2**x` finite, `x**y` for positive `x` and real `y`, a negative
base to an irrational or non-half-integer real exponent (not imaginary),
`x**1.4` for real `x` (not negative), `sqrt` of a negative real
(imaginary), the closure facts (`Q.rational(1/x)` given
`Q.irrational(x)`, `Q.prime(x**2)` given `Q.integer(x)`,
`Q.algebraic(sqrt(sin(7)))`) and `exp(x)**x` for imaginary `x`. Still
"less" among the powers: gate2 1492 and 1553 (`Q.imaginary(x**y)` under
`Q.rational(y) & Q.real(x) & ~Q.integer(2*y)`; each sign of `x` alone is
decided, the case split exhausts the rlimit) and stream 12210
(`Q.zero(sqrt(sign(x)*sign(conjugate(x))))` under `Q.negative(re(x))`:
`x` may be `zoo`, where `re` and `sign` are free, decision 7).

No check hit the 10 s backstop. Wall times (6 jobs, shared machine, load
average 1 to 8): stream 133 s, gate2 35 s; summed query times 794 s and
205 s, against 669 s and 97 s for the trigonometric step. The queries with
a non-integer power cost 50 s (stream) and 86 s (gate2) summed, against 7 s
and 18 s before, when they were None at once: each such power adds the
terms `log(b)`, `x*log(b)`, `exp(x*log(b))` and, for a symbolic base,
`exp(I*pi*x)` with its half-integer term (the last about 20% of the cost
on gate2's 223 distinct power queries, for 3 answers). The rest of the
increase is load: the problem of a query without such a power is
unchanged (but for `exp(I*pi*c)`), and alone such queries vary up to 2x
between runs (stream 3205: 3.6 s and 7.7 s; gate2 916: 8.4 s on both
branches, 0.04 s in the stream run). A pinned benchmark was not run.

Arguments for the 3 new answers of the floor and ceiling step (design.md
"Terms: `floor`, `ceiling`, `frac`"; satassume None, all stream):

- **`floor` of a finite real is an integer** (4961, 5004,
  `Q.integer(floor(x/pi + 1/2))` True under `Q.ge(x, -pi/2)` and
  `Q.le(x, F)` with the Floats `1.5707963267948967`, `1.571`): a relation
  holds only between extended reals, and the Float bound is finite, so
  `x` is a finite real (as in the Float step's argument), and so is
  `x/pi + 1/2` (`pi` finite, nonzero); the greatest integer `<=` a finite
  real is an integer.
- **`I*pi*floor(x/pi + 1/2)` is not zero for `2 <= x <= 5`** (5171,
  False): `x/pi + 1/2` lies in `[2/pi + 1/2, 5/pi + 1/2]`, inside
  `(1.13, 2.10)` (`3.14 < pi < 3.15`), so its floor is 1 or 2, nonzero,
  and `I*pi` times a nonzero integer is nonzero.

The other 47 stream answers that moved, all 47 floor and ceiling queries
that were "less", now agree with satassume: the integer and finiteness
of `floor(x/pi + 1/2)`, `floor((-x + pi/2)/pi + 1/2)` and
`x - 2*pi*floor(x/(2*pi) + 1/2)` for finite real `x` (assumed real, or
in an interval), and `re`, `im` of `floor(y)`, `ceiling(y)` integers and
`ceiling(y)` finite for finite `y` (each part is rounded). On gate2
`Q.irrational(ceiling(y))` (2836) moved to agree (False: a Gaussian
integer is rational or not real, and an infinity or `nan` is not real).
No floor or ceiling query is "less" any more.

One check hit the 10 s backstop: stream 4181 (`Q.zero(tan(x))` under
`-pi/2 <= x < pi/2`, no floor), None in the run, as in the base run and
for satassume; alone it takes 2.9 s with no timeout. Wall times (6 jobs,
shared machine, load average 7 to 12): stream 195 s, gate2 57 s (base
runs: 206 s, 29 s). Gate2 has 7 floor queries; run back to back with main
(c68563e) at load 11, gate2 took 50.7 s on main and 54.1 s on this step,
so its gap is load. The 284 stream queries with `floor`, `ceiling` or
`frac` do cost more: run alone, alternating with main (6 jobs, load 11
to 12), 11 s and 13 s wall (52 s and 67 s summed) on main, 46 s to 82 s
(212 s to 397 s summed) on this step, about 4x, with 16 checks stopped by
the rlimit (each answer None, as satassume's). They are the angle
reductions `x - 2*pi*floor(x/(2*pi) + 1/2)` and their relatives: the
floor of a nonlinear real (`x/pi`), where model search over integers and
nonlinear reals is slow; on main the floor was a free value and these
checks were sat at once. A version with two fresh integers in place of
`ToInt` (bounds `m <= a < m + 1`) had 12 rlimit stops on the subset and
the same answers, but lost `ceiling(x) - floor(x) = 1` off the integers
(rlimit), so `ToInt` stays.

The gamma and factorial step (#21; design.md "Terms: `gamma` and
`factorial`", decision 9) changes 20 answers, 18 stream and 2 gate2, all
from "less" to "agree"; no other answer changes and no query is "more".
The arguments (`factorial(m) = gamma(m + 1)`):

- **`gamma` on the positive reals** (stream 14483 `Q.zero(gamma(x))`,
  14486 `Q.negative(gamma(x))`, False under `Q.positive(x)`): for a finite
  real `x > 0`, `gamma(x)` is the integral of `s**(x - 1)*e**-s > 0` over
  `(0, oo)`, a positive real.
- **The factorial of a nonnegative integer** (stream 14520 to 15132,
  16 queries, `Q.zero` and `Q.negative` False; gate2 1806, 1853,
  `Q.positive(factorial(x))` True under `Q.integer(x) & Q.positive(x)`):
  the argument `m` is an integer `>= 0`: `x - 1` for an integer `x > 0`;
  `n - k` with `k <= n` (as `Q.le(k, n)` or `Q.nonnegative(n - k)`), or
  with `k < 0 <= n`; `x - k` with `x = 0` or `x > 0` and `k < 0`. Then
  `m! = gamma(m + 1)` is a positive integer (`gamma(1) = 1` and
  `gamma(j + 1) = j*gamma(j)`), neither zero nor negative. Gate2 1807 and
  1854 (`Q.positive(factorial(x))` under `Q.integer(x)` alone) stay None,
  as for satassume: `factorial(-1) = zoo`.

No gamma or factorial query is "less" any more; the corpora have no
`loggamma`, `RisingFactorial`, `binomial` or other member of the family.
Two checks hit the 10 s backstop, neither in a gamma or factorial query
and neither changing an answer: stream 4181 (as in the floor step) and
gate2 916 (`Q.finite(x*y*z)` under `Q.finite(x)`, None on both sides;
alone 8.5 s with one rlimit stop and no timeout). The 22 gamma and
factorial queries take 1.7 s of CPU in all on this step and 0.9 s on main
(7310080), run alone in one process (seven alternating rounds, memo
cleared per query), with no check stopped by the rlimit on either.
Wall times (6 jobs, shared machine): stream 268 s, gate2 59 s at load 13
to 15 (floor step's runs: 195 s, 57 s at load 7 to 12). Run back to back
right after, the stream took 316 s on main (load 13 to 19) and 224 s on
this step (load 11 to 19), each with the answers of its own run and only
backstop stops outside gamma (main 4, this step 2, stream 4181 and 5012
on both); the gap is load, not the 22 queries.

### `re`, `im`, `conjugate`, `sign` at the `zoo` kind (#24)

Decision 7 now states, at the infinities of the other kind (`zoo` and the
directed non-real infinities `oo*u`), what each of them gives: `re` is
`+-oo`, `0` or `nan`, `im` is `+-oo` or `nan`, `conjugate` keeps the kind,
`sign` is `nan` or a non-real unit (design.md, "Terms", decision 7). This
changes 45 stream answers, all from None; gate2 is unchanged. 24 of them
were "less" and now agree; 21 are new "more" (satassume None). No answer
moves between True and False. The arguments, for a symbol `x` that may
be any number or infinity (a free symbol is never `nan`, design.md
"Values"; `nan` enters only as the value of a term):

- **`re` or `im` given positive or negative rules out every infinity**
  (stream 10449, 10584, 11194: `Q.finite(x)` True under `Q.positive(im(x))`
  or `Q.positive(re(x))`; and with that, 12034 to 12045, 12065, 12169 to
  12210 under `Q.positive(re(x))`, `Q.nonnegative(re(x))` or
  `Q.negative(re(x))`): `re` and `im` of `+-oo` are `+-oo` and `0`, of the
  other kind `+-oo`, `0` or `nan`, and of `nan` `nan`; none is a finite
  nonzero real (for `nonnegative`: none is a finite real except the `0` of
  `re(oo*I)`, where `conjugate(oo*I) = -oo*I` is still no negative real).
  So `x` is finite, and the rest is finite arithmetic: `x != 0`,
  `sign(x) = x/|x|` has the sign of `re(x)` in its real part, so it is not
  `0` and, given `re(x) > 0`, not a negative or nonpositive real (12038,
  12043, 12044), given `re(x) < 0` not a positive or nonnegative one (12176
  to 12178, and 12200 for `conjugate(x)`, whose real part is `re(x)`); it
  is finite (12045, 12181); `sign(x)*sign(conjugate(x)) = x*conj(x)/|x|**2
  = 1` is positive (12206) and not zero (12202, 12210).
- **`sign` of a nonzero value is never zero, and of a non-real value never
  real** (7365, 7366, 9321, 9501, 9538, 9539 `sign(1/x)`, `sign(x**-2)`
  under `Q.real(x)` or `Q.complex(x)`; 11038, 13187 `Q.zero(sign(x))` under
  `~Q.zero(x)`; 12085 to 12096 under `~Q.zero(im(x))`): at `x = 0` the
  argument is `zoo` (row P1), whose `sign` is `nan`; else `1/x` and
  `x**-2` are finite and nonzero, `x**-2` positive for real `x` (7365,
  9538: `sign = 1`, not negative). Under `~Q.zero(x)`, a finite `x` has
  `|sign(x)| = 1`, `+-oo` has `sign = +-1`, the other kind has `nan` or a
  unit, `nan` has `nan`: never `0`. Under `~Q.zero(im(x))`, `x` is finite
  with `im(x) != 0`, of the other kind, or `nan` (`im(+-oo) = 0` is
  excluded): `sign(x)` is a non-real unit or `nan`, so it is no positive,
  negative, nonnegative or nonpositive extended real (12090, 12092 to
  12096), and `conjugate(x)` (finite non-real, of the other kind, or
  `nan`) is no positive, negative or zero number (12085 to 12087).
- **`re(x)**2 + im(x)**2` under `~Q.zero(x)`** (11022 `Q.zero`, 11024
  `Q.negative`, both False): for finite `x != 0` it is `|x|**2 > 0`; at
  `+-oo` it is `oo**2 + 0 = oo`; at the other kind `im(x)**2` is `oo` or
  `nan`, so the sum is `oo` or `nan`; at `nan`, `nan`. Never zero or
  negative.

Still "less" in this class: stream 12097 `Q.finite(sign(x))` under
`~Q.zero(im(x))` and gate2 954, 955 `Q.finite(sign(x))`: `x` may be `zoo`,
where `sign` is `nan`, and `Q.finite(nan)` is left open (row V1). No
check hit the backstop on the stream; one gate2 check did, with the
answer unchanged.

The sums-with-an-infinity and hyperbolic-limits step (#26; design.md
"Terms: `Add`" and decision 10) changes 17 stream answers, all from "less"
to "agree" (None to False, as satassume); gate2 answers do not change and
no query is "more" or contradicting. The arguments:

- **A sum with an infinite summand is not a number** (stream 15830 to
  15833, 15853 to 15856: `Q.zero(i - j)` and `Q.nonzero(i - j)` with
  `Q.infinite`, `Q.positive_infinite` or `Q.negative_infinite` of `i` or
  `j`, the predicate being the infinity; 15839, 15848, 15942:
  `Q.zero(i - j)` under `Q.ne(i, j)` or `Q.ne(j, i)`): `i - j` is finite
  only when `i` and `j` are (design.md "Terms: `Add`": a bounded term
  cannot cancel an unbounded one, and two unbounded ones that can cancel
  give `nan`). `Q.zero(i - j)` and `Q.nonzero(i - j)` both make `i - j` a
  finite number, so `i`, `j` are finite; then an infinite `i` or `j` is
  impossible, and `i - j = 0` gives `i = j`, against `Q.ne(i, j)`.
- **`coth` on `(0, oo]`** (stream 6395, 6405, 6415: `Q.zero(coth(x))`
  under `Q.extended_positive(x)`, `Q.ge(x, 1)`, `Q.gt(x, 0)`): for finite
  `x > 0`, `coth x = cosh x/sinh x > 1`, as `cosh x > sinh x > 0`; at
  `x = oo` it is `1` (decision 10). Never zero.
- **`cosh` on `(-1, oo]`** (stream 6477, 6487, 6493: `Q.zero(cosh(x))`
  under `Q.extended_nonnegative(x)`, `Q.ge(x, 0)`, `Q.gt(x, -1)`): for
  finite real `x`, `cosh x = (e**x + e**-x)/2 >= 1`; `cosh(oo) = oo`
  (decision 10). Never zero.

Wall times (6 jobs, shared machine): stream 152 s, gate2 43 s; no check
hit the 10 s backstop.

The inverse-functions step (#27; design.md, `_inverse`) changes one
answer, gate2 2172 `Q.positive(acot(x))` under `Q.imaginary(x)`, from
"less" to "agree" (None to False, as satassume); the stream answers do
not change. The argument: `x` is finite and not real. If `w = acot(x)`
were a finite real, then `cot(w) = x`, but `cot` maps the reals into the
reals and `zoo`; so `w` is no finite real, and `Q.positive(w)` is False.
The same holds for the other seven inverse functions z3assume encodes
(`asin`, `acos`, `atan`, `asinh`, `acosh`, `atanh`, `acoth`): on its
finite values each is a right inverse of a function that maps the reals
into the reals and `zoo`.

The rlimit step (#29, decision 11) changes one answer, by the larger
rlimit (the default solver proved it in about 1,050,000 steps; since #28
it needs fewer than 1,000,000, so decision 12 keeps it): stream 12208,
`Q.nonnegative(sign(x)*sign(conjugate(x)))` under `Q.negative(re(x))`,
goes from None to True, and satassume answers None. The argument:
`re(x)` is a finite negative real. Every infinite `x` has `re(x)` in
`{+-oo, 0, nan}` (decision 7), none of which is finite and negative, so
`x` is finite and nonzero. Then `sign(x)*sign(conjugate(x)) =
(x/|x|)*(conjugate(x)/|x|) = |x|**2/|x|**2 = 1`, which is nonnegative. Gate2
answers do not change, and nothing contradicts. Two cases of the public
wester suite come back (decision 11).

The converse integer axiom for sums (#28, closes #23; design.md "Terms:
`Add`") changes no answer on either corpus. It helps queries outside them,
for example `Q.real(gamma(x + 1))` under `Q.real(x) & ~Q.integer(x)` (now
True). It also makes both corpora faster. On a pinned pareto1 core, three
rotating rounds, medians: on a2428ca (after #29) gate2 goes from 33.41 s
to 32.17 s (-4%) and every 8th stream query from 35.40 s to 31.78 s
(-10%); on fb92e31 (before #29) it was 31.75 s to 29.96 s and 32.59 s to
30.72 s (means, about -5%).

The rlimit goes back to 1,000,000 (#31, design.md decision 12) and
changes no answer on either corpus (stream 116.5 s, gate2 18.9 s, against
119.6 s and 20.7 s at f2d67e8, six local jobs). It is measured on the
bench site's 553 public queries instead (one fresh process per query, four
at a time, local): 42 took over 10 s at f2d67e8, 19 do now, 21 did at
fb92e31; the total time goes from 1,081 s to 570 s. Nothing contradicts,
and seven answers become `None`. Each was right, so this is a loss of
completeness only:

- simplipy, `cos(atan(tan(x))) = Abs(cos(x))` for imaginary `x = i*y`
  (True): `tan(i*y) = i*tanh(y)` with `|tanh(y)| < 1`, so
  `atan(i*tanh(y)) = i*y` and both sides are `cosh(y) > 0`.
- simplipy, `cosh(asinh(tan(x))) = Abs(1/cos(x))` for imaginary `x = i*y`
  (True): `asinh(i*tanh(y)) = i*asin(tanh(y))`, and
  `cos(asin(tanh(y))) = sqrt(1 - tanh(y)**2) = 1/cosh(y) = |1/cos(i*y)|`.
- simplipy, `tan(asin(Abs(x))) = Abs(tan(asin(x)))` for real `|x| < 1`
  (True): `tan(asin(t)) = t/sqrt(1 - t**2)` is odd and nonnegative for
  `t >= 0`.
- simplipy, `tanh(asinh(Abs(x))) = cos(atan(1/x))` for imaginary
  nonzero `x = i*y`, `1/x != +-I` (False): the left side is
  `|y|/sqrt(1 + y**2)`, in `(0, 1)`. For `|y| > 1`,
  `atan(-i/y) = -i*atanh(1/y)` and the right side is `cosh(atanh(1/y)) >=
  1`; for `|y| < 1`, `atanh(1/y) = r +- i*pi/2` with `r` real and nonzero,
  and the right side `cos(+-pi/2 - i*r)` is `+-i*sinh(r)`, not real.
- wester, `sqrt(-2 + sqrt(-5))*sqrt(-2 - sqrt(-5)) = 3` (True): the two
  radicands are conjugate and off the negative real axis, so the
  principal roots are conjugate and the product is `|-2 + i*sqrt(5)| = 3`.
- wester, `Abs(1/(a + I/a + I*b)) = 1/sqrt(a**2 + (1/a + b)**2)` for real
  `a != 0`, `b` (True): `a + i*(1/a + b)` has that modulus, which is
  positive, and `|1/w| = 1/|w|`.
- wester, `sign(k*x**n - k*y**n) = 1` under `x > y > 0`, `k > 0`, `n <= 0`
  (False): for `n < 0`, `t -> t**n` decreases on `(0, oo)`, so the sign
  is -1; for `n = 0` the difference is 0.

Three of them (the fourth to sixth) were definite at fb92e31 too: #27 and
#28 made their checks larger, and the 2,000,000 limit hid that. The case
`n > 0` of the last one (decision 11) is lost in the form of
tests/test_limits.py, `Q.zero(sign(...) - 1)`, which needs about
1,130,000 steps; `Eq(sign(...), 1)` is still True at 1,000,000.

The bench site found two more of these losses at 8cf915f (#31). Its
adapter asks `Q.zero(lhs - rhs)` for a query `Eq(lhs, rhs)`, so it uses
the larger form, and both were True at 2,000,000 and are `None` now,
without a timeout. Both answers were right; a `None` is never wrong, and
the limit stays at 1,000,000 because 2,000,000 tripled the bench
timeouts (decision 12):

- wester, `sign(k*x**n - k*y**n) = 1` under `x > y`, `y > 1/10`,
  `x < 10`, `k > 0`, `0 < n < 10`, all real (True). This is the case
  `n > 0` above in the site's form: `y > 0`, and `t -> t**n` increases on
  `(0, oo)` for `n > 0`, so `x**n > y**n` and `k*(x**n - y**n) > 0`.
  Asked as `Eq(sign(...), 1)` it is still True. Rewriting `Q.zero(t + c)`
  for a number `c` as `Q.eq(t, -c)` would recover it; that is #34, not
  done here.
- simplipy, `tan(acos(Abs(x))) = Abs(tan(acos(x)))` for real `|x| <= 1`,
  `cos(acos(|x|)) != 0`, `cos(acos(x)) != 0` (True), the `acos` twin of
  the `asin` case above. `cos(acos(x)) = x`, so `x != 0`; for real `t` in
  `[-1, 1]`, `t != 0`, `acos(t)` is in `[0, pi]` with sine
  `sqrt(1 - t**2) >= 0`, so `tan(acos(t)) = sqrt(1 - t**2)/t`. The left
  side is `sqrt(1 - x**2)/|x|`, and so is the absolute value of the right
  side. It needs more than 1,000,000 steps in the site's form;
  `Eq(...)` itself is `None` even at 8,000,000.

#33 leaves the converse integer axiom of #23 out of sums without free
symbols (design.md decision 13). No stream or gate2 answer changes; of
the 553 public queries, asked as given, none is lost and one comes back:
`sqrt(-2 + sqrt(-5))*sqrt(-2 - sqrt(-5)) = 3`, True, argued above. (In
the site's form `Q.zero(lhs - rhs)` it was True at 8cf915f already.)

#39 bounds the growth of z3's Groebner bases (design.md decision 15). No
stream or gate2 answer changes. Of the 552 public queries in the site's
form `Q.zero(lhs - rhs)`, none is lost and three are decided:

- simplipy, `cosh(asinh(tan(x))) = Abs(1/cos(x))` for imaginary `x`
  (True), argued above (lost at #31). It is an rlimit-edge case: the
  deciding check stops after about 1,001,000 steps and is unknown with
  a limit of 990,000, so it has no test.
- wester, `sign(k*x**n - k*y**n) = 1` under `x > y`, `y > 1/10`,
  `x < 10`, `k > 0`, `0 < n < 10` (True), argued above (lost at #31; the
  test of decision 11 passes again).
- wester, `sqrt(x*y*Abs(z)**2)/(sqrt(x)*Abs(z)) = sqrt(y)` for complex
  `x`, `y`, `z` with `z != 0`, `re(x) < 0 <= im(x)`, `re(y) < 0 <= im(y)`
  (False). `|z|**2` is positive, so the numerator is `|z|*sqrt(x*y)`
  and the left side is `sqrt(x*y)/sqrt(x)`. The principal arguments of
  `x` and `y` are in `(pi/2, pi]`, so their sum is in `(pi, 2*pi]`, and
  the principal argument of `x*y` is that sum minus `2*pi`. So
  `sqrt(x*y) = -sqrt(x)*sqrt(y)`, the left side is `-sqrt(y)`, and that
  equals `sqrt(y)` only for `y = 0`, which `re(y) < 0` excludes. The
  bench's reference timed out on it.

#39 also makes the wall-clock backstop a budget of the whole query, of
which each side of a decision gets half (design.md decision 16). It
changes no answer on the stream, gate2, or the 552 public queries in the
site's form; on those, the queries over 10 s go from 21 to 6 (on a loaded
machine; all of them `None` before and after).

Decisions 17 (`Piecewise` as an `If` chain) and 18 (an inverse undoes its
forward function on the principal strip; `|re asin|`, `|re atan| <=
pi/2`) change no gate2 answer and no CONTRADICT appears. On the stream, 24
queries (24 distinct, 15658 to 15732) move from `None` to False, so "more" goes from 119 to 143 and "agree" from 16,112 to 16,088:

- **The value of a `max`-like `Piecewise` is one of its branches**
  (`Q.positive_infinite` and `Q.negative_infinite` of
  `Piecewise((x, Q.ge(x, y)), (y, Q.lt(x, y)), (nan, True))` and its
  permutations over `x`, `y`, `z`, under all real or all negative; False).
  The conditions are predicates, which z3assume does not read as
  `Piecewise` conditions (decision 17: a free Boolean each), but whatever
  they mean, the value is that of one branch: `x`, `y` or `z`, finite
  reals, or `nan`, and none of them is `+oo` or `-oo` (`nan` is no
  infinity, special-values V1).

Of the 553 public queries in the site's form `Q.zero(lhs - rhs)`, none
is lost and 26 are decided (25 True, 1 False), all matching the bench's
label and none on a contingent case; 6 take over 10 s, as before (all
`None`). By class:

- **`real_root` of a nonnegative real** (simplipy: `real_root(w, n) =
  w**(1/n)` for `n = 5, -5`, `w = acos(x)`, `acosh(x)` or `cosh(x)`
  given `w` real (`x` real for `cosh`), and nonzero for `n < 0`; True). SymPy writes `real_root(w, n)`
  as `Piecewise((Abs(w)**(1/n)*sign(w), Eq(im(w), 0)), (w**(1/n),
  True))`. `w` is real, so the first branch is taken. A real `acos(x)`
  lies in `[0, pi]`, a real `acosh(x)` in `[0, oo)` and `cosh(x)` in
  `[1, oo)`, so `w >= 0`, and
  for `w > 0` `|w| = w`, `sign(w) = 1`; for `w = 0` (only `n = 5`) both
  sides are 0.
- **`real_root` of a positive real** (simplipy: `log(real_root(x, 7)) =
  log(x)/7` for real `x` with `re(x) > 0`; `real_root(exp(x), n) =
  exp(x/n)` for `n = -3`, `-7`, given `exp(x)` real and nonzero and
  `x` real or `|im(x)| < pi`; True). For `x > 0` the first branch is
  taken and is `x**(1/7)`, the positive real root, whose `log` is
  `log(x)/7`. For `exp(x)` SymPy writes
  `Piecewise((exp(re(x)/n)*sign(exp(x)), Eq(exp(re(x))*sin(im(x)), 0)),
  (exp(x)**(1/n), True))`: `exp(x)` real means `sin(im x) = 0`, so the
  first branch is taken, and with `|im x| < pi` (or `x` real) `im x = 0`,
  so `x` is real, `sign(exp(x)) = 1` and the value is `exp(x/n)`.
- **`asin(sin x) = x`, `atan(tan x) = x`, `acos(cos x) = x` on the real
  axis** (simplipy, real `x` in `(-1, 1)` for `asin` and `atan`, in
  `(0, 3)` for `acos`; True): these intervals lie in `[-pi/2, pi/2]`
  and `[0, pi]`, where `asin` and `acos` are the real inverses of `sin`
  and `cos`, and in `(-pi/2, pi/2)`, where `atan` is that of `tan`.
- **The same with a bounded inner value** (simplipy: `acos(cos(sin x))
  = |sin x|` and `atan(tan(cos x)) = cos x` for real `x`; True): `sin
  x`, `cos x` are in `[-1, 1]`, inside `[-pi, pi]` (where `acos(cos v)
  = |v|`) and `(-pi/2, pi/2)`.
- **An imaginary inner value** (simplipy: `asin(sin(tanh x)) = tanh x`,
  `atan(tan(sin x)) = sin x`, `atan(tan(tanh x)) = tanh x` for
  imaginary `x = I*y`, with `cosh x != 0`; True): `tanh(I*y) = I*tan y`
  and `sin(I*y) = I*sinh y` are finite (`cos y = cosh x != 0`) and have
  real part 0, so they lie on the open strip `|re v| < pi/2`, where
  `asin(sin v) = v` and `atan(tan v) = v` (design.md decision 18: `sin`
  and `tan` are injective there and their values avoid the cuts).
- **`atan(tan z) = z` on the open strip** (simplipy, complex `z` with
  `|re z| < pi/2`, or real `z` in `(-pi/2, pi/2)`; True): `tan` is
  injective there and its values are finite and off the cuts of `atan`,
  and `atan` takes values on the open strip off its cuts (decision 18).
- **`atan(tan z) = z` fails off the closed strip** (simplipy, complex `z`
  with `|re z| > pi/2` and `cos z != 0`; False): `tan z` is finite, and
  where `atan(tan z)` is finite its real part is in `[-pi/2, pi/2]`
  (decision 18; the cuts included), so it is not `z`; an infinite value
  is not `z` either.
- **The hyperbolic inverses on the reals** (simplipy: `asinh(sinh x) =
  x`, `atanh(tanh x) = x`, `acosh(cosh x) = |x|` for real `x`; True):
  `sinh` is a bijection of R, `tanh` one of R onto `(-1, 1)`, where
  `atanh` is real, and `cosh x = cosh|x|` with `acosh` the inverse of
  `cosh` on `[0, oo)`.

Decisions 19 (the signs of `cos` and `sin` on `[-4*pi, 4*pi]`) and 20
(`log(exp(w))` and `log(b**x)` on the strips `-pi < im(w) - 2*pi*k <=
pi`) change no answer on gate2, every8 or the stream, and no CONTRADICT
appears: the agree, more and less counts are those of decisions 17
and 18. The only difference is the wall-clock backstop (decision 16):
one gate2 query and one stream query hit it in this run (another stream
query did before), all `None` before and after; alone, each takes about
2.3 s on both trees, so these are the load of the machine.

Of the 553 public queries in the site's form `Q.zero(lhs - rhs)`, none
is lost and 23 are decided (14 True, 9 False), all matching the bench's
label and none on a contingent case; 4 take over 10 s (6 before; all
`None`). By class:

- **`|cos x| = -cos x`, `|sin x| = -sin x` over several periods** (real
  `x` in intervals between `-7*pi/2` and `-pi`; 4 True, 3 False).
  `|f| = -f` iff `f <= 0`. The True cases lie in closed or open intervals
  where `f <= 0` (`cos <= 0` on `[-7*pi/2, -5*pi/2]`, `sin <= 0` on
  `[-3*pi, -2*pi]`), the False cases in open ones where `f > 0`
  throughout (`cos > 0` on `(-5*pi/2, -3*pi/2)`, `sin > 0` on `(-2*pi,
  -pi)`), so there `|f| = f != -f` at every point. The signs: `cos` is
  `> 0` on `((2*j - 1/2)*pi, (2*j + 1/2)*pi)` and `< 0` on `((2*j +
  1/2)*pi, (2*j + 3/2)*pi)`, `sin` is `> 0` on `(2*j*pi, (2*j + 1)*pi)`
  and `< 0` on `((2*j - 1)*pi, 2*j*pi)`, with the zeros at the ends
  (decision 19).
- **`sqrt(exp(z)) = exp(z/2)` past the principal strip** (complex `z`
  with `im z` in `(pi, 3*pi]` or `(-3*pi, -pi]`; False). `sqrt` is the
  principal root: `re sqrt(w) > 0`, or `re = 0` and `im >= 0`. `exp(z/2)
  = e**(a/2)*(cos(b/2) + I*sin(b/2))` with `b/2` in `(pi/2, 3*pi/2]`:
  `cos(b/2) < 0`, or `b/2 = 3*pi/2` and `exp(z/2) = -I*e**(a/2)`, with
  negative imaginary part; so `exp(z/2)` is never that root (for `b/2` in
  `(-3*pi/2, -pi/2]`: `cos < 0`, or `b/2 = -pi/2` and the value is
  `-I*e**(a/2)` again).
- **`atan(tan z) = z` for real `z` in `(pi/2, 3*pi/2)`** (False): `cos z`
  is `< 0` there, so `tan z` is a finite real and `atan(tan z)` lies in
  `(-pi/2, pi/2)`, below `z`.
- **`log(tan(x/2 + pi/4)) = asinh(tan x)` for real `x` in `(pi/2,
  3*pi/2)`** (False): `x/2 + pi/4` lies in `(pi/2, pi)`, where `tan < 0`,
  so the left side has imaginary part `pi`; `cos x != 0` there, so `tan
  x` is a finite real and `asinh` of it is real.
- **`log(exp(w)) = w` on the strip** (complex `w` with `-pi < im w <=
  pi`, also with `re w` bounded or `exp(w) != 0` given; `w = z**2` with
  `|z| < 1`, where `|im z**2| = 2*|a*b| <= a**2 + b**2 < 1`; True):
  decision 20, `log(exp(w)) = w` exactly on that strip.
- **`log(b**x) = x*log(b)`** (`b = 2` and complex `x` on the strip, so
  `|im(x*log 2)| <= pi*log 2 < pi`; `b = x` real in `(-1, 1)`, nonzero,
  where `im(x*log x) = pi*x` for `x < 0`, in `(-pi, 0)`; `b = x > 0` with
  exponent 3; `b = z` with `re z > 0` and exponent 2, where `2*arg z` is
  in `(-pi, pi)`; True): `b**x = exp(x*log b)` (principal), and decision
  20.
- **`log(1/y) = -log(y)` off the negative axis** (`y = cos x` for real
  `x` with `|x| < pi/2` (as `|log(cos x)|`, since `0 < cos x <= 1`) and
  for complex `x` with `|re x| < pi/2`, where `re cos x = cos a * cosh b
  > 0`; `y = log x` for imaginary `x`, where `im log x = +-pi/2`, and for
  a nonzero integer `x`, where `log x` is `>= 0` or has imaginary part
  `pi`; `y = cosh x > 0` for real `x`; True): `im(-log y) = -arg(y)` is
  in `[-pi, pi)`, on the strip unless `arg y = pi`, and none of these
  `y` is a negative real.

Pinned and interleaved (one core, `--jobs 1`, 3 rounds, medians), main
9e59c6f against this change: gate2 30.31 s -> 31.10 s (+2.6%), every8
31.20 s -> 31.50 s (+0.9%). 239 of gate2's 2863 queries and 69 of
every8's 2029 have a number beyond `pi` and so get the signs beyond
`pi` (decision 19).

## Speed

z3assume is about 50 to 60 times slower than satassume. The latest
measurement, at f2d67e8 (24 Oct 2026, pinned pareto1 core, three rotating
rounds, medians), gives 58x on gate2 (32.17 s against 0.557 s) and 47x on
every 8th stream query (31.78 s against 0.681 s); the history is in #15.
The first measurement, 70 to 80 times, was taken with
`bench-container` on one Cortex-A720 core (BENCH_CPU=10, 2.5 GHz), Python
3.13, z3-solver 5.3.1, one process per run, three interleaved rounds after
a warmup (spread under 2%), 23 Oct 2026, z3assume 7ce67e8 (this PR's tools,
encoding as on main) and satassume 9bafaa5:

| stream | queries | satassume | z3assume | ratio |
|---|---|---|---|---|
| every 8th query of the refine stream | 2,029 | 1.08 s | 75.8 s | 70x |
| gate2 | 2,863 | 0.92 s | 72.8 s | 79x |

Per query z3assume takes 20 ms at the median, 86 ms at p90, 405 ms at p99
and 0.89 s at most on the stream sample (gate2: 12, 49, 197 ms, 0.80 s);
satassume about 0.5 ms. Each query is two fresh z3 checks. Both tools
answer a repeated `(prop, assum)` pair from a memo (z3assume's tool from
its own per-worker memo), so repeats cost little on both sides. No check
hit the 10 s backstop; on the full stream 195 checks (in 194 queries) came back `unknown`
from the rlimit or from z3's incompleteness (the answer is then None).
The setup is in `~/dev/z3assume-bench/` on Tilo's machine.
