# A wider zero-free region and its exact bootstrap limit

The local continuation proves a wider exclusion for literal zeta zeros.
It uses a positive term already retained in the full signed phase budget,
without changing the phase coefficients or assuming cancellation in the
remaining ordinary-prime tail. The resulting iteration has a proved
explicit limit. That limit does not reach the critical line.

## The positive reserve

Write `rho = beta + i*t`, `d = 1-beta`, and take the existing sampling
line `sigma = 1+(13/4)*d`. The original budget retains the constant-mode
auxiliary-pole term

```text
a_0 * c(sigma) / (tau(sigma)-1),

tau(sigma) = (1 + sqrt(1+4*sigma^2))/2,
c(sigma) = sigma / (2*tau(sigma)-1).
```

`phaseContactExact_constantPoleReserve_gt` proves that this term is
strictly greater than `2/25` throughout `1 <= sigma <= 4/3`. It uses the
existing exact family's proved bound `a_0 >= 9/50`, the established
`c(sigma) >= 4/9`, and `0 < tau(sigma)-1 < 1`. The earlier final zero
exclusion used only the reserve's nonnegative sign.

Define

```text
L(t) = max(13/10, log(|t|+2)),
A(t) = (366*L(t)-113)/2160,
S = 11/625,     R = 2/25,     H = 4/39.
```

Every actual nontrivial zero has `log(|t|+2) > 13/10`, by the existing
eta height exclusion. The maximum makes the displayed allowance valid
as a positive function at every real ordinate.

`phaseContactExact_poleReserve_strict_zero_budget` proves

```text
S + R*d < A(t)*d                 whenever d <= H.
```

All arithmetic and analytic premises are discharged for the original
zeta function. The complete signed prime work and exact pole budget
remain available in the upstream theorem. Strictness comes from the
positive reserve, so the resulting closed-region nonvanishing theorem
does not rely on a limit with an unresolved endpoint.

## An actual feedback step

For a previously proved exclusion `delta <= d`, define

```text
F_t(delta) = min(H, (S + R*delta)/A(t)).
```

`zetaPoleReserveStep_lt_one_sub_re` proves `F_t(delta) < d` for the
same actual zero. If `d > H`, the sampling cap suffices; otherwise the
strict arithmetic budget proves the step. This is a feedback theorem
with an independently available starting bound, not an assumption of
the new exclusion.

`zetaSignedPole_margin_lt_reserveStep` proves that feeding the preceding
signed-pole margin into this step strictly improves it at every
ordinate allowed by the proved zero-height floor.

Starting at `delta_0=0` and applying `F_t` repeatedly,
`zetaPoleReserveIterate_mono` and `tendsto_zetaPoleReserveIterate` prove
monotone convergence to the unique fixed point

```text
B(t) = min(H, S/(A(t)-R))
     = min(4/39, 4752/(45750*L(t)-35725)).
```

Theorems `zetaPoleReserveStep_fixed_unique` and
`zetaPoleReserveStep_strict_improvement` identify both the endpoint and
the strict gain below it. Every finite iterate is separately proved to
exclude actual zeros. The direct strict budget also proves `B(t) < d`,
including the limiting endpoint.

This establishes a working instance of the proposed iterative strategy,
and its limitation: this particular map stops at `B(t) <= 4/39`. At
large heights it has the same leading reciprocal-logarithm coefficient
as the preceding region, with a better denominator offset. Repeating
this fixed map cannot move the bound to `1/2`; another mathematical
improvement is needed to change its fixed point or its sampling range.

## Literal zero-free region

Let the previous margin be

```text
m_0(t) = 792/(7625*log(|t|+2)-2000),
m(t) = max(m_0(t), B(t)).
```

`nontrivialZetaZero_mem_poleReserve_strip` proves, unconditionally,

```text
m(t) < Re(rho) < 1-m(t)
```

for every genuine nontrivial zeta zero. The maximum preserves the
previous region even at low ordinates where there are no nontrivial
zeros. `zetaSignedPole_margin_lt_poleReserveFixed` proves strict widening
where `log(|t|+2) >= 13/10`, including every possible zero ordinate.

`riemannZeta_ne_zero_of_poleReserve_margin` proves literal nonvanishing
on the closed right-edge region, explicitly away from the pole at one.
This is a project refinement within classical zero-free-region methods;
no historical novelty or best-published bound is claimed.

The shape is shown schematically below. `#` is excluded, blank space is
still allowed by the proved bounds, and `:` is the critical line. The
central empty band uses the independent eta exclusion. The picture is
not to scale; `P` marks the pole at one.

```text
                         Im(s)
                           ^
        0                  1/2                  1
        |#                  :                  #|  +large t
        |##                 :                 ##|
        |####               :               ####|
 +sqrt3 |#######################################|
      0 |###################+###################P --> Re(s)
 -sqrt3 |#######################################|
        |####               :               ####|
        |##                 :                 ##|
        |#                  :                  #|  -large t
```

RH would require excluding every remaining point off the critical line.
The edge widths decrease with absolute height. The feedback limit proved
here leaves an interior strip and does not perform that final exclusion.

## Feeding the gain into the arithmetic estimates

The response is the original quotient `Q(s)=zeta(s)/zeta(2*s)`. The new
common radius about `3/2+i*y` is

```text
r(y) = 1 + min((|y|-1)/2, m(2*|y|+3)/2),       |y|>1.
```

`squarefreeEuler_reserve_disc_safe` proves that the whole closed disc
avoids the numerator pole and every zero or pole of the denominator.
For the doubled argument, the exact horizontal requirement is
`2*(r-1) <= m`, so this also removes the spare factor of two in the
previous conservative radius. The radius is larger than the previous
one whenever `|y| >= 3/2`, which includes every actual zero ordinate.

`analyticOnNhd_squarefreeEulerResponse_reserve` proves analyticity on a
neighbourhood of that disc. The generalized theorem
`exists_squarefreeEuler_variable_radius_bound_of_analytic` transports
any proved disc to the original marked arithmetic filters. Its actual
instantiation `exists_squarefreeEuler_reserve_radius_bound` gives one
positive constant `C_y`, simultaneously for every `0 < r <= r(y)`, all
finite prime sieves `S`, all eligible squarefree marks `P`, and all
complex polynomials `p`:

```text
norm(response(p,S,P,N,3/2+i*y))
 <= C_y * squarefreeEulerBudget(3/2-r,S,P) * r^(-N)
          * sum_k norm(p_k)*r^(-k).
```

The larger domain permits a smaller geometric base. The finite Euler
budget and common Cauchy constant are still paid: the theorem does not
claim that enlarging the radius decreases every complete numerical
bound, or that this alone handles every growing-sieve tradeoff.

The independent cofinal signed bound on the ordinary-prime tail remains
open. These complete squarefree estimates do not prove it. RH remains
unproved.

## Stronger external inputs

The [March 2026 preprint by Bellotti, Trudgian and Yang](https://arxiv.org/html/2603.21490v1)
states nonvanishing for `t >= 3` and `sigma > 1-1/(4.896 log(t))`.
Its smoothing and reflected-zero argument is a candidate for formalization.
That explicit theorem has not been imported or kernel-audited here.

The present radius transport accepts any proved larger analytic disc.
External theorems can therefore strengthen this chain after their complete
dependencies are checked. The prime-tail gap must still be assessed using
the resulting estimates; a wider edge region alone does not close it.

## Local verification

The modules are root-imported and checked with the pinned Lean toolchain.
Verification includes direct compilation with warnings as errors,
focused and full builds, whole-project declaration lint, focused verbose
lint, explicit terminal-theorem axiom checks, and the compiled-environment
soundness audit. Allowed transitive axioms are only `propext`,
`Classical.choice`, and `Quot.sound`. These are local validation results; remote CI is checked separately on the exact commit.
