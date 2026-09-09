# Infinite phases and exact contact geometry

`ZetaSignedInfiniteHeight` proves an unconditional improvement to the
repository's zero-free region. The phase-contact chain, culminating in
`ZetaPhaseExactOptimizer`, proves an exact unique optimizer among all finite
or infinite admissible phase sequences for a specified cost and shift.
These are separate results. Neither proves RH or the open signed Suzuki
arithmetic floor.

## A complete infinite phase family

The fourth-power kernel is multiplied by the Poisson kernel of radius
`1/8`. After scaling by `2^24`, its cosine coefficients are

```
a0 = 712249344
a1 = 1162805760
a2 = 624545856
a3 = 212253192
a(n+4) = 43046721 / 8^n,  n >= 0.
```

`zetaInfinitePhaseKernel_denominator_identity` proves exactly

```
(65 - 16 cos t) P(t) = 8455716864 (1 + cos t)^4.
```

The denominator is positive. The proof establishes absolute convergence
and the interchange of the phase and prime-power series before deriving
`neg_logDeriv_riemannZeta_infinite_height_nonneg`. The full infinite family
of local pole sums is retained in
`infinite_height_localZetaPoleSum_re_le`; selecting one zero preserves its
entire analytic multiplicity.

For every actual nontrivial zero `rho = beta + i gamma` with `|gamma| >= 1`,
`nontrivialZetaZero_mem_infiniteHeight_reciprocal_log_strip` proves

```
1 / (27500 log(|gamma| + 22)) < beta
beta < 1 - 1 / (27500 log(|gamma| + 22)).
```

`fiveHeight_margin_lt_infiniteHeight` compares this with the previous
denominator `28000`. This is a modest improvement within the repository's
formal bounds, not a claim to improve the published zero-free-region record.

## What the sparse-contact theorem actually says

For nonnegative coefficients `a(n)`, write

```
P(t) = sum_n a(n) cos(n t)
w(0) = 1,  w(n) = (n+1)/2 for n >= 1
A = sum_n w(n) a(n)
J = (4/17) a(1) - (4/13) a(0)
D = (8801/500000) A - J.
```

The hypotheses are a finite cost sum and `P(t) >= 0` at every angle.
The cost is connected to the actual zeta estimate by
`phaseContactCost_controls_logHeight`; `J` is the selected-zero source less
the real-axis pole at shift ratio `13/4`. This shift is fixed throughout
the certificate theorem.

Five exact contact cosines and five positive rational weights are specified
in the Lean source. If `mu(i)` is a weight and `theta(i)` its angle, define

```
g(n) = (8801/500000) w(n) - source_coefficient(n)
       - sum_i mu(i) cos(n theta(i)).
```

`phaseContactDeficit_eq_contacts_add_penalties` proves the exact identity

```
D = sum_i mu(i) P(theta(i)) + sum_n a(n) g(n).
```

`phaseContactPenalty_nonneg` proves `g(n) >= 0` for every natural frequency.
`one_div_sixtyFour_le_phaseContactPenalty` proves `g(n) >= 1/64` outside

```
S = {0, 1, 2, 3, 4, 7, 10, 13, 24}.
```

The low frequencies are checked with rational Chebyshev recurrence
calculations. Beyond frequency 37, the growing cost and the total contact
mass prove the bound uniformly. No sampled cosine inequality, floating-point
answer, or external numerical solver enters the Lean proof.

Consequently, `phaseContact_offSupport_mass_le_sixtyFour_mul_deficit` proves

```
sum_{n outside S} a(n) <= 64 D.
```

`phaseContact_contact_values_le_deficit` bounds the positively weighted
contact values by the same deficit. A good kernel must therefore be small
at the contact angles and spend little coefficient mass on frequencies
with large penalties. This is a quantitative explanation for the sparse
frequency pattern. The exact finite set appears in a theorem that applies
to infinite phase families as well as finite ones.

This certificate does **not** prove that an exact optimizer has precisely
support `S`, that any numerical candidate is feasible, or that the stated
upper efficiency bound is attained. The deficit is measured from this
certificate's bound, not from an already identified exact optimum.

## Numerical exploration and the next proof obligation

The exploratory linear programs found persistent small coefficients at
frequencies `7, 10, 13, 24` under the linear cost, including with frequencies
through 64 available and denser angle grids. Removing these coefficients
and reoptimizing worsened the sampled objective, with the strongest effect
at frequency 7 and a very small effect at 24.

Sharpening the cost changes the pattern. Logarithmic height costs favor
pairs such as `7,8`, `11,12`, and `15,16`. The persistent conclusion is the
contact-and-penalty mechanism; the particular residue pattern is sensitive
to the allowance used. No intrinsic arithmetic interpretation for zeta has
been established.

The exact optimizer has **four** interior contact cosines, as proved by
`phaseContactExactKernel_eq_zero_iff`. The fifth contact in the rational bound is
part of a valid approximate certificate; it should not be imposed as an
extra equality in the optimizer equations. In particular, the numerical
kernel is very close to zero at angle pi but has a small positive value
there. Imposing an exact zero there overconstrains the candidate.

The fixed-shift contact system now has an exact existence and isolation
proof, described below. Its matching dual bound is proved at every natural
frequency, including those outside every finite search. Global kernel
positivity and attainment are also proved. Jointly optimizing coefficients
and shift remains open; a new square identity eliminates the shift
symbolically for any fixed admissible coefficient family.

The purpose of the exact optimizer proof is structural: prove which
frequencies are necessary, whether the normalized optimizer is unique, and
which contact constraints force its support. Certifying decimal coefficients
alone is not the research target. Comparing those conclusions under sharper
height costs is then a test of whether the structure reflects the estimate
or offers additional leverage on zeta.

`scripts/probe_zeta_phase_optimizer.py` reproduces the fixed-shift and
free-shift stationary candidates with mpmath. Its output is explicitly
exploratory. The candidate at fixed shift has a well-conditioned numerical
dual system, and exploratory factorization leaves a degree-16 factor with
positive Bernstein coefficients after splitting `[-1,1]` in two. These
observations led to the completed positivity proof. The exact factorization,
rational Bernstein center, and error transfer all have Lean counterparts.

## Exact contact solution and its coefficient family

The new chain is `ZetaPhaseChebyshevBounds`, `ZetaPhaseContactSystem`,
`ZetaPhaseContactRootData`, `ZetaPhaseContactJacobian`,
`ZetaPhaseContactRoot`, `ZetaPhaseContactPrimal`, and
`ZetaPhaseContactFactorization`. It addresses the fixed shift `13/4` and
the linear height allowance defined above.

`exists_unique_phaseContactRoot` proves that the nine dual contact equations
have a unique solution in a specified real ball around an exact rational
center. The coordinates are four cosines, four contact masses, and an
efficiency parameter. Exact Chebyshev secants retain the cosine–mass cross
terms. Lean checks the central residual and both matrix residuals before
Banach's theorem supplies a root. This is an existence proof, not an
assumption that a numerical solver converged.

`phaseContactExactRoot_mass_pos` and
`abs_phaseContactExactRoot_cosine_lt_one` prove that the masses are positive
and the cosines are interior. `phaseContactExactRoot_cosine_strictAnti`
proves that all four contact cosines are distinct.

The same contact matrix determines the coefficients. If `M` is the exact
linearization at this root, the normalized coefficient vector is defined by

```
a(i) = (M inverse)(8,i).
```

`isUnit_phaseContactExactRoot_jacobian` discharges invertibility.
`phaseContactExactCoefficients_cost` and
`phaseContactExactCoefficients_source` prove exactly

```
sum_i a(i) w(n(i)) = 1
sum_i a(i) source_coefficient(n(i)) = lambda.
```

`phaseContactExactKernel_contact` and
`hasDerivAt_phaseContactExactKernel_contact` prove zero value and zero
actual derivative at all four contacts. With this geometry fixed,
`phaseContactExactCoefficients_unique` proves that those eight conditions
and the cost normalization determine the entire coefficient vector in the
selected nine-frequency span.

`phaseContactExactCoefficients_pos` proves that all nine coefficients are
strictly positive, including frequency 24. Thus its very small coefficient
is present in the exact family and is not a rounding artifact. Here nine
includes the constant term; there are eight nonconstant frequencies.

Finally, `exists_phaseContactExactPolynomial_quotient` proves

```
P(x) = product_j (x-q(j))^2 * R(x),   degree(R) <= 16.
```

This removes the four flat contact zeros before the positivity estimate.
`phaseContactExactQuotient_lower` now proves `R >= 483/100000` on `[-1,1]`.

The all-frequency bound, attainment, and uniqueness are now proved.
`existsUnique_phaseContactOptimizer` includes nonnegative coefficients,
the genuine cost sum converging to one, global kernel nonnegativity, and
source exactly equal to the contact root's efficiency.

The older five-contact rational certificate remains valid and separate.
Its all-frequency penalties cannot simply be reassigned to the new exact
four-contact root. This slice does not change the proved zeta zero bound,
prove the open signed arithmetic floor, or establish that this particular
frequency count is intrinsic to zeta.

## All-frequency duality and uniqueness at the bound

`phaseContactExactPenalty_eq_zero_iff` proves that the exact four-contact
penalty vanishes precisely on `S`. At every other natural frequency,
`one_div_tenThousand_le_phaseContactExactPenalty` proves a lower bound of
`1/10000`. The finite part uses exact rational enclosures; beyond frequency
35 the growing cost and bounded contact mass give a uniform argument.

`phaseContactExactDeficit_eq_contacts_add_penalties` preserves the complete
identity

```
lambda A - J = sum_j mu(j) P(theta(j)) + sum_n a(n) penalty(n).
```

All series converge under the actual finite-cost hypothesis.
`phaseContactSource_le_exactContactBound` therefore bounds every admissible
finite or infinite phase family by the same `lambda A`.
`phaseContactExact_offSupport_mass_le` bounds coefficient mass outside `S`
by `10000 (lambda A-J)`. Any positive coefficient outside `S` makes the
source inequality strict.

`phaseContactExactFamily_unique_at_bound` proves that an admissible
cost-one family attaining `lambda` must be the mathematically defined
inverse-row family. The proof first forces finite support, then uses
nonnegativity to turn the four contact values into zero derivatives, and
finally applies the exact matrix uniqueness theorem. Finite support is a
conclusion, not a restriction on the competitors.

## Completed positivity transfer and exact support

`phaseContactExactPolynomial_eq_factor_mul_quotient` defines a canonical
quotient through eight successive monic divisions and proves its exact
factorization with zero remainder. `phaseContactExactQuotient_eq_three_frequencies`
shows that only frequencies `10,13,24` contribute to this quotient. The six
lower frequencies still enforce the vanishing remainder of the full
polynomial; their information is not discarded from the factorization.

`abs_phaseContactExactCoefficients_sub_center_le` encloses each exact
coefficient within `10^-15` of a rational center. Independently,
`phaseContactQuotientCenter_lower` proves that a rational degree-sixteen
center is at least `1/200` on `[-1,1]`, using two exact Bernstein expansions.
The synthetic-division recurrence retains each intermediate polynomial
before propagating the coefficient errors.
`abs_phaseContactDeflate_high_coeff_sub_center_le` bounds every coefficient
of each high-frequency quotient within `10^-10` of its checked center.
Only then are the three exact high-frequency coefficients combined.
`abs_phaseContactExactQuotient_coeff_sub_center_le` gives coefficient error
at most `10^-5`, and `abs_phaseContactExactQuotient_eval_sub_center_le`
gives uniform evaluation error at most `17/100000`. Subtracting this from
`1/200` leaves the positive lower bound `483/100000`.

Consequently `phaseContactExactFamily_kernel_nonneg` closes global
feasibility. `phaseContactExactFamily_maximizes` compares the actual exact
family with every admissible finite or infinite competitor.
`phaseContactExactFamily_unique_optimizer` characterizes equality.
`phaseContactExactFamily_strict_of_missing_frequency` shows that deleting
any selected frequency and reoptimizing must strictly decrease the source
under the same constraints. `phaseContactExactFamily_nonconstant_count`
proves the exact count of eight nonconstant frequencies. Their small
coefficients are necessary features of this optimum, not rounding noise.

The strict quotient bound also proves that the four contact cosines are
the complete zero set. `phaseContactExactKernel_neg_one_pos` proves the
near-contact at angle pi is strictly positive: it is not a fifth exact zero.

## What the optimizer tells us about the zeta strategy

The successor slice, [Arbitrary spectra and prime recurrence](zeta-general-phases-and-prime-recurrence.md),
now gives actual signed zeta and local-zero inequalities for arbitrary
summable real-frequency families. It retains the prime work, proves a
forced prime-power floor using the shared cosine Gram identity, and
identifies the true leading logarithmic height cost for fixed spectra.
These general theorems do not rely on this particular support or shift.

For this fixed shift and linear height cost, adding more phases, even
infinitely many, cannot improve the optimal source-to-cost ratio. Improving
that ratio requires changing a premise of the optimization, such as the
height allowance or the shift, or retaining arithmetic information that is
not represented by this cost. The proof identifies a precise ceiling for
this particular estimate; it does not show that eight phases are intrinsic
to zeta, or supply the missing signed arithmetic cancellation.

`ZetaPhaseShiftEnvelope` removes one optimization parameter exactly. For
`u=sqrt(a0)`, `v=sqrt(a1)`, and any positive shift `kappa`,
`phaseShiftSource_square_deficit` proves

```
(v-u)^2 - [a1/(kappa+1) - a0/kappa]
  = ((v-u)*kappa-u)^2 / [kappa*(kappa+1)].
```

For `0<a0<a1`, `phaseShiftSource_optimalShift` and
`phaseShiftSource_eq_envelope_iff` prove that the unique best shift for this
fixed family is `kappa=u/(v-u)`, with source `(v-u)^2`. This is a structural
elimination of the shift variable. It does not jointly optimize the
coefficients, and it leaves the full phase kernel and its height cost
unchanged. The fixed-shift optimum above remains specifically at `13/4`.

## Local validation

The preceding infinite-phase and exact-contact slices passed their local
validation gates. The optimizer completion passed direct warnings-as-errors
validation, focused builds, and the full build with 9777 jobs.
Whole-project declaration lint and all eleven verbose module audits passed.
All 72 public theorems in this completion were checked transitively and use
only `propext`, `Classical.choice`, and `Quot.sound`. The source placeholder
and whitespace checks passed. No commit, push, remote CI run, README change,
or generated-status update was performed, in accordance with the current
hold on commits.

The general positive-trigonometric-polynomial method and the duality
principle are classical. Relevant primary references include
[Mossinghoff and Trudgian](https://arxiv.org/abs/1410.3926) and
[Mossinghoff, Trudgian and Yang](https://arxiv.org/abs/2212.06867).
No novelty or improved published record is claimed here.
