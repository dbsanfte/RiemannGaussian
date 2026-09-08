# Completed eta current reconstruction and the weighted arithmetic estimate

The user authorized the full objective on 2026-09-06: **reconstruct the
original leading current and prove the uniform weighted arithmetic
estimate**. The objective remains active until both parts are proved and
verified. The completed [signed endpoint package](eta-signed-endpoint-theorem-plan.md)
provides the actual support, gap, phase, Gaussian, and mixed-matrix inputs.

The immediate arithmetic goal is one independent signed inequality that
contradicts the proved finite-band source comparison for every hypothetical
actual zero strictly right of `1/2`. It suffices to beat the source by
more than the complete error allowance at one admissible scale for that
zero. A fixed positive saving at arbitrarily large scales is a convenient
rate-free route; even a shrinking saving suffices if it exceeds the
allowance. Full decay of the band, a bound for its norm or positive spectral
part, and uniformity in the zero are not requirements. The gamma band was
the first candidate because its source and all discarded ranges are
already controlled. Its independent signed estimate remains open.

The user's subsequent `RiemannGaussian_reduced_product_or_signed_current_steer.md`
sets a stopping criterion for more Gamma/gcd layers. The current slice
confirms both the complete reduced-product formula and exact cancellation
of its nonexceptional prime coefficient after two zeta convolutions.
It also proves `EtaGammaQuadratic.completionBoundary_eighth_tendsto_two_source`
and `completionBoundary_eighth_not_tendsto_zero`: the full coefficient
boundary between the actual clipped square and the complete multiplicative
square tends to `2*S_rho`, with `S_rho!=0`.

The primary attack therefore moves to the memo's signed weighted partial
sums of the actual leading current. The
[signed-current slice](eta-signed-current-partial-sums.md) now proves
`pairedEtaLeadingFluxSignedPartialSum_lower_with_offset` and
`pairedEtaLeadingFluxSignedPartialSum_tendsto_side_infinity_of_re_ne_half`
for every hypothetical off-critical actual zero, using the existing principal
endpoint and summable weighted error. The actual cancellation deficit is
summable, so cancellation across cutoff indices changes the oriented sum
by only a finite total. Exact signed summation by parts retains the terminal
weighted energy and the two summable corrections; its complete Abel
expression inherits the same power lower bound. The independent upper
estimate remains open. A uniform bound would suffice, but any upper rate
strictly below the positive displacement power would also suffice. Neither
the new signed criterion nor the Abel identity establishes that estimate.
The complete and clipped Gamma objects, signs, and allowances remain
available. The coefficient audit does not establish absolute Dirichlet
summability of the prime-square correction for `sigma>1/2`, nor prove
that every possible signed Gamma-boundary argument must fail. It does
rule out treating the full completion boundary as a negligible error.

The preceding Gamma branch followed the user's gamma-reflection steering memo:
the full square on `A=u^8`, `U=u^5` is decomposed by its exact gcd before
combining the conjugate-partner and original channels. The
[gcd and reflection ledger](eta-gamma-gcd-reflection.md) records the
compiled terminal theorems. `EtaGammaGcd.norm_largeGcd_le` controls the
entire original contribution above `G^2>=2A` for `sigma>1/2`.
`EtaGammaReflection.norm_gcdCrossDiagonalTail_le` separately controls
the complete reflected common-gcd diagonal by
`4096*norm(chi(rho#))*norm(chi(rho))/G` throughout the strip, when both
physical thresholds are met. Every unequal-gcd interaction remains in
the exact reflected product. The smaller-gcd core still tends to the
nonzero source; neither it nor the reflected off-diagonal has the needed
independent signed saving. No new zero bound or RH proof follows.

The [coprime radical slice](eta-gamma-radical-bulk.md) evaluates the
divisor coefficient separately inside each gcd block. The compiled
`EtaCoprimeRadical.coefficient_square_eq_signed_radical` gives the exact
eligible-radical sign and its cutoff reversal through `n=N^2`, and
`abs_coefficient_le_one` removes the divisor-multiplicity cost there.
`EtaGammaGcd.norm_smoothQuadratic_sub_radicalQuadratic_le` transports this
to the original full quadratic with all gcd tails bounded by
`32*norm(chi)*A*U^2*exp(-U^2/(8*A))`, for `A>0`, `U^2>=8A`.
This preserves the gcd channels before any reflected comparison. The
global Moebius identity already supplies a scalar reduction after those
channels are recombined; the new bound does not improve the global
cancellation rate. The signed estimate across the surviving physical
integers remains open on that branch.

An earlier alternative carrier is the full smooth rectangle in
[EtaGammaRectangular](../RiemannGaussian/EtaGammaRectangular.lean).
`norm_foldedOuterBand_sixth_le` independently bounds the actual signed
outer strip `u^2<a<=u^3`, after completing the inner range `b<=u^5`,
by `C_rho*u^(-6-3*sigma)+1024*norm(chi(rho))*u^18*exp(-u/4)`.
The exact strip identity retains every cross term and the complementary
product tail. The terminal `smoothRectangle_sixth_tendsto_source`
proves that the shorter rectangle `a<=u^2`, `b<=u^5` still tends to
the original source when `sigma>2/5`; both short sums and all source
corrections are included. The independent signed upper estimate is
therefore concentrated on this surviving sum. Ordinary and complex-weighted
Abel transforms with subsequent absolute values gave weaker comparisons
in all 12 numerical samples; their exact endpoints and signed versions
remain available. This rules out no signed Abel argument, but gives no
reason to replace the current target by those absolute envelopes.

The subsequent [exact harmonic balancing rule](../RiemannGaussian/EtaGammaBalancedOuter.lean)
keeps `mu(n)` through `L`, assigns
`c_L=-H_mu(L)/sum_(L<n<=2L)(1/n)` on `(L,2L]`, and vanishes thereafter.
The denominator is at least `1/2` and `|c_L|<=4`. Its full harmonic
moment is exactly zero, so the compiled
`reciprocalProduct_balancedOuter_eq_zero` annihilates every term `C/(a*b)`
against these actual outer coefficients. Completing the inner Möbius sum
proves that the full added correction costs at most
`32*C_rho/u^10+4096*norm(chi(rho))*u^18*exp(-u/4)` on the same scale.
The theorem `norm_balancedRectangle_sixth_sub_source_le` combines this
with every preceding source allowance, and
`balancedRectangle_sixth_tendsto_source` preserves the source for
`sigma>2/5`, without assuming simple zeros. The remaining signed sum
still requires the independent saving. Its direct absolute-row comparison
increases slightly in all 12 numerical samples; exact removal of this
matrix component has not supplied the required inequality.

A subsequent numerical [prime-orbit audit](eta-hyperbola-endgame-assessment.md#small-prime-folding-of-the-balanced-rectangle-numerical-route-audit)
keeps small-prime multiplicativity inside the full balanced inner sum.
Grouping improves the tested coordinate comparisons, but reducing the
remaining cores to primes still reproduces the source after all corrections.
An Abel transform retains every proper prime power and both endpoints.
The available `abs(psi(n)-n)<=5*n` estimate gives upper costs far above the
source. Even using the measured finite prime discrepancy inside that
absolute comparison is insufficient in the critical-line controls. This
adds no Lean theorem; a viable continuation must bound the full signed
prime-discrepancy correlation with the moving arithmetic weight, or supply
a different independent signed estimate for the original rectangle.

The [cumulative prime audit and branch review](eta-hyperbola-endgame-assessment.md#cumulative-prime-audit-and-existing-library-connections)
test the existing Suzuki cumulative estimate on the same moving weight.
Both Abel endpoints, the second-difference terms, and the discrete-to-continuous
correction are retained. Taking absolute values after the second transform
worsens all 12 comparisons. Cutoff jumps contribute little of the tested
first-transform cost; the common-divisor part dominates. The available
other Git branch is already contained in `main`. The useful existing
connections preserve reflected-channel correlations, mixed phase kernels,
and exact heat-compression leakage. Applying these to the actual arithmetic
direction still needs a concrete inequality; their generic positivity or
trace statements do not furnish the missing signed upper bound.

The newest compiled estimate in
[EtaGammaFactorTail](../RiemannGaussian/EtaGammaFactorTail.lean)
retains both vanished factor ranges through the entire majorant argument.
`norm_evaluate_mixed_factor_le` bounds their full cofactor by
`B(rho,A,L,V)=64*norm(chi(rho))*A^2*(L*V)^(-1-sigma)*exp(-L*V/(2*A))`
when `A>0` and `L*V>=2*A`. The balanced source allowance is now the sum of the two
original short allowances, `32*C_rho*L^4/A^3`, `5*B`, and the original
physical endpoint allowance. The compiled
`norm_balancedRectangle_sub_source_factor_le` retains them all.
For the square schedule `A=u^6,U=u^4`, `u>=2`, and `sigma>=1/2`,
`norm_smoothQuadratic_sixth_sub_source_factor_le` gives the complete budget
`2*C_rho*u^(-2-4*sigma)+64*norm(chi(rho))*exp(-u^2/2)` plus the
physical endpoint allowance. This is a substantially smaller error budget;
the main signed upper bound is still required.

The [full product-shell probe](../scripts/probe_eta_gamma_product_shells.py)
keeps every complex block and its heat complement. Both tested shell
absolute comparisons worsen in all 12 cases. A product-heat filter can
make the retained part negative while the removed part exceeds the source.
The next comparison must therefore keep the complete arithmetic direction;
neither the localized part nor its marginal shell envelopes bound it.

## Current first-mean route

The newest estimate uses the full complex first mean of the same completed
Möbius source. The theorem
`norm_pairedEtaCompletedMoebiusSelectedFirstMean_le` in
[EtaMoebiusFirstMean](../RiemannGaussian/EtaMoebiusFirstMean.lean)
bounds every selected divisor family through `D≤A` by
`C_rho*D²*A^(-sigma-1)`. It pairs each parity wave with its divisor shift
before estimating the complex-power difference. Both original
normalization errors are retained. This is a separate linear estimate;
the Fourier sampler's mean-square range remains `A^(2/3)`.

On `A=L=u⁴`, `D=u³`, the low complex mean is at most
`C_rho*u^(2-4*sigma)` and tends to zero for `sigma>1/2`.
[EtaMoebiusQuarterQuotientMean](../RiemannGaussian/EtaMoebiusQuarterQuotientMean.lean)
identifies the high mean with one exact signed product sum with the literal
ramp weights, proves its quotient cap is less than `2*u`, and proves that
it tends to the original nonzero source. The new
[quartic boundary estimate](../RiemannGaussian/EtaMoebiusQuarticBoundary.lean)
now completes the last fibre at a cost of at most `u²` divisors and norm
`C_term*u^(2-4*sigma)`, uniformly for `M≥u⁴`. The boundary's full mean
square also tends to zero. The complete quotient first mean consequently
has source error at most `(C_term+C_mean)*u^(2-4*sigma)` and retains the
same nonzero limit. This is a new estimate for the quartic fibre, not an
application of the earlier cubic bound outside its hypotheses.

The theorem `norm_pairedEtaMoebiusCoprimeLowQuarticFirstMean_le` in
[EtaMoebiusCoprimeFirstMean](../RiemannGaussian/EtaMoebiusCoprimeFirstMean.lean)
now combines that estimate with simultaneous prime exclusion. For odd
`P` dividing `u`, every divided window costs its dividing integer `e`,
so the complete low sieve has norm at most
`C_rho*P²*u^(2-4*sigma)`. The existing explicit
`P_v=product_(j<=v)(2*j+1)`, `u_v=P_v^m`,
`m=ceil(8/(6*sigma-3))+1`, satisfies
`2+m*(2-4*sigma)<0`. Thus the whole first-mean sieve allowance vanishes
while every odd prime through `2*v+1` is excluded together. The terminal
`pairedEtaMoebiusCoprimeQuarticFirstMean_growing_tendsto_source`
retains the original nonzero source in the surviving complex mean.

The new [coprime boundary estimate](../RiemannGaussian/EtaMoebiusCoprimeBoundary.lean)
also completes the sieved quotient blocks. Each prime intersection is
exactly an original term at divisor `d*e`, using `gcd(d,e)=1`; terms
beyond the physical cutoff vanish. The boundary has norm at most
`C_term*P*u^(2-4*sigma)`, with no fixed-modulus assumption. The exact
completion identity and quotient reindexing retain coprimality on both
factors. For `P|u`, the entire complete mean has source error at most
`(C_term+C_mean)*P²*u^(2-4*sigma)`. The terminal theorem
`pairedEtaMoebiusCoprimeCompleteQuarticFirstMean_growing_tendsto_source`
proves that the same explicit schedule makes this allowance vanish.

For this quotient form, the independent arithmetic target is a bound for
its real projection against the conjugate source, including the complete
allowance. A fixed gap below the source square on arbitrarily large scales
would suffice. A bound for the norm is optional. These are still open
arithmetic estimates. No mean-square extension to quartic windows, new
zero bound, full arithmetic decay, or RH proof follows from the new
first-mean bounds alone. The detailed estimate and its limitations are in
the [hyperbola assessment](eta-hyperbola-endgame-assessment.md).

The subsequent surviving-sum audit checks a specific obstruction: the
complete quotient operator applied to logarithmic prefix increments
returns the genuine eta derivative. At a simple zero, normalization by
`1/zeta'(rho)` therefore reproduces the entire nonzero source. Fixed-prime
coprimality has the same model response after the exact Euler factors
cancel. These statements do not estimate the actual Möbius prefix. The
research probe also finds finite sieve gaps in this model that disappear
at larger quotient caps. The next arithmetic estimate must control the
corresponding possible contribution in the actual weighted Möbius sum;
shell sizes or finite gaps alone do not supply it. The assessment records
the precise Lean diagnostic and numerical scope.

The subsequent quadratic audit tests Heath--Brown factorization of the
actual Möbius coefficients. Subtracting its explicit smooth pole leaves
an indefinite form in every numerical case tested. Adding a second eta
factor removes the pole exactly, but a separate Lean diagnostic proves
that the finite arithmetic identity then retains the source square.
Its regularized numerical response is the negative square of the
actual inverse-prefix defect, plus the explicit small eta-tail error.
This does not yield an independent bound for that defect. The audit and
reproducible full-matrix checks are recorded at the end of the assessment.
The primary target remains the complete first mean: the next useful
estimate must use the actual Möbius cross terms, beyond a generic matrix
norm or repeated eta factorization.

The subsequent primary-source correlation review makes another transfer
cost explicit. Direct use of a normalized first-sum error leaves
`epsilon(A)*A^(1-sigma)`; an averaged absolute correlation error in the
first Möbius band leaves `epsilon(D)*D^(2-2*sigma)`, subject also to
the required weighted partial-sum uniformity. Known logarithmic rates
do not yet put these allowances below the source. A separate Lean
diagnostic proves that bounded complete multiplicativity and uniform
logarithmically normalized correlation decay can coexist with a matched
weighted dyadic block of norm at least `1/2` at every scale. Its
coefficients are a comparison sequence, not Möbius. The assessment
records the primary sources and exact theorem scope. The next estimate
must use additional arithmetic of the actual coefficients, preserving
their full complex sum; replacing that sum by normalized correlation
decay alone has not closed the gap.

The newest arithmetic estimate returns to the exact prime identity on
the original product carrier. In
[EtaMoebiusPrimeFirstMean](../RiemannGaussian/EtaMoebiusPrimeFirstMean.lean),
`pairedEtaCompletedMoebiusPrimeProductAggregate_eq_original_annulus`
moves the odd prime into the original divisor index `p*d`. The direct
parity estimate then gives first-mean norm at most
`C_rho*p*u^(2-4*sigma)` for every odd prime `p≤u`, on every quartic
scale `u`; no condition `p|u` is needed.
The theorem `sum_norm_pairedEtaMoebiusPrimeProductFirstMean_growing_le`
bounds the sum of these norms over **all** odd primes through
`floor(u^(sigma-1/2))` by `C_rho*u^(1-2*sigma)`. The whole allowance
tends to zero when `sigma>1/2`, uniformly for complex weights of norm
at most one that may vary with the scale.

The exact weighted residual has product multiplier
`1-sum_(p|n) w(p)`. Every overlap is retained; this is not a prime-free
indicator. Its first mean still tends to the nonzero source. This gives
a controlled family for choosing arithmetic sieve weights on the
original product sum, separate from the complete coprime selection
above. The next bound must estimate the resulting whole signed residual
below the source. Neither a bound for the hard union of these prime
classes nor a whole quartic mean-square estimate is inferred.

The new [exact prime weights](../RiemannGaussian/EtaMoebiusPrimeSieveWeights.lean)
now reach the endpoint of that quadratic cutoff budget. Define
`H_R=sum_(p≤R, p odd prime) 1/(p-1)` and
`w_R(p)=p/((p-1)*(1+H_R))`. Lean proves both `0≤w_R(p)≤1` on the
selected primes and the stronger bound `w_R(p)≤2/(1+H_R)`.
The theorem `norm_pairedEtaMoebiusHarmonicPrimeFirstMean_le` then
bounds the entire weighted prime correction by `2*C_rho/(1+H_R)`
at `R=floor(u^(2*sigma-1))`. The checked divergence of prime
reciprocals proves that this allowance tends to zero for `sigma>1/2`.
Thus these specific arithmetic weights double the earlier cutoff
exponent while retaining all product overlaps. No logarithmic rate for
the harmonic divergence is required or asserted by this theorem.

The [full-weight probe](../scripts/probe_eta_prime_sieve_weights.py)
also checks the candidate against every original physical endpoint,
retaining its whole mean square and every prime-class cross term.
Its exact rational density calculation and the actual Möbius residual
are separate quantities. Finite source gaps in critical-line samples
disappear at larger tested scales even while the density improvement
persists. This does not refute a zero-specific argument, but it supplies
no independent bound for the signed residual. The next estimate must
control that actual residual, including its prime/composite interference;
the new theorem pays for the enlarged weighted correction only.

The subsequent prime/composite audit sharpens that next target. A local
Lean check proves that the small-prime weights leave every active
single-odd-prime ray unchanged; higher powers of its sole odd prime vanish
on quartic windows with `u>=3`. Any active product carrying a prime above
`D=u^3` is that prime or twice that prime, so all remaining composite
products have prime factors at most `D`. The complete numerical Gram
retains these channels' mixed term, which can be positive. An independent
prime-only formula reconstructs the unchanged channel exactly.

Classical partial summation using the prime number theorem predicts more
than a finite obstruction: for fixed `s` in the strip, that channel's
first mean has nonzero leading term
`c_s*A^(1-s)/(log A)^2`, with `A=u^4`. The assessment derives this
consequence and identifies its external analytic input; it is not a Lean
asymptotic theorem or a finite numerical bound. Separate decay of the
prime and composite groups is therefore the wrong intermediate target.
Use the exact prime-removal recurrence on admissible cofactors to keep
their phases and smaller-cutoff Möbius coefficients in one signed sum.
The required estimate still has to control that whole sum below the
source on an absolute scale; relative alignment alone does not suffice.

The newest checked estimate now controls a joint prime/composite group.
[EtaMoebiusLargePrimeFirstMean](../RiemannGaussian/EtaMoebiusLargePrimeFirstMean.lean)
selects all primes `p>2*u^2` through `2*u^4`. No positive product in
the physical window carries two selected primes. The entire original
product group containing one of them differs from its explicit sum at
`p` and `2*p` by exactly the negative original low-divisor family whose
divisors carry a selected prime. The theorem
`norm_pairedEtaMoebiusLargePrimeProductFirstMean_sub_model_le` bounds
this whole first-mean error by `C_rho*u^(2-4*sigma)`; its decay is
checked for `sigma>1/2`. Both the primes and their composites have been
retained in obtaining this estimate.

The remaining candidate is the explicit prime-pair sum **plus all
complementary original products**, taken as a single complex first mean.
`pairedEtaMoebiusPrimeSmoothFirstMean_tendsto_source` proves that it
still tends to the nonzero source. The new theorem does not assert decay
of the prime model or estimate either component separately. It applies
to the original unweighted carrier; the previously proved harmonic
weighted correction remains a separate vanishing term. The next task is
an independent upper bound for this coupled prime/complementary sum,
or its source-directed real projection. The full arithmetic gap and RH
remain open.

The next prime-removal audit exposes a unit term that must survive any
such bound. For the odd small-prime modulus `P`, let `E_P(M)` be the
complete coprime eta prefix and let `V_P(M)` be the dyadic rough-number
model with its unit removed. The local Lean diagnostic
`EtaRoughSourceAudit.roughModel_sub_source` proves exactly
`V_P(M)=S_rho-chi(rho)*(E_P(M)-2^(-rho)*E_P(floor(M/2)))`.
Its fixed-modulus limit is the nonzero source, with the explicit
allowance `2*C_term*P*N^(-sigma)` at `M=2*N`. The factor `P` prevents
silently applying that limit to a growing small-prime modulus.

The [rough-model probe](../scripts/probe_eta_rough_model.py) checks the
second removal down to the growing threshold `2*u`, including prime
powers and all products of up to three rough prime factors. It retains
every physical endpoint and all sixteen entries of the resulting Gram
matrix. Its general growing-cutoff decomposition is still a working
coefficient calculation, not a root-imported Lean theorem. The full
candidate is `S_rho+(Q_u-G_u)`, where `Q_u` is the complementary original
product group and `G_u` is the complete rough eta pair. An independent
fixed negative bound for the source projection of `mean(Q_u-G_u)` would
close the reductio. Decay of `G_u`, or decay of `Q_u-G_u`, would instead
recover the source and leave the gap open. The assessment records the
checked unit identity and the finite evidence; neither is a new zero
bound. The next estimate must address this signed source projection,
not separate rough-prefix decay.

The subsequent smooth-divisor audit now connects the **compiled**
`2*u^2` joint carrier to an exact finite inverse-zeta defect. In
`/tmp/EtaSmoothInverseAudit.lean`,
`primeSmoothFirstMean_eq_inverse_defect_sub_centered` writes it as
`S_rho*(1-zeta(rho)*B_S(rho))-chi(rho)*W_S(rho)`, where `B_S` is the
actual complementary low Möbius polynomial and `W_S` is its centered
eta first mean. Lean proves the finite defect is exactly `1` at every
actual zero and transfers the existing first-mean allowance to `W_S`.
The new [probe](../scripts/probe_eta_smooth_inverse.py) reconstructs all
32 previous whole-product means from independently grouped divisors.
The small values at the nonzero `3/4+it` samples track their inverse
defects; those values do not test a bound at a zero.

A primary-source friable-sum review also identifies a nonzero Buchstab
main term in the **first smooth product band**, where the compiled
coefficient is exactly Möbius. Its weighted band has leading size
`D^(1-sigma)/(log y)^2` at `D=u^3`, `y=2*u`. The assessment derives this
consequence, gives its source and scope, and separates it from the local
Lean checks of the coefficient and its growth. The finite numerical
leading model is not an error bound. Thus the next candidate must retain
cancellation both between smooth bands and with the rough model.
Separate band norms and a finite inverse-zeta factorization supply no
independent source gap. The full signed arithmetic estimate remains the
target; the new audit does not prove a zero bound.

The [cutoff-mixture probe](../scripts/probe_eta_cutoff_mixture.py) now
optimizes several complete rough/smooth cutoffs together, retaining every
entry of their complex physical Gram matrix. The local Lean diagnostic
`/tmp/EtaCutoffMixtureAudit.lean` checks the coefficient budget before any
fitted improvement is interpreted. It combines shared divisor coefficients
as `g(d)=sum_(i:d in S_i) w_i`, then proves the actual source error is at
most `C_rho*A^(-sigma-1)*sum_(d<=D) d*norm(g(d))`. This cost is at most
the previous `C_rho*D^2*A^(-sigma-1)*sum_i norm(w_i)` and can be much
smaller. Exact convex clipping preserves `sum_i w_i=1` and meets the
combined-divisor budget. On the quartic schedule, the budget
`sum_(d<=u^3) d*norm(g(d)) <= u^(5+2*sigma)` gives source error at most
`C_rho*u^(1-2*sigma)`, which tends to zero to the right of `1/2`.

The 16 complete numerical cases test five coefficient choices each.
Combining overlaps admits some fits rejected by the coarse coefficient
budget, but the tested critical-line RMS gaps still shrink as the scale
grows. The small off-critical values remain samples at nonzero zeta
points. Neither a measured error nor a budget shape with its theorem
constant omitted is a certified bound. The new admissibility rule
improves the coefficient search; an independent upper bound below the
source is still missing. These are local diagnostics, with no change to
the root theorem inventory or the zero bounds.

The [centered-cutoff test](../scripts/probe_eta_centered_cutoffs.py) now
checks that next distinction explicitly. Centering adds exactly
`zeta(s)*B_(S_i)(s)` to each source-normalized physical column and
preserves every covariance entry. It leaves the carrier unchanged at
an actual zero. At `u=32`, the first off-critical sample's raw fitted
RMS `0.000235` becomes `1.0000003` under the same coefficients after
centering; refitting and clipping gives `0.999947`. The 96 fits and 12
independent complete checks supply no persistent gap. The local Lean
audit also retains the full inverse term in the total centered Möbius
convolution away from zeros, so centering is not treated as producing
an artificial zero. This numerical signal is no longer a reason to
expand the same cutoff scan.

Positive gamma physical averaging now has a checked chain in four root
modules, ending at
[`EtaGammaPhysicalAverage.lean`](../RiemannGaussian/EtaGammaPhysicalAverage.lean).
Its survival function is `Q(x)=exp(-x)*(1+x+x^2/2)` and its literal
physical weights are `Q(M/A)-Q((M+1)/A)`, including `M=0`. The weights
are nonnegative, have total mass one, and are integrals of the positive
gamma density. The Mellin proof identifies the transformed kernel with
the actual eta function and retains an explicit cubic remainder.

The theorem
`EtaGammaSmoothing.norm_tsum_gammaPhysicalWeight_moebiusSelected_le`
now bounds the **original** selected completed Möbius average by
`C_rho*A^(-3)*D^(4-Re(rho))`. Every finite selection through `D` is
allowed. Discrete Abel summation, absolute convergence, the infinite
boundary, and all complete quotient fibres are discharged in the proof.
The terminal theorem
`EtaGammaSmoothing.tsum_gammaPhysicalWeight_moebiusSelected_sixth_tendsto_zero`
proves decay on `A=u^6`, `D=u^5` for `Re(rho)>2/5`, **including the
critical line**. This is a new positive averaging kernel, not an
extension of the earlier sampler's critical exponent.

The theorem `EtaGammaSmoothing.hasSum_gammaPhysicalWeight_moebiusLarge`
retains the full high family as the exact smoothed source minus the low
family. Its source is
`chi(rho)*(Q(1/A)-2*2^(-rho)*Q(2/A))`, with an explicit cubic endpoint
allowance. The next target is an independent bound for this **whole
signed high average** below the nonzero source at a hypothetical
right-half zero. The stronger low-family bound alone cannot distinguish
such a zero from a critical-line zero. No new zero bound, full arithmetic
decay theorem, or RH proof is established.

The subsequent local audit `/tmp/EtaGammaLogModeAudit.lean` identifies
what smoothing leaves in the high-range comparison mode. The theorem
`integral_gammaDampedEta_div_eq_deriv` proves the full logarithmic
moment `integral_(0,infinity) G_rho(x)/x dx = eta'(rho)`. At a simple
actual zero its completion-normalized value is the original nonzero
source. Positive dilations preserve this moment, and
`norm_source_le_normalized_gammaDilation_mixture` proves that every
finite complex mixture of those scales with coefficient sum one has
logarithmic comparison norm at least the source norm. This is a
statement about the kernel's comparison mode, not a bound or asymptotic
formula for the actual Möbius sequence.

The [new probe](../scripts/probe_eta_gamma_log_mode.py) checks five gamma
orders at three numerical zeros and three off-critical nonzero samples,
with independent integrated Taylor and incomplete-gamma expansions.
All 30 cases preserve the eta-derivative moment. At the first numerical
zero, increasing the order from 1 to 6 moves the real projection of
that comparison moment above `x=1` from about 13% to 93%. The next
estimate must therefore retain the actual signed Möbius coefficients;
normalized scale fitting cannot make this kernel norm vanish. The
assessment records the exact scope, proof checks, and literature audit.
These diagnostics do not add a root milestone or improve a zero bound.

The two subsequent root modules
[`EtaGammaDivisorTail.lean`](../RiemannGaussian/EtaGammaDivisorTail.lean)
and [`EtaGammaFiniteBand.lean`](../RiemannGaussian/EtaGammaFiniteBand.lean)
now localize that original high average to a finite divisor band.
`EtaGammaSmoothing.hasSum_gammaMoebiusTerm` proves that the entire
absolutely convergent damped Möbius series equals the exact smoothed
source. The connection to the original physical average uses a proved
summable dominator; it does not assume Möbius cancellation.

For `R>=2*A`, `norm_gammaPhysicalHigh_sub_band_le` bounds the omitted
tail by `16*norm(chi(rho))*A*R^(-sigma)*exp(-R/(2*A))`. At the literal
rounded cutoff `R(A)=ceil(2*A*(1+2*log A))`, the terminal theorem
`norm_gammaPhysicalHigh_sub_logBand_le` bounds the error by
`16*norm(chi(rho))/A`. Both removed divisor ranges and both source
endpoints therefore have explicit allowances.

Write `B_rho(u)` for the actual finite band on `A=u^6`, `D=u^5`.
`norm_gammaMoebiusSixthBand_sub_source_le` proves
`norm(B_rho(u)-S_rho)<=E_rho(u)`, where

```
E_rho(u) = C_rho*u^(2-5*sigma)
         + 16*norm(chi(rho))/u^6
         + norm(chi(rho))*(1+16*2^(-sigma))/(6*(u^6)^3).
```

`gammaMoebiusSixthBand_tendsto_source` proves convergence to the source
for `sigma>2/5`, including critical-line zeros. These are lower/source
comparison results, not an independent upper estimate for the band.
The direct target is the real source projection
`P_rho(u)=Re(conj(S_rho)*B_rho(u))`. A sufficient independent estimate
at one admissible scale is `P_rho(u)<=U_rho(u)` with
`U_rho(u)+norm(S_rho)*E_rho(u)<norm(S_rho)^2`. A fixed strict gap at
arbitrarily large admissible scales also suffices. No full power-saving
rate is required. The estimate must apply to every hypothetical actual
zero with `sigma>1/2`; the source comparison alone provides no such gap.

Equivalently, write `q_rho(u)=Re(B_rho(u)/S_rho)` and
`e_rho(u)=E_rho(u)/norm(S_rho)`. The source is nonzero, and the checked
comparison implies `q_rho(u)>=1-e_rho(u)`, with `e_rho(u)->0`.
The finite acceptance test is `q_rho(u)<=1-delta_rho(u)` and
`e_rho(u)<delta_rho(u)` at the same admissible scale. The saving may
depend on both the zero and the scale. To avoid proving an explicit
starting scale or a rate, it is sufficient to obtain some `delta_rho>0`
such that, for every `N`, a scale `u>=max(1,N)` has
`q_rho(u)<=1-delta_rho`. Merely bounding `q_rho` by an unspecified
constant cannot contradict its already proved limit of one.

The family-strength audit in the
[assessment](eta-hyperbola-endgame-assessment.md) keeps that minimal
signed acceptance condition as the target. Positive spectral energy,
a scale-independent multiple of its trace, a prescribed decay rate,
and uniform estimates for all coefficient vectors are optional methods.
Retain the negative spectral contribution when it helps; a method's
failure does not establish that the gamma family fails. The existing
source comparison allows arbitrary zero multiplicity. The classical
logarithmic family's critical-line simplicity issue has not been
transported to this band. Alternative arithmetic weights remain
available through the original general-weight interfaces, with their
source normalization and every comparison allowance to be proved.

The [finite-band probe](../scripts/probe_eta_gamma_high.py) retains the
whole signed band, its actual infinite-tail truncation, all dyadic divisor
bands, and all squarefree factor-count channels. Sixteen cases pass the
independent integer product reconstruction and full source split. Four
additional 40-digit checks use direct polylogarithms and independently
enumerated physical coefficients. They are numerical diagnostics, not
certified bounds or evidence that the off-critical sample points are zeros.
The [assessment](eta-hyperbola-endgame-assessment.md) records the checks
and the subsequent prime-error attack. The independent finite-band upper
bound, full arithmetic decay, and RH remain open. Changes in this slice
are local; commits are on hold under the user's latest instruction.

The [full smooth quadratic](../RiemannGaussian/EtaGammaSmoothQuadratic.lean)
removes the sharp product band from an alternative carrier. It proves the exact source identity
`S_(rho,A)=2*Low_(rho,A,U)+Q_(rho,A,U)+J_(rho,A,U)`, absolute
convergence of both cofactor series, and the whole omitted-square bound
`norm(J)<=1024*norm(chi)*A^3*exp(-U^2/(4*A))` for `2*A<=U^2`.
On `A=u^6`, `U=u^4`, both short copies and this new tail tend to zero;
the full smooth quadratic retains the source at every actual zero.
The proof is imported by the root library, together with the subsequent
mixed-cutoff cancellation in `EtaGammaRectangular`. It does not prove
the independent signed saving. Numerical
tests preserve the critical-line source after removing the sharp cutoff.
The assessment records the exact scope and subsequent unequal-cutoff
tests, which retain the actual Möbius sums on one side before evaluating
their outer signed contributions.

## Retained cubic mean-square route

The current research route audits the supplied hyperbola reductio on the
original zero-dependent Möbius source. The
[hyperbola assessment](eta-hyperbola-endgame-assessment.md) records the
checked exact quotient reindexing, complete small-half decay, full signed
correlation form, and quantitative nonzero source limit for the large
half. Retaining the complete sampling-window cost now extends the
controlled divisor range to `A^(2/3)` at a hypothetical right-half zero.
The complement has at most `2*A^(1/3)` quotient blocks. The single clipped
boundary now has a checked vanishing norm and mean-square allowance.
Completing that fibre leaves the same source limit, and the surviving
blocks are grouped into exact dyadic shells with every cross term retained.
The original parity recurrence now holds inside these complete shells:
the even part is `-2^(-rho)` times the odd part at half the physical
cutoff, with the original quotient cap retained. The full shell form is
exactly a two-scale Hermitian parity matrix; its energy retains both whole
odd-channel energies and their phase-weighted mixed correlation.
The subsequent Abel transform now retains both endpoints of every capped
shell and absorbs the upper endpoint into an alternating bilinear
hyperbola. The high aggregate is exactly a completed partial Dirichlet sum
with fixed coefficients `b_D(n)=sum_(qd=n,d>D) eta(q)*mu(d)` throughout the
physical window. Their collision energy is bounded, and their first band
is exactly the original Möbius sequence. The compiled terminal theorem
`pairedEtaCompletedMoebiusLargeMeanSquare_eq_bilinear_window` in
[EtaMoebiusBilinearWindow](../RiemannGaussian/EtaMoebiusBilinearWindow.lean)
evaluates the full physical overlap kernel, retaining every product pair.
The only difference from the complete quotient carrier is the already
controlled boundary fibre, with its complex interference retained in
[EtaMoebiusBilinearEnergy](../RiemannGaussian/EtaMoebiusBilinearEnergy.lean).
This supplies a fixed coefficient vector and an explicit matrix for the
next arithmetic estimate. Its initial product square has kernel one,
including off-diagonal entries, so a coefficient square bound alone does
not control that coherent contribution.
The [weighted collision mass](../RiemannGaussian/NatDivisorSquareDirichlet.lean)
now converges at every exponent above one. Consequently the actual
[product diagonal](../RiemannGaussian/EtaMoebiusBilinearDiagonal.lean) is
at most `C_rho*u^(1-2*sigma)` at `D=u²`, uniformly in the physical window.
The checked short-shift estimate
`norm_pairedEtaCompletedMoebiusBilinearNearForm_twoThirds_le` in
[EtaMoebiusBilinearShortShifts](../RiemannGaussian/EtaMoebiusBilinearShortShifts.lean)
controls the diagonal and every pair with
`abs(n-m)<=floor(u^(sigma-1/2))` together by
`3*C_rho*u^(1/2-sigma)`. For `sigma>1/2` this contribution vanishes and
its radius grows without bound. The exact complementary complex form
retains every longer product shift; its real part still tends to the
source square on the original cubic windows. No sign or cancellation
bound for this remaining form has been assumed.
The [reduced-ratio extension](../RiemannGaussian/EtaMoebiusBilinearRatioBands.lean)
now proves at most `R²` partners per product when both factors of the
reduced ratio are at most `R`. This controls long shifts with both factors
through `floor(u^((sigma-1/2)/2))` by another
`C_rho*u^(1/2-sigma)`, uniformly over windows. The terminal theorem
`norm_pairedEtaCompletedMoebiusLargeMeanSquare_sub_ratioRemainder_twoThirds_le`
bounds the combined removal from the original full energy by
`4*C_rho*u^(1/2-sigma)`. The exact remaining form has a long shift and at
least one large reduced ratio factor; it still has the source-square
limit. Its independent signed upper bound remains open.
The [odd-prime product identity](../RiemannGaussian/EtaMoebiusPrimeProduct.lean)
now makes an arithmetic cancellation inside a whole divisibility class:
the completed product prefix over `p|n`, for any odd prime `p`, is exactly
`-p^(-rho)` times the original divisor annulus `D/p<d<=D`, with `p` not
dividing `d`, at physical cutoff `M/p`. The selected-family Fourier
estimate retains all window and endpoint costs. On original cubic
windows along `u=p*v`, the entire prime-product mean square is at most
`C_(rho,p)*(1+log v)^2*v^(3-6*sigma)` and tends to zero for `sigma>1/2`.
The full mixed correlation with the original high aggregate also tends
to zero. The terminal theorem
`pairedEtaMoebiusLargeMeanSquare_sub_primeFree_tendsto_zero` in
[EtaMoebiusPrimeExclusion](../RiemannGaussian/EtaMoebiusPrimeExclusion.lean)
therefore removes every product row and column divisible by that fixed
prime with a vanishing total signed cost. Its exact complement still
has the source-square limit. That fixed-prime theorem alone does not
justify simultaneous exclusion.
The [finite coprime sieve](../RiemannGaussian/EtaMoebiusCoprimeProduct.lean)
now retains every prime intersection as a selected original divisor
family at its exact divided physical cutoff. For any odd modulus `P`
dividing `u`, the compiled
`pairedEtaMoebiusCoprimeLowCubicEnergy_le` in
[EtaMoebiusCoprimeWindow](../RiemannGaussian/EtaMoebiusCoprimeWindow.lean)
bounds the whole low sieve by
`C_rho*P^4*(1+log u)^2*u^(3-6*sigma)`, with modulus-independent constant.
The explicit growing schedule uses
`P_v=product_(j<=v)(2*j+1)` and
`u_v=P_v^m`, where `m=ceil(8/(6*sigma-3))+1`.
[EtaMoebiusCoprimeGrowth](../RiemannGaussian/EtaMoebiusCoprimeGrowth.lean)
proves the complete allowance tends to zero for `sigma>1/2` and that
every odd prime through `2*v+1` is excluded together.
The terminal theorem
`pairedEtaMoebiusLargeMeanSquare_sub_growingCoprime_tendsto_zero` in
[EtaMoebiusCoprimeExclusion](../RiemannGaussian/EtaMoebiusCoprimeExclusion.lean)
controls deletion of the whole growing selection of product rows and
columns, including all their mixed terms. Its exact complement still
has the nonzero source-square limit. This closes the simultaneous
exclusion and accumulated-error obligations on these explicit cofinal
scales. Products with growing odd prime factors survive; their independent
sub-source bound remains open.
On this cubic energy route, the target is any independent upper bound with a fixed positive
gap below the source square; a decay or power rate is sufficient but not
required. That arithmetic estimate remains open. The present sampler's
`A^(2/3)` range will not be extended as a substitute for this target. The
logarithmic residual program is preserved in the
[arithmetic assessment](eta-parity-endgame-assessment.md); its growing
middle band is also uncontrolled. Neither route has completed the
uniform weighted estimate.

## Actual target and current status

Write `J_rho(N)` for the existing, unchanged
`pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N`. Its literal kernel is the
completed head at analytic multiplicity one and the completed adjacent-moment
kernel otherwise. In the head branch the physical first time is the shifted
coordinate plus `pairedEtaLogTailCutoff(N+1)`.

The arithmetic target is a bound for

\[
 S_\rho(K)=\sum_{N<K}(2N+1)|J_\rho(N)|
\]

uniform in the upper cutoff `K`, for every actual nontrivial zeta zero.
Any allowed dependence on the zero, analytic multiplicity, and completion
factors must be explicit. This must establish the existing universal
first-absolute-moment summability statement, whose equivalence to RH is
already proved in `EtaEnergyLeadingFluxKernel.lean`. Neither that arithmetic
bound nor RH is currently proved. Reconstruction alone does not complete
the objective.

| Obligation | Evidence | Status |
| --- | --- | --- |
| Integrate the ordered return over the entire actual gap | `integrable_leadingCurrent_gapReturn_prod`, `pairedEtaLeadingCurrentIntegratedGapReturn_eq_prod`, and `pairedEtaLeadingCurrentIntegratedTwoTransition_eq_neg_gapReturn` in [EtaIntegratedGapReturn.lean](../RiemannGaussian/EtaIntegratedGapReturn.lean). | Proved for nonnegative tilts with positive sum, positive widths, and measurable phases. |
| Normalize the actual return and reconstruct the original current | Positive gap mass and dominated broad-heat limit in [EtaBroadGapReturn.lean](../RiemannGaussian/EtaBroadGapReturn.lean); `pairedEtaLeadingCurrent_gapReturn_reconstruction` in [EtaLeadingCurrentReconstruction.lean](../RiemannGaussian/EtaLeadingCurrentReconstruction.lean). | Proved as iterated limits at every fixed zero and cutoff. |
| Quantify the dependence of reconstruction on the arithmetic cutoff | Exact multiplier and signed defect in [EtaGapReturnMultiplier.lean](../RiemannGaussian/EtaGapReturnMultiplier.lean); `pairedEtaLeadingCurrentNormalizedGapReturn_error_le` and its small-tilt bound in [EtaCurrentReconstructionError.lean](../RiemannGaussian/EtaCurrentReconstructionError.lean). | Proved with the actual absolute kernel mass and physical endpoint retained. |
| Control the completed absolute kernel masses across cutoffs | The actual measure bounds in [EtaFiniteCurrentMeasureBounds.lean](../RiemannGaussian/EtaFiniteCurrentMeasureBounds.lean), completed envelopes in [EtaCurrentKernelEnvelope.lean](../RiemannGaussian/EtaCurrentKernelEnvelope.lean), and `pairedEtaLeadingCurrentAbsoluteKernelMass_le` in [EtaCurrentKernelMass.lean](../RiemannGaussian/EtaCurrentKernelMass.lean). | Proved with an explicit completion-dependent constant and logarithmic-over-cutoff bound. |
| Choose simultaneous heat and tilt parameters with summable weighted reconstruction error | `pairedEtaLeadingCurrentScheduledGapReturn_weighted_error_le` in [EtaCurrentReconstructionSchedule.lean](../RiemannGaussian/EtaCurrentReconstructionSchedule.lean) and the summability and finite-prefix stability theorems in [EtaCurrentWeightedReconstruction.lean](../RiemannGaussian/EtaCurrentWeightedReconstruction.lean). | Proved with a schedule independent of the zero and a finite completion- and multiplicity-dependent error budget. |
| Compare the actual continuous gap return with composed Gaussian heat | Full-line composition in [EtaTiltedHeatComposition.lean](../RiemannGaussian/EtaTiltedHeatComposition.lean) and `pairedEtaLeadingCurrentIntegratedGapReturn_eq_composed_sub_corrections` in [EtaCurrentFullHeatComparison.lean](../RiemannGaussian/EtaCurrentFullHeatComparison.lean). | Proved with both support and nonpositive-time corrections; all three-time integrals converge even at zero tilt. No cancellation estimate follows from the identity alone. |
| Reconstruct at zero tilt with controlled actual-gap normalization | Arithmetic balance in [EtaDecreasingGapMass.lean](../RiemannGaussian/EtaDecreasingGapMass.lean), Gaussian mass and translation bounds in [EtaGaussianGapMass.lean](../RiemannGaussian/EtaGaussianGapMass.lean), exact multiplier in [EtaZeroTiltGapMultiplier.lean](../RiemannGaussian/EtaZeroTiltGapMultiplier.lean), and the two completed branches in [EtaZeroTiltCurrentReconstruction.lean](../RiemannGaussian/EtaZeroTiltCurrentReconstruction.lean). | Proved using the entire actual gap, without extending the positive-tilt Laplace normalization to zero. |
| Preserve the weighted frontier with zero tilt and quadratic width | `summable_oddEndpoint_mul_norm_pairedEtaLeadingCurrentZeroTiltScheduledReturn_error` and `pairedEtaLeadingCurrentZeroTiltScheduledReturn_firstMoment_stability` in [EtaZeroTiltWeightedReconstruction.lean](../RiemannGaussian/EtaZeroTiltWeightedReconstruction.lean). | Proved at width `2(N+1)²`, with explicit finite error budget and no exponential tilt amplification. |
| Evaluate the literal colour primitive and broad Gaussian gap term | `pairedEtaLogColourPrimitive_wallis_error_le` in [EtaLogColourPrimitive.lean](../RiemannGaussian/EtaLogColourPrimitive.lean), the exact signed remainder in [EtaGaussianColourRemainder.lean](../RiemannGaussian/EtaGaussianColourRemainder.lean), and `pairedEtaGaussianGapMass_wallis_expansion_error_le` in [EtaGaussianGapExpansion.lean](../RiemannGaussian/EtaGaussianGapExpansion.lean). | Proved with the evaluated Wallis constant, exponential primitive error `9 exp(−t)`, and uniform remainder `2(1+c)³/h³`. |
| Identify the first broad-heat coefficient of the original current | The normalized expansion in [EtaZeroTiltFirstCorrection.lean](../RiemannGaussian/EtaZeroTiltFirstCorrection.lean) and `pairedEtaLeadingCurrentZeroTiltGapReturn_midpoint_error_le_arithmetic` in [EtaCurrentMidpointCorrection.lean](../RiemannGaussian/EtaCurrentMidpointCorrection.lean). | Proved in both actual multiplicity branches, retaining an exact signed defect and an explicit inverse-square-width error. Arithmetic cancellation of the midpoint coefficient remains open. |
| Evaluate the midpoint coefficient in finite eta arithmetic | The complex integral identity in [EtaCurrentFiniteMomentPair.lean](../RiemannGaussian/EtaCurrentFiniteMomentPair.lean), the repeated-zero formula in [EtaCurrentAdjacentMidpoint.lean](../RiemannGaussian/EtaCurrentAdjacentMidpoint.lean), and the translated head formula in [EtaCurrentHeadMidpoint.lean](../RiemannGaussian/EtaCurrentHeadMidpoint.lean). | Proved with both physical cutoff origins, all centered orders, and complex channel orientation retained. |
| Apply completed reflection and the actual zero-tail bounds to the midpoint | Both branch decompositions in [EtaCurrentMidpointReflection.lean](../RiemannGaussian/EtaCurrentMidpointReflection.lean), finite moment bounds in [EtaCurrentMomentBounds.lean](../RiemannGaussian/EtaCurrentMomentBounds.lean), and `abs_pairedEtaLeadingCurrentMidpointMoment_le_arithmetic` in [EtaCurrentMidpointBounds.lean](../RiemannGaussian/EtaCurrentMidpointBounds.lean). | Proved with an explicit additional endpoint decay factor. The finite reflection defect times the nonzero leading moment is retained; no vanishing or original-current weighted bound follows. |
| Preserve the weighted frontier at linear heat width | `pairedEtaLeadingCurrentLinearHeatReturn_weighted_error_le` in [EtaCurrentLinearHeatSchedule.lean](../RiemannGaussian/EtaCurrentLinearHeatSchedule.lean), and summability and finite-prefix stability in [EtaCurrentLinearHeatReconstruction.lean](../RiemannGaussian/EtaCurrentLinearHeatReconstruction.lean). | Proved at width `2(N+1)`, with separate summable midpoint and remaining-defect majorants and an explicit finite total error budget. No bound on the return's own weighted moment is proved. |
| Estimate the retained signed arithmetic against explicit endpoint terms | Complex prefix and pair errors in [EtaCurrentEulerMoments.lean](../RiemannGaussian/EtaCurrentEulerMoments.lean) and [EtaCurrentEulerPairs.lean](../RiemannGaussian/EtaCurrentEulerPairs.lean); elementary head and positive adjacent coefficients in [EtaCurrentEulerArithmetic.lean](../RiemannGaussian/EtaCurrentEulerArithmetic.lean); `pairedEtaLeadingCurrentLinearHeatReturn_euler_error_sum_le` in [EtaCurrentEulerEstimate.lean](../RiemannGaussian/EtaCurrentEulerEstimate.lean). | Proved with summable weighted error in both actual branches. The endpoint expression itself still requires an independent weighted bound. The repeated-zero contribution has no cutoff Fourier oscillation. |
| Bound the original return's weighted moment as the cutoff grows | The two-factor estimate in [EtaCurrentArithmeticEnvelope.lean](../RiemannGaussian/EtaCurrentArithmeticEnvelope.lean), the finite power-sum comparison in [EtaCurrentPowerSum.lean](../RiemannGaussian/EtaCurrentPowerSum.lean), and `pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le` in [EtaCurrentReturnGrowth.lean](../RiemannGaussian/EtaCurrentReturnGrowth.lean). | Proved with explicit growth `C_rho*(K+1)^abs(2*Re(rho)-1)` and exact treatment of the critical line. The exponent is below one, and the cutoff-normalized moment tends to zero. A cutoff-independent bound remains open. |
| Couple actual completed eta tails across multiplicatively divided cutoffs | `sum_moebius_mul_pairedEtaCorePartialSum_add_endpoint` in [EtaMoebiusFinitePrefix.lean](../RiemannGaussian/EtaMoebiusFinitePrefix.lean) and `pairedEtaCompletedMoebiusTailAggregate_eq_source` in [EtaMoebiusCompletedTail.lean](../RiemannGaussian/EtaMoebiusCompletedTail.lean). | Proved at every actual zero and every integer cutoff at least two, with all odd endpoint corrections and complex Möbius weights. The resulting linear constraint has no proved quadratic-current bound yet. |
| Bound both complete parity aggregates and their signed block sums | Exact halved-cutoff identities in [EtaMoebiusParityRecurrence.lean](../RiemannGaussian/EtaMoebiusParityRecurrence.lean), `norm_pairedEtaCompletedMoebiusOddAggregate_le` in [EtaMoebiusParityBound.lean](../RiemannGaussian/EtaMoebiusParityBound.lean), and `norm_pairedEtaSignedCompletedMoebiusParityBlock_le` in [EtaMoebiusParityBlocks.lean](../RiemannGaussian/EtaMoebiusParityBlocks.lean). | Proved uniformly in the physical cutoff, with every divisor and both completion channels retained. These are norms of block sums; a bound for the original weighted absolute return does not follow yet. |
| Recover the original simple-zero current from the parity aggregates | `pairedEtaFiniteCompletedMoment_zero_eq_oddInverse` in [EtaMoebiusParityInverse.lean](../RiemannGaussian/EtaMoebiusParityInverse.lean) and `pairedEtaLeadingCurrent_eq_oddInverse_head` in [EtaCurrentMoebiusInverse.lean](../RiemannGaussian/EtaCurrentMoebiusInverse.lean). | The exact inverse weights, divided cutoffs, and both signed head channels are proved. Their absolute weight mass has matching positive-power bounds in [EtaMoebiusInverseWeights.lean](../RiemannGaussian/EtaMoebiusInverseWeights.lean), so termwise norms do not supply a uniform transfer. |
| Sum equal-cutoff inverse phases and retain cancellation with the complementary cutoffs | Complex midpoint control in [EtaOddPowerQuadrature.lean](../RiemannGaussian/EtaOddPowerQuadrature.lean), the nonzero Mellin coefficient in [EtaOddPowerMellin.lean](../RiemannGaussian/EtaOddPowerMellin.lean), and `norm_pairedEtaCompletedOddInverseBottom_add_main_le` in [EtaMoebiusGroupedInverse.lean](../RiemannGaussian/EtaMoebiusGroupedInverse.lean). | The full top inverse block grows after its phases are summed. The complementary block has the opposite explicit complex main term with a decaying error. Their sum is the actual zeroth completed moment; the weighted signed-current bound remains open. |
| Obtain an independent arithmetic exclusion and transport it to the original return | `one_le_etaPrimeProduct_zero_gap` in [EtaZetaPrimeProduct.lean](../RiemannGaussian/EtaZetaPrimeProduct.lean), `nontrivialZetaZero_mem_etaPrimeProduct_strip`, and `pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_etaPrimeProduct` in [EtaPrimeProductZeroMargin.lean](../RiemannGaussian/EtaPrimeProductZeroMargin.lean). | Every actual zero lies between the explicit positive margins `delta(Im rho)` and `1-delta(Im rho)`. The original return is bounded by `C_rho*(K+1)^(1-2*delta(Im rho))`. The exponent remains positive; the uniform weighted goal remains open. |
| Reconstruct and control full Möbius transforms at every centered moment order | `norm_pairedEtaCompletedMomentMoebiusAggregate_le` in [EtaMomentMoebiusTransform.lean](../RiemannGaussian/EtaMomentMoebiusTransform.lean), `pairedEtaFiniteCompletedMoment_eq_momentInverse` in [EtaMomentMoebiusInverse.lean](../RiemannGaussian/EtaMomentMoebiusInverse.lean), and both current branches in [EtaCurrentMomentMoebiusInverse.lean](../RiemannGaussian/EtaCurrentMomentMoebiusInverse.lean). | Exact two-endpoint cancellation and all-cutoff aggregate bounds are proved at fixed centers for every order. The inverse preserves all center shifts and recovers the original repeated-zero double sum. The weighted inverse estimate at moving physical centers remains open. |
| Strengthen the independent zero margin using actual multiplicity | `one_le_etaPrimeProduct_multiplicity_gap` in [EtaPrimeProductMultiplicityGap.lean](../RiemannGaussian/EtaPrimeProductMultiplicityGap.lean), `nontrivialZetaZero_mem_etaPrimeProductMultiplicity_strip` in [EtaPrimeProductMultiplicityMargin.lean](../RiemannGaussian/EtaPrimeProductMultiplicityMargin.lean), and `etaPrimeProductZeroMargin_lt_multiplicity` in [EtaPrimeProductMultiplicityComparison.lean](../RiemannGaussian/EtaPrimeProductMultiplicityComparison.lean). | The exact margin equals the previous bound at multiplicity one and is strictly larger at every nonzero ordinate for multiplicity at least two. The original return has the smaller exponent `1-2*Delta_m(Im rho)`, still in `[7/8,1)`. The uniform weighted goal remains open. |
| Improve the zero margin for simple zeros using height-adapted eta bounds | `norm_riemannZeta₁_le_etaThinStrip` in [EtaThinStripRectangle.lean](../RiemannGaussian/EtaThinStripRectangle.lean), `nontrivialZetaZero_mem_reciprocal_logarithmic_strip` and `etaPrimeProductZeroMargin_lt_logarithmic` in [EtaLogarithmicMarginComparison.lean](../RiemannGaussian/EtaLogarithmicMarginComparison.lean), and `pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_etaRefinedPrimeProduct` in [EtaLogarithmicZeroMargin.lean](../RiemannGaussian/EtaLogarithmicZeroMargin.lean). | A positive explicit logarithmic margin constrains every actual zero; above height twenty-one it dominates `1/(32*C*log(|gamma|+21)^14)`. It strictly improves the earlier ordinate-only margin. The maximum with the previous multiplicity margin retains both bounds and strictly lowers the exponent for simple zeros. The exponent remains in `[7/8,1)`, and the uniform goal is open. |
| Retain signed local zero poles in the prime comparison | `norm_localZetaLogRemainder_le` in [ZetaLocalLogDerivative.lean](../RiemannGaussian/ZetaLocalLogDerivative.lean), `neg_logDeriv_riemannZeta_re_le_sub_zero` in [ZetaSignedLocalEstimate.lean](../RiemannGaussian/ZetaSignedLocalEstimate.lean), and `nontrivialZetaZero_mem_signedLogarithmic_strip` in [ZetaSignedZeroMargin.lean](../RiemannGaussian/ZetaSignedZeroMargin.lean). | Every actual zero has the positive margin `abs(y)/(1800000*(abs(y)+1)*log(abs(y)+22))`. This strictly improves the previous logarithmic margin at every nonzero ordinate. The maximum preserves all previous multiplicity bounds and improves the original return exponent for simple zeros; the exponent remains in `[7/8,1)`. |
| Transport Fourier estimates to actual moving-center moments and inverse entries | `pairedEtaCompletedMomentOriginalMeanSquare_le_quadratic` in [EtaMomentQuadraticMeanSquare.lean](../RiemannGaussian/EtaMomentQuadraticMeanSquare.lean), the signed adjacent bound in [EtaMomentSignedQuadraticFamily.lean](../RiemannGaussian/EtaMomentSignedQuadraticFamily.lean), and `norm_pairedEtaCompletedMomentInversePartialTerm_sub_zero_le` in [EtaMomentInverseReduction.lean](../RiemannGaussian/EtaMomentInverseReduction.lean). | Every order below the actual multiplicity has the original physical mean-square bound for `D²≤A,L`. Each actual inverse center satisfies the required logarithmic interval, giving an explicit inner-range error with the outer complex weight retained. The full inverse sums and uniform current bound remain open. |
| Estimate both actual inverse divisor sums on physical rectangles | `pairedEtaCompletedMomentInverseRectangleMeanSquare_le_quadratic` in [EtaInverseRectangleMeanSquare.lean](../RiemannGaussian/EtaInverseRectangleMeanSquare.lean), with the original signed adjacent bound in [EtaInverseRectangleSigned.lean](../RiemannGaussian/EtaInverseRectangleSigned.lean). | Joint mean square is at most `C_rho,k ED(1+log E)²(1+log(ED))² A^(-2 Re rho)` for `(ED)²≤A,L`, below the actual multiplicity. Exact signed product grouping, collision counts, Fourier support, and physical corrections are all proved. The extension below covers fixed curved regions and their mixed pairs; the complete growing inverse remains open. |
| Extend joint inverse control to curved regions and average the full physical error | `pairedEtaCompletedMomentInverseRegionMeanSquare_le` and the exact original-band identity in [EtaMomentInverseRegion.lean](../RiemannGaussian/EtaMomentInverseRegion.lean); `pairedEtaSignedCompletedMomentInverseHyperbolicBands_adjacent_le` in [EtaInverseRegionSigned.lean](../RiemannGaussian/EtaInverseRegionSigned.lean). | Every fixed subregion of `de≤T` has mean square at most `C_rho,k T(1+log T)^5 A^(-2 Re rho)` for `1≤T≤A` and `T²≤L`. Two independent regions retain all mixed pairs and both reflected channels. Extending the same physical budget to all proportional windows is refuted below; the original weighted current estimate remains open. |
| Test proportional windows and retain the full moving complement | `exists_coherentBand_dyadic_window_exceeding_region_budget` in [EtaCoherentBandWindowObstruction.lean](../RiemannGaussian/EtaCoherentBandWindowObstruction.lean), and `pairedEtaCompletedMomentInverseCoherentComplement_cross_re_le` in [EtaCoherentBandComplement.lean](../RiemannGaussian/EtaCoherentBandComplement.lean). | An explicit original band has coefficient energy `K` and physical mean square at least `abs(X_rho)² K²/4` on windows `A=(B_rho+2)K,L=K`. A quadratic lower bound also persists over `[A,2A)`, refuting the same logarithmic region budget there. The full moving complement has mixed real part at most `-abs(X_rho)² K²/8` in the initial subwindow beyond an explicit threshold. The original signed current estimate remains open. |
| Transport complete zeroth-order inverse cancellation to both original current branches | `pairedEtaLeadingCurrent_fullInverseEnergy_firstMoment_stability` in [EtaCurrentFullInverseEnergy.lean](../RiemannGaussian/EtaCurrentFullInverseEnergy.lean), and `pairedEtaLeadingCurrent_weighted_coherentComplement_error_le` in [EtaCurrentCoherentComplement.lean](../RiemannGaussian/EtaCurrentCoherentComplement.lean). | Both branches reduce to signed complete zeroth energies with positive real coefficients and summable odd-weighted error. Independent band/complement splits retain all mixed products, and the actual coherent bands fit every literal cutoff by integer division. The weighted absolute sum of the full signed energy remains open. |
| Sharpen the actual prime constraint on the current's horizontal growth | `multiplicity_le_quadratic_signed_zero_gap` in [ZetaSignedExactPole.lean](../RiemannGaussian/ZetaSignedExactPole.lean), `nontrivialZetaZero_mem_signedQuadratic_strip` in [ZetaSignedQuadraticMargin.lean](../RiemannGaussian/ZetaSignedQuadraticMargin.lean), and `pairedEtaLeadingCurrent_firstMoment_le_quadraticPrime` in [EtaCurrentQuadraticPrimeBound.lean](../RiemannGaussian/EtaCurrentQuadraticPrimeBound.lean). | Exact pole geometry gives a multiplicity-sensitive margin more than 31 times the previous signed margin at every nonzero ordinate. For absolute ordinate at least one, the margin is at least `1/(56458 log(abs(y)+22))`. Both original current branches, the Gaussian return, and the complete inverse energy inherit the improved exponent while preserving all preceding margins. The exponent remains positive. |
| Bound several nearby actual zeros simultaneously | `sum_multiplicity_le_one_in_signedEdgeWindow` in [ZetaSignedWindowMultiplicity.lean](../RiemannGaussian/ZetaSignedWindowMultiplicity.lean), with reflection, simplicity, separation, and the original head inverse formula in [ZetaSignedZeroSeparation.lean](../RiemannGaussian/ZetaSignedZeroSeparation.lean). | For every center of absolute height at least one, an edge rectangle of width and ordinate half-width `1/(6000 log(abs(y)+22))` contains total analytic multiplicity at most one. The exact selected complex pole sum and full complement are retained. This rules out multiple zeros and close pairs within that layer, while the uniform weighted goal remains open. |
| Establish an independent Gaussian reciprocal contour for the Möbius sums | `norm_zetaReciprocalExtension_le_on_box` in [ZetaReciprocalBox.lean](../RiemannGaussian/ZetaReciprocalBox.lean), and `zetaReciprocalGaussian_contour_shift` with `zetaReciprocalGaussian_right_integral_le` in [ZetaReciprocalGaussianContour.lean](../RiemannGaussian/ZetaReciprocalGaussianContour.lean). | The actual reciprocal is analytic and uniformly bounded on a rectangle crossing real part one. The Gaussian contour shift retains both horizontal corrections and bounds them with their height damping. Its arithmetic identification and infinite-tail estimates are now discharged by the following row. |
| Transfer the full contour to the actual convergent Gaussian Möbius sum | `integral_zetaReciprocalGaussianKernel_eq_gaussianMoebiusSum` in [GaussianMoebiusMellin.lean](../RiemannGaussian/GaussianMoebiusMellin.lean), and `gaussianMoebiusSum_contour_identity` with `gaussianMoebiusSum_contour_bound` in [GaussianMoebiusContourBound.lean](../RiemannGaussian/GaussianMoebiusContourBound.lean). | The full integral equals the arithmetic sum at every abscissa greater than one, with all convergence and interchange premises proved. The actual sum has a left-line bound plus both horizontal corrections and infinite tails. The following row discharges a scale choice and arithmetic rate. |
| Extract an unconditional cancellation rate from the actual Gaussian contour | `moebiusDirichletMass_contour_le_log` in [ZetaMoebiusMassBound.lean](../RiemannGaussian/ZetaMoebiusMassBound.lean), `gaussianMoebiusSum_one_le_logSquare_envelope` in [GaussianMoebiusScaleEnvelope.lean](../RiemannGaussian/GaussianMoebiusScaleEnvelope.lean), and `gaussianMoebiusSum_one_le_reciprocal_log_gain_eventually` with `gaussianMoebiusSum_log_one_div_tendsto_zero` in [GaussianMoebiusCancellation.lean](../RiemannGaussian/GaussianMoebiusCancellation.lean). | At unit heat time and height `T=a`, the actual sum is eventually bounded by `exp(a-a/(1000000 log(a+22)))`, and `S_1(log X)/X→0`. All constants and scale conditions are discharged, with an existential threshold. An estimate of sufficient strength for the original complex weights, physical cutoffs, and completed reflected current remains open. |
| Bound the current power by complete finite eta translate arithmetic | `pairedEtaTranslatedResidualEnergyCutoff_eq_finiteForm` and `pairedEtaTranslatedResidualEnergy_le_finiteBudget` in [EtaTranslatedFiniteResidual.lean](../RiemannGaussian/EtaTranslatedFiniteResidual.lean), followed by `pairedEtaLeadingCurrent_firstMoment_le_translatedProjection` in [EtaCurrentTranslatedProjectionPower.lean](../RiemannGaussian/EtaCurrentTranslatedProjectionPower.lean). | The compact target shares the elementary eta factor and stays nonzero at actual zeta zeros. Every finite nonnegative translate family gives a complete Gram-plus-tail budget for actual horizontal displacement and both current branches. The Gaussian return and full inverse energy inherit the same exponent. A family with vanishing full budget and an improved numerical zero strip remain open. |
| Define an exact growing coefficient law and certify complete finite bounds | `pairedEtaCanonicalTranslateBudget_le_trial` in [EtaCanonicalTranslateBound.lean](../RiemannGaussian/EtaCanonicalTranslateBound.lean), `pairedEtaFourProjection_residualEnergy_lt_one_fifth` in [EtaFourTranslateBound.lean](../RiemannGaussian/EtaFourTranslateBound.lean), and `pairedEtaLeadingCurrent_firstMoment_le_dyadicTranslate` in [EtaCanonicalTranslateFamily.lean](../RiemannGaussian/EtaCanonicalTranslateFamily.lean). | The actual regularized Gram inverse specifies a dyadic family, with complete residual at most its exact deficit. Structured trial coefficients bound that deficit. Four explicit rational coefficients have complete residual below `1/5`; comparison gives canonical four-point deficit below `1/4`. Decay of the growing family deficit remains open. |
| Discharge the full coefficient cost and actual infinite tail for a specified arithmetic candidate | `pairedEtaMoebiusTrialCoefficient_sum_abs_le` in [EtaMoebiusTrialCoefficients.lean](../RiemannGaussian/EtaMoebiusTrialCoefficients.lean), `pairedEtaDyadicMoebiusTrialPenalty_tendsto_zero` in [EtaMoebiusTrialPenalty.lean](../RiemannGaussian/EtaMoebiusTrialPenalty.lean), and `pairedEtaDyadicMoebiusTrialResidualTail_tendsto_zero` in [EtaMoebiusTrialResidual.lean](../RiemannGaussian/EtaMoebiusTrialResidual.lean). | The exact balanced logarithmic Möbius law has zero signed coefficient mass, absolute sum at most `2(k+1)`, and full penalty at most `(k+1)^2/2^k→0`. The actual entire omitted residual integral also tends to zero. The canonical deficit is at most the growing finite residual plus that vanishing allowance. Decay of the finite residual and canonical deficit remains open. |
| Remove grid-refinement costs from the actual arithmetic candidate comparison | `pairedEtaMoebiusTrialRefinementError_le` in [EtaMoebiusTrialRefinement.lean](../RiemannGaussian/EtaMoebiusTrialRefinement.lean), and `pairedEtaDyadicMoebiusResidual_sub_refined_tendsto_zero`, `pairedEtaDyadicTranslateDeficit_le_refined_moebius` in [EtaMoebiusRefinedBudget.lean](../RiemannGaussian/EtaMoebiusRefinedBudget.lean). | With the stage arithmetic weights fixed, every positive integer refinement of the physical grid changes the full critical square approximation and complete residual energy by proved vanishing amounts. The canonical deficit and actual zero displacement are at most any refined arithmetic residual plus an explicit allowance tending to zero. Decay of that arithmetic residual remains open. |
| Prove decay of part of the refined arithmetic residual itself | `pairedEtaMoebiusLogHarmonic_tendsto_zero` in [EtaMoebiusLogHarmonic.lean](../RiemannGaussian/EtaMoebiusLogHarmonic.lean), `pairedEtaMoebiusTrialHeadResidual_eq` in [EtaMoebiusTrialHead.lean](../RiemannGaussian/EtaMoebiusTrialHead.lean), and `pairedEtaDyadicMoebiusRefinedHeadResidual_tendsto_zero` in [EtaMoebiusRefinedHeadDecay.lean](../RiemannGaussian/EtaMoebiusRefinedHeadDecay.lean). | The actual residual square integral on the entire compact target interval tends to zero for every refinement schedule, using the proved signed harmonic Möbius cancellation. The full residual splits exactly into this vanishing term and the complete exterior integral over `t>log 2`. Decay of that exterior arithmetic integral, the full residual, and the canonical deficit remains open. |
| Identify the whole refined exterior with signed arithmetic and a controlled infinite tail | `pairedEtaMoebiusTrialGridCombination_eq_arithmeticPrefix` in [EtaMoebiusGridArithmetic.lean](../RiemannGaussian/EtaMoebiusGridArithmetic.lean), the complete integrable split in [EtaMoebiusExteriorArithmetic.lean](../RiemannGaussian/EtaMoebiusExteriorArithmetic.lean), and `pairedEtaDyadicMoebiusRefinedExteriorEnergy_eq_arithmetic_add_tail` in [EtaMoebiusExteriorBudget.lean](../RiemannGaussian/EtaMoebiusExteriorBudget.lean). | The actual complete exterior equals a growing square integral of the exact signed odd/even primitive formula plus its genuine full tail. That tail is at most `(k+1)^2/4^k→0` for every refinement schedule. Every head, grid, coefficient, and tail cost in the original deficit and zero-displacement comparison is discharged. Decay of the growing signed arithmetic square integral remains open. |
| Identify the full continuum arithmetic residual and discharge its complete grid-transport error | `pairedEtaMoebiusTrialGridCombination_tendsto_continuum` in [EtaMoebiusContinuumCombination.lean](../RiemannGaussian/EtaMoebiusContinuumCombination.lean), `pairedEtaMoebiusContinuumGridError_le` in [EtaMoebiusContinuumEnergy.lean](../RiemannGaussian/EtaMoebiusContinuumEnergy.lean), and `pairedEtaDyadicMoebiusRefinedResidual_sub_continuum_tendsto_zero` in [EtaMoebiusContinuumBudget.lean](../RiemannGaussian/EtaMoebiusContinuumBudget.lean). | The signed continuum formula is the actual grid limit at every time with its strict arithmetic endpoints. Its complete critical-square comparison is integrable and quantitatively controlled. For every refinement schedule, the full original residual differs from the full continuum residual by at most `2R_k→0`. The canonical deficit is bounded by that continuum residual plus the existing vanishing allowance. Decay of the arithmetic residual itself remains open. |
| Prove a signed arithmetic estimate controlling `S_rho(K)` uniformly in `K` | Must preserve completion factors, multiplicity, the head branch, and the correlations needed before taking absolute values. | Open; this is the remaining conjecture-strength objective. |

## Checked reconstruction

Let `G_(sigma,h,tau,k,phi,psi)(t,u,w)` be the existing ordered complex
gap-return core. Its exact identity with two actual commutators has a
negative sign. Before specializing any phase, the new bound is

\[
 |G(t,u,w)|\le
 \frac{e^{-(\sigma+\tau)w/2}}{A(h)A(k)},\qquad
 A(h)=2\sqrt\pi\sqrt2h,
\]

for nonnegative physical endpoint times and tilts, and positive widths.
The literal current is integrable on its finite measure, and the exponential
is integrable on the entire gap when `sigma+tau>0`. Their product proves
genuine three-time integrability. Fubini connects the integrated existing
pairing to the literal current-gap product integral. The negative ordered
two-transition identity survives this integration.

For equal tilts `a>0`, equal widths `h`, and zero probe phases, define

\[
 M(a)=\int_{\mathrm{gap}}e^{-aw}\,dw>0,\qquad
 R_{\rho,N}(a,h)=\frac{8\pi h^2}{M(a)}
 \int_{\mathrm{gap}}\mathrm{GapReturnPairing}_{\rho,N}(a,h,a,h,0,0;w)\,dw.
\]

`pairedEtaLeadingCurrentNormalizedGapReturn` is exactly this normalization of
the existing pairing. Positivity of `M(a)` uses the actual first nonempty gap
interval, and `A(h)^2=8*pi*h^2` is separately proved. Removing the two Gaussian
amplitudes gives the exact profile

\[
 e^{-a(t+u)/2}e^{-aw}
 \exp\left[-\frac{(w-t)^2+(u-w)^2}{8h^2}\right].
\]

It is dominated by `exp(-a*w)` and tends to the same expression without the
Gaussian. Dominated convergence on the actual current-gap product proves

\[
 R_{\rho,N}(a,h)\longrightarrow
 T_{\rho,N}(a)=\int J_{\rho,N}(t,u)e^{-a(t+u)/2}\,d\mu_{\rho,N}(t,u)
 \quad(h\to\infty).
\]

A second dominated-convergence argument proves

\[
 T_{\rho,N}(a)\longrightarrow J_\rho(N)\quad(a\to0^+).
\]

The Lean endpoint is the existing `pairedEtaTopPrefixFiniteEnergyLeadingFlux`,
using the proved exhaustive multiplicity formulas. The completed current is
never replaced by its positive envelope. The raw ordered phase kernel remains
available upstream; only the reconstruction specialization sets the added
probe phases to zero. The ordinate phase inside the completed current remains.

## Checked quantitative error

The new scalar multiplier is the exact gap-time average

\[
 Q_{a,h}(t,u)=\frac1{M(a)}\int_{\mathrm{gap}}e^{-aw}
  \exp\left[-\frac{(w-t)^2+(u-w)^2}{8h^2}\right]\,dw.
\]

It is measurable, genuinely integrable, and between zero and one. Its exact
signed difference from one is retained as an integral before bounding it.
Let `M₂(a)=integral_gap w² exp(-aw) dw`. Lean proves

\[
 0\le M_2(a)\le 2/a^3,\qquad
 |Q_{a,h}(t,u)-1|\le\frac{M_2(a)/M(a)+t^2+u^2}{h^2}.
\]

For `0<a≤1`, monotonicity of the actual gap mass gives
`M₂(a)/M(a) ≤ 2/(M(1)a³)`, with `M(1)>0` proved earlier.
Fubini now identifies the normalized return exactly with the original
current integral against `exp(-a(t+u)/2)*Q`. Consequently its signed error
is the integral of the original current times that multiplier minus one.

The two physical times are proved to lie in `[0,L_N]`, where
`L_N=pairedEtaLogTailCutoff(N+2)=log(2N+5)`, also for the translated head.
Writing `B_rho(N)` for the actual selected kernel's integral of absolute
value, `pairedEtaLeadingCurrentNormalizedGapReturn_error_le` proves

\[
 \|R_{\rho,N}(a,h)-J_\rho(N)\|
 \le B_\rho(N)\left[aL_N+
   \frac{M_2(a)/M(a)+2L_N^2}{h^2}\right].
\]

The small-tilt corollary replaces the moment ratio by `2/(M(1)a³)`.
The factor `B_rho(N)` is finite by the existing genuine kernel integrability.
Its arithmetic growth is now bounded as described below; it has not been
assumed summable across cutoffs. The reconstruction estimate controls the
error of replacing the current by its exact return. The separate weighted
arithmetic target remains unchanged.

## Checked completed kernel mass

Write `sigma=Re rho`, `tau=1-sigma`, and let `W_rho` and `W_partner` be the
existing completed Laplace weights. Every actual zero has `0<sigma,tau<1`.
The finite eta measures are now proved dominated by the full positive-time
Lebesgue measure, giving exponential masses at most `1/sigma`. Their product
has mass at most `1/sigma²`. On the distinct translated head, the first mass
is instead at most the actual cutoff increment `delta_(N+1)`.

The actual head kernel is bounded by twice the sum of its two completed
exponentials at the restored physical coordinate. The adjacent kernel keeps
`2(m-1)delta_(N+1)`, and its centered powers are at most `(1+L_N)^(2m)`.
The phases and signed completion difference remain in the original kernels;
these absolute envelopes are used only downstream to control reconstruction.

Defining the explicit constant

\[
 C_\rho=2m\left[\frac{W_{\mathrm{partner}}}{(1-\Re\rho)^2}
                   +\frac{W_\rho}{(\Re\rho)^2}\right],
\]

`pairedEtaLeadingCurrentAbsoluteKernelMass_le_increment` first retains the
actual increment in `B_rho(N) ≤ C_rho delta_(N+1) (1+L_N)^(2m)`.
The all-cutoff estimate `delta_(N+1) ≤ 1/(N+1)` then proves

\[
 B_\rho(N)\le\frac{C_\rho(1+\log(2N+5))^{2m}}{N+1}.
\]

`pairedEtaLeadingCurrentNormalizedGapReturn_error_le_arithmetic` substitutes
this bound into the small-tilt reconstruction estimate. Every constant in
that result is an actual proved mass, completion weight, zero coordinate,
or analytic multiplicity. No mass bound is left as an antecedent.

## Checked simultaneous weighted reconstruction

Set `x_N=N+1`, `b_N=1+log(2N+5)`, and choose

\[
 a_N=x_N^{-2},\qquad h_N=x_N^4,\qquad
 D_\rho=C_\rho\bigl(3+2/M(1)\bigr).
\]

Every scheduled tilt is positive and at most one, and every width is
positive. The schedule has no dependence on the zero or multiplicity.
The scalar scale estimate proves

\[
 a_NL_N+\frac{2/(M(1)a_N^3)+2L_N^2}{h_N^2}
 \le \bigl(3+2/M(1)\bigr)\frac{b_N^2}{x_N^2}.
\]

Thus the actual scheduled return `R_N=R_(rho,N)(a_N,h_N)` satisfies

\[
 \|R_N-J_\rho(N)\|\le D_\rho\frac{b_N^{2m+2}}{x_N^3},\qquad
 (2N+1)\|R_N-J_\rho(N)\|
 \le 2D_\rho\frac{b_N^{2m+2}}{x_N^2}.
\]

These are the two terminal bounds in
[EtaCurrentReconstructionSchedule.lean](../RiemannGaussian/EtaCurrentReconstructionSchedule.lean).
The proof of `summable_pairedEtaCurrent_logPower_div_sq` compares each fixed
logarithmic power with a square root eventually and then uses the convergent
`3/2` power series. Consequently
`summable_oddEndpoint_mul_norm_pairedEtaLeadingCurrentScheduledGapReturn_error`
proves the required weighted norm-error series converges for every actual
nontrivial zero. The complex weighted error series is also summable, with
its signed difference retained.

Define the genuinely finite error budget

\[
 E_\rho=2D_\rho\sum_{N\ge0}\frac{b_N^{2m+2}}{x_N^2}.
\]

Lean proves that every finite weighted error sum is at most `E_rho`.
The reverse triangle inequality then gives, for every terminal cutoff `K`,

\[
 \left|\sum_{N<K}(2N+1)\|R_N\|-S_\rho(K)\right|\le E_\rho.
\]

The declaration is
`pairedEtaLeadingCurrentScheduledGapReturn_firstMoment_stability` in
[EtaCurrentWeightedReconstruction.lean](../RiemannGaussian/EtaCurrentWeightedReconstruction.lean).
This controls the difference between the two moments uniformly; it does not
bound either moment itself. All completion weights, the actual head branch,
and analytic multiplicity entered through the previously checked mass bound.
No arithmetic cancellation premise was used.

## Checked continuous composition and the exact corrections

Let `K_h` be the existing normalized Gaussian `etaNormalizedHeatKernel h`.
Before imposing any intermediate-time restriction, two equal-width
half-tilted transitions have the positive envelope

\[
 F_{a,h}(t,u,w)=e^{-a(t+w)/2}K_{\sqrt2h}(w-t)
                e^{-a(w+u)/2}K_{\sqrt2h}(u-w).
\]

The exact pointwise factorization is

\[
 F_{a,h}(t,u,w)=
 e^{a^2h^2-a(t+u)}K_{2h}(u-t)
 K_h\!\left(w-\left[\tfrac{t+u}{2}-2ah^2\right]\right).
\]

Consequently its full-line `w` integral is
`exp(a²h²-a(t+u))*K_(2h)(u-t)`. With a common probe phase, the intermediate
phase cancels exactly, leaving `exp(i(phi(t)-phi(u)))`. Arbitrary ordered
probe phases remain in the source kernel and in the subsequent signed
decomposition; only the evaluated composition specializes them to one phase.

For `a≥0`, `h>0`, and nonnegative endpoint times, the full-line slice mass
is at most `exp(a²h²)/(4*sqrt(pi)*h)`. Fubini and this bound prove genuine
three-time integrability against the original integrable current. This
includes **zero tilt** and both actual multiplicity carriers, with the
translated head coordinate restored. Restriction of the intermediate measure
then proves integrability on eta support, eta gap, and nonpositive time.

The measure identity is exactly

\[
 dw=d\mu_{\eta}(w)+d\mu_{\mathrm{gap}}(w)
       +\mathbf1_{(-\infty,0]}(w)\,dw.
\]

Thus `pairedEtaLeadingCurrentIntegratedGapReturn_eq_composed_sub_corrections`
proves that the actual completed gap return equals the explicitly composed
broader Gaussian pairing minus the support return minus the nonpositive-time
correction. Every term retains the original signed completed kernel. The
decomposition does not assert that either correction is negligible.

The checked theorem
`pairedEtaCurrentReconstructionSchedule_fullLine_amplification` evaluates the
full-line envelope factor on the existing reconstruction schedule as
`exp((N+1)^4)`. This is not a lower bound on the signed pairing; it shows why
discarding the signed correction balance does not produce the desired
estimate. The new zero-tilt integrability removes this amplification at the
kernel-composition level, but the old Laplace-mass normalization applies only
at positive tilt. A separate actual-gap Gaussian normalization and weighted
error bound are now proved below.

## Checked zero-tilt reconstruction

For a nonnegative decreasing function integrable on positive time,
consecutive logarithmic unit intervals carry decreasing mass. Summing the
actual alternating support and gap intervals gives

\[
 \int_{\mathrm{gap}}f\le\int_{\eta}f
 \le\int_0^{\log2}f+\int_{\mathrm{gap}}f.
\]

The theorem `pairedEta_decreasing_gap_mass_bounds` retains genuine
integrability and bounds the first interval by `log(2)*f(0)`. For `h>0`, define
`g_h(c)=integral_gap K_h(w-c) dw`. The Gaussian specialization proves

\[
 \frac14-\frac{\log2}{4\sqrt\pi h}\le g_h(0)\le\frac14,
 \qquad g_h(0)\ge\frac18\quad(h\ge2).
\]

Every translated mass is positive and at most one. Its shift estimate is

\[
 |g_h(c)-g_h(0)|\le\frac{3c}{2\sqrt\pi h}\qquad(c\ge0).
\]

The proof compares the absolute Gaussian translation error with
`K_h(w-c)+K_h(w)-2K_h(w+c)` on positive time. Its integral is exactly
three times `integral_0^c K_h`. Domination of the actual gap measure by
positive-time volume then proves the bound; the gap is never assumed
translation invariant or replaced by a density model.

Normalize the existing zero-tilt full-gap return by
`A_h=4*sqrt(pi)*h/g_h(0)`. Lean proves `0<A_h<=32*sqrt(pi)*h` for `h>=2`.
The exact normalized slice is

\[
 Q_h(t,u)=e^{-(u-t)^2/(16h^2)}\frac{g_h((t+u)/2)}{g_h(0)}.
\]

`integral_fullTwoHeat_zero_phase_gap_normalized` connects this formula to
the existing two-transition kernel. Its multiplier is positive, at most
eight, and jointly measurable. For physical endpoints in `[0,L]`,
`pairedEtaZeroTiltGapMultiplier_window_error_le` proves

\[
 |Q_h(t,u)-1|\le\frac{13(1+L)^2}{h}.
\]

Fubini retains the exact signed current integral against `Q_h-1`.
`pairedEtaLeadingCurrentZeroTiltGapReturn_error_le` applies the bound to
both unchanged multiplicity carriers, including the restored head time.
Only the added probe phases are zero; the original ordinate phase and
completion difference remain inside the current.

Set `h_N=2(N+1)²` and write `R_N^0` for this normalized return. The actual
mass bound above now gives

\[
 \|R_N^0-J_\rho(N)\|\le\frac{13C_\rho}{2}
 \frac{b_N^{2m+2}}{(N+1)^3},\qquad
 (2N+1)\|R_N^0-J_\rho(N)\|\le13C_\rho
 \frac{b_N^{2m+2}}{(N+1)^2}.
\]

The existing logarithmic-series theorem proves summability of the weighted
norm errors and the signed complex errors. With the finite budget
`E_rho^0=13*C_rho*sum_N b_N^(2m+2)/(N+1)^2`, Lean proves

\[
 \left|\sum_{N<K}(2N+1)\|R_N^0\|-S_\rho(K)\right|\le E_\rho^0
 \quad\text{for every }K.
\]

This removes the previous tilt-amplification obstruction while retaining
the entire arithmetic gap. It bounds the reconstruction error, not either
first absolute moment. A norm bound on the positive multiplier alone still
gives only the insufficient absolute kernel-mass scale; a new use of the
zero equation and signed completion symmetry is needed.

## Checked Wallis expansion and the actual midpoint correction

Write `ell=log(pi/2)` and let `chi` be the literal eta support indicator.
The actual signed primitive and its remainder are

\[
 A(t)=\int_0^t(2\chi(w)-1)\,dw,\qquad B(t)=A(t)-\ell.
\]

Complete support/gap pairs give exactly `A(log(2n+1))=log(W_n)` for
Mathlib's finite Wallis product. Its two product bounds, together with the
final partial pair, prove `|B(t)| <= 9 exp(-t)` for every `t>=0`.
This uses the actual interval colour at every real time.

For `K_h(r)=exp(-r²/(4h²))/(2 sqrt(pi) h)`, define the signed correction

\[
 C_h(c)=\int_0^\infty B(w)K'_h(w-c)\,dw.
\]

Absolute continuity of the primitive, genuine integrability, and a proved
vanishing endpoint justify integration by parts and give the exact identity

\[
 g_h(c)=\frac14+\frac12\int_0^c K_h(w)\,dw
             -\frac{\ell K_h(c)}2+\frac{C_h(c)}2,
 \qquad |C_h(c)|\le\frac{9(1+c)}{4\sqrt\pi h^3}.
\]

For every `h>0`, `c>=0`, the resulting expansion is

\[
 \left|g_h(c)-\frac14-\frac{c-\ell}{4\sqrt\pi h}\right|
 \le \frac{2(1+c)^3}{h^3}.
\]

Normalization by `g_h(0)` cancels the Wallis constant at first order.
For `h>=2`, the actual ratio has error at most `18(1+c)^3/h²` after
subtracting `1+c/(sqrt(pi)h)`. Including the displacement Gaussian gives

\[
 \left|Q_h(t,u)-1-\frac{(t+u)/2}{\sqrt\pi h}\right|
 \le \frac{19(1+L)^3}{h^2}\quad(0\le t,u\le L).
\]

Let `f_rho,N` be the original selected signed kernel, with its actual
measure, and set

\[
 M_\rho(N)=\int f_{\rho,N}(p)\frac{T(p)+p_2}{2}\,d\mu_{\rho,N}(p).
\]

Here `T(p)=p_1+L_(N+1)` in the simple-zero head and `T(p)=p_1` in the
adjacent-moment branch. Both midpoint integrals are proved integrable.
The exact signed current defect is still an integral against
`Q_h-1-midpoint/(sqrt(pi)h)` before its norm is bounded. The terminal
arithmetic error theorem proves

\[
 \left\|R^0_{\rho,N}(h)-J_\rho(N)
             -\frac{M_\rho(N)}{\sqrt\pi h}\right\|
 \le \frac{19C_\rho(1+L_N)^{2m+3}}{(N+1)h^2}.
\]

The coefficient is the unchanged signed current's physical midpoint
moment. Its finite arithmetic evaluation and a zero-tail gain are now
proved below. An improved reconstruction remainder alone does not give
the uniform weighted bound for `J_rho`.

## Checked midpoint arithmetic, reflection, and endpoint gain

Put `c_rho=pairedEtaXiCompletionFactor(rho)*rho`, and write
`A_rho,k(n)=c_rho*P_k(rho,n)` for the existing centered finite eta moment
with its actual completion factor. The complex pair is

\[
 \Gamma_{k,l}(n)=A_{\rho^*,k}(n)\overline{A_{\rho^*,l}(n)}
                    -\overline{A_{\rho,k}(n)}A_{\rho,l}(n).
\]

The two parity factors cancel exactly in this product, leaving the
original conjugate channel's orientation intact. Genuine integration on
the actual finite product measure evaluates this complex pair. Multiplying
its kernel by the physical midpoint raises either centered order. For
`m>=2`, the checked identity for the unchanged current is

\[
 M_\rho(N)=L_NJ_\rho(N)+(m-1)\delta_{N+1}
   \Re\!\left(\Gamma_{m-1,m-1}(N+2)+\Gamma_{m-2,m}(N+2)\right).
\]

For the simple-zero head let
`H_rho,k(N)=-c_rho*Head_k(rho,N+1)`, with the actual shifted-head moment.
Write `Gamma^H_(k,l)` for the signed complex pair of `H_k` and
`A_l(N+2)` in the same orientation. If `a_N=pairedEtaLogTailCutoff(N+1)`,
the checked simple-zero formula is

\[
 M_\rho(N)=\frac{a_N+L_N}{2}J_\rho(N)
              +\Re\Gamma^H_{1,0}(N)+\Re\Gamma^H_{0,1}(N).
\]

Both the old head origin and the successor prefix center are necessary.
Each product integral has its own genuine integrability proof.

The leading full moment `D_rho=c_rho*P_m(rho)` is proved nonzero.
Completed reflection gives `D_partner=(-1)^m*conj(D_rho)`. Let
`T_rho,k(n)` denote the actual completed centered tail. The exact identity
`A_rho,m(n)=D_rho-T_rho,m(n)` then evaluates the order-`m` pair as

\[
 \Gamma_{k,m}(n)=(-1)^m\Delta_k(n)D_\rho
  -\left(A_{\rho^*,k}(n)\overline{T_{\rho^*,m}(n)}
          -\overline{A_{\rho,k}(n)}T_{\rho,m}(n)\right),
 \quad
 \Delta_k(n)=A_{\rho^*,k}(n)-(-1)^m\overline{A_{\rho,k}(n)}.
\]

The actual head has the same identity with `A_k` replaced by `H_k` and
the successor tail retained. Thus completed symmetry identifies a finite
defect multiplying a nonzero moment; it does not establish that this
defect, or its real pairing in `M`, vanishes.

There is nevertheless a proved arithmetic gain from the existing zero
equation below multiplicity. Define the explicit finite constant

\[
 Q_\rho=|c_\rho|+|D_\rho|
                 +\frac{|c_\rho|\,m!}{(\Re\rho)^{m+1}},
 \qquad d_\rho(N)=(2N+3)^{-\Re\rho}.
\]

At every cutoff, the checked moment bounds give
`|A_rho,k(N+2)|<=Q_rho*d_rho(N)` for `k<m` and
`|A_rho,k(N+2)|<=Q_rho` for `k<=m`. Every actual shifted head order also
satisfies `|H_rho,k(N)|<=Q_rho*delta_(N+1)*d_rho(N)`. Applying these
only after the exact signed identities proves

\[
 |M_\rho(N)|\le\frac{2m(1+L_N)}{N+1}
   \left(Q_{\rho^*}^{\,2}(2N+3)^{-(1-\sigma)}
          +Q_\rho^{\,2}(2N+3)^{-\sigma}\right),\qquad\sigma=\Re\rho.
\]

This removes the growing centered-monomial envelope and retains a
strictly positive endpoint decay exponent in both actual branches. It
bounds the midpoint coefficient; it is not the uniform first absolute
moment estimate for the original current. No new cancellation of the
finite reflection defect has been established.

## Checked linear-width weighted reconstruction

Set `x_N=N+1`, `b_N=1+L_N`, and let `E_rho(N)` denote the two-channel
endpoint envelope in the preceding midpoint bound. The unchanged actual
zero-tilt gap return is now evaluated at `h_N=2x_N`; write it as `R_N` and
retain its signed midpoint term `T_N=M_rho(N)/(sqrt(pi)*h_N)`.
[EtaCurrentLinearHeatSchedule.lean](../RiemannGaussian/EtaCurrentLinearHeatSchedule.lean)
proves, for every actual zero and cutoff,

\[
 (2N+1)|T_N|\le\frac{2m}{\sqrt\pi}\frac{b_NE_\rho(N)}{x_N},
 \qquad
 (2N+1)\|R_N-J_N-T_N\|
 \le\frac{19}{2}C_\rho\frac{b_N^{2m+3}}{x_N^2}.
\]

The general logarithmic series theorem
`summable_pairedEtaCurrent_logPower_div_rpow` in
[EtaCurrentEndpointSeries.lean](../RiemannGaussian/EtaCurrentEndpointSeries.lean)
proves summability of `b_N^k/x_N^p` for every fixed `k` and `p>1`.
The actual zero coordinates supply the strict margins `p=1+Re(rho)`
and `p=1+(1-Re(rho))` needed for the midpoint term. Consequently

\[
 F_\rho(N)=\frac{19}{2}C_\rho\frac{b_N^{2m+3}}{x_N^2}
       +\frac{2m}{\sqrt\pi}\frac{b_NE_\rho(N)}{x_N}
\]

is a proved summable majorant of `(2N+1)*norm(R_N-J_N)`.
[EtaCurrentLinearHeatReconstruction.lean](../RiemannGaussian/EtaCurrentLinearHeatReconstruction.lean)
retains both the norm-summable and signed complex weighted error series.
The explicit finite budget `E_linear(rho)=sum_N F_rho(N)` bounds every
finite error sum. Its terminal theorem
`pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_stability` gives

\[
 \left|\sum_{N<K}(2N+1)\|R_N\|
       -\sum_{N<K}(2N+1)|J_N|\right|\le E_{\mathrm{linear}}(\rho)
 \quad\text{for every }K.
\]

This improves the checked reconstruction width from quadratic to linear
while preserving both original completed carriers. It does not bound
either first absolute moment itself. That independent arithmetic estimate
remains the full goal's unresolved part.

## Checked signed Euler endpoint estimate

The direct arithmetic test now uses the quantitative Euler theorem for
the actual centered eta tails. Define the explicit complex terms

\[
 a_{\rho,k}=\frac{k!}{2\rho^{k+1}},\qquad
 U_{\rho,k}(N)=-c_\rho e^{-\rho L_N}a_{\rho,k},\qquad
 D_{\rho,k}=|c_\rho|\frac{k!(|\rho|+\sigma/2+1)}{(\sigma/2)^k}.
\]

For every `k<m`, the original finite completed moment satisfies the
exact phased identity

\[
 A_{\rho,k}(N+2)-U_{\rho,k}(N)
 =-c_\rho e^{-\rho L_N}
   \bigl(\widetilde T_{\rho,k}(N+2)-a_{\rho,k}\bigr),
\]

where the shifted tail is the genuine eta integral. The compiled theorem
`norm_pairedEtaFiniteCompletedMoment_sub_euler_le` bounds this error by
`D_rho,k*d_rho(N)/(N+1)`. The endpoint phase is retained before its norm
is taken. The signed pair comparison keeps the partner product error
minus the conjugate original product error, and each product keeps both
error positions. All comparison constants are explicit in
[EtaCurrentEulerPairs.lean](../RiemannGaussian/EtaCurrentEulerPairs.lean).

The new expression `J_E(rho,N)=pairedEtaCurrentEulerExpression rho N`
substitutes these `U` terms in the two original current formulas. In the
simple-zero branch it retains the actual order-zero head, which Lean now
evaluates exactly:

\[
 H_{\rho,0}(N)=\operatorname{Completion}(\rho)
   \left(e^{-\rho\log(2N+4)}-e^{-\rho\log(2N+3)}\right).
\]

In the repeated-zero branch, `k=m-2`, Lean proves

\[
 J_E(\rho,N)=2(m-1)\delta_{N+1}
   \left(P_{\rho^*,k}e^{-2(1-\sigma)L_N}
         -P_{\rho,k}e^{-2\sigma L_N}\right),
\]

where each coefficient is strictly positive:

\[
 P_{\rho,k}=|c_\rho|^2\Re(a_{\rho,k}\overline{a_{\rho,k+1}}),
 \qquad
 \Re(a_{\rho,k}\overline{a_{\rho,k+1}})
 =\frac{(k+1)\sigma}{|\rho|^2}|a_{\rho,k}|^2>0.
\]

These are the compiled theorems
`pairedEtaCurrentEulerMoment_mul_conj`,
`pairedEtaCurrentEulerAdjacentCoefficient_pos`, and
`pairedEtaCurrentEulerExpression_eq_adjacent_endpoints`. The first
identity cancels the common endpoint Fourier phase at the complex level;
the remaining coefficients retain their dependence on the actual zero.

The explicit function `B_rho(N)=pairedEtaCurrentEulerErrorEnvelope rho N`
is proved summable. Its head branch is
`Q_partner*D_partner,0*d_partner(N)/(N+1) + Q_rho*D_rho,0*d_rho(N)/(N+1)`.
Its repeated-zero branch is `(m-1)` times the corresponding sum with
pair constants `D_rho,k*Q_rho + |c_rho|*|a_rho,k|*D_rho,k+1`.
The final estimates, valid at every cutoff, are

\[
 (2N+1)|J_\rho(N)-J_E(\rho,N)|\le4B_\rho(N),
\]
\[
 (2N+1)\|R_N-J_E(\rho,N)\|\le F_\rho(N)+4B_\rho(N).
\]

Both error series are proved summable. The terminal theorem
`pairedEtaLeadingCurrentLinearHeatReturn_euler_error_sum_le` bounds every
finite return error sum by the same genuine finite total
`sum_N (F_rho(N)+4B_rho(N))`.

This supplies an arithmetic estimate on the original current and return,
beyond heat reconstruction alone. It also identifies a specific limit of
the proposed phase approach: the repeated-zero leading expression itself
has no cutoff Fourier oscillation left to average away. Our assessment is
that controlling only oscillatory errors cannot finish the argument;
an independent arithmetic constraint must also control this surviving
completed endpoint contribution. No bound on its first absolute moment
has been proved, and no zero-location conclusion follows from the error
estimate alone.

## Checked growth bound for the actual weighted return moment

The direct current estimate now retains both lower-order zero-tail decays.
Write `d_rho(N)=(2N+3)^(-Re(rho))` as above. The two finite moments in
the repeated-zero leading pair are both below multiplicity. In the
simple-zero branch the actual head and successor order-zero prefix each
retain one endpoint decay. Consequently
`pairedEtaLeadingCurrent_weighted_le_doubleDecay` proves

\[
 (2N+1)|J_\rho(N)|\le4m\left(
 Q_{\rho^*}^2d_{\rho^*}(N)^2+Q_\rho^2d_\rho(N)^2\right).
\]

This is a bound on the original current itself. The exact complex signed
pairs and endpoint identities remain available upstream of this norm
estimate. At `Re(rho)=1/2`, the compiled theorem
`pairedEtaLeadingCurrent_eq_zero_of_re_eq_half` proves the original real
current zero at every cutoff in both multiplicity branches.

Set `e_rho=abs(2*Re(rho)-1)` and
`A_rho=4m*(Q_partner^2+Q_rho^2)`. Reflection preserves `e_rho`, and
the actual critical-strip hypotheses give `0<=e_rho<1`. Both endpoint
powers are at most `(N+1)^(e_rho-1)`.
The finite integral comparison `sum_range_nat_add_one_rpow_le` proves

\[
 \sum_{N<K}(N+1)^r\le\frac{(K+1)^{r+1}}{r+1},\qquad -1<r\le0.
\]

For an actual off-critical zero, `e_rho>0` is proved before division.
The current and return therefore satisfy the explicit bounds

\[
 \sum_{N<K}(2N+1)|J_\rho(N)|
 \le\frac{A_\rho}{e_\rho}(K+1)^{e_\rho},
\]
\[
 S_R(\rho,K):=\sum_{N<K}(2N+1)\|R_N\|
 \le E_{\mathrm{linear}}(\rho)
      +\frac{A_\rho}{e_\rho}(K+1)^{e_\rho}.
\]

At a critical-line zero, exact current cancellation instead gives
`S_R(rho,K)<=E_linear(rho)`. Define the explicit finite constant

\[
 C_\rho=E_{\mathrm{linear}}(\rho)+
 \begin{cases}0,&\Re\rho=1/2,\\ A_\rho/e_\rho,&\Re\rho\ne1/2.\end{cases}
\]

The terminal theorem
`pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le` proves
`S_R(rho,K)<=C_rho*(K+1)^e_rho` for every actual zero and cutoff.
The same module proves
`pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_div_cutoff_tendsto_zero`:

\[
 \frac{S_R(\rho,K)}{K+1}\longrightarrow0.
\]

This is a proved sublinear bound for the original weighted return moment,
including all absolute values, completion constants, and multiplicity.
The exponent still depends on the actual zero's unknown horizontal
position. It supplies no new zero-location constraint. The original goal
requires a bound on `S_R(rho,K)` independent of `K`, without dividing by
the cutoff. That requirement is unchanged and remains open.

## Checked common principal endpoints in both multiplicity branches

The simple-zero head's remaining local phase now has an explicit
summable weighted correction. The compiled modules are
[EtaCurrentHeadHalfWidth](../RiemannGaussian/EtaCurrentHeadHalfWidth.lean),
[EtaCurrentHalfStepHead](../RiemannGaussian/EtaCurrentHalfStepHead.lean),
[EtaCurrentHalfStepPairs](../RiemannGaussian/EtaCurrentHalfStepPairs.lean),
and [EtaCurrentPrincipalEndpoints](../RiemannGaussian/EtaCurrentPrincipalEndpoints.lean).

Write `q=2N+3`, `x=N+1`, `a=log(q)`, `L=log(q+2)`,
`delta=log((q+2)/q)`, and `w=log((q+1)/q)`. The exact interval identity
`pairedEtaShiftedLogHeadWidth_sub_half_step_eq` gives

\[
 w-\delta/2=\tfrac12\log\left(1+\frac1{q(q+2)}\right),
 \qquad 0\le w-\delta/2\le\frac1{2x^2}.
\]

For `c_rho=pairedEtaXiCompletionFactor(rho)*rho`, put
`K_rho=norm(rho)*exp(norm(rho))` and
`D_head(rho)=norm(c_rho)*(2*K_rho+1)`. The original completed head
`H_rho(N)` is compared with

\[
 H^{1/2}_\rho(N)=-c_\rho e^{-\rho L}\delta/2
               =\delta\rho U_{\rho,0}(N).
\]

`pairedEtaHeadCompletedMoment_sub_halfStep` retains its exact complex
defect, with the integral variation, unequal support/gap widths, and
endpoint translation separately visible. The compiled theorem
`norm_pairedEtaHeadCompletedMoment_sub_halfStep_le` proves

\[
 \|H_\rho(N)-H^{1/2}_\rho(N)\|
 \le D_{\mathrm{head}}(\rho)d_\rho(N)/x^2.
\]

Define `C_head(rho)=D_head(rho)*pairedEtaCurrentEulerMomentAmplitude(rho,0)`
and the explicitly summable envelope

\[
 B_{\mathrm{head}}(\rho,N)=
 \frac{C_{\mathrm{head}}(\rho^*)d_{\rho^*}(N)
       +C_{\mathrm{head}}(\rho)d_\rho(N)}{x}.
\]

Both signed complex product defects are retained in
`pairedEtaCurrentEulerHeadPair_sub_halfStep`; their real-current error
with the original odd weight is at most `4*B_head(rho,N)`.
The half-step product's common endpoint phase cancels exactly in
`pairedEtaCurrentHalfStepHead_mul_conj_euler`. Its simple coefficient is

\[
 A_{\mathrm{simple}}(\rho)=
 2\sigma\|c_\rho\|^2|a_{\rho,0}|^2>0.
\]

The multiplicity-selected coefficient is

\[
 A_\rho=\begin{cases}
 A_{\mathrm{simple}}(\rho),&m=1,\\
 2(m-1)P_{\rho,m-2},&m\ge2,
 \end{cases}
\]

where `P` is the previously evaluated completed adjacent Euler
coefficient. `pairedEtaCurrentPrincipalCoefficient_pos` proves
`A_rho>0` in both actual branches. Reflection preserves the multiplicity.
The resulting common principal expression is

\[
 J_{\mathrm{principal}}(\rho,N)=\delta_{N+1}
 \left[A_{\rho^*}e^{-2(1-\sigma)L_N}
       -A_\rho e^{-2\sigma L_N}\right].
\]

It equals the repeated-zero Euler expression exactly and the simple
half-step expression exactly. The original current has odd-weighted
error at most `4*B_Euler+4*B_head`. The **unchanged** actual linear-width
return has odd-weighted norm error at most

\[
 F_{\mathrm{principal}}(\rho,N)=
 F_{\mathrm{heat}}(\rho,N)+4B_{\mathrm{Euler}}(\rho,N)
                         +4B_{\mathrm{head}}(\rho,N),
\]

whose series is proved summable. The terminal theorem
`pairedEtaLeadingCurrentLinearHeatReturn_principal_firstMoment_stability`
proves, at every cutoff `K`,

\[
 \left|S_R(\rho,K)-
 \sum_{N<K}(2N+1)|J_{\mathrm{principal}}(\rho,N)|\right|
 \le\sum_{N\ge0}F_{\mathrm{principal}}(\rho,N)<\infty.
\]

The sum's finiteness is the named summability theorem, not an inference
from Lean's totalized `tsum`. This completes the simple-head phase
comparison on the original return. It leaves two positive leading
coefficients and complementary horizontal powers. The next quantitative
test is whether that explicit term forces the previously allowed
displacement-power growth off the critical line. No cutoff-independent
bound for the principal term, original current, or original return has
been proved here.

## Checked sharp growth under the off-critical hypothesis

The quantitative test above is now proved in
[EtaCurrentPrincipalDominance](../RiemannGaussian/EtaCurrentPrincipalDominance.lean),
[EtaCurrentPrincipalLowerBound](../RiemannGaussian/EtaCurrentPrincipalLowerBound.lean),
and [EtaCurrentReturnSharpGrowth](../RiemannGaussian/EtaCurrentReturnSharpGrowth.lean).
It applies to the unchanged actual linear-width Gaussian return. Its
off-critical hypothesis is explicit; it supplies no assertion that such
a zero exists or a contradiction excluding one.

Let `e=abs(2*Re(rho)-1)`. The coefficient `A_dom` is `A_rho` when
`Re(rho)<=1/2` and `A_partner` otherwise; `A_fast` is the other coefficient.
Both are strictly positive. The exact signed factorization
`pairedEtaCurrentPrincipalEndpoint_eq_dominant_factor` retains the side
sign `s_rho=-1` on the left of the critical line and `+1` on the right:

\[
 J_{\mathrm{principal}}(\rho,N)=s_\rho\delta_{N+1}
 e^{(e-1)L_N}\left(A_{\mathrm{dom}}-A_{\mathrm{fast}}e^{-2eL_N}\right).
\]

For an actual off-critical zero, `0<e<1` is proved and
`A_fast*exp(-2eL_N)` tends to zero. Eventually the bracket is at least
`A_dom/2`. The literal cutoff geometry also gives

\[
 (2N+1)\delta_{N+1}\ge\frac25,
 \qquad e^{(e-1)L_N}\ge5^{e-1}(N+1)^{e-1}.
\]

Consequently `pairedEtaCurrentPrincipalEndpoint_weighted_lower_eventually`
proves the eventual bound

\[
 (2N+1)|J_{\mathrm{principal}}(\rho,N)|
 \ge c_{\mathrm{floor}}(\rho)(N+1)^{e-1},
 \qquad c_{\mathrm{floor}}(\rho)=\frac{A_{\mathrm{dom}}}{5}5^{e-1}>0.
\]

The finite power-sum lower comparison is

\[
 \frac{(K+1)^e-1}{e}\le\sum_{N<K}(N+1)^{e-1}.
\]

For a finite cutoff `N0` beyond which dominance holds, define the
explicit allowance

\[
 D_\rho(N_0)=\sum_{N\ge0}F_{\mathrm{principal}}(\rho,N)
 +\frac{c_{\mathrm{floor}}(\rho)}e
 +\sum_{N<N_0}c_{\mathrm{floor}}(\rho)(N+1)^{e-1}.
\]

The infinite error sum is already proved summable, and all terms are
nonnegative. The compiled theorem
`pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_lower_with_offset`
constructs such a finite `N0` and proves, at **every** terminal cutoff,

\[
 S_R(\rho,K)\ge
 \frac{c_{\mathrm{floor}}(\rho)}e(K+1)^e-D_\rho(N_0).
\]

It uses the exact first-absolute-moment stability bound; it does not
replace the original return by a model without accounting for the error.
The terminal theorem
`pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_power_bounds_eventually`
therefore proves

\[
 \frac{c_{\mathrm{floor}}(\rho)}{2e}(K+1)^e
 \le S_R(\rho,K)\le C_\rho(K+1)^e
 \quad\text{eventually}.
\]

`pairedEtaCurrentReturnGrowthLowerCoefficient_pos` supplies the strictly
positive lower coefficient. The same module proves
`pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_tendsto_atTop_of_re_ne_half`:
the actual weighted first absolute moment tends to infinity under the
off-critical hypothesis.

The previous growth exponent is thus sharp for the unchanged return at
any hypothetical off-critical zero. A further approximation whose
weighted norm error has a fixed finite sum cannot remove this positive
power growth. The original goal therefore needs an independent
arithmetic argument excluding the surviving off-critical contribution.
The new lower bound does not provide that argument, improve a zero
proportion, or locate an additional zeta zero.

## Checked finite Möbius constraint on the original completed tails

The sharp growth result rules out progress through a smaller summable
local error alone. The next arithmetic input now couples different
prefixes through their actual multiplicative indices. The compiled
modules are [EtaMoebiusDivisor](../RiemannGaussian/EtaMoebiusDivisor.lean),
[EtaMoebiusFinitePrefix](../RiemannGaussian/EtaMoebiusFinitePrefix.lean),
and [EtaMoebiusCompletedTail](../RiemannGaussian/EtaMoebiusCompletedTail.lean).

Let `a(n)=1` for odd `n` and `-1` for even `n`. Mathlib's classical
Möbius inversion theorem gives the exact finite coefficient identity

\[
 \sum_{dk=n}\mu(d)a(k)=\mathbf1_{n=1}-2\mathbf1_{n=2}
 \qquad(n\ge1).
\]

`sum_moebius_mul_pairedEtaDirichletTerm` retains both complex powers
`d^(-s)` and `k^(-s)`, using their exact natural-product identity.
`sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix` gives a finite
bijection from the divisor fibers to pairs with `1<=d<=M` and
`1<=k<=floor(M/d)`. There is no infinite rearrangement.
Writing `E_m(s)=sum_(1<=k<=m) a(k)k^(-s)`, the resulting identity is

\[
 \sum_{d\le M}\mu(d)d^{-s}E_{\lfloor M/d\rfloor}(s)
 =1-2\,2^{-s},\qquad M\ge2.
\]

Every such prefix is proved to equal the repository's original
`pairedEtaCorePartialSum(m/2,s)` plus `m^(-s)` when `m` is odd.
That endpoint term cannot be omitted. For an actual zero `rho`, let
`X_rho=pairedEtaXiCompletionFactor(rho)` and

\[
 B_\rho(m)=X_\rho\mathbf1_{m\text{ odd}}m^{-\rho}.
\]

The original zeroth completed moment is exactly
`X_rho*pairedEtaCorePartialSum(N,rho)`.
Since the actual multiplicity is positive, its zeroth order is below
the multiplicity and it is the negative genuine completed tail
`-T_rho(N,0)`. Thus the compiled terminal theorem
`pairedEtaCompletedMoebiusTailAggregate_eq_source` proves

\[
 \sum_{d\le M}\mu(d)d^{-\rho}
 \left[-T_\rho\!\left(\left\lfloor
       \frac{\lfloor M/d\rfloor}{2}\right\rfloor,0\right)
       +B_\rho(\lfloor M/d\rfloor)\right]
 =X_\rho(1-2\,2^{-\rho}),\qquad M\ge2.
\]

`pairedEtaCompletedMoebiusSource_ne_zero` proves the right-hand side
nonzero using the actual critical-strip hypotheses. Its norm is therefore
a fixed positive value, independent of `M`, for the complete **signed
linear aggregate**. This is not the original current's weighted first
absolute moment. No quadratic estimate or cancellation of that current
is inferred from this identity.

Möbius inversion itself is classical. The new project interface is its
exact application to the existing completed eta moments, with divided
cutoffs, complex phases, and unpaired endpoints retained. More general
dilation methods are part of the classical
[Nyman–Beurling/Müntz framework](https://arxiv.org/abs/math/0505453);
that connection does not supply the missing approximation or norm estimate.
No priority claim is made here.

The quadratic test below now propagates these simultaneous linear
constraints through the actual completed moment pairs, accounting for
all cross-cutoff terms. Their transfer to the original current and its
Gaussian returns is still open. Taking absolute values before exploiting
the Möbius phases loses the arithmetic cancellation that this identity
has preserved.

## Checked quadratic estimate and surviving cross-cutoff correlations

The compiled modules are
[EtaMoebiusTermBounds](../RiemannGaussian/EtaMoebiusTermBounds.lean) and
[EtaMoebiusQuadratic](../RiemannGaussian/EtaMoebiusQuadratic.lean).
Write `sigma=Re(rho)` and retain each exact completed term as

\[
 F_{\rho,M}(d)=\mu(d)d^{-\rho}
 \left[-T_\rho\!\left(\left\lfloor
       \frac{\lfloor M/d\rfloor}{2}\right\rfloor,0\right)
       +B_\rho(\lfloor M/d\rfloor)\right].
\]

`pairedEtaCompletedMoebiusTerm_eq_completed_prefix` identifies it with
`mu(d)*d^(-rho)*X_rho*E_floor(M/d)(rho)` exactly. No endpoint or phase
has been removed. At every actual zero,
`norm_pairedEtaUnpairedDirichletPrefix_le` proves

\[
 |E_m(\rho)|\le (|\rho|/\sigma+1)m^{-\sigma},\qquad m\ge1.
\]

The original zero-tail bound controls the paired part. The odd endpoint
contributes the additional `1` to the coefficient. For every
`1<=d<=M`, the integer division estimate
`half_le_mul_nat_div` gives `M/2<=d*floor(M/d)`. Keeping the full complex
term before applying its norm yields the compiled bound
`norm_pairedEtaCompletedMoebiusTerm_le`:

\[
 |F_{\rho,M}(d)|\le C_\rho M^{-\sigma},\qquad
 C_\rho=|X_\rho|(|\rho|/\sigma+1)2^\sigma>0.
\]

This coefficient is explicit and independent of both `M` and `d`.
`pairedEtaCompletedMoebiusDiagonal_le` then proves, for every `M>=1`,

\[
 0\le D_\rho(M):=\sum_{d\le M}|F_{\rho,M}(d)|^2
 \le C_\rho^2 M^{1-2\sigma}.
\]

This is a genuine quadratic estimate for the original completed divisor
terms. It does not bound the current's weighted absolute moment.
The complete complex kernel is retained as
`F_rho,M(d)*conj(F_rho,M(e))`. Define its off-diagonal sum by

\[
 O_\rho(M)=\sum_{d\le M}\sum_{\substack{e\le M\\e\ne d}}
 F_{\rho,M}(d)\overline{F_{\rho,M}(e)}.
\]

`pairedEtaCompletedMoebiusOffDiagonal_eq_source_sub_diagonal`
proves the exact complex identity

\[
 O_\rho(M)=|C_{\mu,\rho}|^2-D_\rho(M),\qquad
 C_{\mu,\rho}=X_\rho(1-2\,2^{-\rho})\ne0,\quad M\ge2.
\]

Consequently,
`norm_pairedEtaCompletedMoebiusOffDiagonal_sub_source_le` proves

\[
 \left|O_\rho(M)-|C_{\mu,\rho}|^2\right|
 \le C_\rho^2M^{1-2\sigma}.
\]

The reflected signed kernel uses the existing
`etaSignedCompletedPair(F_partner(d), F_partner(e), F_rho(d), F_rho(e))`.
`sum_offDiagonal_pairedEtaSignedCompletedMoebiusPairKernel`
retains both original completion channels and their exact orientation:
its sum over distinct divisors is the signed source pair minus
`D_partner(M)-D_rho(M)`. The subtraction of the diagonal is an identity,
not permission to omit it or its off-diagonal complement.

At a hypothetical actual zero with `sigma>1/2`, the proved exponent is
negative. The terminal theorem
`pairedEtaCompletedMoebiusOffDiagonal_tendsto_source_of_half_lt_re`
therefore gives

\[
 D_\rho(M)\longrightarrow0,
 \qquad O_\rho(M)\longrightarrow |C_{\mu,\rho}|^2>0.
\]

`pairedEtaCompletedMoebiusOffDiagonal_re_lower_eventually` additionally
proves that the real part is eventually at least
`|C_mu,rho|^2/2`. The distinct-divisor correlations carry a fixed positive
amount even though the positive diagonal energy vanishes. A quadratic
argument must therefore retain and estimate these correlations. Smallness
of the individual terms or their squared-norm sum does not make the
complete pair sum small.

This test provides an explicit arithmetic rate and identifies the terms
that prevent a diagonal reduction. It does not exclude an off-critical
zero. No new zero-location bound, uniform bound for the original return,
or RH theorem follows from this slice. Priority for the auxiliary estimate
has not been established.

## Checked dyadic cancellation in the actual completed correlations

The next arithmetic estimate is now compiled in
[EtaMoebiusEndpointPhase](../RiemannGaussian/EtaMoebiusEndpointPhase.lean),
[EtaMoebiusDyadicPhase](../RiemannGaussian/EtaMoebiusDyadicPhase.lean), and
[EtaMoebiusDyadicCorrelation](../RiemannGaussian/EtaMoebiusDyadicCorrelation.lean).
It applies to the original **zeroth** completed Möbius terms. It uses the
arithmetic parity of their actual divided cutoffs to cancel an entire
odd/even divisor interaction over a full period.

Write

\[
 q(m)=2\lfloor m/2\rfloor+1,
 \qquad
 \widehat F_{\rho,M}(d)=(d\,q(\lfloor M/d\rfloor))^\rho F_{\rho,M}(d),
 \qquad
 V_{\rho,M}(d)=\frac{\mu(d)X_\rho}{2}a(\lfloor M/d\rfloor).
\]

The normalization is the **complex power of each literal divisor times
its paired odd endpoint**. It is not an implicit common cutoff or a
replacement of the original current. The theorem
`pairedEtaCompletedMoebiusEndpointPair_eq_physical_kernel` retains both
such powers multiplying the original complex pair kernel.

`pairedEtaUnpairedDirichletPrefix_endpoint_phase_error` proves the exact
complex identity

\[
 q(m)^\rho E_m(\rho)-a(m)/2
 =-\left(G_{\rho,\lfloor m/2\rfloor}+1/2\right),
\]

where `G` is the repository's original normalized finite eta-gap error.
This uses the actual zero equation and retains the unpaired odd term.
The proved Euler gap estimate and `|mu(d)|<=1` give

\[
 |\widehat F_{\rho,M}(d)-V_{\rho,M}(d)|
 \le \frac{H_\rho}{q(\lfloor M/d\rfloor)}
 \le \frac{2H_\rho d}{M},\qquad M,d\ge1,
 \qquad H_\rho=|X_\rho|\,|\rho|\,|\rho+1|.
\]

The terminal bound for this step is
`norm_pairedEtaCompletedMoebiusEndpointPhase_sub_parity_cutoff_le`.
The divisor dependence is explicit. The coefficient `H_rho` is finite
and independent of both the divisor and the cutoff.

Let `d` be odd and `e=2k` be any positive even divisor. A shift by `d*e`
adds the even number `e` to `floor(M/d)` and the odd number `d` to
`floor(M/e)`. The first parity phase is preserved and the second changes
sign. Consequently,
`sum_pairedEtaCompletedMoebiusParityPair_period_eq_zero` proves, for
every starting integer `A`,

\[
 \sum_{0\le r<2de}V_{\rho,A+r}(d)\overline{V_{\rho,A+r}(e)}=0.
\]

Both completion and Möbius coefficients remain in this exact complex
identity. The proof does not average absolute values of the leading terms.
The actual pair error is then split at both complex positions before
taking its norm. Define

\[
 \mathcal E_\rho(d,e,A)=
 \frac{H_\rho|X_\rho|(d+e)}{A}
 +\frac{4H_\rho^2de}{A^2}.
\]

`norm_pairedEtaCompletedMoebiusDyadicCorrelation_le` proves

\[
 \left|\frac1{2de}\sum_{0\le r<2de}
   \widehat F_{\rho,A+r}(d)\overline{\widehat F_{\rho,A+r}(e)}\right|
 \le \mathcal E_\rho(d,e,A),\qquad A\ge1.
\]

This controls the actual completed terms, including their finite-tail
error. The quadratic error term `de/A^2` is retained. For each fixed pair
of divisors the right side tends to zero, giving the compiled limit
`pairedEtaCompletedMoebiusDyadicCorrelation_tendsto_zero` at every
actual zero, without a critical-line hypothesis.

The original `etaSignedCompletedPair` orientation is carried through the
same period average. Its exact channel identity is the partner average
minus the conjugate original average. The terminal theorem
`norm_pairedEtaSignedCompletedMoebiusDyadicCorrelation_le` bounds its
norm by

\[
 \mathcal E_{\rho^*}(d,e,A)+\mathcal E_\rho(d,e,A).
\]

`pairedEtaSignedCompletedMoebiusDyadicCorrelation_tendsto_zero`
proves the corresponding signed limit with both actual completion
channels. No multiplicity-one assumption is used; the carrier here is
still the zeroth completed moment, not all higher centered orders.

The arithmetic cancellation is a new checked estimate on an existing
carrier. Its present limits matter to the full goal: the normalizers
depend on the divisor, the period length is `2*d*e`, and the error grows
with both divisor sizes. A fixed-pair period average does not control the
growing divisor family at a single cutoff or the original weighted
absolute-return sum. The same-parity interactions, higher centered
orders, and simple-zero head must still be handled in any transfer to
that target. No zero-location bound or RH theorem is claimed here.

As a research check, the related Nyman–Beurling asymptotic of
[Bettin–Conrey–Farmer](https://arxiv.org/abs/1211.5191) assumes RH and an
additional derivative-moment estimate. It supplies no unconditional
bound for this goal. The estimate above instead uses the repository's
proved Euler error and a finite parity identity; no external analytic
premise was added. Priority for the combined auxiliary mathematics has
not been established.

### Global parity recurrences and uniform block bounds

The growing zeroth-order divisor family is now controlled at each physical
cutoff by an exact recurrence, rather than by summing fixed-pair error
bounds. The source object is unchanged:

\[
 F_{\rho,M}(d)=\mu(d)d^{-\rho}X_\rho
 E_{\lfloor M/d\rfloor}(\rho),\qquad
 O_\rho(M)=\sum_{\substack{1\le d\le M\\d\text{ odd}}}F_{\rho,M}(d),
 \quad E_\rho(M)=\sum_{\substack{1\le d\le M\\d\text{ even}}}F_{\rho,M}(d).
\]

Here the unpaired prefix in the first expression is still exactly the
negative actual completed tail plus its possible odd endpoint, with the
original completion factor. The symbol `E_rho(M)` in the last expression
denotes the even aggregate, not that prefix. Put
`r_rho = 2^(-rho)` and `C_rho = X_rho*(1-2*r_rho)`.

`pairedEtaCompletedMoebiusEvenAggregate_eq_half_odd` and
`pairedEtaCompletedMoebiusOddAggregate_recurrence` prove the exact
complex identities

\[
 E_\rho(M)=-r_\rho O_\rho(\lfloor M/2\rfloor),\qquad
 O_\rho(M)=C_\rho+r_\rho O_\rho(\lfloor M/2\rfloor)\quad(M\ge2).
\]

The initial values are `O_rho(0)=0` and `O_rho(1)=X_rho`. The proof uses
the checked coefficient identity
`mu(2*d) = if Odd d then -mu(d) else 0` and a bijection of the entire
even divisor set with the halved cutoff. All endpoints and complex phases
survive these steps. The full finite Möbius source identity supplies the
second recurrence.

Since `a_rho = |r_rho| = 2^(-Re rho) < 1`, define the explicit finite
constant

\[
 B_\rho=|X_\rho|+\frac{|C_\rho|}{1-a_\rho}.
\]

The terminal theorems `norm_pairedEtaCompletedMoebiusOddAggregate_le`
and `norm_pairedEtaCompletedMoebiusEvenAggregate_le` prove, for every
natural cutoff including zero,

\[
 |O_\rho(M)|\le B_\rho,\qquad |E_\rho(M)|\le a_\rho B_\rho.
\]

Strong induction on the cutoff applies the strict contraction at its
halved argument. There is no divisor-dependent normalizer, period average,
or restriction to a fixed divisor family in these bounds.

For parity labels `p,q`, let `A_rho(M,p)` be the appropriate odd or even
aggregate and `b_rho(p)` its above bound. The literal block retains
every pair at the common physical cutoff:

\[
 Q_\rho(M;p,q)=\sum_{d\in I_p(M)}\sum_{e\in I_q(M)}
 F_{\rho,M}(d)\overline{F_{\rho,M}(e)}.
\]

`pairedEtaCompletedMoebiusParityBlock_eq_pair` identifies this with
`A_rho(M,p)*conj(A_rho(M,q))` before applying any norm. The theorem
`norm_pairedEtaCompletedMoebiusParityBlock_le` bounds all four block
sums by `b_rho(p)*b_rho(q)`, including the same-parity interactions.
For the original signed reflected kernel,
`pairedEtaSignedCompletedMoebiusParityBlock_eq_channels` retains the
partner block minus the conjugate original block. The terminal estimate
`norm_pairedEtaSignedCompletedMoebiusParityBlock_le` gives

\[
 |Q^{\mathrm{signed}}_\rho(M;p,q)|\le
 b_{\rho^*}(p)b_{\rho^*}(q)+b_\rho(p)b_\rho(q).
\]

These are uniform bounds on the **sums of the full blocks**, not sums of
the absolute values of their entries or bounds for arbitrary
divisor-dependent feature vectors. They also do not sum over physical
cutoffs with the original current's weights. They hold throughout
`0 < Re rho < 1`, so the estimate itself does not exclude an off-critical
zero. The existing conditional power-growth theorem for the original
return remains compatible with them. A proved estimate recovering the
original current from the retained divisor data is still missing,
including the higher centered moments and the simple-zero head. The
contraction and finite inversion are classical arithmetic; no priority
claim is made for their application here.

### Exact inverse to the original current and its weight cost

The first transfer identity is now proved, with its missing estimate
distinguished from the identity. Classical odd-divisor inversion gives
`sum_pairedEtaCompletedOddInverseTerm`:

\[
 X_\rho E_M(\rho)=\sum_{\substack{1\le d\le M\\d\text{ odd}}}
 d^{-\rho}O_\rho(\lfloor M/d\rfloor).
\]

The prefix `E_M` in this formula is the original unpaired Dirichlet
prefix. The proof checks the odd-restricted Möbius convolution, retains
the exact complex product powers, and regroups only finite divisor
fibers. It includes cutoff zero with its actual zero initial value.
At an even endpoint, `pairedEtaFiniteCompletedMoment_zero_eq_oddInverse`
therefore gives the original completed moment

\[
 A_\rho(N,0)=\sum_{\substack{1\le d\le2N\\d\text{ odd}}}
 d^{-\rho}O_\rho(\lfloor2N/d\rfloor).
\]

For the head current put `M=2*(N+2)` and define, just for this display,
`B_rho(N,d)=d^(-rho)*O_rho(floor(M/d))`. Before taking its real part,
`pairedEtaHeadCompletedMomentPair_zero_eq_oddInverse` retains the
complex signed sum

\[
 \sum_{\substack{1\le d\le M\\d\text{ odd}}}
 \operatorname{etaSignedCompletedPair}
   (H_{\rho^*}(N,0),B_{\rho^*}(N,d),H_\rho(N,0),B_\rho(N,d)).
\]

`pairedEtaLeadingCurrent_eq_oddInverse_head` proves that twice the real
part of this sum is exactly `J_rho(N)` when the actual multiplicity is
one. The original shifted head coordinate, successor prefix cutoff,
completion factors, and conjugation orientation all remain unchanged.
This is a proved connection to the original current in that branch,
not a bound for its weighted absolute moment. Higher centered orders
are not covered by this zeroth-order inverse.

Taking norms term by term introduces the literal weight mass

\[
 W_\rho(M)=\sum_{\substack{1\le d\le M\\d\text{ odd}}}|d^{-\rho}|.
\]

`norm_completed_pairedEtaUnpairedDirichletPrefix_le_oddInverseWeightMass`
proves the resulting bound `|X_rho E_M(rho)| <= B_rho W_rho(M)` using the
previous uniform odd-aggregate constant. The exact index count and the
finite integral comparison now give

\[
 \frac{M^{1-\sigma}}2\le W_\rho(M)\le
 \frac{(M+1)^{1-\sigma}}{1-\sigma}\qquad(M\ge1),
 \quad \sigma=\Re\rho.
\]

The compiled endpoints are `pairedEtaOddInverseWeightMass_lower`,
`pairedEtaOddInverseWeightMass_upper`, and
`pairedEtaOddInverseWeightMass_tendsto_atTop`. In particular, the weight
cost diverges at **every** actual zero, including the critical line.
This diagnoses the loss in this particular triangle estimate. It does
not prove that the inverse operator norm diverges after grouping equal
divided cutoffs, nor that the original signed current diverges. No
cancellation in the richer inverse sum has been ruled out.

The next estimate must therefore act on that weighted signed sum before
absolute values, with an accumulated cutoff bound strong enough for the
original `S_rho(K)`. Merely inserting the uniform aggregate constant
under a sum of inverse-weight norms cannot give it. The inversion and
power comparison are classical; no novelty priority is claimed.

### Grouped inverse Mellin phases and actual cross-cutoff cancellation

The next test sums the inverse weights with a common divided cutoff
before taking any norm. It therefore goes beyond the previous sum of
individual weight norms. At physical cutoff `4*K`, all odd indices in
`2*K < d <= 4*K` have divided cutoff one. The complete power sum is

\[
 G_\rho(K)=\sum_{0\le k<K}(2K+2k+1)^{-\rho},\qquad
 b_\rho=\frac{2^{1-\rho}-1}{2(1-\rho)}.
\]

`norm_pairedEtaOddTopPowerSum_sub_half_integral_le` compares this
literal midpoint sum with half its complex power integral. The proof
uses an explicit positive-axis derivative bound, checks interval
integrability, and joins every adjacent interval exactly. The theorem
`half_integral_cpow_eq_pairedEtaOddTopPowerMain` evaluates that integral
without discarding its phase. Consequently
`norm_pairedEtaOddTopPowerSum_sub_main_le` proves

\[
 \left|G_\rho(K)-(2K)^{1-\rho}b_\rho\right|
 \le \frac{|\rho|}{2}(2K)^{-\sigma},\qquad K\ge1,
 \quad\sigma=\Re\rho.
\]

The coefficient retains its ordinate dependence. It is nonzero throughout
the open critical strip: `pairedEtaOddTopPowerCoefficient_ne_zero` uses
`|2^(1-rho)|=2^(1-sigma)>1`. The lower estimate
`pairedEtaOddTopPowerSum_norm_lower_of_cutoff` gives

\[
 |G_\rho(K)|\ge\frac{|b_\rho|}{2}(2K)^{1-\sigma}
 \quad\text{if }K\ge1\text{ and }|\rho|\le2K|b_\rho|.
\]

`pairedEtaOddTopPowerSum_norm_tendsto_atTop` therefore proves that
this **whole grouped coefficient**, not only its termwise absolute
majorant, is unbounded. No inverse operator norm is introduced here.

For the actual completed inverse define its two retained pieces

\[
 T_\rho(K)=\sum_{\substack{2K<d\le4K\\d\text{ odd}}}
 d^{-\rho}O_\rho(\lfloor4K/d\rfloor),\qquad
 B_\rho(K)=\sum_{\substack{1\le d\le2K\\d\text{ odd}}}
 d^{-\rho}O_\rho(\lfloor4K/d\rfloor).
\]

The symbols `B_rho(K)` and `b_rho` here denote the bottom inverse block
and Mellin coefficient, respectively, not the earlier uniform parity
constant. `pairedEtaCompletedOddInverseTop_eq_powerSum` gives the exact
complex equality `T_rho(K)=X_rho*G_rho(K)`. The finite partition theorem
`pairedEtaCompletedOddInverseBottom_add_top` retains
`B_rho(K)+T_rho(K)=A_rho(2*K,0)`.

With `L_rho(K)=X_rho*(2*K)^(1-rho)*b_rho`, the terminal estimates are

\[
 |T_\rho(K)-L_\rho(K)|
 \le |X_\rho|\frac{|\rho|}{2}(2K)^{-\sigma},
\]
\[
 |B_\rho(K)+L_\rho(K)|
 \le |X_\rho|\left[
 (|\rho|/\sigma+1)(4K)^{-\sigma}
 +\frac{|\rho|}{2}(2K)^{-\sigma}\right].
\]

These are `norm_pairedEtaCompletedOddInverseTop_sub_main_le` and
`norm_pairedEtaCompletedOddInverseBottom_add_main_le`. The latter
uses the actual zero-prefix decay only after retaining the exact sum
of the two inverse blocks. The theorem
`pairedEtaCompletedOddInverseTop_norm_tendsto_atTop` proves that the
top completed piece itself is unbounded. Its growing phase is canceled
by the other divided cutoffs, with the explicit decaying error above.

Thus grouping equal cutoffs does not justify bounding each grouped
inverse piece separately by a cutoff-independent constant. The new
constraint preserves the cancellation across different cutoffs that
such a transfer would lose. It is still a zeroth-moment statement,
valid separately in both completion channels, and does not establish
the original signed current's uniform weighted absolute moment. The
existing conditional off-critical power growth remains compatible with
all these identities. Midpoint quadrature and Mellin integration are
classical; no priority claim is made for this application.

### Independent prime positivity and an explicit zero margin

The preceding inverse identities are compatible with off-critical power
growth. A new arithmetic input comes from the classical three-four-one
Euler-product inequality, already proved in pinned Mathlib as
`DirichletCharacter.norm_LFunction_product_ge_one`. Its specialization
`one_le_riemannZeta_three_four_one` preserves the actual zeta values:

\[
 1\le |\zeta(1+x)|^3|\zeta(1+x+i\gamma)|^4
       |\zeta(1+x+2i\gamma)|,\qquad x>0.
\]

No positivity of a difference of heat Grams is inferred. Instead, the
literal eta support bound supplies the needed analytic upper estimates.
Write `Z1(s)=riemannZeta₁(s)` for Mathlib's entire completion of
`(s-1)*zeta(s)` at one. `norm_pairedEtaCore_le_div_re` proves
`|eta(s)| <= |s|/Re(s)` throughout the positive half-plane. The exact
identity `pairedEtaCore_mul_sub_one_eq_factor_riemannZeta₁` retains

\[
 (s-1)\eta(s)=(1-2\cdot2^{-s})Z_1(s),
\]

including the removable point. Rectangles centered at integer multiples
of `2*pi/log(2)` have horizontal edges at dyadic phase minus one and
vertical edges at real parts `1/2` and `3/2`. The factor's norm is at least
`1/4` on the full boundary. The maximum-modulus principle for the entire
`Z1` therefore crosses all interior dyadic resonances without dividing
by a vanishing factor. The terminal bounds are

\[
 |Z_1(s)|\le8(|\Im s|+20)^2,
 \qquad \tfrac12\le\Re s\le\tfrac32,
\]
\[
 |Z_1'(s)|\le32(|\Im s|+21)^2,
 \qquad \tfrac34\le\Re s\le\tfrac54.
\]

These are `norm_riemannZeta₁_le_etaStrip` and
`norm_deriv_riemannZeta₁_le_etaStrip`; the latter uses Cauchy's estimate
on an actual disc of radius `1/4`. The horizontal mean-value theorem
then compares the original function to a genuine zero. For
`rho=sigma+i*gamma`, `sigma>=3/4`, `d=1-sigma`, and `t=|gamma|`,
`norm_riemannZeta₁_reflected_across_one_le` gives

\[
 |Z_1(1+d+i\gamma)|\le64(t+21)^2d.
\]

The zero's ordinate is nonzero by the strict positivity of the original
eta mass at frequency zero, checked in
`NontrivialZetaZero.im_ne_zero_of_eta_mass`. The pole denominator and
the same strip bound also prove

\[
 |\zeta(1+d)|\le3200/d,\qquad
 |\zeta(1+d+2i\gamma)|\le16(t+21)^2/t.
\]

Combining these actual upper bounds with prime positivity yields
`one_le_etaPrimeProduct_zero_gap`:

\[
 1\le\frac{16\cdot3200^3\cdot64^4(t+21)^{10}}{t^5}(1-\sigma).
\]

Define the explicit function, with the Cauchy strip threshold retained,

\[
 \delta(y)=\min\left\{\frac14,
 \frac{|y|^5}{16\cdot3200^3\cdot64^4(|y|+21)^{10}}\right\}.
\]

It is strictly positive when `y!=0` by
`etaPrimeProductZeroMargin_pos`. Reflection supplies the left margin
at the same ordinate. Thus
`nontrivialZetaZero_mem_etaPrimeProduct_strip` proves for **every actual
nontrivial zero**, with no growth or zero-free premise,

\[
 \delta(\gamma)\le\sigma\le1-\delta(\gamma).
\]

This is a deliberately crude zero-location bound derived using classical
methods. The [classical prime-positivity argument](https://people.math.harvard.edu/~elkies/M229.20/free.pdf)
has long supported substantially stronger analytic zero-free regions;
no improvement over that literature or novelty priority is claimed here.
The contribution to this proof chain is the fully discharged eta-based
estimate and its transport to the unchanged current/return exponent.

Specifically,
`pairedEtaCurrentHorizontalDisplacement_le_etaPrimeProduct` bounds
`abs(2*sigma-1)` by `1-2*delta(gamma)`, and
`pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_etaPrimeProduct`
proves

\[
 S_R(\rho,K)\le C_\rho(K+1)^{1-2\delta(\gamma)}.
\]

The existing completion- and multiplicity-dependent constant is retained.
Both analytic multiplicity branches are covered by the original return
growth theorem. `etaPrimeProduct_return_exponent_bounds` explicitly places
the new exponent in `[1/2,1)`. It therefore still permits cutoff growth.
The interior off-critical contribution remains unexcluded, and the full
cutoff-independent weighted arithmetic estimate remains open.

## Centered Möbius reconstruction at every moment order

The full moment transform now extends the arithmetic reconstruction to every
order, including the adjacent pair required at repeated zeros. Write
`c_rho = X_rho*rho` and let `Q_(k,rho)(u)` denote the existing centered
antiderivative polynomial, expressed in its offset `u`:

\[
 Q_{0,\rho}(u)=\rho^{-1},\qquad
 Q_{k+1,\rho}(u)=\frac{u^{k+1}}\rho+
   \frac{k+1}\rho Q_{k,\rho}(u).
\]

The new unpaired arithmetic prefix is

\[
 E_{k,\rho}(M,a)=\sum_{1\le n\le M}
   a(n)n^{-\rho}Q_{k,\rho}(\log n-a),
\]

where `a(n)` is the original odd-positive/even-negative eta coefficient.
`pairedEtaUnpairedCenteredMomentPrefix_even` identifies its even cutoffs
with the original finite centered eta moment. The theorem
`pairedEtaUnpairedCenteredMomentPrefix_eq_paired_add_endpoint` retains the
exact odd endpoint at every divided cutoff. All integral hypotheses come
from the existing interval antiderivative theorem; its nonzero spectral
parameter is discharged for every actual zero.

Define the full completed transform

\[
 T_{k,\rho}(M,a)=\sum_{1\le d\le M}\mu(d)d^{-\rho}
   c_\rho E_{k,\rho}(\lfloor M/d\rfloor,a-\log d).
\]

The center translation applies to every term of the endpoint polynomial.
`pairedEtaCompletedMomentMoebiusAggregate_eq_source` proves, for `M>=2`,

\[
 T_{k,\rho}(M,a)=c_\rho\left(
   Q_{k,\rho}(-a)-2\,2^{-\rho}Q_{k,\rho}(\log2-a)\right).
\]

This follows from actual finite divisor cancellation, with both Mellin
phases recombined before the Möbius convolution is evaluated. At order
zero, `pairedEtaCompletedMomentMoebiusTerm_zero` proves exact agreement
with the previously used completed divisor term.

The explicit nonnegative polynomial envelope is

\[
 B_{0,\rho}(R)=\|\rho\|^{-1},\qquad
 B_{k+1,\rho}(R)=\frac{R^{k+1}}{\|\rho\|}+
   \frac{k+1}{\|\rho\|}B_{k,\rho}(R).
\]

`norm_pairedEtaCompletedMomentMoebiusAggregate_le` proves, for **every**
integer cutoff `M`,

\[
 \|T_{k,\rho}(M,a)\|\le
 \|c_\rho\|(1+2\|2^{-\rho}\|)B_{k,\rho}(|a|+\log2).
\]

This is uniform in `M` at each fixed center `a`. Its center dependence is
explicit and cannot be discarded at a moving physical center.

Finite inversion translates the center and the cutoff together. The
terminal theorem `pairedEtaFiniteCompletedMoment_eq_momentInverse` proves

\[
 A_{\rho,N,k}=\sum_{1\le d\le2N}d^{-\rho}
   T_{k,\rho}(\lfloor2N/d\rfloor,L_N-\log d),
 \qquad L_N=\texttt{pairedEtaLogTailCutoff}(N).
\]

The complex pair theorem
`pairedEtaFiniteCompletedMomentPair_eq_momentInverse` keeps both independent
divisor indices. It yields
`pairedEtaLeadingCurrent_eq_momentInverse_adjacent` for the original
repeated-zero current at orders `m-2,m-1`, with the original factor
`2*(m-1)*delta_N` and physical cutoff `2*(N+2)`. The simple-zero branch is
`pairedEtaLeadingCurrent_eq_momentInverse_head`, retaining the actual head
and the order-zero inverse sum. These theorems precede any absolute-value
estimate and keep both completed reflection channels.

The higher-order reconstruction interface is now discharged. The full
transformed moments have proved fixed-center bounds, but their inverses
use complex weights and centers depending on `N` and each divisor. No
bound for the unchanged weighted current follows by discarding those
dependencies. The earlier sharp off-critical return growth remains in
force; excluding that contribution remains the open objective. This slice
does not improve the explicit zero-location margin or claim novelty priority.

## Independent prime positivity with full zero multiplicity

The fixed-center moment transform does not itself remove the original
current's proved off-critical growth. A separate use of the actual analytic
multiplicity now strengthens the independent prime-product exclusion.
Write `m=analyticZetaZeroMultiplicity rho>=1`, `t=abs(Im rho)`, and
`d=1-Re rho>0`.

`riemannZeta₁_eventuallyEq_multiplicity_factor` proves that the entire
pole-removed zeta function has the local form

\[
 Z_1(z)=(z-\rho)^m g(z),
\]

with `g` analytic and nonzero at the original zero. It uses the checked analytic
multiplicity of the literal zeta function and the factor `z-1`, which is
nonzero at that zero. No assumed derivative vanishing or assigned
multiplicity enters the estimate. This supplies the full little-oh
condition for Mathlib's higher-order Schwarz lemma.

The actual eta strip estimate bounds the whole radius-`1/4` disc by
`8*(t+21)^2` when `Re rho>=3/4`.
`norm_riemannZeta₁_le_etaMultiplicity_ball` consequently proves

\[
 \|Z_1(z)\|\le8(t+21)^2(4\|z-\rho\|)^m
 \quad\text{for }|z-\rho|<1/4.
\]

If `Re rho>=15/16`, the point `2-Re rho+i*Im rho` lies strictly inside
this disc. The terminal small-value theorem
`norm_riemannZeta₁_reflected_across_one_le_multiplicity` gives

\[
 \|Z_1(1+d+i\gamma)\|\le8(t+21)^2(8d)^m.
\]

Inserting that value into the already specialized three-four-one
prime-product inequality proves
`one_le_etaPrimeProduct_multiplicity_gap`. Its equivalent positive
power form, `etaPrimeProduct_multiplicity_gap_power_le`, is

\[
 d^{4m-3}\ge
 \frac{t^5}{16\cdot3200^3\cdot8^{4m+4}(t+21)^{10}}.
\]

The real-axis pole costs three powers of `d`; the actual multiplicity
supplies `4m` powers through the middle zeta factor. The previous real-axis
and double-ordinate bounds are reused with all their hypotheses discharged.

Define the explicit margin

\[
 \Delta_m(y)=\min\left\{\frac1{16},
 \left(\frac{|y|^5}{16\cdot3200^3\cdot8^{4m+4}(|y|+21)^{10}}\right)^{1/(4m-3)}\right\}.
\]

The exponent denominator is proved positive at every actual zero. The
original eta mass excludes ordinate zero, so the margin is positive there.
Reflection preserves both the ordinate and analytic multiplicity;
`nontrivialZetaZero_mem_etaPrimeProductMultiplicity_strip` proves

\[
 \Delta_m(\gamma)\le\operatorname{Re}\rho\le1-\Delta_m(\gamma)
\]

for every literal nontrivial zero, including those outside the small-disc
threshold by the explicit minimum.

The comparison with the previous margin is itself checked:
`etaPrimeProductMultiplicityZeroMargin_one` proves `Delta_1(y)=delta(y)`
for every real ordinate. For `m>=2` and `y!=0`,
`etaPrimeProductZeroMargin_lt_multiplicity` proves the strict inequality
`delta(y)<Delta_m(y)`. Thus this result never weakens the earlier bound and
strictly strengthens it for a repeated actual zero. It makes no assertion
that repeated zeros exist. The methods are classical; the improvement here
is relative to the repository's earlier bound, with no priority or
improvement over established analytic zero-free regions claimed.

Finally,
`pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_etaPrimeProductMultiplicity`
proves the actual return estimate

\[
 S_R(\rho,K)\le C_\rho(K+1)^{1-2\Delta_m(\gamma)}.
\]

`etaPrimeProductMultiplicity_return_exponent_lt` proves the exponent is
strictly smaller than the earlier one when `m>=2`.
`etaPrimeProductMultiplicity_return_exponent_bounds` still places it in
`[7/8,1)`. The unchanged completion-dependent constant is retained, and the
simple-zero exponent is unchanged. This leaves positive cutoff growth and
does not exclude the remaining interior off-critical zeros. The uniform
weighted arithmetic estimate and RH remain open.

## Height-adapted eta bounds and a logarithmic zero margin

The earlier eta mass estimate loses a full power of height before the
dyadic-factor argument. The finite arithmetic prefix and the actual tail
give a stronger estimate when used at the same height-adapted cutoff.
For `0<epsilon<=1/2` and `Re(s)>=1-epsilon`,
[EtaThinStripPrefix.lean](../RiemannGaussian/EtaThinStripPrefix.lean) proves

\[
 \|\eta_{2N}(s)\|\le\frac{(2N+1)^\epsilon}{\epsilon},\qquad
 \|\eta(s)-\eta_{2N}(s)\|\le2(2N+1)^\epsilon
 \quad(\|s\|\le2N+1).
\]

The first bound uses the existing exact odd/even prefix identity and a
finite power-sum comparison. The second uses the existing literal eta-tail
integral. Choosing `N=ceil(T)` proves
`norm_pairedEtaCore_le_thinStrip_height`:

\[
 \|\eta(s)\|\le\frac{6T^\epsilon}{\epsilon}
 \quad(T\ge3,\ \|s\|\le T).
\]

[EtaThinStripFactor.lean](../RiemannGaussian/EtaThinStripFactor.lean) bounds
the dyadic factor below by `epsilon/4` at both vertical edges
`Re(s)=1+-epsilon`. The negative dyadic phase still bounds it below by one
on the horizontal edges. Maximum modulus for the entire pole-removed
function therefore proves `norm_riemannZeta₁_le_etaThinStrip`:

\[
 \|Z_1(s)\|\le
 \frac{24(|\Im s|+20)(|\Im s|+20)^\epsilon}{\epsilon^2}
 \quad(1-\epsilon\le\Re s\le1+\epsilon).
\]

The estimate includes every interior dyadic resonance and the removable
point at one. Independently, the real eta mass is at most one, which
improves the pole constant to `norm(zeta(1+x))<=4/x` for `0<x<=1/2`.

Set `t=|gamma|`, `T=t+21`, and `L=log(T)>2`. At `epsilon=1/L`,
`T^epsilon=exp(1)<3`. For every actual zero `rho=sigma+i*gamma`
with `sigma>=1-1/(16*L)`, its entire disc of radius `1/(4*L)` has
`norm(Z1)<=72*T*L^2`. Schwarz's lemma on that actual disc yields
`norm_riemannZeta₁_reflected_across_one_le_etaLog`:

\[
 \|Z_1(2-\sigma+i\gamma)\|\le576TL^3(1-\sigma).
\]

All analytic inputs are discharged in
[EtaLogarithmicStrip.lean](../RiemannGaussian/EtaLogarithmicStrip.lean).
The original eta mass already proves `gamma!=0`, so division by the
ordinate is valid. At `d=1-sigma`, the three actual zeta values obey

\[
 \|\zeta(1+d)\|\le4/d,\qquad
 \|\zeta(1+d+i\gamma)\|\le576TL^3d/t,\qquad
 \|\zeta(1+d+2i\gamma)\|\le144TL^2/t.
\]

Their classical three-four-one product is at least one. Substitution
proves `one_le_etaLogPrimeProduct_zero_gap` in
[EtaLogarithmicPrimeProduct.lean](../RiemannGaussian/EtaLogarithmicPrimeProduct.lean):

\[
 1\le\frac{CT^5L^{14}}{t^5}d,\qquad C=144\cdot4^3\cdot576^4.
\]

The ratio `delta_log(y)=|y|^5/(C*(|y|+21)^5*log(|y|+21)^14)`
is at most the disc threshold `1/(16*L)` for every real ordinate.
The near-edge argument and its complementary case consequently prove
`nontrivialZetaZero_mem_etaLogPrimeProduct_strip`:

\[
 0<\delta_{\log}(\gamma)\le\sigma\le1-\delta_{\log}(\gamma)
\]

for every actual nontrivial zero. No zero-location estimate is an
antecedent of this theorem. For `t>=21`, `T<=2t`, and
`nontrivialZetaZero_mem_reciprocal_logarithmic_strip` gives the explicit
two-sided edge margin `1/(32*C*L^14)`.

The comparison is also checked. A positive term of the exponential
series proves `L^14<=15*T^5`; the exact constants then show
`etaPrimeProductZeroMargin_lt_logarithmic`, strictly at every nonzero
ordinate. Define

\[
 \widehat\Delta_m(y)=\max\{\Delta_m(y),\delta_{\log}(y)\}.
\]

This preserves the earlier full-multiplicity constraint. For an actual
simple zero, `etaRefinedPrimeProductZeroMargin_eq_logarithmic_of_simple`
identifies the maximum with the strictly larger logarithmic margin.
The actual unchanged return satisfies
`pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_etaRefinedPrimeProduct`:

\[
 S_R(\rho,K)\le C_\rho(K+1)^{1-2\widehat\Delta_m(\gamma)}.
\]

`etaRefinedPrimeProduct_return_exponent_lt_of_simple` proves the strict
improvement for every actual simple zero, and
`etaRefinedPrimeProduct_return_exponent_bounds` retains the range `[7/8,1)`.
The logarithmic zero-free region is weaker than the
[classical reciprocal-logarithm bound](https://people.math.harvard.edu/~elkies/M229.20/free.pdf).
This is an improvement to the repository's checked estimate, with no
novelty priority claim. Interior off-critical exclusion and the uniform
weighted estimate remain open.

## Signed local poles and an explicit reciprocal-logarithm margin

The next independent arithmetic constraint uses the signed logarithmic
derivative rather than norms of three zeta values. The actual local function
is `f_y(z)=Z1(3/2+i*y+z)`, where `Z1(s)=(s-1)*zeta(s)` away from one and
`Z1(1)=1`. The following inputs are proved at every real ordinate:

- `norm_localZetaPoleRemoved_le` gives `norm(f_y(z))<=8*(abs(y)+22)^2`
  on the entire closed unit disc. The eta rectangle and safe-line factor
  estimates cover the full disc.
- `sixteenth_le_norm_localZetaPoleRemoved_zero` gives the center floor
  `1/16`, using the actual absolutely convergent Möbius series at real
  part `3/2`.
- `exists_localZetaSphere_zeroFree` selects a radius `3/4<R_y<7/8` with
  no boundary zeros. `localZetaCanonicalResidual_decomp` removes the
  **complete** enclosed divisor and leaves a nonvanishing analytic residual.
  The exact boundary norms and center floor survive this removal.
- `norm_logDeriv_localZetaCanonicalResidual_le` bounds the residual
  logarithmic derivative by `320*L_y` on `norm(z)<=1/2`, where
  `L_y=log(abs(y)+22)>2`. This follows from a normalized analytic logarithm,
  Borel--Carathéodory, and Cauchy's derivative estimate.
- `sum_divisor_localZetaPoleRemoved_canonicalBall_le` bounds the full
  multiplicity count by `32*L_y`. Jensen's inequality uses the outer unit
  disc and the actual center floor.

These declarations are in [ZetaLocalDiscBounds.lean](../RiemannGaussian/ZetaLocalDiscBounds.lean),
[ZetaLocalCanonical.lean](../RiemannGaussian/ZetaLocalCanonical.lean),
[ZetaLocalResidualBounds.lean](../RiemannGaussian/ZetaLocalResidualBounds.lean),
[ZetaLocalResidualLog.lean](../RiemannGaussian/ZetaLocalResidualLog.lean), and
[ZetaLocalJensen.lean](../RiemannGaussian/ZetaLocalJensen.lean).

The exact complex decomposition
`logDeriv_localZetaPoleRemoved_eq_remainder_add_poleSum` in
[ZetaLocalLogDerivative.lean](../RiemannGaussian/ZetaLocalLogDerivative.lean)
keeps every local divisor coefficient in the pole sum. Only the analytic
remainder is norm-bounded: `norm_localZetaLogRemainder_le` gives `448*L_y`.
No infinite partial-fraction limit or unproved residual bound is assumed.

For `0<x<=1/4`, all local zero Cauchy terms have nonnegative real part at
`s=1+x+i*y`. At an actual zero `rho=sigma+i*gamma` with `sigma>=3/4`,
`divisor_localZetaPoleRemoved_nontrivialZero` identifies its coefficient
with the **full genuine multiplicity** `m`. Thus
`neg_logDeriv_riemannZeta_re_le_sub_zero` proves

\[
 -\Re\frac{\zeta'}{\zeta}(1+x+i\gamma)
 \le \frac1{|\gamma|}+448\log(|\gamma|+22)
       -\frac{m}{x+1-\sigma}.
\]

The simple pole at one also keeps its leading coefficient exactly:
`neg_logDeriv_riemannZeta_real_le` gives `1/x+28224` for
`0<x<=1/28224`. See [ZetaSignedPoleControl.lean](../RiemannGaussian/ZetaSignedPoleControl.lean)
and [ZetaSignedLocalEstimate.lean](../RiemannGaussian/ZetaSignedLocalEstimate.lean).

The exact complex von Mangoldt identity and absolute convergence precede
the real inequality in [ZetaSignedPrimeSeries.lean](../RiemannGaussian/ZetaSignedPrimeSeries.lean).
`neg_logDeriv_riemannZeta_three_height_nonneg` proves the signed `3-4-1`
inequality by the nonnegative square `2*(1+cos(theta))^2`.
Combining these actual inputs proves
`four_mul_multiplicity_div_gap_le_signedLogHeight`:

\[
 \frac{4m}{x+1-\sigma}
 \le \frac3x+90000\log(|\gamma|+22)(1+1/|\gamma|).
\]

Choosing `x=4*(1-sigma)` gives
`one_le_signedLogHeight_mul_zero_gap` in
[ZetaSignedLogarithmicGap.lean](../RiemannGaussian/ZetaSignedLogarithmicGap.lean).
The resulting ratio lies below the required near-pole threshold at every
ordinate. Reflection then proves the unconditional terminal theorem
`nontrivialZetaZero_mem_signedLogarithmic_strip`:

\[
 0<\delta_{\rm signed}(\gamma)\le\sigma\le1-\delta_{\rm signed}(\gamma),
 \qquad
 \delta_{\rm signed}(y)=
 \frac{|y|}{1800000(|y|+1)\log(|y|+22)}.
\]

For `abs(gamma)>=1`, `nontrivialZetaZero_mem_reciprocal_log_strip` gives
the simpler margin `1/(3600000*log(abs(gamma)+22))`. Both are in
[ZetaSignedZeroMargin.lean](../RiemannGaussian/ZetaSignedZeroMargin.lean).
`etaLogPrimeProductZeroMargin_lt_signed` in
[ZetaSignedMarginComparison.lean](../RiemannGaussian/ZetaSignedMarginComparison.lean)
proves strict improvement over the previous fourteenth-logarithmic-power
margin at **every** nonzero ordinate, including small heights.

The combined margin `etaSignedPrimeProductZeroMargin` takes the maximum
with all previous bounds. The terminal theorem
`pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_etaSignedPrimeProduct`
keeps the original `C_rho` and the unchanged Gaussian return, with exponent
`1-2*etaSignedPrimeProductZeroMargin(m,gamma)`. The exponent strictly decreases
for every actual simple zero, while all previously established multiplicity
constraints survive. `etaSignedPrimeProduct_return_exponent_bounds` proves
that it remains in `[7/8,1)`; no cutoff-independent bound follows.

This is the shape of the [classical reciprocal-logarithm argument](https://people.math.harvard.edu/~elkies/M229.20/free.pdf),
with conservative explicit constants obtained from the repository's eta
and complete local divisor estimates. It is an improvement to the checked
project bound, with no novelty priority or improvement over the literature
claimed. The signed prime comparison excludes edge regions, while the
interior off-critical contribution and the original uniform weighted goal
remain open. No RH proof or `13/18` certificate is claimed.

## Growing divisor covariance on the actual completed family

The earlier odd/even estimate concerned one fixed divisor pair. The
following package bounds a whole family while keeping its size, physical
normalizers, and averaging errors explicit. Its terminal theorems concern
the actual completed zeroth-order terms; they do not establish the original
weighted current bound.

Let `a(n)=pairedEtaDirichletSign(n)`, with `a(n)=-1` for even `n` and `+1`
for odd `n`. For positive `d,e`, put `g=gcd(d,e)` and

\[
 c_{d,e}=\begin{cases}
   g^2/(de),&d/g\text{ and }e/g\text{ are both odd},\\
   0,&\text{otherwise}.
 \end{cases}
\]

`sum_range_pairedEtaDivisorParity_eq_gcd` in
[EtaDivisorParityGcd.lean](../RiemannGaussian/EtaDivisorParityGcd.lean)
proves the exact complete-period identity

\[
 \sum_{M<2de}a(\lfloor M/d\rfloor)a(\lfloor M/e\rfloor)
 =2de\,c_{d,e}.
\]

Thus odd coprime columns retain a nonzero covariance. An independence
assumption would lose a real arithmetic contribution. Chinese remainders,
common-divisor blocks, and exact sign reversal prove the formula without
an asymptotic premise. The arbitrary-window theorem
`abs_pairedEtaDivisorParityAverage_sub_covariance_le` in
[EtaDivisorParityAverage.lean](../RiemannGaussian/EtaDivisorParityAverage.lean)
gives, for every `A` and positive `L`,

\[
 \left|\frac1L\sum_{r<L}
   a(\lfloor(A+r)/d\rfloor)a(\lfloor(A+r)/e\rfloor)-c_{d,e}\right|
 \le\frac{4de}{L}.
\]

`sum_Icc_pairedEtaDivisorParityCovariance_le_log` in
[EtaDivisorGcdBound.lean](../RiemannGaussian/EtaDivisorGcdBound.lean)
then proves

\[
 \sum_{d,e\le D}c_{d,e}
 \le\sum_{d,e\le D}\frac{\gcd(d,e)^2}{de}
 \le2D\sum_{g=1}^D\frac1g\le2D(1+\log D).
\]

The proof keeps a common-divisor decomposition and the exact divided-cutoff
harmonic sums before using finite Cauchy--Schwarz and a telescoping
inverse-square bound.

For the actual carrier, set `X_rho=pairedEtaXiCompletionFactor(rho)` and
`H_rho=norm(X_rho)*norm(rho)*norm(rho+1)`. Write

\[
 Q(m)=2\lfloor m/2\rfloor+1,\qquad
 F_\rho(M,d)=(dQ(\lfloor M/d\rfloor))^\rho\,
   \operatorname{pairedEtaCompletedMoebiusTerm}(\rho,M,d).
\]

This is the existing `pairedEtaCompletedMoebiusEndpointPhase`; its complex
physical power is part of the statement. The exact theorem
`pairedEtaCompletedMoebiusDivisorCorrelation_eq_covariance_add_errors` in
[EtaMoebiusDivisorCorrelation.lean](../RiemannGaussian/EtaMoebiusDivisorCorrelation.lean)
retains the main coefficient `mu(d)*mu(e)*norm(X_rho)^2/4`, the full
covariance, the literal unfinished-period remainder, and the complex
endpoint error. Only its downstream norm bound discards the two Möbius
signs. The theorem
`pairedEtaCompletedMoebiusEndpointFamily_norm_sq_eq_physical_kernel` in
[EtaMoebiusFamilyMeanSquare.lean](../RiemannGaussian/EtaMoebiusFamilyMeanSquare.lean)
retains both endpoint powers on every entry of the original pair kernel.

The actual mean-square terminal theorem
`pairedEtaCompletedMoebiusFamilyMeanSquare_le` proves, for `A,L>=1`,

\[
 \begin{aligned}
 \frac1L\sum_{r<L}\left|\sum_{d=1}^D F_\rho(A+r,d)\right|^2
 &\le \frac{\|X_\rho\|^2}{2}D(1+\log D)
   +\frac{\|X_\rho\|^2D^4}{L}\\
 &\quad+\frac{2H_\rho\|X_\rho\|D^3}{A}
   +\frac{4H_\rho^2D^4}{A^2}.
 \end{aligned}
\]

`pairedEtaCompletedMoebiusFamilyMeanSquare_le_growing` in
[EtaMoebiusGrowingFamily.lean](../RiemannGaussian/EtaMoebiusGrowingFamily.lean)
therefore gives the bound `K_rho*D*(1+log D)` when `D>=1` and
`D^3<=A,L`, with the evaluated constant

\[
 K_\rho=2\|X_\rho\|^2+2H_\rho\|X_\rho\|+4H_\rho^2.
\]

The signed pair remains the repository's original `etaSignedCompletedPair`
on the two completed families. Its exact double sum and oriented difference
of channel squares precede the estimate.
`pairedEtaSignedCompletedMoebiusFamilyMeanAbsolute_le_growing` in
[EtaMoebiusSignedFamily.lean](../RiemannGaussian/EtaMoebiusSignedFamily.lean)
bounds its first absolute window average by
`(K_partner+K_rho)*D*(1+log D)` in the same cubic range. These results apply
to every actual nontrivial zero, without a critical-line or simplicity
assumption.

The remaining transfer is substantive. The divisor cutoff is truncated to
the cubic range; the full current requires all physical divisors. The
period-error term `norm(X_rho)^2*D^4/L` cannot be suppressed when the family
grows as fast as the averaging window. The complex endpoint powers must
also be transported back through the original inverse weights and moving
centers. Repeated-zero currents involve adjacent higher moments, whereas
this estimate concerns zeroth-order family self-pairs. Finally, a finite
window average is not the original odd-weighted first absolute partial sum.
None of those open transfers is supplied as an assumption or declared proved.

Gcd covariance bounds and their relation to periodic dilations have
[established prior work by Aistleitner, Berkes, and Seip](https://arxiv.org/abs/1210.0741).
No literature improvement or novelty priority is claimed. The checked
contribution here is the explicit arithmetic identity and quantitative
application to the actual completed eta carriers with all finite-window
dependencies retained. The previous reciprocal-logarithm zero-free margin
is unchanged. The uniform weighted goal, RH, and the `13/18` certificate
remain open.

## Removing the individual physical endpoint powers

The growing-family covariance estimate now applies to the original
`pairedEtaCompletedMoebiusTerm` itself, without its separate complex
endpoint multiplier. This discharges the normalization transfer for the
zeroth-order forward Möbius family. It does not discharge the full divisor
range or the inverse-weighted current estimate.

For `1<=d<=M`, the literal endpoint `p=d*Q(floor(M/d))` satisfies
`M/2<=p` and `abs(M-p)<=d`:
`pairedEtaDivisorOddEndpoint_physical_bounds` in
[EtaMoebiusPhysicalNormalization.lean](../RiemannGaussian/EtaMoebiusPhysicalNormalization.lean).
The existing complex-power derivative bound and the actual completed-term
decay therefore give

\[
 \left|M^\rho T_\rho(M,d)-p^\rho T_\rho(M,d)\right|
 \le B_\rho\frac dM,\qquad
 B_\rho=2\|\rho\|\operatorname{pairedEtaCompletedMoebiusTermConstant}(\rho).
\]

This is
`norm_pairedEtaCompletedMoebiusTerm_physical_sub_endpoint_le`. Its inputs
hold over the entire physical divisor range; it does not assume that `d/M`
is small. The exact complex difference is kept before taking a norm.

Write `P_rho(M,D)=sum_{d=1}^D T_rho(M,d)` for
`pairedEtaCompletedMoebiusPartialAggregate`. At `D=M` it is exactly the
previous completed tail aggregate. The theorem
`pairedEtaCompletedMoebiusPartialAggregate_norm_sq_eq_kernel` retains its
full original complex pair kernel, with no individual endpoint powers.
The exact normalization-error sum and its quantitative consequence are
proved in [EtaMoebiusPhysicalFamily.lean](../RiemannGaussian/EtaMoebiusPhysicalFamily.lean):

\[
 \begin{aligned}
 M^\rho P_\rho(M,D)-\sum_{d=1}^D F_\rho(M,d)
 &=\sum_{d=1}^D(M^\rho-p_d^\rho)T_\rho(M,d),\\
 \left|M^\rho P_\rho(M,D)-\sum_{d=1}^D F_\rho(M,d)\right|
 &\le B_\rho D^2/M\qquad(D\le M).
 \end{aligned}
\]

The estimate is
`norm_pairedEtaCompletedMoebiusPartialAggregate_physical_sub_endpoint_le`.
It is a bound for the actual summed complex normalization error.

`pairedEtaCompletedMoebiusPhysicalMeanSquare_le_endpoint` in
[EtaMoebiusPhysicalMeanSquare.lean](../RiemannGaussian/EtaMoebiusPhysicalMeanSquare.lean)
then bounds the mean square of `M^rho*P_rho(M,D)` by twice the previous
endpoint-family mean square plus `2*B_rho^2*D^4/A^2`, for `D<=A` and
positive `A,L`. The exact norm identity evaluates the common factor as
the original physical decay. Consequently the terminal theorem
`pairedEtaCompletedMoebiusOriginalMeanSquare_le_growing` proves

\[
 \frac1L\sum_{r<L}|P_\rho(A+r,D)|^2
 \le C_\rho D(1+\log D)A^{-2\operatorname{Re}\rho},\qquad
 C_\rho=2K_\rho+2B_\rho^2,
\]

for `D>=1` and `D^3<=A,L`. The constant `K_rho` is evaluated in the preceding
section; `C_rho` is `pairedEtaCompletedMoebiusOriginalFamilyConstant`.

The exact signed pair of the two original sums is expanded into every
original divisor pair before its norm is bounded.
`pairedEtaSignedCompletedMoebiusOriginalMeanAbsolute_le_growing` in
[EtaMoebiusOriginalSignedFamily.lean](../RiemannGaussian/EtaMoebiusOriginalSignedFamily.lean)
proves the first absolute average bound

\[
 \frac1L\sum_{r<L}
  \left|\operatorname{etaSignedCompletedPair}
    (P_{\rho^*},P_{\rho^*},P_\rho,P_\rho)(A+r,D)\right|
 \le D(1+\log D)
   \left(C_{\rho^*}A^{-2(1-\sigma)}+C_\rho A^{-2\sigma}\right),
 \qquad \sigma=\operatorname{Re}\rho.
\]

Here `rho*` is the original conjugate partner. Both complementary rates
come from the actual zero coordinates. No critical-line or simplicity
hypothesis is imposed. The oriented channel difference also has an exact
average identity before the absolute estimate.

The retained `D^2/M` normalization error is small only in a suitable range,
and the covariance estimate still requires cubic separation of the family
size from the physical averaging scales. The full forward aggregate already
has its proved nonzero dyadic source; a bound for it is not a bound for the
current. The latter requires the inverse-weighted head sum and the adjacent
higher moments at moving centers. Those transfers and the original uniform
odd-weighted first absolute partial-sum bound remain open. This slice does
not exclude any additional zero, tighten the previous zero-free margin,
or prove RH or a `13/18` certificate.

## Checked Fourier sampling and the quadratic divisor range

The original forward-family estimate now holds when
`D² ≤ min(A,L)`, enlarging the previous cubic range with a new explicit
constant. The terminal theorems are
[pairedEtaCompletedMoebiusOriginalMeanSquare_le_quadratic](../RiemannGaussian/EtaMoebiusOriginalQuadraticFamily.lean)
and
[pairedEtaSignedCompletedMoebiusOriginalMeanAbsolute_le_quadratic](../RiemannGaussian/EtaMoebiusOriginalQuadraticFamily.lean).
They retain the original completed terms, their physical decay, both
reflected channels, and every actual zero without a simplicity hypothesis.

Write `S = 4 + 16 pi²`, `X = pairedEtaXiCompletionFactor(rho)`,
`H = pairedEtaCompletedMoebiusPhaseErrorConstant(rho)`, and
`B = pairedEtaCompletedMoebiusPhysicalErrorConstant(rho)`. Define

\[
 K^{(2)}_\rho=5S|X|^2+8H^2,\qquad
 C^{(2)}_\rho=2K^{(2)}_\rho+2B^2.
\]

These are the literal Lean definitions
`pairedEtaCompletedMoebiusQuadraticFamilyConstant` and
`pairedEtaCompletedMoebiusOriginalQuadraticConstant`. For `D ≥ 1` and
`D² ≤ A,L`, the endpoint family has mean square at most
`K^(2)_rho D(1+log D)`, and the unmodified completed terms satisfy

\[
 \frac1L\sum_{n<L}\left|\sum_{d=1}^D T_\rho(A+n,d)\right|^2
 \le C^{(2)}_\rho D(1+\log D)A^{-2\operatorname{Re}\rho}.
\]

The corresponding first absolute average of the original signed pair is
at most

\[
 D(1+\log D)\left(
 C^{(2)}_{\rho^*} A^{-2(1-\operatorname{Re}\rho)}+
 C^{(2)}_\rho A^{-2\operatorname{Re}\rho}\right).
\]

The proof uses the following checked interfaces, with exact complex
identities retained before all scalar estimates:

1. [sum_norm_sq_separated_sampling_le](../RiemannGaussian/FiniteSeparatedSampling.lean)
   proves a discrete sampling inequality from the local forward-difference
   estimate. Disjoint blocks and a doubled complete period bound samples by
   `(4/h)` times the full energy plus `4h` times the full difference energy.
   [sum_range_finiteCircleSynthesis_mul_conj](../RiemannGaussian/FiniteCircleEnergy.lean)
   retains both coefficient families and every frequency coincidence;
   orthogonality evaluates the two energies exactly for a distinct band.
2. [sum_range_finiteCircleSynthesis_separated_le](../RiemannGaussian/FiniteCircleDualSampling.lean)
   transfers the band estimate by an exact complex transpose identity and
   finite Cauchy--Schwarz. With `Q=hT`, `L≤T`, and representative gaps at
   least `h`, the physical `L`-sample energy is at most `S T` times the
   complete coefficient energy.
3. The auxiliary arithmetic grid is
   `h=2(D!)²`, `T=4D²+L`, and `Q=hT`. Every literal divisor period `2d`
   and every pair period `2de` divides `Q` for `1≤d,e≤D`.
   [pairedEtaDivisorFourierSpectrum_separated](../RiemannGaussian/EtaDivisorFourierGrid.lean)
   proves separation from exact divisibility: distinct frequencies with
   divisor witnesses `d,e` satisfy `Q | 4de(l.val-k.val)`, which forces
   `l.val-k.val ≥ h`. No frequency rounding is used.
4. [pairedEtaCompletedMoebiusParityFamily_fourier_eq_zero](../RiemannGaussian/EtaMoebiusFourierSpectrum.lean)
   derives the actual Fourier support from literal quotient periodicity.
   Exact inversion reconstructs the original parity family at every
   physical sample. Its coefficient energy equals its complete-period
   energy; neither spectral support nor a bound on it is assumed.
5. [pairedEtaCompletedMoebiusParityFamily_period_energy_eq](../RiemannGaussian/EtaMoebiusParityEnergy.lean)
   evaluates that energy as the full signed sum
   `sum_(d,e≤D) mu(d)mu(e)|X|² c(d,e)/4`.
   The earlier gcd-sum bound gives `|X|² D(1+log D)/2`.
   [pairedEtaCompletedMoebiusParityFamily_window_sq_le](../RiemannGaussian/EtaMoebiusParitySampling.lean)
   consequently bounds the physical window energy by
   `S(4D²+L)|X|² D(1+log D)/2`; the auxiliary grid size cancels.
6. [pairedEtaCompletedMoebiusFamilyMeanSquare_le_quadratic](../RiemannGaussian/EtaMoebiusQuadraticFamily.lean)
   uses the retained complex endpoint-family error of norm at most
   `2H D²/M`. The resulting square error is `8H² D⁴/A²`, at most `8H²`
   when `D²≤A`. The previous exact physical normalization then transfers
   this result to the original terms with error `2B² D⁴/A²`.

Finite Fourier sampling and large-sieve duality are classical methods;
see P. X. Gallagher,
[The large sieve](https://www.cambridge.org/core/journals/mathematika/article/abs/large-sieve/4DC1EC8072D840195F1EF81F5828BB0F),
*Mathematika* 14 (1967), 14–20. The checked contribution here is the explicit
application to the literal completed eta family with its full arithmetic
covariance and physical normalization. No optimal constant or claim of
mathematical priority is asserted.

This removes the cubic restriction for this forward-family estimate, but
the full physical divisor range remains outside the new quadratic range.
The original inverse-weighted head, adjacent higher moments, and moving
centers are still not bounded by this theorem. The existing zero-free
strip is unchanged, and the uniform odd-weighted first absolute moment
goal remains open. No RH proof or `13/18` certificate follows from this slice.

## Checked moving-center moments and reduction inside the actual inverse

The quadratic divisor-range estimate now applies to every order below
the actual analytic zero multiplicity, including the adjacent orders
that occur in the repeated-zero current. The terminal mean-square theorem is
[pairedEtaCompletedMomentOriginalMeanSquare_le_quadratic](../RiemannGaussian/EtaMomentQuadraticMeanSquare.lean).
The corresponding signed statement is
[pairedEtaSignedCompletedMomentOriginalMeanAbsolute_le_quadratic](../RiemannGaussian/EtaMomentSignedQuadraticFamily.lean);
[pairedEtaSignedCompletedMomentOriginalMeanAbsolute_adjacent_le_quadratic](../RiemannGaussian/EtaMomentSignedQuadraticFamily.lean)
discharges the order conditions for `k=m-2`, `l=m-1`, when `m≥2`.
The companion inverse-entry estimate is
[norm_pairedEtaCompletedMomentInversePartialTerm_sub_zero_le](../RiemannGaussian/EtaMomentInverseReduction.lean).
These statements use the original completed moments and actual moving
centers, with all their analytic and geometric premises proved.

Write `m=analyticZetaZeroMultiplicity(rho)`, `sigma=Re rho`,
`X=pairedEtaXiCompletionFactor(rho)`, and

\[
 U_{\rho,k}(a;M,d)
 =\operatorname{pairedEtaCompletedMomentMoebiusTerm}(\rho,k,a,M,d),
 \qquad
 F_{\rho,k}(a;M,D)=\sum_{d=1}^D U_{\rho,k}(a;M,d).
\]

The terms retain their literal factor `mu(d)d^(-rho)X rho`, centered
endpoint polynomial, and divided cutoff `floor(M/d)`. At order zero
they equal the existing terms `T_rho(M,d)`, independently of `a`.
The exact complex reduction has coefficient

\[
 \alpha_{\rho,k}=\frac{k!}{\rho^k}.
\]

[pairedEtaMomentParityCoefficient_eq](../RiemannGaussian/EtaMomentDivisorPhase.lean)
evaluates this coefficient. For `k<m`, `1≤d≤M`, and
`log M≤a≤log(M+1)`,
[norm_pairedEtaCompletedMomentMoebiusTerm_physical_sub_zero_le](../RiemannGaussian/EtaMomentPhysicalReduction.lean)
proves

\[
 \left|M^\rho\left(
 U_{\rho,k}(a;M,d)-\alpha_{\rho,k}T_\rho(M,d)\right)\right|
 \le R_{\rho,k}\frac dM.
\]

Here are the explicit constants in that estimate, using nonnegative radii `r`. Let
`c_(rho,k)=pairedEtaCenteredTailQuantitativeAsymptoticConstant(k,rho)` and
`E_(rho,k)=pairedEtaCurrentEulerMomentValue(rho,k)`. Define

\[
 \begin{aligned}
 W_{\rho,k}&=|E_{\rho,k}|+c_{\rho,k},\\
 B_{\rho,k}(r)&=\sum_{j<k}\binom kj r^{k-j-1}W_{\rho,j},\\
 V_{\rho,0}(r)&=0,\qquad
 V_{\rho,k+1}(r)=\frac{r^k}{|\rho|}
                  +\frac{k+1}{|\rho|}V_{\rho,k}(r),\\
 H_{\rho,k}&=|X\rho|\bigl(2c_{\rho,k}
                     +4(B_{\rho,k}(4)+V_{\rho,k}(4))\bigr),\\
 R_{\rho,k}&=2\bigl(H_{\rho,k}+2|\alpha_{\rho,k}|H_\rho\bigr).
 \end{aligned}
\]

The last `H_rho` is the previously proved zeroth-order phase-error
constant `|X| |rho| |rho+1|`. The new `R_(rho,k)` is the literal definition
`pairedEtaCompletedMomentPhysicalErrorConstant`. All these constants
are finite and nonnegative. No simplicity or critical-line assumption
is used.

The proof first retains the exact binomial center transport of the
actual eta tail and the odd unpaired endpoint. The central endpoint
polynomial evaluates to `k!/rho^(k+1)`, and its displacement error is
bounded by `V_(rho,k)(r)|delta|`. The actual divisor geometry gives
`|delta|≤4d/M`, including every physical divisor. The complex physical
normalization ratio has norm at most two.
[pairedEtaCompletedMomentMoebiusTerm_physical_sub_zero](../RiemannGaussian/EtaMomentPhysicalReduction.lean)
retains the resulting complex difference before its norm is bounded.

For `D≤M`, the exact family difference is the sum of those original term
differences, and
[norm_pairedEtaCompletedMomentOriginalFamily_physical_sub_zero_le](../RiemannGaussian/EtaMomentPhysicalFamily.lean)
gives

\[
 \left|M^\rho\left(
 F_{\rho,k}(a;M,D)-\alpha_{\rho,k}F_{\rho,0}(a;M,D)\right)\right|
 \le R_{\rho,k}\frac{D^2}{M}.
\]

Every original mixed divisor pair remains in
`pairedEtaCompletedMomentOriginalFamily_norm_sq_eq_pairs`. Consequently,
at the actual moving center `a(M)=log(M+1)`, the proved Fourier bound yields

\[
 \frac1L\sum_{n<L}
 |F_{\rho,k}(\log(A+n+1);A+n,D)|^2
 \le C_{\rho,k}D(1+\log D)A^{-2\sigma},
 \qquad k<m,\quad 1\le D,\quad D^2\le A,L,
\]

where
`C_(rho,k)=2|alpha_(rho,k)|² C^(2)_rho+2R_(rho,k)²` is
`pairedEtaCompletedMomentQuadraticConstant`. The retained square error
is `2R_(rho,k)²D⁴/A²`, and `D²≤A` bounds its scale factor by one.
For any `k,l<m`, the original signed mixed family has first absolute
average at most

\[
 D(1+\log D)\left(
 C^{\rm mix}_{\rho^*,k,l}A^{-2(1-\sigma)}
 +C^{\rm mix}_{\rho,k,l}A^{-2\sigma}\right),\qquad
 C^{\rm mix}_{\rho,k,l}=\frac{C_{\rho,k}+C_{\rho,l}}2.
\]

The exact signed double sum is retained before this estimate, and
reflection preserves the actual analytic multiplicity.

The inverse interface also uses the original arithmetic carrier. Put
`q=floor(M/d)` and

\[
 I_{\rho,k}(a;M,d,D)
 =d^{-\rho}F_{\rho,k}(a-\log d;q,D).
\]

At `D=q`,
[pairedEtaCompletedMomentInversePartialTerm_full](../RiemannGaussian/EtaMomentInverseReduction.lean)
identifies this exactly with the existing
`pairedEtaCompletedMomentInverseTerm`. For every `1≤d≤M`,
[pairedEtaMomentInverseCenter_mem_interval](../RiemannGaussian/EtaMomentPhysicalGeometry.lean)
proves `log q≤log(M+1)-log d≤log(q+1)`. Thus the center condition is
discharged inside each actual inverse term. For `k<m` and `D≤q`,

\[
 \left|q^\rho\left(
 I_{\rho,k}(\log(M+1);M,d,D)
 -\alpha_{\rho,k}I_{\rho,0}(\log(M+1);M,d,D)\right)\right|
 \le d^{-\sigma}R_{\rho,k}\frac{D^2}{q}.
\]

The exact identity preceding this estimate keeps the outer complex weight
`d^(-rho)` and the inner normalized family error.

This resolves the lower-order moving-center transfer in the truncated
forward family and supplies an error bound inside each original inverse
entry. It does not bound the full inverse sum: at `D=q` the inner error
scale is `q`, and subsequent outer divisor sums require cancellation
across their different cutoffs. The original inverse-weighted head and
adjacent mixed sums still need that cancellation to control the unchanged
odd-weighted first absolute current moment. The zero-free strip is
unchanged, and the uniform bound and RH remain open. The proof uses
binomial moment transport and the preceding classical Fourier estimate;
no mathematical priority claim is made.

## Checked joint estimate for the original inverse rectangles

The next transfer now estimates both divisor sums in an actual inverse
rectangle together. The terminal theorem is
[pairedEtaCompletedMomentInverseRectangleMeanSquare_le_quadratic](../RiemannGaussian/EtaInverseRectangleMeanSquare.lean).
The corresponding signed first absolute bound is
[pairedEtaSignedCompletedMomentInverseRectangleMeanAbsolute_le_quadratic](../RiemannGaussian/EtaInverseRectangleSigned.lean),
and
[pairedEtaSignedCompletedMomentInverseRectangleMeanAbsolute_adjacent_le_quadratic](../RiemannGaussian/EtaInverseRectangleSigned.lean)
discharges the adjacent-order conditions in the repeated-zero branch.

Write `I_(rho,k)(a;M,d,D)` for the original inverse partial term from the
preceding section. The new quantity is its literal outer sum,

\[
 V_{\rho,k}(a;M,E,D)=\sum_{d=1}^E I_{\rho,k}(a;M,d,D),
 \qquad V_{\rho,k}(M;E,D)=V_{\rho,k}(\log(M+1);M,E,D).
\]

This is `pairedEtaCompletedMomentInverseRectangle`.
[pairedEtaCompletedMomentInverseRectangle_inner_cutoff](../RiemannGaussian/EtaMomentInverseRectangle.lean)
proves that `ED≤M` places every inner range `D` inside the original
divided cutoff `floor(M/d)`. Thus each rectangle in the estimate consists
of actual inverse terms.

Set `T=ED` and define the actual signed product coefficients

\[
 w_{E,D}(n)=\sum_{\substack{1\le d\le E,\;1\le e\le D\\de=n}}\mu(e).
\]

The Möbius sign is on the inner factor `e`; it is never replaced by
`mu(de)`. The unchanged completed atom is

\[
 A_{\rho,k}(a;M,n)=n^{-\rho}(X_\rho\rho)
 \operatorname{pairedEtaUnpairedCenteredMomentPrefix}
       (k,\rho,a-\log n,\lfloor M/n\rfloor).
\]

[pairedEtaMomentInverseCell_eq_atom](../RiemannGaussian/EtaMomentDivisorAtom.lean)
combines both complex inverse powers and both center translations at
their exact product.
[pairedEtaCompletedMomentInverseRectangle_eq_atoms](../RiemannGaussian/EtaMomentInverseRectangle.lean)
then proves the complete complex identity

\[
 V_{\rho,k}(a;M,E,D)=\sum_{n=1}^{T}w_{E,D}(n)A_{\rho,k}(a;M,n).
\]

The proof supplies two quantitative bounds for these exact coefficients:

\[
 \sum_{n\le T}|w_{E,D}(n)|\le ED,\qquad
 \sum_{n\le T}|w_{E,D}(n)|^2\le ED(1+\log E)^2
 \quad(E\ge1).
\]

The second is
[sum_sq_pairedEtaInverseProductCoefficient_le_log_sq](../RiemannGaussian/EtaInverseProductCoefficients.lean).
It is derived from a count of all equal products, rather than an assumption
that the factors are independent.
[card_Icc_product_collision_le_gcd](../RiemannGaussian/NatProductCollision.lean)
bounds the number of `(b,d)∈[1,D]²` satisfying `ab=cd` by
`D gcd(a,c)/a`. A complete common-divisor expansion gives
`sum_(a,c≤E) gcd(a,c)/a ≤ E H_E²`. Consequently
[mulEnergy_Icc_le_log_sq](../RiemannGaussian/NatRectangleEnergy.lean)
bounds the full rectangular multiplicative energy by `ED(1+log E)²`.
Coincident factorizations are all counted before estimating the signed
coefficient energy.

For the original quotient-parity covariance `c(n,m)`,
[sum_Icc_pairedEtaDivisorParityCovariance_row_le](../RiemannGaussian/EtaDivisorCovarianceOperator.lean)
proves that every complete row up to `T` is at most `H_T²`. Symmetry and
the nonnegative covariance entries therefore give a proved operator bound
for arbitrary signed coefficients:

\[
 \sum_{n,m\le T}w(n)w(m)c(n,m)
 \le (1+\log T)^2\sum_{n\le T}w(n)^2.
\]

The exact complete-period energy retains this full signed covariance.
Literal divisor periodicity proves the Fourier support, and the existing
separated sampling theorem gives

\[
 \frac1L\sum_{r<L}
 \left|\sum_{n\le T}w_{E,D}(n)
             \operatorname{sign}_\eta(\lfloor(A+r)/n\rfloor)\right|^2
 \le 5S\,ED(1+\log E)^2(1+\log T)^2,
 \qquad T^2\le L,
\]

where `S=4+16 pi²` and `E,D≥1`. This is
[pairedEtaInverseRectangleParityFamily_meanSquare_le](../RiemannGaussian/EtaInverseRectanglePhase.lean);
its preceding identity retains the original double divisor phase sum.

The physical correction is also proved for the actual completed atoms.
Put

\[
 \beta_{\rho,k}=\frac{X_\rho\alpha_{\rho,k}}2,\qquad
 \Gamma_{\rho,k}=2\bigl(H_{\rho,k}+|\rho|\,|\beta_{\rho,k}|\bigr),
\]

where `alpha_(rho,k)=k!/rho^k` and `H_(rho,k)` is the preceding completed
moment-phase error constant. These are the literal definitions
`pairedEtaMomentDivisorAmplitude` and
`pairedEtaMomentDivisorAtomPhysicalConstant`. The actual normalization
ratio satisfies `|ratio-1|≤2|rho|n/M`. For `k<m`, `1≤n≤M`, and every center
`log M≤a≤log(M+1)`, the complete atom error consequently has norm at most
`Gamma_(rho,k)n/M`.
[norm_pairedEtaCompletedMomentInverseRectangle_physical_sub_parity_le](../RiemannGaussian/EtaMomentInverseRectangle.lean)
sums the retained signed errors over the entire rectangle and proves

\[
 \left|M^\rho V_{\rho,k}(a;M,E,D)
   -\beta_{\rho,k}\sum_{n\le T}w_{E,D}(n)
        \operatorname{sign}_\eta(\lfloor M/n\rfloor)\right|
 \le \Gamma_{\rho,k}\frac{T^2}{M}.
\]

No norm estimate replaces the exact complex difference preceding this
bound. At the original moving center, define

\[
 \mathcal B(E,D)=ED(1+\log E)^2(1+\log(ED))^2,\qquad
 C^\square_{\rho,k}=10S|\beta_{\rho,k}|^2+2\Gamma_{\rho,k}^2.
\]

Then the terminal theorem proves

\[
 \frac1L\sum_{r<L}|V_{\rho,k}(A+r;E,D)|^2
 \le C^\square_{\rho,k}\mathcal B(E,D)A^{-2\operatorname{Re}\rho},
 \quad k<m,\quad E,D\ge1,\quad (ED)^2\le A,L.
\]

The physical square correction is `2 Gamma_(rho,k)² T⁴/A²`; the product-range
condition bounds its scale factor by one. The unmodified rectangle's
complex pair identity retains every original outer pair and both inner
sums. For `k,l<m`, the actual signed mixed rectangle has first absolute
average at most

\[
 \mathcal B(E,D)\left(
 C^{\square,\mathrm{mix}}_{\rho^*,k,l}A^{-2(1-\operatorname{Re}\rho)}
 +C^{\square,\mathrm{mix}}_{\rho,k,l}A^{-2\operatorname{Re}\rho}\right),
 \quad C^{\square,\mathrm{mix}}_{\rho,k,l}
       =\frac{C^\square_{\rho,k}+C^\square_{\rho,l}}2.
\]

This rectangle theorem supplies a joint estimate for a genuine part of
the original inverse, including its adjacent repeated-zero orders. It
requires `(ED)²≤min(A,L)`. The following extension handles fixed curved
regions and their mixed interactions with a weaker starting-cutoff
condition. The unchanged weighted head and mixed current sums still need
an independent global cancellation estimate. The uniform weighted goal
and RH remain open, and the zero-free strip is unchanged.

The connection between gcd sums and multiplicative energy is classical;
see de la Bretèche, Munsch, and Tenenbaum,
[Small Gál sums and applications](https://tenenb.perso.math.cnrs.fr/PPP/sGs.pdf),
section 1.2. The checked contribution here is the explicit application to the
original completed inverse with all product coefficients, moving centers,
and physical error costs retained. No priority claim is made.

## Checked curved inverse regions and averaged physical errors

The terminal estimate is now
[pairedEtaCompletedMomentInverseRegionMeanSquare_le](../RiemannGaussian/EtaMomentInverseRegion.lean).
It applies to every fixed finite subset `S` of

\[
 \mathcal H_T=\{(d,e):d,e\ge1,\ de\le T\}.
\]

The carrier `pairedEtaCompletedMomentInverseRegion` is the literal sum
of the original inverse cells:

\[
 V_{\rho,k}(a;M,S)=
 \sum_{(d,e)\in S}d^{-\rho}
 U_{\rho,k}(a-\log d;\lfloor M/d\rfloor,e).
\]

Here `U` is `pairedEtaCompletedMomentMoebiusTerm` from the preceding
moment reconstruction. The compiled
`pairedEtaInverseHyperbolicRegion_inner_cutoff` proves
`e≤floor(M/d)` whenever `(d,e)∈H_T` and `T≤M`.
For the actual outer band
`S_(T,E,F)={(d,e)∈H_T:E<d≤F}`,
[pairedEtaCompletedMomentInverseHyperbolicBand_eq_sum](../RiemannGaussian/EtaMomentInverseRegion.lean)
proves the exact original nested form

\[
 V_{\rho,k}(a;M,S_{T,E,F})
 =\sum_{E<d\le F}
 I_{\rho,k}(a;M,d,\lfloor T/d\rfloor).
\]

Every inner range is curved, and the translated centers and original
physical cutoff `M` remain intact. Exact product grouping gives

\[
 w_S(n)=\sum_{\substack{(d,e)\in S\\de=n}}\mu(e),\qquad
 V_{\rho,k}(a;M,S)=\sum_{n\le T}w_S(n)A_{\rho,k}(a;M,n).
\]

The latter is
`pairedEtaCompletedMomentInverseRegion_eq_atoms`; the atom `A` is the
same original completed atom used for rectangles. The complete complex
kernel on two independently selected regions is retained by
`pairedEtaCompletedMomentInverseRegion_mul_conj_eq_pairs` and
`pairedEtaSignedCompletedMomentInverseRegionPair_eq_double_sum`.
Neither region has to be a rectangle, and no disjointness is required.

The arithmetic estimate counts every pair of divisors through its
common-multiple condition:

\[
 \sum_{n\le T}\tau(n)^2
 =\sum_{d,e\le T}\left\lfloor
       \frac{T}{\operatorname{lcm}(d,e)}\right\rfloor
 \le T\sum_{d,e\le T}\frac{\gcd(d,e)}{de}
 \le T H_T^3\le T(1+\log T)^3.
\]

[sum_Icc_card_divisors_sq_le_log_cube](../RiemannGaussian/NatDivisorSquareMean.lean)
proves the final bound, using the full common-divisor expansion in
[sum_Icc_gcd_div_mul_le_harmonic_cube](../RiemannGaussian/NatDivisorCommonGcd.lean).
Each positive product fiber embeds in its actual divisor antidiagonal.
Consequently
[sum_sq_pairedEtaInverseRegionCoefficient_le_log_cube](../RiemannGaussian/EtaInverseHyperbolicCoefficients.lean)
proves `sum_(n≤T) w_S(n)²≤T(1+log T)³`, including interactions
between separate parts of the selected region.

The physical correction now uses the same coefficient energy
`E_w=sum_(n≤T)w(n)²` as Fourier sampling. For any real signed coefficients,
`k<m`, `T≤M`, and `log M≤a≤log(M+1)`,
[pairedEtaWeightedMomentDivisorFamily_physical_error_sq_le](../RiemannGaussian/EtaWeightedAtomPhysical.lean)
proves

\[
 \left|M^\rho\sum_{n\le T}w(n)A_{\rho,k}(a;M,n)
 -\beta_{\rho,k}\sum_{n\le T}w(n)
          \operatorname{sign}_\eta(\lfloor M/n\rfloor)\right|^2
 \le \Gamma_{\rho,k}^2\frac{T^3}{M^2}E_w.
\]

Its preceding theorem retains the full complex signed error sum.
[mean_range_inv_sq_le](../RiemannGaussian/FiniteInverseSquareWindow.lean)
uses an adjacent reciprocal telescope to prove

\[
 \frac1L\sum_{r<L}\frac1{(A+r)^2}
 \le\frac2{A(A+L)},\qquad A,L\ge1.
\]

This replaces a uniform `A^(-2)` error cost with the average over
the actual window. The physical square correction therefore costs at most
`4 Gamma_(rho,k)² T³ E_w/[A(A+L)]`. For `1≤T≤A` and `T²≤L`,
its scale factor `T³/[A(A+L)]` is at most one. Combined with the
proved weighted Fourier estimate, this gives

\[
 \frac1L\sum_{r<L}|V_{\rho,k}(\log(A+r+1);A+r,S)|^2
 \le C_{\rho,k}\,T(1+\log T)^5 A^{-2\operatorname{Re}\rho},
 \quad C_{\rho,k}=10S_0|\beta_{\rho,k}|^2+4\Gamma_{\rho,k}^2,
 \quad S_0=4+16\pi^2.
\]

The theorem is valid below the actual analytic zero multiplicity.
The corresponding signed mixed first absolute estimate is
[pairedEtaSignedCompletedMomentInverseRegionMeanAbsolute_le](../RiemannGaussian/EtaInverseRegionSigned.lean).
Its right side is

\[
 T(1+\log T)^5
 \left(C^{\mathrm{mix}}_{\rho^*,k,l}A^{-2(1-\operatorname{Re}\rho)}
       +C^{\mathrm{mix}}_{\rho,k,l}A^{-2\operatorname{Re}\rho}\right),
 \qquad C^{\mathrm{mix}}_{\rho,k,l}=(C_{\rho,k}+C_{\rho,l})/2.
\]

The compiled terminal
`pairedEtaSignedCompletedMomentInverseHyperbolicBands_adjacent_le`
discharges both band inclusions and the two adjacent orders
`k=m−2,l=m−1` for `m≥2`. This controls mixed pairs between independently
selected curved bands as well as pairs within one band.

The precise gain is `T≤A` in place of the previous `T²≤A` condition,
and control of fixed curved regions rather than just rectangles.
The region is fixed while `M=A+r` varies, and `L≥T²` remains necessary
for this stated estimate. In particular, setting `T=A` covers the whole
physical region at the start of a long window, not the full growing
region `H_(A+r)` at every index. The original odd-weighted first absolute
current bound is still open. Its conditional off-critical power growth
has not been excluded; RH, the explicit zero-free strip, and certificate
status are unchanged. No mathematical priority claim is made for this
finite estimate or its elementary divisor-counting inputs.

## Checked coherent windows and the complete moving complement

The proposed extension to every proportional window is false when it
must hold uniformly for all original inverse subregions.
[exists_coherentBand_dyadic_window_exceeding_region_budget](../RiemannGaussian/EtaCoherentBandWindowObstruction.lean)
proves a counterexample on the actual completed inverse at every actual
zero. It makes no assumption that the zero is off the critical line.
The same slice quantifies the compensating mixed contribution from
the full moving complement in
[pairedEtaCompletedMomentInverseCoherentComplement_cross_re_le](../RiemannGaussian/EtaCoherentBandComplement.lean).

For a fixed actual zero set

\[
 B=B_\rho=4(1+\lceil|\rho|\rceil),\quad
 S_{B,K}=\{(BK+2j+1,1):0\le j<K\},\quad
 A=T=(B+2)K,\quad L=K.
\]

These are `pairedEtaInverseCoherenceScale` and
`pairedEtaInverseCoherentBand`. The scale obeys `B≥4` and `B≥4|rho|`.
Every outer divisor is odd, every inner Möbius factor is literally
`mu(1)=1`, and the entire band belongs to `H_T`. For `M=A+r`,
`0≤r<K`, the actual quotient `floor(M/(BK+2j+1))` stays one.
Thus the original order-zero band is constant on the whole window:

\[
 V_{\rho,0}(a;M,S_{B,K})=
 X_\rho\sum_{j<K}(BK+2j+1)^{-\rho}.
\]

[pairedEtaCompletedMomentInverseCoherentBand_eq_powerSum](../RiemannGaussian/EtaInverseCoherentBand.lean)
retains this exact complex identity for every center `a`, including
`log(M+1)`. The selected product coefficient is exactly the indicator
of these divisors.
[sum_sq_pairedEtaInverseRegionCoefficient_coherentBand](../RiemannGaussian/EtaCoherentBandCoefficients.lean)
proves its energy is `K`, and
`pairedEtaWeightedDivisorParityFamily_coherentBand_eq` proves the
complete original parity sum is `K` at every index in the window.

The analytic comparison also retains the full complex phase. The
positive-axis power derivative gives

\[
 \left|\sum_{j<K}(BK+2j+1)^{-\rho}-K(BK)^{-\rho}\right|
 \le \frac K2(BK)^{-\operatorname{Re}\rho}.
\]

This is
[norm_pairedEtaCoherentBandPowerSum_sub_anchor_le](../RiemannGaussian/EtaCoherentBandPhase.lean),
with the phase condition discharged by the explicit `B_rho`.
Writing `P_M=M^\rho V_(rho,0)(a;M,S_(B,K))`, the compiled
`pairedEtaCompletedMomentInverseCoherentBand_physical_norm_lower`
therefore gives `abs(P_M)≥abs(X_rho)K/2` throughout the window.
Consequently

\[
 \frac1K\sum_{r<K}|P_{A+r}|^2
 \ge \frac{|X_\rho|^2}{4}K^2,\qquad
 \frac{\frac1K\sum_{r<K}|P_{A+r}|^2}
      {\sum_{n\le T}w_{S_{B,K}}(n)^2}
 \ge\frac{|X_\rho|^2}{4}K.
\]

The two terminal bounds are
[pairedEtaCompletedMomentInverseCoherentBandPhysicalMeanSquare_lower](../RiemannGaussian/EtaCoherentBandLowerBound.lean)
and `pairedEtaCompletedMomentInverseCoherentBand_energy_ratio_lower`.
The coefficient `abs(X_rho)²/4` is strictly positive for every actual
zero. Keeping the coherent initial subwindow inside the full doubling
window gives the stronger domain statement

\[
 \frac1A\sum_{r<A}|P_{A+r}|^2
 \ge \frac{|X_\rho|^2}{4(B_\rho+2)}K^2,
 \qquad A=(B_\rho+2)K.
\]

This is
`pairedEtaCompletedMomentInverseCoherentBandPhysicalMeanSquare_dyadic_lower`.
The remaining window terms are retained through their nonnegative
norm squares; their quotients need not stay one. A proved
scaled-logarithm limit shows that
`T(1+log T)^5/K²→0` for `T=(B+2)K`. Hence every fixed constant
multiple of that previous physical region budget is exceeded by some
member of this explicit family even on `[A,2A)`. This does not claim
that the original quadratic window condition
is optimal in every regime; it rules out its unrestricted proportional
extension with the same region budget.

Every remaining original inverse cell is retained in

\[
 R_{B,K,M}=\mathcal H_M\setminus S_{B,K},\qquad
 Q_M=M^\rho V_{\rho,0}(a;M,R_{B,K,M}).
\]

The complete region `H_M` now moves with `M`. Exact finite inversion gives

\[
 P_M+Q_M=M^\rho X_\rho
       \operatorname{pairedEtaUnpairedDirichletPrefix}(M,\rho).
\]

This is the composition of
`pairedEtaCompletedMomentInverseCoherentComplement_add_band` and
`pairedEtaCompletedMomentInverseRegion_full_zero`, using the existing
full moment inversion rather than a new cancellation premise.
The whole physical prefix has norm at most
`abs(X_rho) Z_rho`, where `Z_rho=abs(rho)/Re(rho)+1`.
Before any norm or real part is taken,
`pairedEtaCompletedMomentInverseCoherentComplement_cross_eq` proves

\[
 Q_M\overline{P_M}+|P_M|^2
 =\left(M^\rho X_\rho
       \operatorname{pairedEtaUnpairedDirichletPrefix}(M,\rho)\right)
       \overline{P_M}.
\]

Its exact complex correction has norm at most
`abs(X_rho) Z_rho abs(P_M)`. If `K≥4Z_rho`, the anchored lower
bound implies

\[
 \operatorname{Re}(Q_M\overline{P_M})
 \le-\frac{|X_\rho|^2}{8}K^2,\qquad 0\le r<K.
\]

This identifies a quantitative negative interaction with the full moving
complement at order zero. Taking separate region norms before this
interaction is used loses a leading quadratic cancellation. The result
does not control the completed signed current's weighted first absolute
moment, and it does not compare away the surviving off-critical principal
endpoint. The next estimate must retain the full cross-region identity,
both reflected completion channels, and the actual head and adjacent
moment orders. The global goal, zero-free strip, and certificate status
are unchanged; no mathematical priority claim is made.

## Checked transport to complete zeroth-order inverse energies

The compiled terminal
[pairedEtaLeadingCurrent_fullInverseEnergy_firstMoment_stability](../RiemannGaussian/EtaCurrentFullInverseEnergy.lean)
proves a uniform finite difference between the original current's first
absolute moment and that of a signed expression in the **full original**
zeroth-order inverse regions. The companion
`pairedEtaLeadingCurrentLinearHeatReturn_fullInverseEnergy_firstMoment_stability`
retains the actual Gaussian return and its additional summable heat error.
These are estimates for the transport error; neither bounds the signed
energy's first absolute moment itself.

Write `m=analyticZetaZeroMultiplicity rho`, `M_N=2(N+2)`,
`L_N=pairedEtaLogTailCutoff(N+2)`, and
`F_k(N)=pairedEtaFiniteCompletedMoment rho (N+2) k`. The exact
complex coefficient is `alpha_k=k!/rho^k`.
[pairedEtaFiniteCompletedMoment_sub_coefficient_mul_zero](../RiemannGaussian/EtaCurrentZeroMomentReduction.lean)
retains both Euler defects:

\[
 F_k-\alpha_kF_0=(F_k-e_k)-\alpha_k(F_0-e_0).
\]

For every `k<m`, the same file proves

\[
 |F_k-\alpha_kF_0|
 \le (E_k+|\alpha_k|E_0)\frac{D_\rho(N)}{N+1},
 \qquad D_\rho(N)=(2(N+1)+1)^{-\operatorname{Re}\rho},
\]

where `E_k` is the existing explicit completed Euler error constant.
The actual zero multiplicity supplies every lower-moment hypothesis.
For the literal head `H_rho(N)`,
`pairedEtaHeadCompletedMoment_sub_shift_mul_zero` keeps the geometric
half-step defect and the zeroth Euler defect separately. Its norm is at
most

\[
 |H_\rho-\delta_N\rho F_0|
 \le (H_{\rm half}+|\rho|E_0)\frac{D_\rho(N)}{(N+1)^2}.
\]

Here `H_half` is the existing explicit half-step error constant.
The complete product identity
`pairedEtaFiniteCompletedMoment_product_sub_zero` retains both positions
before estimating. If `A_k=E_k+|alpha_k|E_0` and
`Q_rho=pairedEtaCurrentMomentConstant rho`, its error constant is
`P_(k,l)=A_k Q_rho+|alpha_k|Q_rho A_l`.
Both exact complex branch errors and their weighted estimates are in
[EtaCurrentZeroEnergyTransport.lean](../RiemannGaussian/EtaCurrentZeroEnergyTransport.lean).

Define the complex coefficient

\[
 c_\rho=
 \begin{cases}
 \rho,&m=1,\\
 (m-1)\alpha_{m-2}\overline{\alpha_{m-1}},&m\ge2.
 \end{cases}
\]

`pairedEtaCurrentZeroEnergyCoefficient_re_pos` proves
`Re(c_rho)>0` for both actual branches. No completion factor is dropped:
it remains inside `F_0` and the original inverse terms.
`pairedEtaFiniteCompletedMoment_eq_fullInverseRegion` gives the exact
identity

\[
 F_0(N)=V_{\rho,0}(L_N;M_N,\mathcal H_{M_N}),
 \qquad \mathcal H_M=\{(d,e):d,e\ge1,\ de\le M\}.
\]

Thus the derived full inverse energy is

\[
 E_\rho(N)=2\delta_N\left[
   \operatorname{Re}(c_{\rho^*})|V_{\rho^*,0}|^2
   -\operatorname{Re}(c_\rho)|V_{\rho,0}|^2\right].
\]

Let `C_rho` equal `(H_half+|rho|E_0)Q_rho` in the simple branch
and `(m-1)P_(m-2,m-1)` otherwise. The pointwise terminal
`pairedEtaLeadingCurrent_weighted_fullInverseEnergy_error_le` proves

\[
 (2N+1)|J_\rho(N)-E_\rho(N)|
 \le e_\rho(N):=
 4\,\frac{C_{\rho^*}D_{\rho^*}(N)+C_\rho D_\rho(N)}{N+1}.
\]

`summable_pairedEtaCurrentZeroEnergyErrorEnvelope` proves
`sum_N e_rho(N)<infinity` from the actual positive horizontal coordinates.
The uniform stability budget is its genuine finite sum. Adding the
already summable linear-width heat majorant gives the corresponding
return budget; the signed complex weighted return-error series is also
proved summable.

The complete carrier remains available before these norm estimates.
`pairedEtaCompletedMomentInverseRegion_full_product_eq_split`
retains all four ordered complex products for two independently selected
subregions and arbitrary moment orders. In each zeroth channel,
`pairedEtaCurrentFullInverseEnergy_eq_split` keeps

\[
 |V_{\rho,0}|^2=|Q_\rho|^2+|P_\rho|^2
                  +2\operatorname{Re}(Q_\rho\overline{P_\rho}),
\]

where `P` is the chosen region and `Q` its entire moving complement.
[EtaCurrentCoherentComplement.lean](../RiemannGaussian/EtaCurrentCoherentComplement.lean)
chooses the original coherent region with
`K=floor(M_N/(B_rho+2))`, `B_rho=4(1+ceil(norm(rho)))`.
`pairedEtaCurrentCoherentBand_subset` discharges its physical inclusion
at every `N`.
`pairedEtaLeadingCurrent_weighted_coherentComplement_error_le` then
states the original-current estimate directly in these full signed split
energies with the same summable envelope and no auxiliary region premise.
For `K≥B_rho+2` and `K≥4(norm(rho)/Re(rho)+1)`,
`pairedEtaCurrentCoherentComplement_cross_re_le` transfers the negative
physical mixed bound `-|X_rho|²K²/8` to this literal current cutoff.
The integer remainder is smaller than `B_rho+2≤K`, so the original
coherence window condition is proved.

The remaining obligation is now directly on `sum_(N<K) (2N+1)|E_rho(N)|`,
uniformly in `K`. The internal complement cancellation and its transport
to both multiplicities are established. They do not cancel the different
horizontal powers in the two reflected full channels. The existing
conditional positive-power lower bound still applies at a hypothetical
off-critical zero. The uniform bound, an off-critical exclusion, and RH
remain open. That transport did not alter the concrete zero-free strip;
the following arithmetic estimate strengthens it. No priority claim or
new zero-proportion certificate is made.

## Checked exact-pole quadratic margin and the original current

The compiled terminal
[nontrivialZetaZero_mem_signedQuadratic_strip](../RiemannGaussian/ZetaSignedQuadraticMargin.lean)
gives a strictly stronger explicit region containing every actual
nontrivial zero. Its arithmetic input is the unchanged von Mangoldt
series with signed `3-4-1` positivity and the complete local divisor.
The canonical disc contains a selected zero near the right boundary,
not both reflected zeros simultaneously. Reflection is applied only after
proving the right margin.

The real-axis estimate
`neg_logDeriv_riemannZeta_real_le_local` in
[ZetaSignedExactPole.lean](../RiemannGaussian/ZetaSignedExactPole.lean)
uses the existing signed decomposition at height zero:

\[
 \operatorname{Re}\!\left(-\frac{\zeta'}{\zeta}(1+x)\right)
 \le \frac1x+448\log 22,\qquad 0<x\le\frac14.
\]

This removes the preceding error `28224` and the much smaller restriction
`x≤1/28224`. The exact identity
`zetaPole_real_part` retains

\[
 \operatorname{Re}\frac1{x+i y}=\frac{x}{x^2+y^2}.
\]

`neg_logDeriv_riemannZeta_re_le_exactPole_sub_poleSum` keeps the
entire signed local zero sum beside this term. At `y≠0` it is at
most `x/y²`. At the selected actual zero, the full analytic
multiplicity contributes `-m/(x+1-beta)`.
`four_mul_multiplicity_div_gap_le_exactPole` therefore proves

\[
 \frac{4m}{x+1-\beta}\le\frac3x+
 448\bigl(3L(0)+4L(y)+L(2y)\bigr)+\frac{17x}{4y^2},
 \qquad L(y)=\log(|y|+22),
\]

for `beta≥3/4` and `0<x≤1/4`. The full complex prime series and
local logarithmic-derivative identities remain available upstream.
Using `L(0)≤L(y)` and `L(2y)≤2L(y)` bounds the logarithmic
error by `4032L(y)`.

Set `d=1-beta`. When `d≤1/24`, choosing `x=6d` preserves every
analytic side condition. The terminal
`multiplicity_le_quadratic_signed_zero_gap` proves

\[
 8m-7\le 56448L(y)d+357\frac{d^2}{y^2}.
\]

The rational subsolution in
`rational_margin_le_of_quadratic_gap` gives the explicit margin

\[
 q_m=8m-7,\qquad
 \delta_{\rm quad}(m,y)=
 \min\!\left\{\frac1{24},
 \frac{q_m|y|}{56448L(y)|y|+19q_m}\right\}.
\]

Every actual analytic multiplicity has `m≥1` and `q_m≥1`. The
implemented weight is `8*(m-1)+1` with natural subtraction so its unused
order-zero definition is also positive; `zetaSignedMultiplicityWeight_eq`
proves the displayed coefficient at every actual order.
The cap handles zeros outside the local boundary neighborhood.
Completed reflection preserves the ordinate and multiplicity, giving

\[
 \delta_{\rm quad}(m,\gamma)
 \le\operatorname{Re}\rho
 \le1-\delta_{\rm quad}(m,\gamma).
\]

[thirtyOne_mul_signedLogZeroMargin_lt_quadratic](../RiemannGaussian/ZetaSignedQuadraticComparison.lean)
proves the exact strict comparison
`31*delta_signed(y)<delta_quad(m,y)` for every `y≠0`.
`nontrivialZetaZero_mem_quadratic_reciprocal_log_strip` gives the simpler
margin `1/(56458 log(abs(gamma)+22))` for `abs(gamma)≥1`.
These are bounds on the literal zeros, with all analytic premises
discharged. They improve the preceding project formalisation; they are
not presented as improving classical analytic zero-free regions.

The bridge in
[EtaCurrentQuadraticPrimeBound.lean](../RiemannGaussian/EtaCurrentQuadraticPrimeBound.lean)
takes the maximum `Delta(m,y)` of this new margin and every previous
signed, eta, and multiplicity margin. The compiled terminals
`pairedEtaLeadingCurrent_firstMoment_le_quadraticPrime` and
`pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_quadraticPrime`
give the unchanged current and actual return the bound

\[
 S_\rho(K),\ S^{\rm return}_\rho(K)
 \le C_\rho(K+1)^{\,1-2\Delta(m,\gamma)}.
\]

The existing explicit `pairedEtaCurrentReturnGrowthConstant` supplies
`C_rho`, with exact critical-line cancellation handled separately.
`pairedEtaCurrentFullInverseEnergy_firstMoment_le_quadraticPrime` gives
the complete signed inverse energy the same exponent and the constant
`C_rho+sum_N pairedEtaCurrentZeroEnergyErrorEnvelope rho N`.
That additional sum is already proved finite, and all band/complement
cross terms remain available in the exact inverse representation.

`etaQuadraticPrimeProduct_return_exponent_lt_of_simple` proves strict
improvement over the preceding exponent at every actual simple zero.
`etaQuadraticPrimeProduct_return_exponent_bounds` still places the
stated exponent in `[7/8,1)`. This does not establish the uniform
cutoff-independent estimate or exclude every off-critical zero.
The global goal remains open, with no new zero-proportion certificate
or novelty-priority claim.

## Checked simultaneous edge-window multiplicity and separation

The new terminal theorem
[sum_multiplicity_le_one_in_signedEdgeWindow](../RiemannGaussian/ZetaSignedWindowMultiplicity.lean)
is stated for actual nontrivial zeta zeros and their full analytic
multiplicities. For an arbitrary real center `y` with `abs(y) ≥ 1`, define

\[
 L(y)=\log(|y|+22),\qquad D(y)=\frac1{6000L(y)}.
\]

Every finite set `S` of actual zeros satisfying

\[
 1-D(y)\le\Re\rho<1,\qquad |\Im\rho-y|\le D(y)
 \quad(\rho\in S)
\]

has

\[
 \sum_{\rho\in S}m_\rho\le1.
\]

This is a simultaneous count, rather than an estimate that selects just
one zero. [ZetaSignedZeroSeparation](../RiemannGaussian/ZetaSignedZeroSeparation.lean)
discharges its consequences on the actual carrier:

- `analyticZetaZeroMultiplicity_eq_one_in_signedEdgeWindow` proves every
  zero there is simple.
- `eq_of_mem_signedEdgeWindow` proves any two zeros in that window equal.
- `signedEdgeWindowWidth_lt_im_sub_of_ne` proves
  `abs(Im tau - Im rho) > D(Im rho)` for distinct zeros when
  `abs(Im rho) ≥ 1` and both real parts are at least `1-D(Im rho)`.
- `sum_multiplicity_le_one_in_signedLeftEdgeWindow` transfers the entire
  finite multiplicity count by `rho ↦ 1-conj(rho)` to
  `0 < Re rho ≤ D(y)` with the same ordinate window.

The common-center analytic input is proved in
[ZetaSignedWindowPole](../RiemannGaussian/ZetaSignedWindowPole.lean).
`localZetaZeroTranslate_mem_canonicalBall` places every selected actual
zero in the common canonical disc; translation retains its full
meromorphic order. Before taking real parts,
`localZetaPoleSum_eq_selected_add_complement` reconstructs the full
complex pole sum from the selected zero terms and every remaining
divisor term. Thus ordinate displacement, phase, and multiplicity are
retained in an exact source identity.

`four_mul_localZetaPoleSum_re_le_quadraticHeight` proves, for
`0 < x ≤ 1/4` and `y ≠ 0`,

\[
 4\Re P_y(x-\tfrac12)
 \le \frac3x+4032L(y)+\frac{17x}{4y^2}.
\]

All selected zeros are evaluated at the same `x=4D`. Writing
`u=1+4D-Re rho` and `v=y-Im rho` gives `4D≤u≤5D` and `abs(v)≤D`.
The checked Cauchy floor is

\[
 \frac{u}{u^2+v^2}\ge\frac5{26D}.
\]

The real contributions of every complementary divisor point are
nonnegative. A total multiplicity of at least two would therefore imply

\[
 \frac{20}{13}
 \le\frac34+\frac{4032}{6000}+17D^2
 \le\frac34+\frac{4032}{6000}+\frac{17}{256}
 <\frac{20}{13},
\]

an exact rational contradiction. Positivity of `D`, `D≤1/16`,
`L(y)D=1/6000`, and `y²≥1` are all discharged in Lean.

Finally,
`analyticZetaZeroMultiplicity_eq_one_of_near_edge` proves simplicity
when `abs(Im rho)≥1` and
`min(Re rho,1-Re rho)≤D(Im rho)`.
`pairedEtaLeadingCurrent_eq_momentInverse_head_of_near_edge` then gives
the unchanged original current's complete head inverse sum at every
physical cutoff. Both completion colours and every original inverse
term remain present; multiplicity one is a consequence of location,
not an extra analytic premise.

The new result is a local simplicity and separation constraint. It does
not improve the preceding all-zero zero-free strip or the positive
current-growth exponent, and it does not establish global simplicity.
A possible isolated simple off-critical zero still produces the
previously proved positive-power current obstruction. The uniform
weighted arithmetic bound and RH remain open. This slice makes no
novelty-priority or improvement-over-literature claim.

## Checked Gaussian reciprocal-zeta contour with complete corrections

The compiled terminal
[zetaReciprocalGaussian_right_integral_le](../RiemannGaussian/ZetaReciprocalGaussianContour.lean)
gives an independent analytic bound for the actual reciprocal-zeta
Gaussian kernel. It is intended to feed estimates for the original
Möbius coefficients. It is not yet an estimate for their infinite
Gaussian sum or for the signed eta current.

Write `L(y)=log(abs(y)+22)` and `e(y)=1/(500000 L(y))`.
[ZetaReciprocalGeometry](../RiemannGaussian/ZetaReciprocalGeometry.lean)
proves nonvanishing of the actual pole-removed zeta function on
`Re s ≥ 1-e(Im s)` when `abs(Im s)≥1`. For a common local center with
`abs(y)≥2`, every nonzero divisor coefficient has

\[
 \Re i\le-\frac12-4e(y).
\]

Consequently every point with `Re z≥-1/2-e(y)` stays at norm distance at
least `3e(y)` from every enclosed pole. The proof constructs each
divisor point as an actual nontrivial zero and applies the previously
checked margin at its own ordinate; neighbouring logarithmic heights
are compared explicitly.

[ZetaLocalReciprocal](../RiemannGaussian/ZetaLocalReciprocal.lean)
retains the complete complex factorisation before taking a norm:

\[
 \left(\prod_i B_i(z)^{d_i}\right) f_y(z)
 =\exp(\mathcal L_y(z))g_y(0).
\]

Here `f_y` is the actual translated pole-removed zeta function, `d_i` its
complete local analytic divisor, `B_i` its canonical factors, `g_y`
its nonvanishing residual, and `mathcal L_y(0)=0` the normalized
logarithm. The named source is
`localZetaPoleRemoved_mul_canonical_eq_exp`. On `norm(z)≤5/8`,
`norm_localZetaCanonicalLog_le_forty` gives `norm(mathcal L_y(z))≤40L(y)`.
The proved pole distance bounds each canonical factor by `2/e(y)`.
Jensen's complete multiplicity count gives

\[
 \sum_i d_i\log|B_i(z)|\le32L(y)\log(2/e(y)).
\]

Together with the safe-center norm floor `1/16` this proves
`norm_inv_localZetaPoleRemoved_le`. At an actual point
`1-e(y)≤Re s≤3/2`, `Im s=y`, `abs(y)≥2`, the resulting bound is

\[
 B_h(y)=16(|y|+1)
 \exp\!\left(40L(y)+32L(y)\log(1000000L(y))\right).
\]

The compact middle of the contour is also discharged.
[ZetaReciprocalLowHeight](../RiemannGaussian/ZetaReciprocalLowHeight.lean)
constructs a fixed `c>0` such that
`c≤norm(riemannZeta₁(1+i y))` for every `abs(y)≤2`.
This constant is obtained from an actual positive compact minimum,
not supplied as a hypothesis and not asserted to have a checked
numerical value. The eta derivative bound is at most `16928` throughout
the required horizontal segments. Thus

\[
 w_0=\min\!\left(\frac18,\frac{c}{33856}\right)>0
\]

preserves the lower bound `c/2` when `abs(Re s-1)≤w0` and `abs(Im s)≤2`.
The genuine reciprocal extension

\[
 E(s)=\frac{s-1}{\operatorname{riemannZeta}_1(s)}
\]

is exactly `1/zeta(s)` away from one and has its removable value
`E(1)=0`. Its norm is at most `6/c` on the low-height rectangle.
The extension and its analytic identity are proved; no singular
expression is used as though nonzero at the pole.

[ZetaReciprocalBox](../RiemannGaussian/ZetaReciprocalBox.lean) defines

\[
 w(T)=\min(w_0,e(T)),\qquad B(T)=\max(6/c,B_h(T)).
\]

`riemannZeta₁_ne_zero_on_reciprocalBox`,
`analyticAt_zetaReciprocalExtension_on_box`, and
`norm_zetaReciprocalExtension_le_on_box` prove that `E` is analytic near
every point of the whole closed rectangle
`abs(Re s-1)≤w(T)`, `abs(Im s)≤T` and has norm at most `B(T)` there.
Both bounds are finite and positive. The threshold theorem proves
`w(T)=e(T)` whenever
`T≥max(2, exp(1/(500000 w0)))`.

For the actual kernel `K(s)=exp(a s+tau s²)E(s)`, let `V_sigma` be its
vertical integral with ordinates from `-T` to `T`, and `H_t` its
horizontal integral from `1-w` to `1+w` at ordinate `t`.
`zetaReciprocalGaussian_contour_shift` retains the exact orientation:

\[
 iV_{1+w}=iV_{1-w}+H_T-H_{-T}.
\]

For `T≥2`, `a≥0`, and `tau≥0`, the compiled right-integral bound is

\[
 |V_{1+w}|
 \le 2TB(T)e^{a(1-w)+\tau(1-w)^2}
   +4wB(T)e^{a(1+w)+\tau(1+w)^2-\tau T^2}.
\]

The horizontal-integral theorem bounds each correction separately.
All zero avoidance and analyticity needed by Cauchy's theorem are
discharged on the actual full rectangle, including the middle segment.
The exact complex kernel retains its Gaussian phase before the norm
estimate is taken.

The full right-line Gaussian integral is now identified with its
original Möbius series, with sum-integral exchange and both
unbounded vertical tails justified in the following slice. The subsequent
unit-time scale choice supplies a proved arithmetic cancellation rate.
An estimate of sufficient strength for transfer to the
original inverse energy is still needed. That transfer must preserve the moving
physical cutoffs, completion factors, and both reflected channels.
The current contour stays at real part at least `7/8`; this result does
not by itself supply the missing critical-strength arithmetic estimate.
It changes neither the established zero-free margin nor the original
current's positive growth exponent. The uniform weighted goal and RH
remain open, with no novelty-priority or new certificate claim.

## Checked full Gaussian Möbius identity and arithmetic contour bound

[GaussianMellinVertical.lean](../RiemannGaussian/GaussianMellinVertical.lean),
[ZetaReciprocalDirichlet.lean](../RiemannGaussian/ZetaReciprocalDirichlet.lean),
[GaussianMoebiusMellin.lean](../RiemannGaussian/GaussianMoebiusMellin.lean),
and [GaussianMoebiusContourBound.lean](../RiemannGaussian/GaussianMoebiusContourBound.lean)
close the full arithmetic identification and all infinite-tail obligations
for the preceding contour.

For real `a` and `tau>0`, define the actual signed sum

\[
 S_\tau(a)=\sum_{n\ge1}\mu(n)
  \exp\!\left(-\frac{(a-\log n)^2}{4\tau}\right).
\]

The Lean series runs over natural numbers; its zero term is exactly zero
because `mu(0)=0`. `summable_gaussianMoebiusSummand` proves convergence,
without assuming a conjectural Möbius cancellation estimate.
`zetaReciprocalExtension_eq_moebius_LSeries` identifies the genuine
reciprocal with its absolutely convergent Dirichlet series for every
`Re(s)>1`. The original complex summands keep their full logarithmic
phases in `moebius_LSeries_term_eq_exp` and
`gaussianMoebiusMellinTerm_eq_atom`.

`integral_gaussianMellin_vertical` gives the exact full Gaussian atom:

\[
 \int_{\mathbb R}e^{b(\sigma+it)+\tau(\sigma+it)^2}\,dt
 =\sqrt{\pi/\tau}\,e^{-b^2/(4\tau)}.
\]

The cancellation of the abscissa occurs only after integration.
Individual integrability, full reciprocal-kernel integrability, and
summability of the norm integrals are established before exchanging the
full series and integral. Thus
`integral_zetaReciprocalGaussianKernel_eq_gaussianMoebiusSum` proves,
for every real `sigma>1`,

\[
 \int_{\mathbb R}
  \frac{e^{a(\sigma+it)+\tau(\sigma+it)^2}}{\zeta(\sigma+it)}\,dt
 =\sqrt{\pi/\tau}\,S_\tau(a).
\]

Let `D(sigma)=sum_n |mu(n)|/n^sigma` be
`moebiusDirichletMass sigma`. Its summability is proved at every
`sigma>1`, as is the uniform vertical reciprocal bound by `D(sigma)`.
At every `T>=0`,
`zetaReciprocalGaussian_infinite_tails_le` bounds the integral over
the complement of `(-T,T]` by

\[
 D(\sigma)\sqrt{2\pi/\tau}\,
 e^{a\sigma+\tau\sigma^2-\tau T^2/2}.
\]

Both tails are included. Half the Gaussian exponent supplies height
suppression, and the other half supplies an integrable majorant.
`gaussianMoebiusSum_eq_truncated_add_tail` proves the exact finite/full
split. At the actual contour abscissa `sigma=1+w(T)`,
`gaussianMoebiusSum_contour_identity` retains

\[
 i\sqrt{\pi/\tau}\,S_\tau(a)
 =iV_{1-w}+H_T-H_{-T}+iR_{1+w,T},
\]

where `R` is the complete right-line tail integral and `V,H` are
the original finite contour segments. No boundary or phase term is
discarded from this source identity.

Finally, `gaussianMoebiusSum_contour_bound` proves for
`a>=0,tau>0,T>=2`, with `ell=1-w(T)` and `sigma=1+w(T)`,

\[
 |S_\tau(a)|\le
 \frac{
 2TB(T)e^{a\ell+\tau\ell^2}
 +4w(T)B(T)e^{a\sigma+\tau\sigma^2-\tau T^2}
 +D(\sigma)\sqrt{2\pi/\tau}\,
    e^{a\sigma+\tau\sigma^2-\tau T^2/2}
 }{\sqrt{\pi/\tau}}.
\]

This is an unconditional bound for the actual arithmetic Gaussian sum.
The following slice controls `D(1+w(T))` and chooses `tau,T` relative
to `a` to extract a quantitative cancellation rate. An estimate of
sufficient strength is still needed for the original full inverse
energy, preserving physical cutoffs, completion factors, reflected
channels, and every mixed term. The contour remains near real part one;
the unchanged uniform weighted target remains open.

## Checked unit-time Gaussian Möbius cancellation rate

[ZetaMoebiusMassBound.lean](../RiemannGaussian/ZetaMoebiusMassBound.lean),
[GaussianMoebiusScaleConstants.lean](../RiemannGaussian/GaussianMoebiusScaleConstants.lean),
[GaussianMoebiusScaleEnvelope.lean](../RiemannGaussian/GaussianMoebiusScaleEnvelope.lean),
and [GaussianMoebiusCancellation.lean](../RiemannGaussian/GaussianMoebiusCancellation.lean)
give the next independent arithmetic input with all scale assumptions
discharged.

The actual Möbius mass is at most the positive real zeta series:
`moebiusDirichletMass_le_norm_zeta` proves
`D(sigma)≤norm(zeta(sigma))` for `sigma>1`.
The original eta support estimate then gives
`moebiusDirichletMass_contour_le_four_div`:

\[
 D(1+w(T))\le \frac4{w(T)}.
\]

Beyond the already proved fixed threshold where
`w(T)=1/(500000 L(T))`, this is at most `2000000 L(T)`.
No Möbius cancellation is assumed in this bound.

Define the fixed constants

\[
 C=\max(6/c,16),\qquad
 P=C(3+4000000\sqrt{2\pi})e^2,\qquad
 G=33000001+|\log P|.
\]

Here `c>0` is the previously proved compact pole-removed zeta norm floor;
none of these constants depends on height or arithmetic scale.
`zetaReciprocalContourBound_le_logSquare` gives

\[
 B(T)\le C\,e^{33000000L(T)^2}.
\]

Choose the actual contour height `T=a` and fix heat time `tau=1`.
For `a≥22` beyond the width threshold,
`gaussianMoebiusSum_one_le_scale_prefactor` retains all three
contour contributions in the bound

\[
 |S_1(a)|\le P\,a\,e^{33000000L(a)^2}e^{a(1-w(a))}.
\]

Both horizontal corrections and both infinite tails are included.
The first tail suppression `e^{-a^2/2}` already absorbs the cost of
using the right line. The fixed prefactor and `a` can also be absorbed,
giving `gaussianMoebiusSum_one_le_logSquare_envelope`:

\[
 |S_1(a)|\le
 e^{a-a/(500000L(a))+G L(a)^2}.
\]

`tendsto_localZetaLogHeight_pow_div_zero` proves `L(a)^n/a→0`
for every fixed natural `n`.
In particular, `eventually_gaussianMoebiusScaleCost_le_half_gain`
proves `G L(a)^2≤a/(1000000L(a))` eventually.
The terminal theorem
`gaussianMoebiusSum_one_le_reciprocal_log_gain_eventually` therefore
has no open scale, convergence, or arithmetic hypotheses:

\[
 \text{eventually}\quad
 |S_1(a)|\le
 \exp\!\left(a-\frac{a}{1000000\log(a+22)}\right).
\]

The threshold is proved to exist; no numerical starting point is
asserted. `gaussianMoebiusSum_one_exp_ratio_tendsto_zero` proves
`S_1(a)/exp(a)→0`, and
`gaussianMoebiusSum_log_one_div_tendsto_zero` carries this to
`S_1(log X)/X→0` on the original multiplicative scale.
The earlier complex atoms and full oriented contour identity remain
available; the scalar estimate is a named downstream consequence.

The displayed saving is not a fixed power saving in `X`. An estimate
strong enough for the original complex weights and moving physical
cutoffs is still needed before transferring to the signed full inverse
energy. Completion factors, both reflected channels, and mixed terms
must survive that transfer. The new rate does not improve the existing
zero-free strip or the current's established positive exponent. It
does not exclude an interior off-critical zero or prove the uniform
weighted current bound. No novelty priority or new certificate is claimed.

## Checked complex-weighted Gaussian Möbius cancellation

[GaussianMoebiusNormalized.lean](../RiemannGaussian/GaussianMoebiusNormalized.lean),
[ComplexGaussianMoebius.lean](../RiemannGaussian/ComplexGaussianMoebius.lean),
[GaussianMoebiusPhaseAtom.lean](../RiemannGaussian/GaussianMoebiusPhaseAtom.lean),
[GaussianMoebiusPhaseHeat.lean](../RiemannGaussian/GaussianMoebiusPhaseHeat.lean),
and [GaussianMoebiusComplexCancellation.lean](../RiemannGaussian/GaussianMoebiusComplexCancellation.lean)
transfer the actual signed unit-time cancellation to every fixed complex
Mellin weight. No convergence or domination hypothesis is left open.

The full arithmetic family is

\[
 W_{s,\tau}(a)=\sum_{n\ge1}\mu(n)n^{-s}
 \exp\!\left(-\frac{(a-\log n)^2}{4\tau}\right).
\]

`complexGaussianMoebiusSummand_eq_cpow` retains exactly the original
complex Dirichlet power, including the vanishing zero index.
The exact norm identity `norm_complexGaussianMoebiusSummand` is

\[
 \|W_{s,\tau,n}(a)\|
 =e^{-\Re(s)a+\tau\Re(s)^2}
   |S_{\tau,n}(a-2\tau\Re(s))|.
\]

Thus `summable_complexGaussianMoebiusSummand` proves absolute convergence
for every complex `s`, real center `a`, and positive `tau`.
This summability uses no zeta-zero premise.

Let `F(a)=S_1(a)/exp(a)`. The proved unit-time cancellation gives
`F(a)→0` at the positive end. A direct absolutely convergent reciprocal-line
bound controls every remaining real center:
`abs_gaussianMoebiusSum_le_dirichlet` proves
`|S_tau(a)|≤D(sigma) exp(a sigma+tau sigma²)` for all real `a`,
`tau>0`, and `sigma>1`. Combining these two estimates,
`exists_bound_normalizedGaussianMoebius` proves one finite global bound
`|F(a)|≤C` for every real `a`.

The phase kernel is

\[
 K_s(v)=e^{(1-2s)v-v^2/4}.
\]

For the actual signed source atom
`H_s,a,n(v)=S_1,n(a+v) exp(−a−v) K_s(v)`,
`integral_complexGaussianMoebiusHeatTerm` evaluates the full complex
Gaussian integral:

\[
 \int_{\mathbb R}H_{s,a,n}(v)\,dv
 =\sqrt{2\pi}\,e^{(s-1)a+2s^2}W_{s,2,n}(a).
\]

Every atom is integrable, and the exact norm integral is
`sqrt(2 pi) exp((Re(s)−1)a+2 Re(s)²) norm(W_s,2,n(a))`.
`summable_integral_norm_complexGaussianMoebiusHeatTerm` therefore
discharges the infinite arithmetic exchange. The full signed identity
`integral_normalizedGaussianMoebius_heat` is

\[
 \int_{\mathbb R}F(a+v)K_s(v)\,dv
 =\sqrt{2\pi}\,e^{(s-1)a+2s^2}W_{s,2}(a).
\]

The fixed kernel is integrable for every complex `s`. The global source
bound supplies the integrable dominator `C norm(K_s(v))`, and each fixed
translate of `F` tends to zero. Dominated convergence gives the terminal
theorem `complexGaussianMoebiusSum_two_normalized_tendsto_zero`:

\[
 e^{(s-1)a}W_{s,2}(a)\longrightarrow0
 \quad(a\longrightarrow+\infty).
\]

The normalization retains its complex phase. The separate theorem
`complexGaussianMoebiusSum_log_two_normalized_tendsto_zero` gives
`X^(s−1) W_s,2(log X)→0` using the actual complex power.
Only downstream,
`complexGaussianMoebiusSum_log_two_norm_ratio_tendsto_zero` takes norms
to obtain `norm(W_s,2(log X))/X^(1−Re(s))→0`.

These are fixed-weight limits for infinite Gaussian sums. They assert
neither uniformity in `s` nor a fixed power saving. For an actual zero
`rho`, both natural comparison exponents `1−Re(rho)` and `Re(rho)`
remain positive. No estimate here transfers the cancellation to the
original divisor-dependent finite cutoffs or compares their completed
reflected energies. Such a transfer needs a sufficiently strong bound
while retaining every divided cutoff, completion factor, and mixed term.
The current exponent and zero-free strip are unchanged. The uniform
weighted arithmetic goal remains open; no novelty priority is claimed.

## Checked finite Möbius cancellation and original quotient blocks

The new finite-cutoff chain removes the Gaussian smoothing and then
applies the resulting cancellation to the original complex coefficient
blocks with a common divided cutoff.

[GaussianMoebiusHeatScale.lean](../RiemannGaussian/GaussianMoebiusHeatScale.lean)
proves `gaussianMoebiusSum_le_reciprocal_log_gain_eventually` at every
fixed `tau>0`. The full contour estimate still includes both horizontal
corrections and both infinite tails. The threshold depends on `tau`;
arbitrarily small positive heat times are permitted.
[GaussianMoebiusPrimitive.lean](../RiemannGaussian/GaussianMoebiusPrimitive.lean)
proves a global bound for `S_tau(a)/exp(a)` and the cumulative limit

\[
 U_\tau(a)=\int_{-\infty}^a S_\tau(u)\,du,
 \qquad U_\tau(a)/e^a\longrightarrow0.
\]

Let

\[
 M_\mu(M)=\sum_{n=1}^M\mu(n),\qquad
 g_\tau(v)=e^{-v^2/(4\tau)},\qquad
 A_\tau=\sqrt{4\pi\tau}.
\]

[GaussianMoebiusCumulativeAtoms.lean](../RiemannGaussian/GaussianMoebiusCumulativeAtoms.lean)
proves summability of the absolute integrals of the actual arithmetic
atoms up to each real cutoff.
[MoebiusGaussianCutoff.lean](../RiemannGaussian/MoebiusGaussianCutoff.lean)
then proves `gaussianMoebiusCumulative_eq_smoothed_finitePrefix`:

\[
 U_\tau(a)=
 \int_{\mathbb R}g_\tau(v)M_\mu(\lfloor e^{a+v}\rfloor)\,dv.
\]

The source identity retains every signed integer endpoint.
[MoebiusFiniteCutoff.lean](../RiemannGaussian/MoebiusFiniteCutoff.lean)
proves the literal prefix displacement bound with one floor-error unit.
Consequently, `abs_moebiusFinitePrefix_gaussian_error_le` gives

\[
 |A_\tau M_\mu(\lfloor e^a\rfloor)-U_\tau(a)|
 \le e^a\int_{\mathbb R}g_\tau(v)|e^v-1|\,dv+A_\tau.
\]

The exact exponential moments in
[GaussianMoebiusCutoffKernel.lean](../RiemannGaussian/GaussianMoebiusCutoffKernel.lean)
give, for every `eta>0`,

\[
 \frac{\int g_\tau(v)|e^v-1|\,dv}{A_\tau}
 \le \eta+\frac{e^{4\tau}-2e^\tau+1}{\eta}.
\]

`exists_moebiusCutoffGaussian_error_le` proves that a positive heat
time makes this normalized error as small as prescribed.
All integrability and arithmetic exchanges are discharged.
[MoebiusFiniteCancellation.lean](../RiemannGaussian/MoebiusFiniteCancellation.lean)
therefore proves `moebiusFinitePrefix_div_tendsto_zero`:

\[
 M_\mu(M)/M\longrightarrow0.
\]

This is the ordinary unsmoothed finite sum. The real-cutoff version
retains `floor(X)` and proves `M_mu(floor X)/X→0` as well.

The original complex weights are then retained in
[MoebiusFiniteMellin.lean](../RiemannGaussian/MoebiusFiniteMellin.lean).
Writing `P_s(M)=sum_{1≤n≤M} mu(n)n^(-s)`,
`complexMoebiusFinitePrefix_eq_abel` proves the exact finite identity

\[
 P_s(M)=M_\mu(M)(M+1)^{-s}
 +\sum_{n=0}^{M-1}M_\mu(n+1)
   \bigl((n+1)^{-s}-(n+2)^{-s}\bigr).
\]

The complete endpoint and weight differences remain complex.
The existing positive-axis power derivative bound and the proved finite
Möbius remainder give
[exists_complexMoebiusFinitePrefix_power_remainder](../RiemannGaussian/MoebiusFiniteMellinBound.lean):
for every fixed `0<Re(s)<1` and `eps>0`, one finite `C_s,eps` satisfies

\[
 \|P_s(M)\|\le\varepsilon(M+1)^{1-\Re(s)}+C_{s,\varepsilon}
 \quad\hbox{for every }M.
\]

[complexMoebiusFinitePrefix_normalized_tendsto_zero](../RiemannGaussian/MoebiusFiniteMellinCancellation.lean)
proves the full complex limit `(M+1)^(s−1)P_s(M)→0`.
The original eta completion is retained in the actual-zero
specialization in the same module.

[MoebiusDividedCutoffBlocks.lean](../RiemannGaussian/MoebiusDividedCutoffBlocks.lean)
now keeps the actual divisor set `{d∈[1,M] : M/d=q}`, for `q>0`.
It is exactly `[M/(q+1)+1,M/q]` with integer division. Its full complex
coefficient is

\[
 D_s(M,q)=\sum_{\substack{1\le d\le M\\ \lfloor M/d\rfloor=q}}
   \mu(d)d^{-s}
 =P_s(\lfloor M/q\rfloor)-P_s(\lfloor M/(q+1)\rfloor).
\]

`exists_complexMoebiusDividedCutoffBlock_power_remainder` supplies one
remainder independent of both `M` and `q`:

\[
 \|D_s(M,q)\|\le
 \varepsilon(\lfloor M/q\rfloor+1)^{1-\Re(s)}+C_{s,\varepsilon}.
\]

Finally,
[EtaMoebiusDividedBlockCancellation.lean](../RiemannGaussian/EtaMoebiusDividedBlockCancellation.lean)
identifies the original zeroth completed moment block exactly as

\[
 \sum_{\substack{1\le d\le M\\ \lfloor M/d\rfloor=q}}
   \operatorname{MomentMoebiusTerm}_{\rho,0}(a;M,d)
 =D_\rho(M,q)\,X_\rho\,
   \operatorname{UnpairedEtaPrefix}_{\rho}(q).
\]

Every divided cutoff, completion phase, and odd last endpoint survives.
The terminal theorem
`exists_pairedEtaCompletedMoebius_divided_block_remainder` bounds the
norm of this actual block by

\[
 \bigl[\varepsilon(\lfloor M/q\rfloor+1)^{1-\beta}+C_{\rho,\varepsilon}\bigr]\,
 \|X_\rho\|\left(\frac{\|\rho\|}{\beta}+1\right)q^{-\beta},
 \qquad \beta=\Re(\rho).
\]

The constant is independent of `a,M,q`; the zero equation supplies the
displayed endpoint factor. The result applies equally to the actual
reflected partner by instantiation.

This closes a finite-cutoff coefficient estimate, not the original
full inverse-energy estimate. Its scale still has a positive power, and
the remainder cannot simply be summed over the growing quotient family
and outer inverse weights. Both reflected mixed energies must still be
controlled jointly with a stronger bound. No fixed power saving, improved
zero strip, uniform weighted current bound, or novelty priority is claimed.

## Checked quantitative finite Möbius rate and completed blocks

The finite-cutoff cancellation now has a specified decay rate and a
specified dependence of its all-cutoff remainder on the scale. The
terminal actual-carrier theorem is
[exists_pairedEtaCompletedMoebius_divided_block_cubic_rate](../RiemannGaussian/EtaMoebiusDividedBlockRate.lean).
Its bound applies above a stated arithmetic cutoff, with the original
completion, divided cutoff, and odd eta endpoint intact.

Write `G(a,tau,T)=gaussianMoebiusContourMajorant a tau T` for the complete
three-term contour envelope. The checked cumulative estimate is

\[
 |U_\tau(a)|\le D(2)e^{4\tau}/2+2G(a,\tau,T),
 \qquad a\ge0,\quad\tau>0,\quad T\ge2.
\]

[abs_gaussianMoebiusCumulative_le_contourMajorant](../RiemannGaussian/GaussianMoebiusCumulativeBound.lean)
includes the entire negative-center integral and every left-line,
horizontal, and infinite-tail contribution. Every center exponential is
integrable over the full one-sided range. The upstream signed arithmetic
and oriented contour identities remain available.

[integral_moebiusCutoffGaussian_error_div_le_sqrt](../RiemannGaussian/MoebiusFiniteContourBound.lean)
gives the normalized absolute cutoff error at most `9 sqrt(tau)` for
`0<tau≤1/4`. The Gaussian normalization identity is exact, and integer
rounding still contributes the normalized unit `exp(−a)`.

The coupled schedule is

\[
 A(h)=10^{15}h^3,\qquad T=e^h,\qquad\tau=e^{-h}.
\]

The actual local height is at most `2h`; the reciprocal norm is at most
`C exp(132000000 h²)`; the width gain satisfies
`A(h) w(exp h) ≥ 1000000000 h²`; the moving absolute Möbius mass is at
most `4000000 h`. Here `C=gaussianMoebiusContourConstant` is the proved
fixed constant including the compact reciprocal bound. All these inputs
are discharged in
[MoebiusExponentialContourScale.lean](../RiemannGaussian/MoebiusExponentialContourScale.lean).

For `h≥22`, `h≥1/(500000 w0)`, and `exp(h)≥4A(h)`,
[gaussianMoebiusContourMajorant_exponentialScale_le](../RiemannGaussian/MoebiusExponentialContourBound.lean)
proves `G(A(h),exp(−h),exp(h)) ≤ P exp(A(h)−h)`, with
`P=3C+4000000 sqrt(2 pi)`. The tail suppression is exactly
`tau*T²=exp(h)`. The simultaneous size conditions hold eventually.

Put `C_mu=10+D(2) exp(4)/2+2P`. The unsmoothed terminal bound is

\[
 |M_\mu(\lfloor e^{A(h)}\rfloor)|
 \le C_\mu e^{A(h)-h/2}
\]

for all sufficiently large `h`
([abs_moebiusLogPrefix_cubic_le_eventually](../RiemannGaussian/MoebiusFiniteQuantitativeCancellation.lean)).
The stronger all-cutoff interface supplies one `H≥22` such that, for
every `h≥H` and every integer `M`,

\[
 |M_\mu(M)|\le C_\mu e^{-h/2}M+e^{A(h)}.
\]

This replaces the unspecified epsilon remainder with its specified
scale dependence. The threshold `H` is proved to exist and is not
numerically evaluated. No numerical starting cutoff is claimed.

The exact finite complex Abel identity then carries both contributions.
For `0<Re(s)<1`, let

\[
 p=1-\Re(s),\quad Z_s=\sum_{n\ge0}(n+1)^{-\Re(s)-1},\quad
 C_s=C_\mu\left(1+\frac{\|s\|}{p}\right)
       +1+\|s\|Z_s.
\]

`Z_s` is the previously proved summable derivative mass. One common
`H` works for all these weights. For `h≥H`,
[exists_complexMoebiusFinitePrefix_cubic_rate](../RiemannGaussian/MoebiusFiniteMellinRate.lean)
proves

\[
 \|P_s(M)\|\le C_s(M+1)^p e^{-h/2}
 \quad\text{if }M+1\ge e^{2A(h)/p}.
\]

For the literal quotient block, put `U=floor(M/q)+1`. Its exact
complex prefix-difference identity and the all-cutoff Abel remainder give

\[
 \|D_s(M,q)\|\le2C_s U^p e^{-h/2},
 \qquad q>0,\quad U\ge e^{2A(h)/p}.
\]

Both endpoints are included; the smaller prefix need not separately
satisfy the size threshold. The terminal theorem on the original carrier
multiplies this coefficient bound by

\[
 \|X_\rho\|
 \left(\frac{\|\rho\|}{\Re(\rho)}+1\right)q^{-\Re(\rho)}.
\]

The common scale threshold also works for every actual zero, while the
constant and the arithmetic cutoff retain the zero dependence. The
original complex coefficient, completion phase, and unpaired endpoint
remain in the upstream exact block identity.

This is quantitative decay on a positive power scale; it gives no fixed
power saving. The blocks below the stated cutoff and the complete
reflected inverse interactions remain open at the strength required for
the original uniform weighted bound. Exact full inversion cancels the
Möbius convolution, so finite-prefix cancellation alone cannot be treated
as an extra saving on the full current. This slice changes neither the
proved zero strip nor the hypothetical off-critical current exponent.
No novelty priority is claimed.

## Checked harmonic cancellation and the actual inverse coefficient sum

The terminal theorem is
[exists_pairedEtaInverseInnerCapCoefficient_cubic_rate](../RiemannGaussian/EtaInverseHarmonicCoefficients.lean).
It controls the signed product coefficients throughout an entire original
inner-truncated physical inverse region. All arithmetic premises are
discharged. The estimate is linear in these coefficients; the completed
quadratic current remains the open obligation.

Write `M_mu(N)=sum_{n≤N} mu(n)` and `H_mu(D)=sum_{d≤D} mu(d)/d`.
The exact finite identity

\[
 \sum_{d\le D}\mu(d)\lfloor DQ/d\rfloor
 +\sum_{q\le Q}M_\mu(\lfloor DQ/q\rfloor)
 =1+Q M_\mu(D),\qquad D,Q>0,
\]

is proved by the actual finite Möbius convolution and a bijective
hyperbola regrouping, in
[moebiusFinitePrefix_hyperbola_identity](../RiemannGaussian/MoebiusFiniteHyperbola.lean).
Retaining the signed remainder `sum_{d≤D} mu(d)*((DQ) mod d)/d`, whose
absolute value is at most `D`, gives

\[
 |H_\mu(D)|\le 2/Q+\delta(2+\log Q)
 \quad\text{if }|M_\mu(n)|\le\delta n\text{ for every }n\ge D.
\]

This intermediate premise is discharged by the previous quantitative
unsmoothed estimate: with `A(h)=10^15 h^3`, for all sufficiently large
`h` and `D≥exp(2A(h))`, every `n≥D` satisfies
`abs(M_mu(n))≤(C_mu+1)*exp(−h/2)*n`.
Choose `Q=ceil(exp(h/8))`. The complete quotient and rounding costs yield

\[
 |H_\mu(D)|\le C_H e^{-h/8},\qquad C_H=6+4C_\mu.
\]

[exists_moebiusHarmonicPrefix_cubic_rate](../RiemannGaussian/MoebiusHarmonicCancellation.lean)
has one common scale threshold, proved to exist. No numerical starting
cutoff is asserted.
[moebiusHarmonicPrefix_tendsto_zero](../RiemannGaussian/MoebiusHarmonicCancellation.lean)
proves the limit of the ordered finite prefixes. It does not assert
unordered or absolute convergence of the harmonic Möbius series.

For the actual region

\[
 S_{M,D}=\{(e,d):e,d\ge1,\ ed\le M,\ d\le D\},
 \qquad c_D(n)=\sum_{(e,d)\in S_{M,D},\ ed=n}\mu(d),
\]

[pairedEtaCompletedMomentInverseInnerCap_eq_atoms](../RiemannGaussian/EtaInverseHarmonicCoefficients.lean)
retains the unmodified completed moments, complex weights, translated
centers, and integer divided cutoffs in the original inverse. Before
taking an absolute value, the entire signed coefficient sum obeys

\[
 \sum_{n\le M}c_D(n)
 =\sum_{d\le D}\mu(d)\lfloor M/d\rfloor
 =M H_\mu(D)-\sum_{d\le D}\mu(d)\frac{M\bmod d}{d}.
\]

The exact floor contribution has absolute value at most `D`. Therefore,
for every `M` and every inner cutoff `D≥exp(2A(h))`,

\[
 \left|\sum_{n\le M}c_D(n)\right|\le C_H e^{-h/8}M+D.
\]

This supplies cancellation across the complete two-divisor coefficient
region, including its curved boundary. Its relative remainder is `D/M`,
so the estimate is useful when the inner cutoff is large but small
relative to the physical cutoff. It does not control the absolute mass
`sum |c_D(n)|`, products of two coefficients, or the same sum against the
original varying completed eta atoms. In particular, multiplying two
Möbius factors on a diagonal replaces the sign by its square; the linear
cancellation cannot simply be inserted into that quadratic sum.

No improved zero strip, fixed power saving for the original return,
or uniform weighted current bound follows from this slice. Novelty
priority for these auxiliary results has not been established.

## Checked finite eta phase bounds on the surviving cutoff power

**Terminal original-current theorem:**
[pairedEtaLeadingCurrent_firstMoment_le_finitePhase](../RiemannGaussian/EtaCurrentFinitePhasePower.lean).
The same module proves the corresponding statements for the literal
linear-width Gaussian return and the full signed inverse energy. These
are unconditional theorems for actual nontrivial zeros, every finite eta
cutoff, and every physical current cutoff. Both analytic multiplicity
branches and their original completion constants are retained.

The preceding Möbius estimates improve a coefficient on a positive power
scale. This slice instead constrains the horizontal displacement that
is the original current's sharp exponent. Write

\[
 F(s)=\frac{\eta(s)}s
     =\int_{\text{actual eta support}}e^{-st}\,dt,
 \quad \rho=\beta+i\gamma,
 \quad a_\beta=\frac{2\beta-1}{\beta}.
\]

For `beta>1/2`, retain the full real projection residual

\[
 r_\beta(t)=e^{-t/2}-a_\beta e^{-(\beta-1/2)t}.
\]

[integral_etaPhaseProjectionResidual_sq](../RiemannGaussian/EtaPhaseProjectionKernel.lean)
proves the exact integral, including its cross term and all three decay
rates:

\[
 \int_0^\infty r_\beta(t)^2\,dt
 =1-\frac{2a_\beta}{\beta}
      +\frac{a_\beta^2}{2\beta-1}
 =\left(\frac{1-\beta}{\beta}\right)^2.
\]

Every integrability premise is discharged. Restriction of this
nonnegative square to the literal eta measure preserves the bound.
Before taking any norm,
[pairedEtaPhaseProjectionKernel_eq_phase](../RiemannGaussian/EtaPhaseProjectionBound.lean)
and `integral_pairedEtaPhaseProjectionKernel` preserve the exact complex
identity

\[
 e^{-(1+i\gamma)t}-a_\beta e^{-(\beta+i\gamma)t}
 =e^{-i\gamma t}e^{-t/2}r_\beta(t),
 \qquad
 \int_{\rm eta}(\cdots)=F(1+i\gamma)-a_\beta F(\rho).
\]

The actual zero annihilates `F(rho)`. Cauchy--Schwarz and the proved
base square mass at most one therefore give
[norm_pairedEtaPhaseBoundaryValue_le_zero_ratio](../RiemannGaussian/EtaPhaseProjectionBound.lean):

\[
 q(\gamma):=|F(1+i\gamma)|\le\frac{1-\beta}{\beta}
 \quad(\beta>1/2).
\]

With `delta=q/(1+q)`, the right edge bound is immediate in this half
strip and follows from `delta≤1/2` in the other half. Completion
reflection sends an actual zero to `1-conj(rho)` at the same ordinate,
so
[nontrivialZetaZero_mem_etaPhaseProjection_strip](../RiemannGaussian/EtaPhaseProjectionMargin.lean)
proves `delta(gamma)≤beta≤1-delta(gamma)` for every actual zero.

For the original paired prefix `eta_N`, with exactly `2N` terms, set

\[
 P_N(y)=\frac{\eta_N(1+iy)}{1+iy},\qquad
 \varepsilon_N=\frac1{2N+1},\qquad
 q_N(y)=\max(0,|P_N(y)|-\varepsilon_N),\qquad
 \delta_N(y)=\frac{q_N(y)}{1+q_N(y)}.
\]

[norm_pairedEtaPhaseBoundaryValue_sub_finite_le](../RiemannGaussian/EtaFinitePhaseMargin.lean)
proves `|F(1+iy)-P_N(y)|≤epsilon_N` at every `N,y`. This is the
original full paired-eta tail estimate, divided by the same nonzero
complex spectral parameter. In particular,

\[
 0\le q_N\le q,\qquad q-q_N\le2\varepsilon_N,
 \qquad0\le\delta-\delta_N\le2\varepsilon_N.
\]

Thus
[nontrivialZetaZero_mem_etaFinitePhase_strip](../RiemannGaussian/EtaFinitePhaseMargin.lean)
is a literal finite arithmetic zero-location bound with no assumed
approximation, convergence, or numerical tail certificate.

Combine it with the preceding multiplicity-sensitive prime margin:

\[
 p_{\rm old}(m,y)=1-2\Delta_{\rm prime}(m,y),\qquad
 \kappa_{m,N}(y)=\min\left(p_{\rm old}(m,y),
                  \frac{1-q_N(y)}{1+q_N(y)}\right).
\]

[pairedEtaCurrentHorizontalDisplacement_le_finitePhase](../RiemannGaussian/EtaCurrentFinitePhasePower.lean)
proves `|2 beta-1|≤kappa_{m,N}(gamma)`, where `m` is the actual
analytic multiplicity. The minimum never increases the previous exponent.
The original current consequently obeys

\[
 \sum_{n<K}(2n+1)|J_\rho(n)|
 \le C_\rho(K+1)^{\kappa_{m,N}(\gamma)}
 \quad\text{for every }N,K.
\]

The actual Gaussian return has the same constant and exponent. For
`E_rho`, the full signed inverse energy, the constant is the same
`C_rho` plus the original summable zero-energy transport budget.
`etaFinitePhaseCurrentExponent_bounds` also proves the combined exponent
is below one. No current, physical cutoff, weight, or multiplicity has
been replaced by an auxiliary model.

**Proved limitation of this particular bound.** The boundary norm is
at most its zero-frequency value. The exact first prefix
`P_1(0)=1/2` and its tail at most `1/3` give `q(y)≤5/6` for all
ordinates. Since `p_old≥7/8`,
[one_eleventh_le_etaFinitePhaseCurrentExponent](../RiemannGaussian/EtaCurrentFinitePhasePower.lean)
proves

\[
 \kappa_{m,N}(\gamma)\ge\frac1{11}
 \quad\text{for every actual zero and every }N.
\]

This is a lower bound on the **available upper-bound exponent**, not
on `|2 beta-1|` and not on any actual current's growth. It shows that
simply increasing this one finite prefix cannot remove the positive
power. The finite approximation converges to a fixed boundary value,
not to a value that forces `beta=1/2`. No strict improvement at a
specified numerical ordinate or height window is certified here, and
no zero-count proportion or RH proof follows.

The Hilbert projection mechanism is classical in character. Burnol's
[quantitative Nyman--Beurling projection work](https://arxiv.org/abs/math/9910055)
is relevant prior context. The
[generalized polynomial approximation work of Alouges, Darses, and Hillion](https://arxiv.org/abs/2006.02953)
also separates approximation from the remaining coefficient/Gram
control. Neither supplies the missing unconditional estimate here.
This slice adds the explicit actual eta projection, finite tail transport,
and both-branch original-current exponent theorem to this repository;
novelty priority is not claimed.

## Checked compact-target eta translates and the full finite Gram budget

The preceding single-phase bound has a proved `1/11` exponent floor.
This slice develops a different, finite-family estimate on the actual
eta indicator, including its full complex transform, all mixed overlap
terms, and the complete coefficient-dependent infinite tail.

**Target choice and actual zero identity.** Write `L=log 2`,
`chi=pairedEtaLogIndicator`, and `F(s)=eta(s)/s`. For any finite family
of nonnegative real translates `a_j` and arbitrary complex coefficients
`c_j`, set

\[
 U_{a,c}(t)=\sum_j c_j\chi(t-a_j),\qquad
 h(t)=e^t\mathbf1_{(0,L]}(t),\qquad R_{a,c}=h-U_{a,c}.
\]

[integral_pairedEtaTranslatedCombination](../RiemannGaussian/EtaTranslatedLaplace.lean)
proves the complete complex identity

\[
 \int_{\mathbb R}U_{a,c}(t)e^{-st}\,dt
 =F(s)\sum_j c_je^{-sa_j},\qquad\Re s>0.
\]

Every actual nontrivial zero therefore annihilates the full combination.
Nonnegative translates keep the entire residual supported on positive
time. All relevant Laplace and critical-square integrability is proved.

A plain exponential target would fail at the additional zeros of the
eta factor `1-2^(1-s)`. The chosen target has the actual integral transform

\[
 H(s)=\int_0^L e^{(1-s)t}\,dt
 =\frac{1-2^{1-s}}{s-1}\quad(s\ne1).
\]

The definition is the integral, including at the removable point `s=1`.
[pairedEtaProjectionHeadTransform_eq_zero_of_factor](../RiemannGaussian/EtaProjectionHeadTarget.lean)
retains the shared nonremovable factor zeros, while
[pairedEtaProjectionHeadTransform_ne_zero](../RiemannGaussian/EtaProjectionHeadTarget.lean)
proves `H(rho)≠0` at every actual nontrivial zeta zero. The complete
critical square mass of `h` is exactly one. This target removes the
specific elementary-factor mismatch; no density theorem or absence of
other approximation obstructions is asserted.

Define the unchanged complete energy

\[
 E(a,c)=\int_0^\infty e^{-t}|R_{a,c}(t)|^2\,dt.
\]

[integral_Ioi_pairedEtaTranslatedResidual_mul_exp_zero](../RiemannGaussian/EtaTranslatedResidual.lean)
recovers exactly `H(rho)` from the residual at an actual zero. The proved
Cauchy--Schwarz estimate
[two_mul_re_sub_one_mul_head_norm_sq_le_residual](../RiemannGaussian/EtaTranslatedProjectionBound.lean)
then gives

\[
 (2\beta-1)|H(\rho)|^2\le E(a,c),\qquad\beta=\Re\rho>1/2.
\]

**Exact finite arithmetic and every omitted tail term.** For `N≥1`, put
`T_N=log(2N+1)`. Throughout `t≤T_N`,
[pairedEtaTranslatedColour_eq_prefix](../RiemannGaussian/EtaTranslatedFiniteIntervals.lean)
identifies every full translated colour with its first `N` original
intervals

\[
 I_{a,n}=(a+\log(2n+1),a+\log(2n+2)].
\]

For arbitrary endpoints, the exact exponential interval mass is
`M(l,u)=max(0,exp(-l)-exp(-u))`, including empty intervals. Define

\[
 G_{N,T}(a,b)=\sum_{n,m<N}
 M\!\left(\max(0,a+\log(2n+1),b+\log(2m+1)),
          \min(T,a+\log(2n+2),b+\log(2m+2))\right).
\]

[integral_pairedEtaTranslatedColour_product_eq_finiteGram](../RiemannGaussian/EtaTranslatedFiniteGram.lean)
proves that this is the literal cutoff Gram integral. Its full complex
quadratic form is retained before taking real parts. The target pairing
is also evaluated exactly:

\[
 b(a)=\max(0,L-a),\qquad
 \int_0^T e^{-t}h(t)\overline{U_{a,c}(t)}\,dt
 =\sum_j\overline{c_j}b(a_j),\qquad T\ge L.
\]

For `L≤T≤T_N`,
[pairedEtaTranslatedResidualEnergyCutoff_eq_finiteForm](../RiemannGaussian/EtaTranslatedFiniteResidual.lean)
proves the full finite residual identity

\[
 E_T(a,c)=Q_{N,T}(a,c)
 :=1+\sum_{j,k}\Re(c_j\overline{c_k})G_{N,T}(a_j,a_k)
       -2\sum_j\Re(c_j)b(a_j).
\]

This form is nonnegative because it equals the actual energy; no
independent matrix positivity assumption is introduced. Beyond the
compact target, `R=-U`, so the complete omitted tail is bounded by
`exp(-T)(sum_j |c_j|)^2`. Consequently
[pairedEtaTranslatedResidualEnergy_le_finiteBudget](../RiemannGaussian/EtaTranslatedFiniteResidual.lean)
proves, for every finite family and `N≥1`,

\[
 E(a,c)\le B_N(a,c)
 :=Q_{N,T_N}(a,c)+\frac{(\sum_j|c_j|)^2}{2N+1}.
\]

Every term on the right is finite elementary arithmetic in the original
translated interval endpoints and coefficients. It is an upper bound for
the complete energy, not just a finite-window approximation. The richer
exact residual and cutoff-plus-tail identities remain available.

**Return to the original current.** Let `rho*=1-conj(rho)` and put

\[
 W_\rho=\min(|H(\rho)|^2,|H(\rho^*)|^2)>0.
\]

[pairedEtaCurrentHorizontalDisplacement_le_translatedFiniteBudget](../RiemannGaussian/EtaCurrentTranslatedProjectionPower.lean)
uses the reflected actual zero to prove

\[
 |2\beta-1|\le\frac{B_N(a,c)}{W_\rho}.
\]

With the preceding phase/prime exponent `kappa_{m,N}(gamma)`, define

\[
 p_{\rho,N,a,c}=\min\left(\kappa_{m,N}(\gamma),
                         B_N(a,c)/W_\rho\right).
\]

The new exponent is proved nonnegative and below one, and never exceeds
the preceding exponent. The terminal theorem
[pairedEtaLeadingCurrent_firstMoment_le_translatedProjection](../RiemannGaussian/EtaCurrentTranslatedProjectionPower.lean)
proves

\[
 \sum_{n<K}(2n+1)|J_\rho(n)|
 \le C_\rho(K+1)^{p_{\rho,N,a,c}}
 \quad\text{for every }K,
\]

for both original multiplicity branches. The literal linear-width
Gaussian return has the same constant and exponent. The full signed
inverse energy retains the same exponent and adds its existing summable
zero-energy error to the constant. No current or weighted cutoff is
replaced by the auxiliary residual.

**Precise remaining estimate.** No coefficient family making `B_N` tend
to zero is constructed. The positive normalization `W_rho` depends on the
actual zero coordinates, so this theorem is not yet a new numerical
ordinate-only zero strip. The old single-phase `1/11` floor is not proved
for this larger family; neither is a family overcoming it. A useful
construction must control the full residual and coefficient growth
together. Finite-interval approximation alone, with an uncontrolled
`(sum |c_j|)^2/(2N+1)` tail cost, cannot establish the target. Nonnegative
real translates are allowed; no restriction to integer dilation factors
is imposed. The uniform weighted arithmetic bound and RH remain open.

The approximation mechanism has substantial prior context in
[Báez-Duarte's generalized Nyman--Beurling criterion](https://arxiv.org/abs/math/0505453).
[Alouges, Darses, and Hillion](https://www.numdam.org/articles/10.5802/jtnb.1227/)
explicitly distinguish approximation from the coefficient/Gram control
that remains difficult. Neither paper supplies the missing unconditional
coefficient estimate here. This slice proves the stated actual eta
identities and transports their full finite budget to the existing
current; novelty priority is not claimed.

## Checked exact coefficient laws and the four-translate residual bound

The next slice constructs mathematically specified coefficients for the
actual eta translates, and proves a concrete complete approximation bound.
Numerical experiments guided the choice of grid and a small rational trial
vector. The coefficients and theorems below are independent of floating-point
output. No convergence theorem for the growing family is asserted.

**Exact coefficient rule.** For any nonnegative translates `a_j`, let
`G=G_(N,T_N)` be the real matrix of all actual overlap integrals, and let
`b_j=max(0,log 2-a_j)`. In dimension `d`, define

\[
 \lambda=\frac{d+1}{2N+1},\qquad A=G+\lambda I,\qquad
 c_*=A^{-1}b,\qquad \mathcal D=1-b^Tc_*.
\]

[EtaCanonicalTranslateMatrix.lean](../RiemannGaussian/EtaCanonicalTranslateMatrix.lean)
identifies the quadratic form of `G` with the actual weighted square
integral, proves `G` positive semidefinite, and proves `A` positive definite.
Thus the inverse and normal equation `Ac_*=b` are justified for every
finite nonnegative translate family, without an independence hypothesis.
The positive regularization also handles the empty family.

For real coefficients `c`, the regularized objective is

\[
 \mathcal Q(c)=1+c^TAc-2b^Tc
             =E_{T_N}(a,c)+\lambda\sum_j c_j^2.
\]

The dimension-dependent square penalty pays for the whole infinite tail:

\[
 \frac{(\sum_j|c_j|)^2}{2N+1}
 \le\lambda\sum_jc_j^2.
\]

All mixed entries remain in `G`; the original complex translated carrier
and its exact tail decomposition remain available upstream.
[pairedEtaTranslateRidgeObjective_eq_canonical_add_square](../RiemannGaussian/EtaCanonicalTranslateBound.lean)
proves the exact identity

\[
 \mathcal Q(c)=\mathcal D+(c-c_*)^TA(c-c_*).
\]

Consequently the canonical rule minimizes this regularized objective.
For `N≥1`, the checked bounds give

\[
 0\le E(a,c_*)\le B_N(a,c_*)\le\mathcal D\le1,
 \qquad \mathcal D\le\mathcal Q(c)\quad\text{for every real trial vector }c.
\]

The last inequality is
[pairedEtaCanonicalTranslateBudget_le_trial](../RiemannGaussian/EtaCanonicalTranslateBound.lean).
It is the intended route from arithmetic trial coefficients to a bound
for the exact canonical rule. The unresolved estimate is now explicit:
control both the trial residual and the square penalty along a growing
family. Existence of the inverse or its minimizing property alone does
not imply that its deficit vanishes.

**A fully specified growing family.**
[EtaCanonicalTranslateFamily.lean](../RiemannGaussian/EtaCanonicalTranslateFamily.lean)
fixes every parameter by

\[
 d_k=2^k,\quad N_k=4d_k^2,\quad
 r_{k,j}=\frac{j+1}{d_k},\quad a_{k,j}=-\log r_{k,j},
 \quad 0\le j<d_k.
\]

The coefficients use the same formula `c_k=(G_k+lambda_k I)^(-1)b_k`
at every stage. In particular, neither an optimizer output nor a choice
of a favorable subsequence enters their definition. Lean proves
`0≤D_k≤1`, full residual `E_k≤D_k`, and, for every actual zero,

\[
 |2\Re\rho-1|W_\rho\le\mathcal D_k.
\]

The terminal theorem
[pairedEtaLeadingCurrent_firstMoment_le_dyadicTranslate](../RiemannGaussian/EtaCanonicalTranslateFamily.lean)
therefore proves, for both original multiplicity branches and every `K`,

\[
 S_\rho(K)\le C_\rho(K+1)^{p_{\rho,k}},\qquad
 p_{\rho,k}=\min\bigl(\kappa_{m,N_k}(\Im\rho),\mathcal D_k/W_\rho\bigr).
\]

The literal Gaussian return and full signed inverse energy inherit the
same exponent and their existing finite transport budgets. `W_rho` is
the original strictly positive reflected target weight; it still depends
on the actual zero coordinates.

**An exact four-coefficient bound.** At `N=64`, choose

\[
 r=(1/4,1/2,3/4,1),\qquad c=(-1/2,-1/2,1/2,1).
\]

The resulting actual function is

\[
 U(t)=\chi(t)+\tfrac12\chi(t-\log(4/3))
       -\tfrac12\chi(t-\log2)-\tfrac12\chi(t-\log4).
\]

[EtaRationalTranslateGram.lean](../RiemannGaussian/EtaRationalTranslateGram.lean)
proves that positive rational physical scales give an exact rational
formula for every Gram entry. With `R_N` denoting the quadratic Gram term
plus the entire coefficient tail, the full budget is

\[
 B_N=1+R_N-2\sum_jc_j\max(0,\log(2r_j)).
\]

[pairedEtaFourProjection_rationalQuadraticBudget_lt](../RiemannGaussian/EtaFourTranslateProjection.lean)
checks `R_64<99/100` by Lean kernel reduction of ten separate exact Gram
entries and symmetry. The entries are checked serially to keep the
calculation within CI memory; the final rational inequality is assembled
from those proofs. The exact target pairing
is `(log 2+log 3)/2`. Rigorous logarithm bounds then give
[pairedEtaFourProjection_finiteBudget_lt_one_fifth](../RiemannGaussian/EtaFourTranslateBound.lean)
and `pairedEtaFourProjection_residualEnergy_lt_one_fifth`:

\[
 E(a,c)\le B_{64}(a,c)<1/5.
\]

Thus every actual zero satisfies `|2 Re rho-1| W_rho<1/5`. This is a
normalized coordinate constraint, not a certified improvement of an
ordinate-only zero strip. The rational check uses no compiler-trusting
decision procedure and imports no numerical result.

The dyadic stage `k=2` has exactly this four-point grid. Its trial square
penalty exceeds the preceding tail allowance by exactly `5/258`, so
comparison gives

\[
 \mathcal D_2\le B_{64}(a,c)+5/258<1/4.
\]

This is
[pairedEtaDyadicTranslateDeficit_two_lt_one_quarter](../RiemannGaussian/EtaCanonicalTranslateFamily.lean).
It is a finite-stage anchor for the exact family, not an asymptotic rate.

**Exploratory comparison, not Lean-certified numerical bounds.**
[search_eta_translate_coefficients.py](../scripts/search_eta_translate_coefficients.py)
evaluates the full finite interval formulas in floating point and compares
the exact canonical law with free numerical optimization of `B_N`.
The tested uniform physical grids gave:

| Dimension `d` | Cutoff `N` | Canonical deficit `D` | Canonical full budget `B` | Canonical tail allowance | Freely optimized `B` |
| --- | --- | --- | --- | --- | --- |
| 4 | 64 | 0.20302740 | 0.18835512 | 0.03844739 | 0.18787523 |
| 16 | 1024 | 0.08321057 | 0.07920480 | 0.00479720 | 0.07901803 |
| 64 | 16384 | 0.05432276 | 0.05291250 | 0.00065742 | 0.05284615 |

Reproduce with NumPy and SciPy (tested versions `2.2.6` and `1.15.3`):

```bash
python scripts/search_eta_translate_coefficients.py --dimensions 4 16 64 \
  --solvers canonical free --output /tmp/eta-coefficients.json
```

The output retains all coefficients, finite residuals, full tail
allowances, and numerical diagnostics. The interval formulas were also
compared with direct pairwise interval intersection on small grids.
The observed agreement supports investigating the exact rule, but proves
neither monotonicity nor convergence. It also shows why checking the
residual alone is insufficient: the regularization and tail costs must
be tracked separately.

One proposed source of structured trials is the desired transform
multiplier `H(s)/F(s)=s/((s-1) zeta(s))` on `Re s>1`, which suggests a
Möbius inversion followed by a continuous integration term. Turning that
suggestion into actual finite trial vectors and proving their full
critical residual and coefficient estimates remains work to do. The
existing harmonic Möbius cancellation does not itself provide the required
power-strength bound. No novelty priority claim is made for the general
regularized projection method.

## Checked balanced Möbius candidates: vanishing penalty and actual infinite tail

This slice defines an arithmetic coefficient family on the unchanged
dyadic eta grids and discharges its complete coefficient and tail costs.
It does **not** prove that the canonical family's deficit tends to zero.
The new open term is an explicitly defined actual growing finite residual,
rather than an omitted coefficient or infinite-tail assumption.

**Exact signed atoms and harmonic correction.** For integers `n≥1`, set

\[
 u_n(x)=\mathbf1_{[n,\infty)}(x),\qquad
 v_n(x)=\mathbf1_{[1,\infty)}(x)\frac{\min(x,n)}n,
 \qquad \psi_n(x)=u_n(x)-v_n(x).
\]

[EtaMoebiusTrialAtoms.lean](../RiemannGaussian/EtaMoebiusTrialAtoms.lean)
retains these two monotone channels separately, proves both are between
zero and one, and bounds the entire sampled variation of their signed
difference by two. The sampling coordinates are the original
`x_j=d/(j+1)`. No arithmetic cancellation hypothesis enters that bound.

For weights `w(n)`, define

\[
 A_{M,w}(x)=\sum_{1\le n\le M}\mu(n)w(n)\psi_n(x),\qquad
 c_{d,M,w,j}=A_{M,w}\!\left(\frac d{j+1}\right)
             -A_{M,w}\!\left(\frac d{j+2}\right),\quad 0\le j<d.
\]

The exact signed harmonic identity is

\[
 A_{M,w}(x)=x\left(
   \sum_{\substack{1\le n\le M\\n\le x}}\frac{\mu(n)w(n)}n
   -\sum_{1\le n\le M}\frac{\mu(n)w(n)}n\right)\quad(x\ge1).
\]

This is
[pairedEtaMoebiusTrialPrimitive_eq_harmonic_difference](../RiemannGaussian/EtaMoebiusTrialCoefficients.lean).
The complete endpoint correction is part of the definition. The primitive
vanishes below one and at or beyond `M`, so `M≤d` gives exact telescoping
`sum_j c_(d,M,w,j)=0`. The coefficient remains a signed sum of the two
atom-channel differences. Only its downstream bound takes absolute values:

\[
 |w(n)|\le1\ (1\le n\le M)quad\Longrightarrow\quad
 \sum_j|c_{d,M,w,j}|\le2M,\qquad \sum_jc_{d,M,w,j}^2\le4M^2.
\]

These are
`pairedEtaMoebiusTrialCoefficient_sum_abs_le` and
`pairedEtaMoebiusTrialCoefficient_sum_sq_le`. Both bounds are independent
of the grid dimension. The finite primitive motivates an arithmetic
approximation to the desired transform multiplier; this slice does not
assert an exact identity between the gridded translate polynomial and a
continuous inverse-transform formula.

**The specified stage law.** Keep
`d_k=2^k`, `N_k=4d_k²`, and `a_(k,j)=-log((j+1)/d_k)`. Choose

\[
 M_k=k+1,\qquad
 w_M(n)=
 \begin{cases}1-\log(n)/\log(M),&M>1,\\0,&M\le1,\end{cases}
 \qquad c_{k,j}=c_{d_k,M_k,w_{M_k},j}.
\]

Lean proves `M_k≤d_k` and `0≤w_M(n)≤1` on every active arithmetic
index, with the singular unit cutoff handled explicitly. Every coefficient
is thus mathematically defined; numerical optimization is not used to
choose it. The bounds above give zero total mass and
`sum_j abs(c_(k,j))≤2(k+1)` at every stage.

**The complete coefficient cost tends to zero.** Use the unchanged
regularization `lambda_k=(d_k+1)/(2N_k+1)` and define

\[
 P_k=\lambda_k\sum_jc_{k,j}^2,\qquad L_k=\frac{(k+1)^2}{2^k}.
\]

[EtaMoebiusTrialPenalty.lean](../RiemannGaussian/EtaMoebiusTrialPenalty.lean)
proves `lambda_k≤1/(4d_k)`, and hence

\[
 0\le P_k\le L_k\longrightarrow0.
\]

Both limits are compiled theorems:
`pairedEtaDyadicMoebiusTrialAllowance_tendsto_zero` and
`pairedEtaDyadicMoebiusTrialPenalty_tendsto_zero`. The result is
unconditional for this exact growing family. It does not use a bound for
its approximation residual.

**Actual finite and infinite residuals.** Let `T_k=log(2N_k+1)` and retain
the original actual indicator `chi` and compact target `h`. Write

\[
 R_k(t)=h(t)-\sum_jc_{k,j}\chi(t-a_{k,j}),\quad
 E_k=\int_{(0,T_k]}e^{-t}|R_k(t)|^2\,dt,\quad
 \tau_k=\int_{(T_k,\infty)}e^{-t}|R_k(t)|^2\,dt.
\]

[EtaMoebiusTrialResidual.lean](../RiemannGaussian/EtaMoebiusTrialResidual.lean)
defines these actual integrals and proves the full accounting:

\[
 \mathcal Q_k(c_k)=E_k+P_k,\qquad
 \mathcal D_k\le E_k+P_k\le E_k+L_k,
\]
\[
 0\le\tau_k\le
 \frac{(\sum_j|c_{k,j}|)^2}{2N_k+1}\le P_k\longrightarrow0,
 \qquad E(c_k)=E_k+\tau_k\le E_k+L_k.
\]

The terminal actual-tail theorem is
`pairedEtaDyadicMoebiusTrialResidualTail_tendsto_zero`. The original
canonical comparison remains unchanged, and the original actual zero
coordinates inherit

\[
 |2\Re\rho-1|W_\rho\le E_k+L_k
\]

through
`pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_moebius_cutoff_add_allowance`.
The full residual decomposition and the signed primitive identities remain
available alongside these inequalities.

**How the candidate is assessed.** A successful candidate would have a
proved bound `E_k+P_k≤f(k)` with `f(k)→0`; the exact comparison would then
give `D_k→0`. The present slice proves only the `P_k` and actual `tau_k`
limits. The remaining `E_k→0` statement concerns a growing interval.
Pointwise or fixed-window approximation does not justify moving that limit
through the full weighted square integral. In particular, existing harmonic
Möbius cancellation is not a proved dominating square-integral estimate.

The numerical explorer now evaluates exactly this stage law, retains the
finite residual and full coefficient costs separately, and compares with
the same-stage canonical minimizer. The following values are exploratory
floating-point evaluations, not Lean-certified bounds:

| Stage `k` | Dimension `d_k` | Arithmetic cutoff `M_k` | Finite residual `E_k` | Penalty `P_k` | Score `E_k+P_k` | Canonical deficit `D_k` |
| --- | --- | --- | --- | --- | --- | --- |
| 2 | 4 | 3 | 0.73077777 | 0.00381302 | 0.73459079 | 0.20302740 |
| 4 | 16 | 5 | 0.43058143 | 0.00399969 | 0.43458112 | 0.08321057 |
| 6 | 64 | 7 | 0.31266283 | 0.00166384 | 0.31432667 | 0.05432276 |
| 7 | 128 | 8 | 0.27642524 | 0.00097687 | 0.27740211 | 0.04749796 |

Reproduce with the same NumPy and SciPy versions used above:

```bash
python scripts/search_eta_translate_coefficients.py --dimensions 4 16 64 128 \
  --solvers moebius_log --output /tmp/eta-log-moebius.json
```

The output also evaluates the exact comparison identity numerically:
`Q(c)-D=(c-c_*)^T A(c-c_*)`. The observed error in this identity is below
`4e-16` in the listed cases. This is a consistency check, not a proof of
decay. These sizes suggest that residual error dominates the penalty and
that the specified logarithmic law leaves substantial room compared with
the minimizer. They prove neither convergence nor a positive limiting
floor for this candidate. Changing the taper or arithmetic cutoff must be
assessed with the full objective and must retain proved coefficient costs.

All four modules and the root pass strict direct elaboration and the full
warning-as-error build. The verbose root declaration audit and eighteen
terminal axiom checks use only `propext`, `Classical.choice`, and
`Quot.sound`. No numerical optimizer or floating-point constant enters a
Lean theorem. Mathematical priority for this combined candidate construction
is not claimed. This slice proves no sharper numerical zero strip and does
not close the original uniform weighted current bound.

## Checked full grid-refinement and target-residual stability

This slice controls the complete effect of refining the physical grid
while keeping the arithmetic cutoff and weights fixed. It combines the
existing eta support-mismatch theorem with exact signed Möbius coefficient
blocks. The result reaches the unchanged canonical deficit and actual
zero coordinates. It does **not** prove decay of the arithmetic residual
or of `D_k`.

**Complete translate distance, including the initial interval.** Define

\[
 I(a,b)=\int_0^\infty e^{-t}|\chi(t-a)-\chi(t-b)|^2\,dt.
\]

[EtaTranslateDifference.lean](../RiemannGaussian/EtaTranslateDifference.lean)
proves integrability and the exact identities

\[
 I(a,a+r)=e^{-a}I(0,r)\quad(a,r\ge0),
\]
\[
 I(0,r)=1-e^{-r}+e^{-r}\operatorname{Mismatch}(1/2,r)
 \quad(0\le r\le\log2).
\]

The first term is the actual initial support interval; the second is
the entire original arithmetic mismatch. Applying the existing checked
critical mismatch estimate gives

\[
 I(0,r)\le r\log(1/r)+6r\le8\sqrt r\quad(0<r\le1/8).
\]

Consequently `a,b≥0` and `|a-b|≤r≤1/8` give `I(a,b)≤8 sqrt(r)`.
There is no finite-time tail assumption in this modulus.

**Complex coefficients retained until weighted Cauchy--Schwarz.** For
two grids carrying the same coefficients, the exact difference remains

\[
 U_a(t)-U_b(t)=\sum_jc_j\bigl(\chi(t-a_j)-\chi(t-b_j)\bigr).
\]

[EtaTranslateGridError.lean](../RiemannGaussian/EtaTranslateGridError.lean)
proves the complete integral bound

\[
 \int_0^\infty e^{-t}|U_a-U_b|^2dt
 \le\left(\sum_j|c_j|\right)\sum_j|c_j|I(a_j,b_j)
 \le8\sqrt r\left(\sum_j|c_j|\right)^2.
\]

Only active coefficients need the shift bound. The estimate depends on
their complete absolute sum, rather than the dimension. The signed
pointwise identity and every original pair distance remain available
before this norm estimate.

**Exact refinement of the original arithmetic coefficients.** Using the
unchanged signed primitive `A_(M,w)`, index a coefficient by its physical
denominator:

\[
 C_{d,M,w}(m)=A_{M,w}(d/m)-A_{M,w}(d/(m+1)),\qquad m\ge1.
\]

On `1≤m≤d` these are precisely the original coefficients. They vanish
when `M(m+1)≤d` and when `m>d`. For every positive integer refinement
factor `q`, the entire signed block identity is

\[
 \sum_{0\le l<q} C_{dq,M,w}\bigl(q(j+1)+l\bigr)
 =C_{d,M,w}(j+1).
\]

[EtaMoebiusTrialGridBlocks.lean](../RiemannGaussian/EtaMoebiusTrialGridBlocks.lean)
also proves all reindexing boundary terms zero when `M≤d`. Therefore
regrouping preserves the whole original coarse and fine combinations,
and the reindexed fine coefficients still have absolute sum at most `2M`
for `|w(n)|≤1` on `1≤n≤M`.

An active fine coefficient satisfies `d<M(j+2)` in its coarse cell.
[EtaMoebiusTrialGridGeometry.lean](../RiemannGaussian/EtaMoebiusTrialGridGeometry.lean)
uses this exact support fact to prove

\[
 \left|\log\frac d{j+1}
 -\log\frac{dq}{q(j+1)+l}\right|\le\frac{2M}{d}.
\]

The nonnegative extension of logarithmic grid points outside the valid
index range affects only coefficients already proved zero. On every
original grid index it is exactly `-log(m/d)`.

**Full refinement error, uniform in the refinement factor.** Write
`U_(d,M,w)` for the actual finite eta combination. With `d≥1`,
`1≤q`, `M≤d`, bounded weights, and `2M/d≤1/8`,
[pairedEtaMoebiusTrialRefinementError_le](../RiemannGaussian/EtaMoebiusTrialRefinement.lean)
proves

\[
 \int_0^\infty e^{-t}|U_{d,M,w}(t)-U_{dq,M,w}(t)|^2dt
 \le32M^2\sqrt{2M/d}.
\]

All hypotheses are discharged for the original stage parameters
`M_k=k+1`, `d_k=2^k`, and exact logarithmic weights once `k≥7`.
The refinement factor is arbitrary. Lean indexes it by `q+1`, so every
natural index specifies a positive integer refinement without a further
premise. The resulting allowance is

\[
 G_k=32\sqrt{\frac{2(k+1)^5}{2^k}}\longrightarrow0.
\]

[pairedEtaDyadicMoebiusTrialRefinementError_tendsto_zero](../RiemannGaussian/EtaMoebiusTrialRefinementLimit.lean)
proves convergence of the actual entire square-error integral for every
refinement schedule. The arithmetic cutoff remains `k+1` on both grids;
the fine grid is not silently assigned a later stage's arithmetic weights.

**Stability of the complete target residual itself.** The original full
target residual energy is `E(d,M,w)=integral_0^infinity e^(-t)|h-U|²`.
[EtaTranslateResidualStability.lean](../RiemannGaussian/EtaTranslateResidualStability.lean)
first proves, for every positive `epsilon`, the same-coefficient bound

\[
 |E(a,c)-E(b,c)|
 \le\epsilon\left(2+\sum_j|c_j|\right)^2
 +(1+1/\epsilon)\int_0^\infty e^{-t}|U_a-U_b|^2dt.
\]

This uses weighted Young's inequality and genuine integrability of every
term. Taking `epsilon=M^(-3)` after the exact refinement identities gives
[abs_pairedEtaMoebiusTrialGridResidualEnergy_sub_le_explicit](../RiemannGaussian/EtaMoebiusTrialResidualRefinement.lean):

\[
 |E(d,M,w)-E(dq,M,w)|
 \le\frac{16}{M}+64\sqrt{\frac{2M^{11}}d}\quad(M\ge1).
\]

Thus at the original stages, uniformly in all positive integer refinements,

\[
 |E_k-E'_k|\le R_k:=\frac{16}{k+1}
       +64\sqrt{\frac{2(k+1)^{11}}{2^k}}\longrightarrow0.
\]

The actual limit is
[pairedEtaDyadicMoebiusResidual_sub_refined_tendsto_zero](../RiemannGaussian/EtaMoebiusRefinedBudget.lean).
It concerns the difference of the complete energies. It does not assert
that either energy has a limit or tends to zero.

**Back to the original deficit and zero coordinates.** Combine this with
the preceding coefficient allowance `L_k=(k+1)^2/2^k` and set
`A_k=R_k+L_k`. Lean proves `A_k→0` and, for every `k≥7` and refinement,

\[
 |2\Re\rho-1|W_\rho\le\mathcal D_k\le E'_k+A_k.
\]

These are `pairedEtaDyadicMoebiusRefinedAllowance_tendsto_zero`,
`pairedEtaDyadicTranslateDeficit_le_refined_moebius`, and
`pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_refined_moebius`.
The canonical definition, compact target, complete residual, and positive
zero weight are unchanged. The remaining estimate is the actual refined
arithmetic residual `E'_k→0`; the vanishing added costs do not prove it.

**Reproducible construction checks and the next analytic bridge.** The
numerical coefficient constructor accepts an explicit arithmetic cutoff
so refinement experiments preserve the same weights:

```python
from scripts.search_eta_translate_coefficients import moebius_log_coefficients
d, M, q = 16, 5, 3
coarse = moebius_log_coefficients(d, M)
fine = moebius_log_coefficients(d * q, M)
```

Finite construction checks covered 48 combinations of dimensions,
arithmetic cutoffs, and refinement factors. The tested block sums had
zero floating-point discrepancy; the sampled whole-combination identities
differed by at most `2.3e-16`. These checks validate the explorer's
implementation and are not Lean-certified numerical approximation bounds.
The default stage law and preceding numerical scores remain unchanged.

The full-grid estimates support investigating a continuous arithmetic
representation. An exact identification of that representation with the
Möbius primitive, and a possible von-Mangoldt shell formula for its
residual, are still analytic obligations. Neither a continuous-transform
identity nor a critical mean-square bound is imported from an informal
calculation. Fixed-window or pointwise convergence alone remains
insufficient for the complete residual. No sharper numerical zero strip,
uniform weighted current bound, or mathematical priority claim follows
from this slice.

All nine modules and the root pass strict direct elaboration and the
warning-as-error full build. Whole-project and verbose root declaration
lint pass; twenty-one terminal axiom audits use only the three permitted
standard axioms. The numerical constructor is outside the proof chain.

## Checked arithmetic residual decay on the entire target interval

The user's next instruction was to attack the refined arithmetic residual
itself. This slice proves unconditional decay of its genuine square
integral over the full compact target support. The exterior integral is
retained exactly and remains the open part. This is not a proof of decay
of the full residual or the canonical deficit.

### Signed logarithmic harmonic cancellation

For `M>1`, put

\[
 p_M=\sum_{n=1}^M\frac{\mu(n)}n
      \left(1-\frac{\log n}{\log M}\right),\qquad
 H_\mu(n)=\sum_{j=1}^n\frac{\mu(j)}j.
\]

`pairedEtaMoebiusLogHarmonic_eq_log_average` proves the exact discrete
Abel identity

\[
 p_M=\frac1{\log M}\sum_{n<M}H_\mu(n)
                    (\log(n+1)-\log n).
\]

The zero-index term vanishes because `H_mu(0)=0`; all positive-index
terms use ordinary real logarithms. The singular unit cutoff is handled
by the existing separate zero-weight branch, not by applying the formula
at `M=1`.

If `|H_mu(n)|≤epsilon` for every `n≥N`, then for `M≥N`, `M>1`, Lean
proves the full finite estimate

\[
 |p_M|\le\epsilon+\frac1{\log M}
     \sum_{n<N}|H_\mu(n)|(\log(n+1)-\log n).
\]

The finite initial sum is independent of `M`. Combining this with the
existing `moebiusHarmonicPrefix_tendsto_zero` gives
`pairedEtaMoebiusLogHarmonic_tendsto_zero`. Thus the endpoint correction
has an arithmetic proof of decay, without fitting numerical coefficients.
The original signed average is retained before the absolute estimate.

### Exact original head and its rounding error

Let `U_(d,M)` be the unchanged finite-grid combination with the exact
logarithmic weights. Set

\[
 y_d(t)=\frac d{\lfloor d/e^t\rfloor+1}.
\]

For `d>0`, `0<t≤log 2`, the exact eta endpoint convention selects the
coefficient tail with `floor(d/exp(t))≤j`. The complete sum telescopes:

\[
 U_{d,M}(t)=A_{M,w_M}(y_d(t))=y_d(t)(1-p_M),\qquad M>1.
\]

These are `pairedEtaMoebiusTrialGridCombination_eq_head_primitive` and
`pairedEtaMoebiusTrialGridCombination_eq_head`. Both boundary coefficients
and the original complex casts are retained. No continuous Möbius
candidate is substituted for the actual finite-grid combination.

`pairedEtaMoebiusTrialHeadCoordinate_bounds` and
`abs_exp_sub_pairedEtaMoebiusTrialHeadCoordinate_le` give

\[
 1\le y_d(t)<e^t,\qquad |e^t-y_d(t)|\le4/d.
\]

The signed identity `pairedEtaMoebiusTrialHeadResidual_eq` is

\[
 h(t)-U_{d,M}(t)=e^t p_M+(e^t-y_d(t))(1-p_M).
\]

Only after that identity is proved does the norm estimate give

\[
 \|h(t)-U_{d,M}(t)\|
 \le 2|p_M|+4|1-p_M|/d.
\]

Actual integrability is inherited from the unchanged residual. Integrating
over the whole target interval proves
`pairedEtaMoebiusTrialHeadResidualEnergy_le`:

\[
 E^{\rm head}_{d,M}:=
 \int_{(0,\log2]}e^{-t}|h(t)-U_{d,M}(t)|^2dt
 \le(2|p_M|+4|1-p_M|/d)^2.
\]

This bound deliberately uses the larger full exponential mass `1`; no
unproved endpoint or integral evaluation is needed.

### Uniform refined limit and exact remaining exterior

For the original arithmetic cutoff `M=k+1`, every positive integer
refinement has dimension `d=2^k(q_k+1)`. For `k≥1`, its head energy is
bounded by

\[
 B_k=\left(2|p_{k+1}|+\frac{4|1-p_{k+1}|}{2^k}\right)^2\to0.
\]

The compiled terminal theorem
`pairedEtaDyadicMoebiusRefinedHeadResidual_tendsto_zero` proves the limit
of the actual head integral for **every** schedule `q : Nat → Nat`.
It has no residual-decay premise. This is the displayed new milestone.

Define the entire unchanged exterior integral

\[
 X'_k(q)=\int_{\log2}^{\infty}e^{-t}|U_{2^k(q+1),k+1}(t)|^2dt.
\]

`pairedEtaDyadicMoebiusRefinedResidual_eq_head_add_exterior` proves

\[
 E'_k(q)=E^{\rm head}_{2^k(q+1),k+1}+X'_k(q).
\]

Consequently `E'_k(q_k)-X'_k(q_k)→0` is proved, while neither individual
zero limit is asserted. With the previous full refinement and coefficient
allowance `A_k→0`, the actual comparison is

\[
 |2\Re\rho-1|W_\rho\le D_k
 \le X'_k(q)+\underbrace{B_k+A_k}_{\to0},\qquad k\ge7.
\]

The terminal transport is
`pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_moebius_exterior`.
It bounds the original actual zero displacement, not a substituted model.

**Remaining mathematical obligation:** prove `X'_k(q_k)→0` for a specified
refinement schedule, with the full exterior range included. The known
far-tail bound beyond the original large eta cutoff does not control the
intermediate growing region. Pointwise cancellation, convergence on a
fixed compact interval, and this head estimate do not supply a bound on
that entire region. No sharper numerical zero strip or cutoff-independent
current bound is certified by this slice.

An exterior research lead is the signed logarithmic divisor identity
`sum_(d|n) mu(d)*(1-log(d)/log(M))=1_(n=1)+Lambda(n)/log(M)` when `n≤M`.
The corresponding prime-power and harmonic dyadic shell terms must stay
paired. A continuous arithmetic formula suggested by those terms has
**not** been identified with our refined carrier in Lean, and it is not
used in the checked head theorem. The similar logarithmic Dirichlet
polynomial studied by [Bettin, Conrey, and Farmer](https://arxiv.org/abs/1211.5191)
has an optimal mean-square asymptotic under RH and an additional
inverse-derivative moment assumption; that result cannot supply the
unconditional exterior bound required here.

## Checked complete exterior arithmetic and its infinite tail

The previous turn proved actual head-residual decay. The next slice retains
the entire exterior and identifies its original finite-grid combination in
explicit signed arithmetic. The result does not replace the exterior by
a fixed compact region, a continuum approximation, or a numerical model.

### Exact causal steps and paired arithmetic

For arbitrary arithmetic weights `w`, write `A_(M,w)` for the unchanged
balanced Möbius primitive. Its exact physical-grid coefficients satisfy

\[
 \sum_j c_{d,M,w,j}\,1_{\{a_{d,j}<v\}}
   =A_{M,w}\!\left(\frac d{\lfloor d/e^v\rfloor+1}\right).
\]

`pairedEtaMoebiusTrialGridStep_sum` proves this identity at every real
`v`, including nonpositive times, with no bounded-weight premise. All
initial and terminal coefficients are included. The preceding head theorem
is now a specialization of this actual causal-step identity; its statement
and proof of arithmetic head decay are preserved.

Each original eta interval is the difference of its two causal steps.
With `y_d(v)=d/(floor(d/exp(v))+1)`, define

\[
 F_{N,d,M,w}(t)=\sum_{n<N}\left[
  A_{M,w}(y_d(t-\log(2n+1)))
 -A_{M,w}(y_d(t-\log(2n+2)))\right].
\]

`pairedEtaMoebiusTrialGridCombination_eq_arithmeticPrefix` proves

\[
 U_{d,M,w}(t)=F_{N,d,M,w}(t),\qquad t\le\log(2N+1).
\]

This is equality of the original complex carrier with the real arithmetic
formula embedded in `Complex`. It keeps each odd/even endpoint, harmonic
correction, weight, and exact integer rounding before any norm or square.
The formula works for every `d`, `M`, and real weight function; alternative
coefficient laws can therefore use the same arithmetic interface.

### Complete exterior integral and quantitative omitted range

Let `L=log 2` and `T_N=log(2N+1)`. The actual combination has an integrable
critical square on every upper half-line. Its equality with `F` proves
genuine integrability of `exp(-t)*F(t)^2` on the complete finite exterior
window. For `N≥1`,
`pairedEtaMoebiusTrialExteriorEnergy_eq_arithmetic_add_tail` gives

\[
 \int_L^\infty e^{-t}|U_{d,M,w}(t)|^2dt
  =\int_L^{T_N}e^{-t}F_{N,d,M,w}(t)^2dt
   +\int_{T_N}^\infty e^{-t}|U_{d,M,w}(t)|^2dt.
\]

The last term is the actual entire integral, not a replaced allowance.
For `|w(n)|≤1` on `1≤n≤M`, the complete coefficient mass bound gives

\[
 \int_{T_N}^\infty e^{-t}|U_{d,M,w}(t)|^2dt
 \le\frac{4M^2}{2N+1}.
\]

The estimate is independent of `d` and includes every infinite eta band.
For the original logarithmic family, let

\[
 d'_{k,q}=2^k(q+1),\quad M_k=k+1,\quad N_k=4(2^k)^2,
\]

and let `V_k(q)` be the actual growing arithmetic square integral of `F`
on `(log 2,T_(N_k)]`. The existing exterior `X'_k(q)` satisfies

\[
 X'_k(q)=V_k(q)+\tau'_k(q),\qquad
 0\le\tau'_k(q)\le L^{\rm far}_k:=(k+1)^2/4^k\to0.
\]

`pairedEtaDyadicMoebiusRefinedExteriorEnergy_eq_arithmetic_add_tail`
retains the exact equality. The actual entire tail limit is
`pairedEtaDyadicMoebiusRefinedArithmeticTail_tendsto_zero`, proved for
every `q : Nat → Nat`. Thus `X'_k(q_k)-V_k(q_k)→0`, with the complete
omitted region controlled uniformly in the refinement schedule.

Adding the previously proved head, grid, and coefficient allowance `C_k`
gives the unchanged original comparison

\[
 |2\Re\rho-1|W_\rho\le D_k\le V_k(q)+
       \underbrace{L^{\rm far}_k+C_k}_{\to0}.
\]

Its compiled terminal theorem is
`pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_moebius_exterior_arithmetic`.
Every ancestor in this chain remains unconditional. **The limit of
`V_k(q_k)` itself is not proved.** Its square retains all cross terms,
and its integration interval grows with the original cutoff. Bounding
individual primitive values or replacing the signed square by a sum of
absolute channel bounds does not establish the missing joint estimate.

### Coefficient-family audit from primary literature

The classical logarithmic Möbius polynomial has an additional possible
obstruction which must inform the coefficient search. [Wei and Wu,
Proposition 1.9](https://bimsa.net/doc/publication/1424.pdf), in
*A characterization of the zero-free region of the Riemann zeta function
and its applications*, proves that decay of its standard critical-line
Nyman–Beurling mean square implies RH **and simplicity of all zeros**.
Their Theorem 1.10 gives an RH equivalence using lines strictly to the
right of the critical line, and also a critical-line boundedness criterion.
These are external mathematical results, not imported Lean theorems.

Our balanced eta primitive has an extra harmonic correction and eta
factor. A rigorous norm comparison with that classical approximation is
not yet in the checked chain. Consequently this slice does **not** claim
that our exact family is impossible, that it forces simplicity, or that
RH alone suffices to make it converge. The general-weight arithmetic
identity keeps alternative bounded tapers available without changing the
canonical minimizing family or the original weighted-current objective.
The next mathematical work is to estimate the full signed arithmetic
square and audit such a comparison before assuming that the linear
logarithmic taper is the final sufficient coefficient law.

## Checked complete critical-square transport to continuum arithmetic

The preceding exterior formula retained physical-grid rounding inside
every arithmetic endpoint. Direct divisor regrouping needs a formula
whose arguments are the actual physical ratios. This slice identifies
that precise arithmetic carrier and proves its complete critical-square
comparison with the original grids.

### Signed primitive and exact endpoint convention

The rounded coordinate `y_d(v)` is strictly below `exp(v)` for every
grid size and converges to it as `d→∞`. Consequently the actual sampled
primitive selects strict arithmetic steps, including when `exp(v)` is
an integer. Define

\[
 A^-_{M,w}(x)=x\sum_{n\le M}\frac{\mu(n)w(n)}n
      \left(1_{n<x}-1_{1<x}\right).
\]

`pairedEtaMoebiusTrialPrimitive_tendsto_continuum` proves
`A_(M,w)(y_d(v))→A^-_(M,w)(exp(v))` at every real `v`, for arbitrary
real arithmetic weights. It keeps the entire harmonic correction and
handles the unit and all other integer endpoints explicitly. In
particular, this is not justified by assuming continuity of the original
discontinuous primitive.

The complete signed arithmetic carrier is

\[
 U^\infty_{M,w}(t)=\sum_{j\ge0}\left[
 A^-_{M,w}(e^t/(2j+1))-A^-_{M,w}(e^t/(2j+2))\right].
\]

Only finitely many terms are nonzero at any given time. For
`t≤log(2N+1)` the first `N` pairs give the full sum, including the
cutoff endpoint. `pairedEtaMoebiusTrialGridCombination_tendsto_continuum`
proves `U_(d,M,w)(t)→U^∞_(M,w)(t)` at every real time. The limit is
the original complex-valued combination, with the signed real arithmetic
embedded in `Complex`; no norm is taken during its identification.

### Entire critical square and quantitative grid error

The continuum combination is measurable as the actual everywhere limit.
For `|w(n)|≤1` on the active arithmetic indices, both the grids and the
continuum carrier have norm at most `2M` at every time. Thus their full
critical square differences and target residuals have genuine
integrability on `(0,∞)`. Dominated convergence uses an exponential
majorant on that entire domain at each fixed `M`.

`pairedEtaMoebiusTrialRefinementError_tendsto_continuum` passes the
original full refinement integral to its continuum value. For `d>0`,
`M≤d`, and `2M/d≤1/8`,
`pairedEtaMoebiusContinuumGridError_le` gives

\[
 \int_0^\infty e^{-t}
    |U_{d,M,w}(t)-U^\infty_{M,w}(t)|^2\,dt
 \le32M^2\sqrt{2M/d}.
\]

The bound includes the entire infinite time range. At `d=2^k`,
`M=k+1`, and the original logarithmic weights, it is at most the existing
`G_k=32√(2(k+1)^5/2^k)→0`. The actual full square distance limit is
`pairedEtaDyadicMoebiusContinuumGridError_tendsto_zero`.

### Growing arithmetic cutoff without exchanging uncontrolled limits

Write

\[
 E^\infty_k=\int_0^\infty e^{-t}
   |h(t)-U^\infty_{k+1,w_{k+1}}(t)|^2\,dt.
\]

At fixed `k`, `pairedEtaDyadicMoebiusRefinedResidual_tendsto_continuum`
proves that the existing full refined energy `E'_k(q)` tends to
`E^∞_k` as `q→∞`. The existing uniform comparison with the original
coarse-grid energy gives

\[
 |E^{\rm coarse}_k-E^\infty_k|\le R_k,
 \qquad |E'_k(q)-E^\infty_k|\le2R_k,
\]

where the unchanged proved allowance is

\[
 R_k=\frac{16}{k+1}
      +64\sqrt{\frac{2(k+1)^{11}}{2^k}}\longrightarrow0.
\]

This pointwise-in-`k`, uniform-in-`q` inequality is established before
allowing `k` to grow. Consequently
`pairedEtaDyadicMoebiusRefinedResidual_sub_continuum_tendsto_zero`
proves `|E'_k(q_k)-E^∞_k|→0` for every refinement schedule. A
fixed-arithmetic-cutoff dominated-convergence theorem alone would not
justify that conclusion.

Finally, with the unchanged `A_k=R_k+L_k→0`,

\[
 |2\Re\rho-1|W_\rho\le D_k\le E^\infty_k+A_k.
\]

The compiled terminal comparison is
`pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_moebius_continuum`.
The original canonical family, zero weight, target residual, and weighted
current objective are unchanged.

**Decay of `E^∞_k` remains open.** Direct divisor regrouping, the complete
cell square-sum identity, and the exact interior prime-variance identity
are now proved in the work described below. The next estimate
must control their joint square on a growing range. A Mellin comparison
with the classical logarithmic Nyman–Beurling approximation has not been
proved for this carrier. The coefficient-family simplicity
issue recorded above therefore remains a research lead, not a transported
Lean consequence. No full arithmetic residual decay, canonical-deficit
decay, RH proof, or new numerical zero strip follows from this slice.

## Complete arithmetic squares and the exterior-parity steer

The current arithmetic development identifies the entire continuum energy as
`∑_(L≥1) r_M(L)^2`, with `HasSum` and square summability proved in
[EtaMoebiusArithmeticEnergy.lean](../RiemannGaussian/EtaMoebiusArithmeticEnergy.lean).
For the actual logarithmic coefficients and `1≤L≤M`,
`pairedEtaMoebiusArithmeticCellResidual_log_eq_primeShell` gives

\[
 r_M(L)=p_M H_\eta(L)-\frac{P(L)}{\log M},\qquad
 P(L)=\sum_{n\le L}\frac{\Lambda(n)}n-
      \sum_{n\le L/2}\frac{\Lambda(n)}n.
\]

The exact complete energy, prime variance, fixed-cell decay, quartic tail
bound, and the subsequent parity route are recorded in the
[endgame assessment](eta-parity-endgame-assessment.md). In particular,
`pairedEtaMoebiusContinuumResidualEnergy_eq_primeVariance_add_exterior`
retains all three nonnegative terms: prime variance, actual normalization
cost, and the entire exterior arithmetic square sum.

The supplied exterior-leakage steer now has these compiled interfaces:

- `pairedEtaMoebiusTrialGridCombination_eq_paritySum`: exact original-grid
  identity at every positive physical coordinate, including endpoints.
- `integral_pairedEtaMoebiusGrid_exterior_eq_parity`: the entire original
  exterior is `1/(4d) ∫_(2/d,∞) F(z)^2/z^2 dz`.
- `pairedEtaMoebiusGridParitySum_eq_primitive_differences`: summation by
  parts with both original primitive endpoints proved zero.
- `integral_pairedEtaMoebiusGridParitySum_sq_eq_covariance`: the exact
  signed covariance on the requested short interval, including all pairs.
- `integral_pairedEtaMoebiusGrid_exterior_le_near_add_allowance`: the
  entire far part costs at most `M²/(2d)`.
- `pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_moebius_nearParity`:
  the unchanged original zero displacement and canonical deficit are
  bounded by the near-parity energy plus a proved vanishing allowance.

The required uniform estimate for that near energy is still unproved.
The existing divisor sampling theorem has its explicit `4T²+L` cost and
its quadratic-range corollary assumes `T²≤L`. No new theorem removes this
cost or replaces the short-window kernel by a full-period gcd covariance.
The actual two-cell lower bound also rules out treating the logarithmic
family's exterior error as exponentially small in its dyadic grid stage;
the precise compiled lower bound and the rate inference are distinguished
in the assessment.

The arithmetic-decay goal has not been completed or weakened.

## Signed quotient amplitudes and the complete quadratic tail

The exact alternating-harmonic remainder now has its positive amplitude
`I_L=∫_0^1 x^L/(1+x) dx` and its original parity sign. The compiled
`etaAlternatingHarmonicAmplitude_quotient_error_le` proves
`|I_floor(L/n)/n-1/(2L)|≤n/(2L²)` for every positive `L,n`.
The complete truncated divisor sum is regrouped without losing its
Möbius signs or quotient endpoints in
`pairedEtaMoebiusArithmeticCellResidual_eq_signed_quotient_amplitudes`.
The logarithmic constants cancel exactly.

For `M≥1,L≥2` and bounded original weights, the checked comparison is

\[
 \left|r_{M,w}(L)-\frac{p_{M,w}\eta(L)-S_{M,w}(L)}{2L}\right|
 \le\frac{M^2}{L^2},\qquad
 S_{M,w}(L)=\sum_{n\le M}\mu(n)w(n)\eta(\lfloor L/n\rfloor).
\]

`S` is the existing signed quotient-parity family. Its full square enters
the sampler before any absolute bound on that family is taken. The
original quadratic window condition is retained. With `R≥M²`,
`pairedEtaMoebiusArithmeticSquareTail_le_sampling` proves

\[
 \sum_{L>R}r_{M,w}(L)^2\le
 \frac{2[p_{M,w}^2+5C(1+\log M)^2M]}R+\frac{4M^4}{R^3},
\]

where `C=finiteCircleSamplingConstant`. Genuine square summability and
the quotient/remainder equivalence justify regrouping every tail cell
into consecutive blocks. A telescoping reciprocal majorant includes
the whole infinite tail.

For the exact logarithmic weights at `R=M²`, the bound becomes
`(2p_M²+4)/M²+10C(1+log M)²/M`, whose decay follows from the already
proved harmonic cancellation and logarithmic limits. Both the bound and
the limit are checked in
[EtaMoebiusArithmeticSamplingTail.lean](../RiemannGaussian/EtaMoebiusArithmeticSamplingTail.lean).
Its terminal theorem
`pairedEtaMoebiusContinuumResidualEnergy_sub_quadraticPrefix_tendsto_zero`
states that the full continuum energy minus its unchanged signed prefix
through `M²` tends to zero. The unresolved growing range is now through
`M²`, including the interior prime variance and actual normalization
cost. No full arithmetic decay or canonical-deficit decay follows yet.

## Exact Hardy and dyadic norm audit of the coefficient family

The next checked interface identifies the original balanced floor cell
`B(0)=0`, `B(L)=1−Σ_(n≤M) μ(n)w(n)floor(L/n)+pL` for `L≥1`.
Its exact remainder formula gives `|B(L)|≤1+M` for bounded original
weights. The associated unpaired harmonic primitive has increment
`(B(L+1)−B(L))/(L+1)`, and its dyadic difference is the unchanged
eta residual at every cell.

The full discrete Hardy transform

\[
 q(L)=\frac{B(L)}{L+1}-\sum_{j>L}\frac{B(j)}{j(j+1)}
\]

has the exact finite energy identity

\[
 \sum_{L=0}^{N}q(L)^2
 =\sum_{L=1}^{N}\frac{B(L)^2}{L(L+1)}+(N+1)T(N)^2,
 \qquad T(N)=\sum_{j>N}\frac{B(j)}{j(j+1)}.
\]

All sums are genuinely summable, and the boundary square tends to zero.
`tsum_etaDiscreteHardyTransform_sq_eq` therefore preserves the complete
weighted norm, rather than only a finite truncation. The original
residual is exactly `q(L)−q(floor(L/2))`. Every parent appears twice;
the full signed parent-child cross moment remains explicit before
universal estimates are applied.

The terminal theorem
`pairedEtaMoebiusContinuumResidualEnergy_beurling_bounds` proves

\[
 \frac16\sum_{L\ge1}\frac{B(L)^2}{L(L+1)}
 \le E^\infty_{M,w}\le
 6\sum_{L\ge1}\frac{B(L)^2}{L(L+1)}.
\]

For the logarithmic family, decay of the two full norms is equivalent.
This audits the strength of the representation; it does not prove
either decay assertion. Separate estimates now control the growing
logarithmic head and complete tail beyond `M²`. The further classical fractional-part
integral/Mellin comparison and the external simplicity consequence have
not been transported into Lean. The detailed distinction and literature
attribution appear in the [endgame assessment](eta-parity-endgame-assessment.md).

## Quantitative normalization and the complete growing arithmetic head

`EtaMoebiusLogHarmonicBound` retains the exact finite identity
`p_M log M=1−γ m(M)−Σ_(n≤M) μ(n)e(M,n)/n`, where
`e(M,n)=H(floor(M/n))−log(M/n)−γ`. The full Möbius–harmonic
convolution equals one; the elementary remainder bound `|e(M,n)|≤2n/M`
controls the entire signed remainder sum by `2`. With the proved
`|m(M)|≤2`, the actual coefficient normalization satisfies
`|p_M|≤5/log M` for all `M>1`.

`EtaMoebiusArithmeticGrowingHead` uses the original prime-shell identity
and the proved Chebyshev bound to establish `0≤P(L)≤12` and
`|r_M(L)|≤22/log M` for every `1≤L≤M`. Its joint estimate is

\[
 \sum_{L\le R}r_M(L)^2\le484R/(\log M)^2\quad(M>1,\ R\le M).
\]

The compiled theorem
`pairedEtaMoebiusArithmeticSquarePrefix_logarithmic_tendsto_zero`
therefore controls the complete growing head through `floor(log M)`.
The cutoff itself is proved to grow to infinity. The former complete
quadratic-tail theorem controls the other end. With the original finite
middle sum `Q_M=Σ_(floor(log M)<L≤M²)r_M(L)^2`, the exact three-part
identity proves `E^∞_M−Q_M→0`.

`EtaMoebiusMiddleBudget` carries this estimate to the original canonical
deficit and actual zero displacement. For `k≥7`,
`d_rho W_rho≤D_k≤Q_(k+1)+B_k`, where
`B_k=484/log(k+1)+QuadraticTailAllowance(k+1)+RefinedAllowance(k)`
is proved to tend to zero. Its terminal theorem is
`pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_moebius_middle`.

The middle sum remains uncontrolled. The sharper normalization main term
is now proved below; the complete prime variance still requires a bound,
and no full arithmetic decay or sharper numerical zero strip follows.
These are partial arithmetic estimates on the original family, not a
replacement for the active full-current objective. The
[endgame assessment](eta-parity-endgame-assessment.md) records the full
formulas and the classical provenance of the elementary harmonic bound.

## Full Euler correction decay and the original normalization main term

The actual finite harmonic Möbius tail has a checked signed Abel
identity, including both original endpoints and every monotone-weight
increment. `MoebiusHarmonicMonotoneTail` proves its absolute bound
`2ε b(D+1)` for nonnegative decreasing weights when every original
harmonic prefix from `D` through `M` has absolute value at most `ε`.

`EtaMoebiusLogEulerCancellation` applies this to the two actual quotient
weights in `C_M=Σ_(n≤M) μ(n)e(M,n)/n`. At `D=floor(M/Q)`, `Q≥2`, the
low part costs at most `2/Q`, and the complete complementary sum costs
at most `4ε(1+log Q)`. The repo's harmonic Möbius cancellation supplies
the uniform prefix hypothesis as `M` grows for each fixed `Q`.
The entire correction therefore tends to zero, with no exchange of a
growing arithmetic limit and an uncontrolled infinite sum.

The terminal normalization theorem
`pairedEtaMoebiusLogHarmonic_mul_log_tendsto_one` in
`EtaMoebiusNormalizationMainTerm` proves `p_M log M→1`. With the exact
error `e_M=p_M log M−1` and `Δ(L)=H_eta(L)−P(L)`, every original cell
`1≤L≤M` satisfies `log M*r_M(L)=Δ(L)+e_M H_eta(L)`. The error from
the prime discrepancy is uniformly at most `2|e_M|`, and that allowance
tends to zero over the entire interior.

Before any estimate, the full square expansion retains
`ΣΔ²+2e_M ΣH_eta Δ+e_M²ΣH_eta²`, all divided by `log² M`.
The proved upper bound for a prefix of length `R≤M` is
`(2Σ_(L≤R)Δ(L)²+8R e_M²)/log² M`. Its growing dimension cost remains;
qualitative `e_M→0` does not make it vanish at `R=M`. Neither the full
prime-discrepancy square estimate nor the full intervening arithmetic
band has been bounded. The full weighted-current objective is unchanged.

## Next mathematical obligations

The exact-pole prime input now excludes the larger explicit
multiplicity-sensitive edge regions above, preserving every earlier
margin. Its improvement over the previous signed margin exceeds a
factor of thirty-one at every nonzero ordinate. The simultaneous edge
windows now additionally exclude multiple zeros and nearby distinct pairs
in their stated rectangles, and discharge the original head branch near
either edge. These constraints do not force real part `1/2`,
and the return bound retains a positive exponent. The single-phase eta
projection has a proved `1/11` exponent floor. The exact dyadic translate
family now supplies a different bound through its canonical deficit
`D_k=1-b_k^T (G_k+lambda_k I)^(-1)b_k`. Its definition, complete tail
control, minimizing identity, and four-point `D_2<1/4` bound are checked.
The exact balanced logarithmic Möbius candidates now discharge their
complete penalty, actual infinite-tail, and full grid-refinement costs.
With the stage arithmetic cutoff and weights fixed, every finer physical
grid has full target residual `E'_k` satisfying `D_k≤E'_k+A_k`, where
`A_k→0` is proved. The actual residual integral on `(0,log 2]` now tends
to zero by the exact logarithmic harmonic identity and complete finite-grid
head formula. The full residual equals this vanishing head term plus the
unchanged exterior energy `X'_k` on `t>log 2`; the canonical deficit is
at most `X'_k` plus a proved vanishing allowance. The whole exterior now
also equals a growing square integral `V_k` of the exact signed odd/even
primitive formula plus a genuine infinite tail at most `(k+1)^2/4^k`.
The original zero displacement is bounded by `V_k` plus an allowance
tending to zero. The immediate task is a joint estimate for this full
growing arithmetic square, or a better structured candidate with a
provable complete bound. The identity is available for arbitrary real
weights, retaining every physical rounding and signed endpoint. The
classical linear logarithmic taper has the additional simplicity issue
recorded above; that issue has not been transported to our carrier in
Lean. The full signed continuum arithmetic carrier is now identified
at every time and in the complete critical-square comparison. Every
refined full residual differs from its continuum counterpart by at most
`2R_k→0`, and `D_k≤E^∞_k+A_k` with `A_k→0`. Direct divisor cancellation
now identifies its exact infinite square sum and interior prime variance.
The parity rewrite additionally identifies the original near-exterior
short-window covariance with every far cost vanishing. The exact quotient
amplitude comparison now applies the existing sampler in its valid
range and proves decay of every arithmetic cell beyond `M²`. The new
joint prefix bound also controls the complete head through `floor(log M)`.
The next task is a uniform signed estimate on `floor(log M)<L≤M²`,
including its prime variance and normalization cost. The normalization
main term is now exactly `p_M log M→1`, with a uniform interior
prime-discrepancy formula; its growing square cost still needs a rate.
The estimate must respect its
physical-window dependence and the two-cell inverse-logarithmic lower
rate. The full balanced floor-cell norm is now equivalent to the original
eta residual norm, so changing that representation alone cannot supply
decay for the same coefficients. A Mellin-multiplier comparison with the classical approximation
and full residual decay are not proved. The desired `D_k→0` remains open. Numerical
decreases and the definition of a minimizing coefficient law do not prove
this estimate. The positive target normalization must also be bounded
in the intended zero region if a numerical strip is to be certified.
Positivity of a finite Gram or convergence of each separate entry does
not supply that control. The remaining target is to rule out the interior off-critical
contribution while retaining the unchanged absolute weighted moment. The
following inverse and heat carriers remain available for that task; their
established identities alone do not supply the missing estimate.
The independent Gaussian reciprocal contour now gives a bound for the
actual convergent Möbius sum, with its full integral identification and
every horizontal and infinite-tail correction proved. The moving mass
and unit-time scale choice now give the unconditional eventual rate above.
The exact complex heat transport remains available upstream. Removing
Gaussian smoothing now also gives the ordinary finite Möbius cancellation,
and exact Abel summation carries it to the original finite complex weights.
The actual quotient blocks and completed zeroth eta blocks now also have
the quantitative cubic-scale rate above, with their odd endpoints retained.
The all-cutoff remainder has specified scale dependence and is absorbed
above an explicit weight-dependent cutoff. The positive power scale,
smaller blocks, and accumulation through the complete two-divisor inverse
remain obstacles. The next step requires a
stronger joint estimate for that inverse and both completed reflected mixed
energies. The harmonic hyperbola estimate now also controls the accumulated
signed coefficients of an entire inner-truncated inverse region, with exact
rounding cost `D`. It does not yet control their original complex eta
weights or quadratic products. The finite coefficient cancellation does
not establish the signed full inverse-energy bound.

1. Bound the signed full zeroth-order inverse energy's weighted absolute
   moment uniformly. The checked transport above now covers both the
   original head and the repeated-zero adjacent pair, with a finite
   odd-weighted error budget at their literal physical cutoffs.
   The entire odd and even aggregate and all four quadratic block sums
   already have uniform bounds at one physical cutoff. The simple-zero
   current now has an exact reconstruction from those odd aggregates.
   Its termwise absolute inverse-weight cost, however, has proved growth
   `M^(1-Re rho)`; bounding each aggregate separately cannot close this
   transfer estimate. Summing phases within an equal-cutoff block also
   leaves a proved positive-power main term. The complementary cutoffs
   cancel that term with the quantitative complex error above, so their
   interaction must survive any subsequent estimate for the signed pair.
   This zeroth-moment cancellation alone does not exclude an off-critical
   zero or improve the known sharp original-return exponent. Any use of the earlier
   fixed-pair estimate must still account for its divisor-dependent
   normalizers and averaging period. The earlier diagonal bound has a complementary correlation
   sum with a possible nonzero limit; that sum cannot be dropped.
   No uniform estimate for the original weighted return is currently proved.
   All cross-cutoff terms and odd endpoint corrections must be retained. The
   proved matching power bounds show that removing the cutoff growth
   requires such an exclusion; a sharper local approximation alone cannot
   provide it. The signed Euler, half-step head, and heat reconstruction
   errors are now summable in both actual multiplicity branches. Bounds for a positive heat Gram
   or a norm of a single phase channel do not establish the required signed
   completed-current bound. The small-width signed endpoint theorem and the
   broad-width reconstruction concern different regimes; a use of one to
   bound the other requires a proved intervening identity and estimate.
2. Use the proved uniform reconstruction stability to transport a proved
   return bound to the original current, without another exchange of an
   uncontrolled limit and weighted series.
3. Only after that bound is discharged, prove the existing first-moment
   summability statement and use its existing equivalence to derive
   `RiemannHypothesis`. Audit the terminal theorem, all transitive axioms,
   full library, generated status, and exact-commit CI before any completion
   claim.

## Assessment of the combined research direction

The most concrete combination is literal eta interval geometry, complex
phase probes, ordered Gaussian support/gap returns, and the completed
arithmetic current. It now preserves the first absolute-moment frontier up
to the proved finite error budget above. This is a stronger application
interface than fixed-cutoff reconstruction alone. Priority for the combined
mathematics has not been established.

The operator-theoretic theme itself has substantial prior work. Suzuki's
[2026 paper on the Weil form](https://arxiv.org/html/2606.09096v1) relates
continuous screw kernels to finite-interval operators, proves continuity
of the lowest eigenvalue, and gives a small-interval asymptotic. Its proposed
limiting spectral identification remains conjectural. The repository's
candidate contribution should therefore be judged at the level of the
specific eta arithmetic and completed signed estimates.

The checked two-transition comparison also remains available for a
quantitative comparison between heat scales with the completion channels
retained. Any use of it must respect the surviving cross-cutoff
correlations above. The table distinguishes the completed identity from
proposed estimates and longer-path targets. None of the open targets is
a premise to add to Lean:

| Step | Existing input | Concrete target and acceptance condition |
| --- | --- | --- |
| Compare ordered heat compositions on the actual domain | The exact continuous composition, full three-time integrability, and zero-tilt weighted reconstruction above. | The normalization and reconstruction error are now controlled with linear width. The next estimate must preserve cancellation of the signed completed current against the composed term and both corrections. |
| Keep all support/gap paths | The actual two-transition decomposition above, the finite two-stage identity in [ProjectionHeatLeakage](../RiemannGaussian/Hybrid/ProjectionHeatLeakage.lean), and ordered cubic paths in [EtaSpectralHeatCubicPaths](../RiemannGaussian/Hybrid/EtaSpectralHeatCubicPaths.lean). | For any longer-path comparison, prove its identities on the actual continuous eta measure and pair every path with both completed current branches. Include every omitted-time and compression term with its sign. The existing finite matrix algebra alone is insufficient. |
| Test a quantitative scale comparison | The signed two-endpoint heat law, full mixed phase matrix, and the new reconstruction error budget. | Derive an estimate for the actual signed return with cutoff, phase-family size, moving tilt, multiplicity, and accumulated path error explicit. A sufficient endpoint would be a summable majorant for `(2N+1)‖R_N‖`; the exact target is a bound on its partial sums uniform in `K`. |

The decisive test is whether the zero condition and completion symmetry
supply a new cancellation in that comparison. Positive Gram bounds, a
fixed-size matrix limit, or discarding path signs cannot provide it by
themselves. In particular, fixed moving-tilt asymptotics do not control a
fixed off-axis zero: their tilt parameter grows with the logarithmic scale.
If no estimate survives these dependencies, the next result should state
the obstruction precisely rather than rename it as another RH criterion.

### Next estimates on the retained signed arithmetic

The exact branch formulas, completed reflection defect, endpoint gain,
linear-width summability, signed principal errors, and matching conditional
off-critical power bounds for the actual weighted return are now proved.
Excluding the surviving off-critical endpoint contribution remains open. The next targets are
**proposed work**, not assumptions to add to the proof chain.

1. Seek an arithmetic estimate on the retained cross-cutoff interactions
   that controls the original completed moment pairs. Their finite
   Möbius constraint, positive diagonal bound, and odd/even fixed-pair
   cancellation are now checked, as are the uniform bounds for the whole
   growing parity aggregates and all four signed block sums. The exact
   simple-zero current now reconstructs by the odd inverse formula.
   Its inverse-weight mass has positive-power growth even on the critical
   line; the next estimate must exploit cancellation in the weighted
   signed sum rather than replace it with termwise absolute values.
   The grouped top inverse block now has its nonzero Mellin main term,
   and the complementary cutoffs have the opposite term with a decaying
   error. These relations must remain available when estimating the
   two completed channels together.
   Full transformed moments now have fixed-center bounds at every order,
   and the original repeated-zero current has an exact double inverse sum.
   Uniform control of that inverse sum at moving centers remains open.
   The Fourier sampling estimate above supplies a quantitative bound in the
   quadratic truncated range, replacing the earlier `D^4/L` window error
   by a complete-energy cost with factor `1+4D²/L`. Extending it to the
   full physical range must control that remaining scale dependence and
   the `D^4/A²` physical correction. The individual endpoint powers are
   now removed for the original zeroth-order forward terms with their exact
   physical decay. The moving-center transfer now extends this truncated
   estimate to all moments below the actual multiplicity, including the
   signed adjacent pair. The inverse-entry error above retains each outer
   complex weight and proves its translated center condition, but its
   `D²/q` cost does not control the full inner range. Summing the actual
   inverse head and adjacent mixed terms over all outer cutoffs remains open.
   The rectangle estimate controls both divisor sums jointly on
   `(ED)²≤A,L`, with area cost `ED` and explicit logarithmic factors.
   The curved-region extension now controls any fixed subregion of `de≤T`
   and mixed pairs of independently selected regions, using the actual
   signed product coefficients. Averaging the physical error weakens the
   starting constraint to `T≤A`, but the window must still satisfy `T²≤L`.
   The coherent-band counterexample now rules out extending that same
   physical budget uniformly to all proportional windows. The complete
   moving complement supplies a proved negative mixed contribution at
   order zero. The checked full inverse-energy transport now carries
   that complete split to the original head and adjacent reflected
   moment pairs with summable weighted error. The exact complex
   correction remains available in every channel.
   Separate-band norm bounds cannot replace that leading cancellation.
   Controlling the original weighted signed current still requires an
   additional arithmetic estimate on the full completed channels.
   Any use of the earlier period averages must also preserve their
   divisor-dependent normalizers and errors. Any use of the
   mixed phase matrix must identify the actual finite eta feature vector
   and control its dimension, scale, and compression errors. The above
   midpoint and Euler error estimates alone cannot bound `S_rho(K)`
   independently of cutoff. The proved lower bound forces growth
   under the hypothesis that the actual zero is off the critical line.
2. Preserve the unchanged final target: partial sums of
   `(2N+1)*|J_rho(N)|` bounded uniformly in `K` for every actual zero.
   That bound would imply RH through the already checked equivalence;
   it is not an auxiliary estimate already supplied by this package.

Broader claims of novelty require comparison with the literature.
Gaussian expansions, moment raising, and operator positivity are
established techniques; the contribution checked here is their explicit
combination on the original completed eta carriers.

No reconstruction or summability premise has been introduced as an axiom.
The goal remains open because the uniform weighted arithmetic estimate is
not yet established. No `13/18` certificate or RH proof is claimed.
