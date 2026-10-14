# Signed arithmetic control toward RH

The objective is an independently verified operator and arithmetic estimate
that controls ordinary zeta across every scale, working toward a proof of RH.
Historical priority is an annotation. **The objective remains open. No
RH-sufficient uniform signed estimate and no RH proof has been obtained.**
A known imported logarithmic signed bound now provides an all-scale calibration;
it remains below RH strength and retains its named external dependency.
The factorial trace also gives signed harmonic and reciprocal-tail control of
actual prime powers at every real scale, without an imported prime-distribution
estimate. Those bounds recover ordinary zeta only at exponent one.

The primary runner is now:

```bash
../.venv/bin/python run_expanded_probe.py --mellin-only
../.venv/bin/python run_expanded_probe.py --signed-defects-only
../.venv/bin/python run_expanded_probe.py --fractional-powers-only --max-root-denominator 12
../.venv/bin/python run_expanded_probe.py --pole-neutral-only
../.venv/bin/python run_expanded_probe.py --parameter-jets-only
../.venv/bin/python run_expanded_probe.py --prime-error-only
../.venv/bin/python run_expanded_probe.py --prime-discrepancy-only
../.venv/bin/python run_expanded_probe.py --prime-twists-only
../.venv/bin/python run_expanded_probe.py --prime-oscillation-only
../.venv/bin/python run_expanded_probe.py --mellin-kernels-only
../.venv/bin/python run_expanded_probe.py --root-lattices-only
../.venv/bin/python run_expanded_probe.py --divisor-preconditioners-only
../.venv/bin/python run_expanded_probe.py --signed-global-only
```

It creates a fresh run directory, freezes source hashes and search rules,
learns or samples signed operators, seals an archive, draws evaluator-owned
final cases, and independently checks complete arithmetic moments or complete
point sums, according to the declared stage. Guided identity calibrations are
reported separately from candidate discovery. Existing
sealed runs retain their code and data fingerprints. Rebuild the combined
report without rerunning arithmetic using `--summarize-only`.

## The proof target

Let μ be the constant-one Dirichlet inverse, M its cumulative sum, and M̃ its
linear interpolation. The learner produces μ by divisor inversion without
a prime or factor oracle. An independent evaluator uses a prime sieve.

The current operator language includes rational signed dilation polynomials

\[
R(t)=P(S_b)\widetilde M(t),\qquad S_b f(t)=f(t/b),\qquad P(0)=1.
\]

Their ordinary-zeta bridge is

\[
\int_1^\infty R(t)t^{-s-1}\,dt
=\frac{P(b^{-s})}{s\zeta(s)}+H(s),
\]

where H is holomorphic on Re(s)>0. Exact rational disk certificates can prove
that P(b⁻ˢ) stays nonzero at every height on Re(s)≥1/2. The grammar allows
signed coefficients beyond the triangle-contraction domain and retains
programs for which this proof backend supplies no global certificate.

For a rational moment order q≥1, define

\[
A_q(X)=\int_X^{2X}|R(t)|^q\,dt.
\]

If **every dyadic X≥1** satisfies A_q(X)≤C Xᵝ with a finite scale-independent
C, Hölder's inequality makes its Mellin transform holomorphic on
Re(s)>max((β−1)/q,0). The relevant exponent is

\[
\eta=\frac{\beta-1}{q}.
\]

A **single fixed moment order** with β=q/2+1 would suffice for RH when the
multiplier remains nonzero throughout the critical half-plane. Constants
and multiplier costs are retained in quantitative reciprocal-zeta bounds.
The initial Lipschitz-to-pointwise route had a larger exponent loss.

This corrects the initial pilot report's overly broad statement that a finite
list of moment orders is always insufficient. A limiting family is one route.
A fixed-order uniform estimate, including an allowable logarithmic loss, is
another. The original frozen pilot is preserved; the later correction is
recorded in `signed_mellin_proof.txt` and the combined report.

A known ordinary critical-line zero with nonzero multiplier rules out any
uniform claim with β<q/2+1 for q≥1. This stronger obstruction does not assume RH.

## Rational powers, roots and fractional moments

The new typed extension `rational_power_grammar.py` accepts **general exact
rational exponents p/d**, including square, cube and sixth roots. Its semantics
do not restrict denominators to a named list. A frozen run declares a finite
denominator budget; `--max-root-denominator` controls that search cost.

The productions have separate meanings:

- Ordinary real powers require nonnegative inputs for an even reduced
  denominator. Negative cube roots are real; negative square roots are outside
  this domain. Nonpositive exponents exclude zero.
- Signed powers are Sₐ(x)=sgn(x)|x|ᵃ. For a>0 they retain the sign and have
  inverse S₁/ₐ. They are useful on signed arithmetic residuals.
- Absolute powers retain magnitudes and lose signs.
- Principal complex powers declare their logarithm branch and reject balls
  crossing its cut. A root around a zeta zero retains fractional monodromy;
  computing one branch does not prove a global continuation.
- Normalized Dirichlet powers act on coefficient sequences with f(1)=1 and
  use finite-at-each-index binomial expansions. The existing exact backend
  already supported rational exponents; the new search exposes and audits it.

These productions compose with sums, products, divisions and other roots.
Irrational real values receive certified ball enclosures. Finite Dirichlet
coefficient roots remain exact rational values.

The estimate layer now integrates every unit interval for arbitrary positive
rational q. If a residual is affine from u to v on that interval, its moment is

\[
\int_0^1|u+t(v-u)|^qdt
=\frac{G_q(v)-G_q(u)}{(q+1)(v-u)},\qquad
G_q(x)=\operatorname{sgn}(x)|x|^{q+1},
\]

with the constant case handled separately. This includes intervals crossing
zero. Fractional whole-window moments are certified algebraic enclosures,
not exact rational numbers or sampled quadrature.

The detector charges the recovery cost. A p-th absolute moment of S₁/𝑑(R)
is exactly the effective p/d moment of R. A root's smaller amplitude therefore
does not establish additional signed cancellation. Nested nonlinear sums of
roots require their own ordinary-zeta bridge; the linear bridge is not
silently transferred to them.

For q≥1 the same Hölder–Mellin proof gives η=(β−1)/q. For 0<q<1 the detector
uses an explicit Lipschitz peak bound followed by an L1 estimate, giving the
sufficient exponent η=2β/(q+1)−1. Applying Hölder with exponent below one
would be invalid. These conditional transfer arguments and all domains are
recorded in `rational_power_proof.txt`. The required uniform signed moment
premise remains unproved.

The frozen `fractional-moment-results/pilot-001` run used 26 effective orders
through denominator twelve, generated 557 estimates and archived eighteen.
Its independent audit passed 11/11 checks, recomputing 6,420 complete-window
actual moments, checking 8,492 exact Dirichlet coefficients by a separate
log/exp implementation, and verifying 66 native zeta root values against
proved absolute tails. The complete final μ prefix reaches 114,186.
All eighteen archived estimates passed fresh complete windows. Four retained
RH-sufficient obligations have integer effective orders; this run found no
RH-strength advantage from the fractional orders. All uniform signed premises
remain unproved. Both all-positive controls and delayed-positive controls
violate each archived estimate on at least one final window.

A separate **guided local branch calibration**, not another independent
arithmetic discovery claim, passed 6/6 checks in
`fractional-branch-results/audit-001`. Different rigorous native contours
around s=1 certify winding −1, one simple pole and zero zeros. For a rational
exponent a, the local divisor order of ζᵃ is −a. Every noninteger exponent
therefore has a branch obstruction at one, which lies inside Re(s)>1/2.
This applies to the seemingly promising fractional inverse powers as well.
Multiplying outside the power by a single-valued analytic factor of integer
vanishing order cannot cancel that fractional order.

Taking the power after combining pole orders, for example
((s−1)ζ(s))ᵃ, repairs the local order at one. It supplies neither a global
branch nor an all-scale signed arithmetic estimate. At ordinary zeros,
negative powers retain a singularity at every positive multiplicity. Positive
fractional powers require additional zero-faithfulness conditions because a
multiple zero can have integral powered multiplicity. A known simple critical
zero checks local monodromy; its location on the boundary does not contradict
RH. Full proof and scope: `fractional_zeta_branch_proof.txt`.

## Fractional arithmetic coefficients and pole-compatible kernels

The extension `pole_neutral_grammar.py` varies three parameters independently:
the signed coefficient power νₐ=μ⁎ᵃ, a logarithmic integral order b, and a real
kernel shift κ. For 0<a≤1 and 0<b≤1, it computes complete sums

\[
G_{a,b,\kappa}(x)=\sum_{n\le x}\nu_a(n)K_{b,\kappa}(\log(x/n)),\qquad
K_{b,\kappa}(u)=\frac1{\Gamma(b)}\int_0^u e^{\kappa v}v^{b-1}\,dv.
\]

The b=0 production is the unsmoothed coefficient sum. These are new
coefficient sequences, distinct from pointwise roots of M. At a prime,
νₐ(p)=−a; its prime-power recurrence is c₀=1,
cₖ=cₖ₋₁(k−1−a)/k. The producer obtains the coefficients by factor-free
Dirichlet inversion and binomial powers. The evaluator recomputes them from
an independent prime sieve. The universal bound |νₐ(n)|≤1 is available on
this declared exponent domain.

The initial Mellin transform is

\[
\mathcal M G_{a,b,\kappa}(s)=\frac{\zeta(s)^{-a}(s-\kappa)^{-b}}s,
\qquad \Re s>\max(1,\kappa).
\]

The local divisor audit identifies compatible parameters. In particular,
a=b and κ=1 give the pole-removed expression
`((s−1)ζ(s))^(−a)/s`. A power is taken after combining the local pole orders.
The generator does not assume matching exponents, though archive coverage of
matched families is an explicit selection rule. Mismatched branches and
introduced shift singularities are retained and diagnosed.

The frozen `pole-neutral-results/pilot-001` run generated 328 programs and
11,014 learned estimates. Its independent audit passed 10/10 checks, verifying
62,438 exact coefficients, 5,686 complete signed point values, 30 native Mellin
comparisons with proved coefficient tails, and 20 independent kernel
quadratures. The final complete coefficient prefix reaches 8,178. Ten of
twelve archived bounds passed fresh points and are RH-sufficient if their
uniform integer premises hold. The ten obligations include the original M
and matched square, cube, fourth, fifth and sixth coefficient/kernel roots.

The proof supplies an integer-to-real extension and a denominator-clearing
identity that preserves every ordinary zero multiplicity. Quantitative
recovery charges the inverse exponent 1/a and the height factor. Smaller
fractional sums have not demonstrated better signed control after that cost.
All RH-strength signed premises remain unproved. These are complete point
tests, not complete-window moment tests. Proof: `pole_neutral_proof.txt`.

## Parameter derivatives expose actual prime information

`parameter_jets.py` adds a general operation: the Taylor coefficients of
f⁎⁽ᵃ⁺ʰ⁾ for any rational sequence with f(1)=1, any rational centre a, and any
nonnegative derivative order. It uses

\[
[h^j]f^{*(a+h)}=f^{*a}*(\log_D f)^{*j}/j!.
\]

No multiplicativity or prime labels are required. The operation composes with
one-sided parameter jets of the logarithmic kernel. Coefficient and kernel
slopes can vary independently. Higher jets expose convolution correlations
of the arithmetic coefficients.

For the matched family Gₐ=Gₐ,ₐ,₁, a guided recovery calculation gives an exact
identity for every fixed real x>1:

\[
E(x)=\lim_{a\downarrow0}\frac{G_a(x)-1}{a}
=\operatorname{li}(x)-\Pi_{<}(x),\qquad
\Pi_{<}(x)=\sum_{p^k<x}\frac1k.
\]

This follows because the first coefficient of μ⁎ᵃ is −1/k on actual prime
powers pᵏ and zero elsewhere, while the kernel derivative is Ei(log(x/n)).
At integer x the endpoint is strict: Kₐ,₁(0)=0 for every a>0. The two limits
a→0 and u→0 cannot be interchanged. Root-count inversion then recovers the
ordinary strict prime count:

\[
\pi_{<}(x)=\sum_{k\ge1}\frac{\mu(k)}k\Pi_{<}(x^{1/k}).
\]

Only finitely many terms contribute; the implementation uses exact nᵏ<x
comparisons to avoid numerical root-boundary mistakes. The producer has no
prime or factor oracle. These all-scale arithmetic identities supply a
representation of actual prime information, not a new distribution estimate.
Their mathematical proofs are in `parameter_jet_proof.txt`; the analytic
arguments are not machine-formalized. The separately frozen calibration
checks arbitrary inputs, actual-prime identities and native parameter
derivatives, and makes no autonomous-discovery claim.

`parameter-jet-results/calibration-001` passed 8/8 independent checks. It
verified 8,960 exact coefficient values, 48 kernel Taylor coefficients by
rigorous Cauchy contours, 168 complete arithmetic family-jet values, and 42
finite difference quotients. All fourteen tested x values showed smaller
quotient error at the smallest tested exponent. Exact root-count inversion
agreed with an independent prime sieve at those fourteen inputs, including
strict prime-power boundaries. These finite checks support the universal
identity argument; they establish no uniform error bound.

The signed-control target is consequently more precise:

\[
\forall x\ge2,\quad\forall\,0<a\le a_0,\qquad
|G_a(x)-1|\le C a\sqrt{x}(1+\log x)^L,
\]

for finite positive C,a₀ and fixed nonnegative integer L. Dividing by a and
taking the fixed-x limit would prove a uniform square-root prime-power error
bound. Its Mellin transform is `−log((s−1)ζ(s))/s`; holomorphy on Re(s)>1/2
would exclude every ordinary zero there and imply RH. **The coupled uniform
signed bound is unproved.** Finite exponent tests and constants of order one
do not provide the required order-a control. The restriction x≥2 matters:
the derivative diverges as x approaches one.

## Prime-error filters need no all-height nonvanishing gate

The first jet also supports direct signed-bound searches, without first
proving a coupled estimate for every small exponent. Define E(x)=0 for x<2
and E(x) equal to li(x) minus the prime-power count for x≥2, retaining the strict
endpoint described above. This removes the integrable log-log singularity
on a bounded interval and changes the Mellin transform by an entire compact
correction B₀(s). The finite dilation grammar now accepts

\[
R(t)=\sum_jc_jE(t/d_j),\qquad D(s)=\sum_jc_jd_j^{-s},\qquad
d_0=c_0=1,\quad d_j>1\ (j>0).
\]

D is entire and tends to one along the positive real axis, so it is not
identically zero. **It may vanish inside the critical half-plane.** If a
uniform signed bound makes H(s)=Mellin(R)(s) holomorphic there, then

\[
Q(s)=\frac{sH(s)}{D(s)}+sB_0(s)
\]

is meromorphic and satisfies Q′(s)=−F′(s)/F(s), with
F(s)=(s−1)ζ(s), initially on Re(s)>1 and then by the meromorphic identity
theorem on the claimed half-plane. A derivative of a meromorphic function
has residue zero. At any ordinary zeta zero of multiplicity m≥1, −F′/F has
residue −m. This contradiction preserves every zero even if D vanishes at
that same point. The earlier all-height nonvanishing gate belongs to the
direct inverse-zeta bridge; it is unnecessary for this logarithmic bridge.
The proof is written mathematics, not a machine-formalized analytic theorem.

For example, the admitted operator R(t)=E(t)−2E(t/2) has
D(s)=1−2⁽¹⁻ˢ⁾ and D(1)=0. A uniform bound on R at square-root growth would
still imply RH. The new gate does not assert that such a bound exists.

The whole-unit increment has a universal bound B: between consecutive
integer inputs, the smooth li contribution has derivative at most 1/log2,
and the strict prime-power count makes at most one jump per delayed input,
of magnitude at most one. Rational noninteger delays also receive an explicit
activation cost at two. Consequently, for θ,ℓ≥0,

\[
\forall n\in\mathbb N,\ n\ge1:\ |R(n)-A|\le Cn^\theta\log(e+n)^\ell
\quad\Longrightarrow\quad
\forall t\ge1:\ |R(t)-A|\le Ct^\theta\log(e+t)^\ell+B.
\]

Thus θ≤1/2 gives an RH-sufficient premise with no growth-exponent loss.
The jump bound is proved over every scale; the signed integer premise is
unproved. The grammar permits general rational power and logarithmic
exponents, with finite declared search grids.

The frozen `prime-error-results/pilot-001` run generated 228 signed filter
programs and 28,691 power/logarithmic estimates. Candidate coefficients,
centres and constants were selected by numerical rules frozen before
validation, and final irregular inputs were drawn after archive closure.
The producer formed logarithmic coefficients without a prime or factor
oracle. Its independent audit passed 10/10 checks, including deterministic
isolated replay, 31,001 exact coefficient checks, 4,524 complete signed point
values, 120 complete support-control values and three native zeta-logarithm
comparisons with proved absolute tails. The complete final prefix reaches
30,104; these are point tests, not complete-window moment tests.

Ten of twelve archived bounds passed the fresh points and are RH-sufficient
if their uniform premises hold. Three survivors have D(1)=0, proving that the
new bridge admits useful numerical leads excluded by the older gate. The
archived claim below square-root growth and the claim with mismatched prime
weight both failed fresh points and were independently ruled out analytically.
The symbolic residue rule detects their global obstruction regardless of
finite survival. Positive-support and delayed-support controls were checked
and rejected; no globally false final pass is reported for this pilot.

The native zero calibration separately uses analytic multipliers Fᵏ that
vanish at an actual certified critical zero. Four contour integrals distinguish
the nonzero residue of F′/F from the zero residue of derivatives of F⁻ᵏ.
They use a local zeta Taylor polynomial with a rigorously bounded twelfth
derivative remainder, so the enclosures cover actual zeta values. The failed
direct-quadrature preflight is retained with its original source and parameters;
it consumed no discovery-final inputs. This guided calibration is separate
from numerical filter selection.

Reconstructing reciprocal zeta from its logarithm costs an exponential.
The detector charges that cost at a declared point away from D zeros.
An all-height quantitative bound needs an additional removable-division
certificate; qualitative zero-faithfulness does not supply it. The surviving
filters have not demonstrated a uniform arithmetic advantage over the
unfiltered prime-error baseline. **All RH-strength signed bounds remain open.**
Proof: `prime_error_proof.txt`.

## Actual-prime density and signed pair information

The separate floor-carry grammar enumerates integer vectors
\((1,c_2,\ldots,c_6)\) within a declared coefficient budget. It certifies
zero drift and every cell of the complete period of
\(K(u)=\sum_d c_d\lfloor u/d\rfloor\). A nonnegative period table proves
nonnegativity for every real input, including discontinuity endpoints.
No expected winning vector is supplied to the discovery runner.

The frozen `prime-discrepancy-results/pilot-001` run passed 12/12 independent
checks. It enumerated 16,807 floor programs and proved 16 universal positive
periodic certificates. Its selected kernel is
\(K(u)=\lfloor u\rfloor-2\lfloor u/2\rfloor\), yielding
\(\psi(x)\le(359/128)x\) for every real \(x\ge1\).

The factorial identity

\[
\sum_{n\le N}\Lambda(n)\lfloor N/n\rfloor=\log(N!)
\]

turns these certificates into actual-prime density bounds. An elementary
factorial remainder, dyadic summation and a complete finite patch give a
proved bound \(\psi(x)\le C_\psi x\) for every real \(x\ge1\).
This stage imports no prime-distribution estimate. It recovers a classical
type of density information; historical novelty is not an acceptance gate.

Let \(U_\beta\) interpolate the integer values of
\(\operatorname{li}(n)-\beta\sum_{m<n}\lambda(m)\), and let
\(a_n=U_\beta(n)-U_\beta(n-1)\). These increments preserve signed arithmetic
prime-power discrepancies. The density bound and an explicit monotone tail
prove

\[
\sum_{n\le N}a_n^2\le C_a\frac{N}{\log(e+N)},\qquad N\ge1.
\]

For a finite signed filter \(T(t)=\sum_d c_dU_\beta(t/d)\), complete ramp
Gram integration separates

\[
A_2(X)=D(X)+C_{\mathrm{off}}(X),\qquad
D(X)\le3C_a\Bigl(\sum_d|c_d|\Bigr)^2\frac{X^2}{\log(e+X)}.
\]

**These all-scale prime and diagonal bounds are unsigned.** The missing
signed information is in the pair terms \(C_{\mathrm{off}}\). Regression
and generic rational grids learn possible estimates

\[
C_{\mathrm{off}}(X)\le\rho D(X)+BX^\gamma,
\qquad\text{every integer }X\ge1.
\]

For matched prime error \(\beta=1\), \(\rho>-1\) and \(\gamma\le2\) would
give an RH-sufficient global moment bound. At \(\rho\le-1\), the separate
exponent rule rejects impossibly strong estimates using an actual enclosed
critical-line zero. The logarithmic residue bridge permits isolated zeros
of the filter multiplier. A bounded interpolation error preserves that
ordinary-zeta bridge.

The search uses all 228 parent programs regardless of their prior final
outcomes. Candidates are frozen before discovery-validation and the archive
is sealed before fresh final windows. The checker uses a prime-power sieve,
an alternative logarithmic-integral evaluation, exact Simpson integration
on every polynomial cell, and separate per-increment ramp Gram integration.
Positive-support controls never receive the actual-prime density certificate.
Finite cancellation success is a conjectural signed premise. **No uniform
signed pair bound, and no RH proof, is established.**
Proof: `prime_discrepancy_proof.txt`.

The run inferred 32,357 estimates from 228 programs and archived 24.
Twenty-two passed the fresh windows; 19 are RH-sufficient if uniform.
Both globally impossible diagnostics failed at the larger final windows.
The final complete coefficient prefix is 16,384. A surviving unfiltered
candidate is \(C_{\mathrm{off}}(X)\le147/512\); another claims
\(C_{\mathrm{off}}(X)\le-31D(X)/32+41571/1024\).
The actual-prime density finite patch through 8,192 belongs to development
evidence. Final window starts were drawn after sealing; their observables
are newly evaluated, and some coefficient prefixes overlap that proof patch.
The final evaluation tests the declared moment claims, without asserting
that every underlying arithmetic coefficient was previously unseen.

## Fractional arithmetic twists and signed negative decay

The general arithmetic grammar now allows finite rational polynomials in
\(\tau_a f(n)=n^{-a}f(n)\), including square, cubic and sixth roots and
arbitrary positive rational shift denominators. The pilot's denominator
budget does not limit the semantics. There are two channels, using
\(\lambda(p^k)=1/k\) and \(\Lambda(n)=\lambda(n)\log n\), and independent
smooth normalizers. Signed polynomials are admissible even when their
arithmetic weights are neither positive nor multiplicative.

The growth grammar permits negative rational exponents. At a negative
output Mellin exponent, it requires the exact compiled finite-part center,
rather than a nearby rational fitted from data. For example, the harmonic
log channel has center \(\gamma-\log 2\). Fractional normalizers have
explicit regular conventions at their zero exponent.

The factorial trace and the preceding density certificate prove

\[
-1\le Q(x):=\sum_{p^k<x}\frac{\log p}{p^k}-\log x
\le\frac{359}{128},\qquad\text{every real }x\ge2.
\]

Partial summation then gives

\[
\left|\sum_{p^k<x}\frac1{k p^k}-\log\log x-\gamma\right|
\le\frac{487}{128\log x},\qquad\text{every real }x\ge2.
\]

More generally, the centered signed tail for the paired fractional twist
of order \(\nu\ge1\) is bounded by
\((487/128)x^{1-\nu}/\log x\), uniformly for every real \(x\ge2\)
and every real \(\nu\ge1\). These are supplied, independently checked
arithmetic proof backends. They do not claim autonomous proof invention or
historical novelty. **They remain below RH strength:** recovering ordinary
zeta charges the leading twist, so \((1-\nu)+\nu=1\).

For learned integer decay \(n^\theta\log(e+n)^\ell\), the ordinary-zeta
exponent is

\[
\eta=\max(\theta,-a)+\nu,
\]

where \(a\) is the smallest shift in either arithmetic coefficients or
normalizers, and \(\nu\) is the leading nonzero arithmetic shift.
The unit-interval prime jumps and the cost of undoing that shift are charged.
A uniform bound with \(\eta\le1/2\) would suffice for RH. The proof follows
a finite chain of right-shifted zero multiplicities until it reaches the
zero-free Euler half-plane; local cancellations of coincident shifted zeros
are allowed. Quantitative recovery charges every recurrence path and, for
the log channel, integration from an Euler endpoint.

The stronger harmonic target \(|Q(x)+\gamma|\le
C x^{-1/2}\log(e+x)^\ell\) is an RH-sufficient open premise. The verified
boundedness of \(Q\) does not assert this decay or even its limiting center.

Stronger false controls agree with actual \(\lambda\) through 8,192, then
use \((1-n^{-\delta})\lambda(n)\), for
\(\delta=1/6,1/4,1/3\). They preserve every actual prime-power location,
obey the same global prime-density bound and retain the preceding diagonal
bound. Their original \(1/k\) weights change above the cutoff. With the
original logarithmic-integral normalizer, an extra pole logarithm at
\(1-\delta>1/2\) makes a uniform RH-strength bound impossible. Native
singular-part integrals and pole-neutral zeta enclosures check that
obstruction. The purpose is to distinguish signed arithmetic control from
prime support, density and finite-window agreement.

The protocol freezes every candidate before validation and seals the archive
before fresh final points, unrelated signed-input arrays and complete moment
windows are generated. Final window starts exceed the prior coefficient
cutoff. Their cumulative arithmetic prefixes still overlap development
data; complete disjointness of the underlying coefficients is not claimed.
All RH-strength uniform decay premises remain unproved.
Proof: `prime_twist_proof.txt`.

The pilot passed 14/14 independent audit groups. It generated 1,223 programs
and 42,745 estimates, archived 20, and checked a complete coefficient prefix
through 64,320. Sixteen archived bounds passed the fresh points; fifteen
would suffice for RH if uniform, including one with negative growth.
That lead is the paired weighted twist of order \(2/3\), with its exact
Mellin center and a conjectural bound \((37/64)n^{-1/6}\).
The charged ordinary-zeta exponent is \(-1/6+2/3=1/2\).
No bound rejected by that pilot's pole and isolated-zero gates passed the
fresh points. The later oscillation audit below rules out one of these
finite survivors globally. All three
attenuated controls failed every one of the three source moment bounds on
each complete fresh window. Their density and diagonal bounds still hold.
The source code, final cases, deterministic replay and rejected candidates
are retained. Evidence figure:
`prime-twist-results/pilot-001/prime_twist_evidence.pdf`.

The independent coverage extension tested all 20 frozen archived estimates
at **every integer through 131,072**, using 2,621,440 interval comparisons.
It also checked all three unfiltered signed pair bounds at every complete
window start through 65,536, giving 196,608 moment comparisons. All fifteen
then-compatible point estimates and all three pair bounds passed. These
are exhaustive finite calculations; the following analytic gate shows that
even such coverage can retain a mathematically impossible uniform bound.
Report: `prime-twist-coverage-results/coverage-001/report.txt`.

## Oscillation compatibility and automatic positive-log repair

The original pure \(\sqrt{x}\) \(\Lambda\)-channel target survives the
entire numerical prefix but is false over all scales. The named classical
[Hardy-Littlewood paper, section 5.1](https://mwolf.pracownicy.uksw.edu.pl/Hardy_Littlewood%20zeta.pdf)
gives \(\psi(x)-x=\Omega_\pm(\sqrt{x}\log\log\log x)\).
This oscillation theorem is an **external import**. Its classical proof has
not been independently re-proved or machine-formalized here.

The new gate applies to a general program class. A normalized finite signed
polynomial in positive rational arithmetic shifts is eventually positive.
An exact rational certificate bounds its inverse and derivative there.
Stieltjes integration then shows that a compensated pure critical-power
\(\Lambda\)-channel point bound would imply
\(\psi(x)-x=O(\sqrt{x})\), which contradicts the import. This covers
fractional monomials, negative output growth and signed polynomials, rather
than relying on a named candidate formula.

The full 42,745-candidate batch received 894 rejection certificates across
482 eventual-inverse programs. One archived finite survivor is thereby
ruled out. The fourteen remaining original RH-compatible finite estimates
use the weighted \(\lambda\) channel. Its inverse to \(\psi\) introduces
a logarithmic loss and is outside this rejection rule.

Every positive rational log-power remains eligible in the \(\Lambda\)
channel. The selector automatically chose a repair already present in the
original candidate batch, using discovery-validation and full recovery cost.
The selected repair was sealed before evaluation on **every integer from
131,073 through 201,481**. All 70,409 independent interval comparisons passed,
and the audit passed 10/10 groups. Its still-unproved uniform target is

\[
\left|n-2-\sum_{p^k<n}\log p\right|
\le\frac{231}{1024}\sqrt n\log(e+n),\qquad
\text{every integer }n\ge2.
\]

This target would suffice for RH if proved uniformly. Compatibility with
oscillation and complete finite success do not prove it. All original source
code, candidate formulas, fitted constants and finite outcomes are retained;
the later gate supersedes their plausibility interpretation. The proof of
the inverse/Stieltjes consequence and its imported dependency are explicit
in `prime_oscillation_proof.txt`. Current report:
`prime-oscillation-results/audit-001/report.txt`.

## Known imported all-scale signed calibration

The separate `signed-global-results/calibration-001` stage passed 6/6 checks.
It combines a complete independent μ and M check through 1,798,118 with the
explicit infinite-range bound in Ramaré and Zuniga Alterman,
[arXiv:2408.05969v2, Theorem 1.1](https://arxiv.org/abs/2408.05969v2).
The source PDF, version, threshold and hash are pinned. **The imported
analytic argument and its prime estimates have not been independently
re-proved.**

The independently audited finite patch and concave interpolation yield

\[
|\widetilde M(t)|\le\frac{85}{64}\frac{t}{\log(e+t)},\qquad t\ge0.
\]

Explicit dilation costs transfer this signed o(t) control to the eight source
residuals and their moments. Positive and delayed-positive controls violate
the uniform sublinear claim. The result depends on the named signed import;
it proves neither additional filter cancellation nor RH-strength control.
It establishes a useful calibration that distinguishes actual global signed
control from unsupported extrapolation. Proof: `signed_global_calibration_proof.txt`.

## Results that survived numerical and analytic scrutiny

The primary `mellin-search-results/pilot-001` run generated 255 programs and
sealed eight. Its independent audit passed 11/11 checks, including deterministic
selection replay, exact rational Schur recursions, independently computed
reciprocal coefficients, actual-zero checks, an independent complete μ prefix
through 929,168, and 352 exact complete-window moment values.

Nine viable archived moment obligations passed the fresh windows. Six have
η=1/2, so their **unproved uniform premises** would suffice for RH. These are
proof obligations, not verified arithmetic estimates.

Finite survival does not demonstrate that these filters improve arithmetic
control compared with M itself. A rejected growth fit is an objection to that
estimate, not to the underlying operator. Broader growth models and uniform
defect inequalities remain necessary parts of the estimate search.

For example, exact weighted least squares produced

\[
R(t)=\widetilde M(t)-\frac{65}{128}\widetilde M(t/2).
\]

Its fitted quadratic obligation is

\[
\forall X=2^j\ge1,\qquad
\int_X^{2X}|R(t)|^2dt\le\frac{1075}{1024}X^2.
\]

The tested complete windows satisfy it. **No argument presently proves it for
every dyadic scale.** A different finite uniform constant would also suffice;
the proof search need not reproduce this particular fitted constant.

The earlier signed pilot generated 292 programs and passed 8/8 independent
checks. The subsequent polynomial expansion generated 249, certified 151
all-height multipliers, including 46 beyond triangle contraction, retained 98
unsupported programs, and also passed 8/8 independent checks. These counts
describe separate runs and do not measure distinct historically new operators.

An additional analytic audit of those two earlier pilots examined 541 programs
and 2,164 moment estimates, passing 6/6 independent checks. It ruled out
**43 estimates that nevertheless passed all their finite final windows**.
Two archived estimates survived that obstruction. This audit used already
inspected data, made no reselection, and made no fresh held-out claim.

The core earlier catalogue remains ten families, twenty arithmetic consequences,
and 150 complete native-zeta comparison groups. New stages retain separate
scope and counts. None of those counts constitutes an RH proof.

## Isolating the arithmetic that still needs a proof

The quadratic moment has a universal exact correlation rewrite. Set

\[
\phi_n(u)=\max(0,\min(1,u-n+1)),\quad
\psi_n(t)=\sum_j c_j\phi_n(t/b^j),\quad
K_X(n,m)=\int_X^{2X}\psi_n(t)\psi_m(t)dt.
\]

Then

\[
A_2(X)=D(X)+C_{\rm off}(X),
\]

\[
D(X)=\sum_n\mu(n)^2K_X(n,n),\qquad
C_{\rm off}(X)=\sum_{n\ne m}\mu(n)\mu(m)K_X(n,m).
\]

Writing S=Σ|c_j|, the diagonal has the **proved all-scale bound**

\[
0\le D(X)\le2S^2X^2.
\]

Thus one possible sufficient arithmetic target is

\[
\forall X=2^j\ge1,\qquad C_{\rm off}(X)\le KX^2
\]

for some finite K≥0. This would prove the quadratic moment estimate with
constant 2S²+K. The signed off-diagonal bound is unproved. The kernel identity
and the diagonal estimate do not supply it. Removing arithmetic signs gives
only a generic O(X³) energy estimate; the positive control attains that order.

The diagnostic computes D exactly from μ² and nμ² prefixes, with the exceptional
n=1 term integrated separately. Independent tests integrate each individual
ramp squared, including boundary windows, without using the fast prefix formula.
`correlation_obligations.json` contains the exact signed off-diagonal values for
each archived operator. These use already inspected finite moments.

There is also a more flexible sufficient recurrence:

\[
\forall X=2^j\ge1,\qquad A_2(2X)-4A_2(X)\le BX^2.
\]

It implies A₂(X)=O(X² log X), which still makes the Mellin transform holomorphic
on Re(s)>1/2. The general backend permits signed recurrence coefficients:
for d=q/2+1, a uniform A_q(2X)−ρA_q(X)≤BXᵞ with ρ≤2ᵈ and γ≤d gives
an RH-sufficient logarithmic moment bound. Its uniform premise is unproved.
The proof search can therefore pursue a defect inequality rather than requiring
a perfectly fitted pure-power constant.

The frozen `signed-defect-results/pilot-001` search inferred 1,583 recurrence
estimates from complete moments and archived twelve. Its independent audit
passed 9/9 checks, including 1,088 exact actual moment values and 96 exact
delayed-positive control values, with a complete coefficient prefix through
821,556. All twelve archived recurrences passed the fresh complete windows;
eleven are RH-sufficient **if their uniform premises can be proved**.

For example, the original Möbius sum produced the lead

\[
A_2(2X)-4A_2(X)\le\frac{1515}{512}X^{31/16}.
\]

The multiplier four was inferred from cross-scale responses. A uniform proof
would imply an RH-sufficient quadratic moment bound; no such proof has been
obtained. Several surviving obligations use the original sum. This search
does not demonstrate an advantage of the filtered operators over that baseline.

## Fractional arithmetic remainders and infinite parameter families

The new `fractional_remainder_search.py` stage varies a fractional arithmetic
logarithm and its continuous counterpart together. For order \(0\le\beta\le1\),

\[
T_\beta=\mu*D_\beta 1,\qquad
J_\beta(y)=\int_1^y(\log t)^\beta\,dt,\qquad
R_\beta(x)=\sum_{n\le x}T_\beta(n)-\sum_{d\le x}\mu(d)J_\beta(x/d).
\]

The logarithmic weight at index one is zero even at order zero. This makes
\(R_0(x)=1-x\sum_{d\le x}\mu(d)/d\), rather than a constant or a unit operator.
Positive rational orders have no semantic denominator ceiling. The search
forms signed rational combinations at orders \(ja\), with independently
chosen continuous normalizers. It learns coefficients and growth exponents,
promotes useful compositions by a frozen rule, and runs an equal proposal
budget ablation. The supplied primitives and proof methods remain explicit
design assumptions.

The continuous correction removes the fractional singularity at zeta's pole.
Its Mellin numerator is an entire function of \(s\), checked numerically by
different native difference and derivative integrals with certified infinite
tails. For compensated positive orders, a fixed nonzero family has a nonzero
parameter-pole residue at its first negative-order boundary. The identity
theorem therefore prevents *all* its fractional orders from erasing the same
ordinary zeta zero. This applies even when several small-order terms cancel.
It supplies a qualitative bridge at every height without a scalar
nonvanishing requirement on each individual fractional order.

The exact missing premise is a bound such as

\[
|V_{a_q}(n)|\le C a_q^\kappa n^{1/2}\log(e+n)^\ell,
\qquad a_q=\frac1{\max(1,D)q},
\]

for **every integer \(n\ge1\) and every integer \(q\ge2\)**. A finite
parameter grid cannot supply that premise. A fixed fractional numerator can
cancel a zero, so it is not assigned the family's all-height conclusion.

The backend proves weaker signed parameter cancellation and bounds on unit
increments over every real scale, using the actual prime-factor structure
of the coefficients and full native Cauchy covers. Their growth exponent in
\(x\) is one, so they do not establish RH or a new prime-distribution estimate.
The exact parameter vanishing order also rejects claimed decay faster than
the family can have at a fixed integer. Conditional reciprocal costs include
the small numerator, parameter power and correction from integers to reals;
small numerical amplitude alone is not evidence of stronger zeta control.

The code's mathematical backends are supplied proofs, not autonomous proof
invention, and have not been machine formalized. Earlier Mobius data and
implementation preflights are development evidence. Fresh final scales and
fractional parameters are generated after the archive is sealed.

Run a fresh experiment through `run_expanded_probe.py --fractional-remainders-only`
with an optional `--fractional-remainders-run-dir`. Earlier sealed stages and
the exact seventeen-loader integration snapshot are retained.

A later generic limit audit checks pure square-root, parameter-power-zero
bounds against their \(a\to0\) limit. It writes that limit as
\(S-Bxm(x)+(B-S)M(x)\), then charges a rational Volterra inverse before
comparing its recovered constant with a named Mertens extremum lower bound.
The dependency is [Hurst's primary paper, Theorem 6.1](https://arxiv.org/pdf/1610.08551v2).
Its large numerical zero/phase computation is imported and has not been
independently reproduced here. Positive log losses and vanishing limit
families remain eligible. Repairs are chosen from the original frozen
candidate batch without refitting and sealed before new evaluation.
The later gate supersedes plausibility counts in the original fractional
report; its successful finite computations and proof identities are retained.

## Complete arithmetic tails and bounds approaching the critical exponent

The new kernel stage changes two restrictions in the earlier numerical searches.
It encloses infinite inverse-arithmetic sums, and it permits growth bounds whose
exponents approach the critical line with separate constants for each parameter.
Neither change proves the signed growth estimate.

For rational \(k>1\), \(\ell>0\), \(b>1\), and finite rational coefficients,

\[
K(y)=\sum_{m,j}c_{m,j}(b^j y)^m e^{-b^j y},\qquad
F_K(X)=X^k\sum_{n\ge1}\frac{\mu(n)}{n^k}K((X/n)^\ell).
\]

All positive rational root exponents are legal. A pilot's finite moment,
dilation, precision and proposal budgets are recorded resource limits.
The grammar admits signed mixtures, small-argument moment nullspaces, learned
response combinations, promoted dilations and Euler derivatives. It does not
require positivity or a scalar nonvanishing certificate before preserving a lead.

Every numerical sum includes its infinite arithmetic tail. The evaluator uses

\[
\sum_{n>N}\mu(n)n^{-w}
=\zeta(w)^{-1}-\sum_{n\le N}\mu(n)n^{-w},\qquad w>1,
\]

in a Taylor expansion with an explicit rigorous remainder. Precision increases
to resolve that subtraction. This identity includes actual arithmetic at every
index, using ordinary zeta only in its established absolute-convergence region.
It supplies no new prime-distribution bound. Independent checking uses a
factorized inverse sequence, different cutoffs and a different tail expansion.

The Mellin transform is

\[
H_K(s)=\frac{\Gamma(v)P_K(v,b^{-v})}{\ell\zeta(s)},\qquad
v=(k-s)/\ell,\quad P_K(v,z)=\sum_{m,j}c_{m,j}(v)_m z^j.
\]

The certificate search can find exact rational polynomial identities

\[
\sum_i A_i(v,z)P_{K_i}(v,z)=(v)_r z^h.
\]

Their right side is nonzero for \(\operatorname{Re}v>0\), \(z\ne0\).
Consequently these kernels cannot all hide an ordinary zeta zero, at any height
or multiplicity. A failed bounded identity search leaves recovery unresolved.
The resulting native costs charge the gamma factor and every contributing
kernel; a very small smoothed response does not give control for free.

The growth target is now

\[
\forall q\ge2\ \exists C_{i,q}<\infty\ \forall N\ge1:\quad
|F_{K_i}(N)|\le C_{i,q}N^{\eta+\epsilon/q^\nu}\log(e+N)^d,
\qquad \epsilon,\nu>0.
\]

There is no prescribed growth rate for the constants as \(q\) increases.
At \(\eta=1/2\), a bank with the exact recovery identity gives an RH-equivalent
target. The necessity direction uses the named classical RH consequence for
the Mertens sum in Titchmarsh's Theorem 14.25(C); that conditional theorem is
not used as a proof of any new estimate. The sufficient direction is the
bank's continuation argument. For each ordinary zero right of \(\eta\),
all sufficiently large \(q\) give exponents below that zero. Finite \(q\)
grids never establish the premise. New parameter constants are calibrated
on frozen training scales and sealed before fresh final scales are generated.

This also clarifies the earlier fractional-remainder family: cofinal exponents
and freely varying constants still fit its parameter identity-theorem argument.
The earlier common-constant amplitude and small-order Mertens rejections apply
to their original frozen targets, not automatically to this new quantifier order.

The all-scale certificate attempt proves \(|F_K(X)|\le W_K X\), and a uniform
derivative bound that controls the gap between consecutive integers. It also
proves the exact signed forcing equation

\[
\sum_{d\ge1}F_K(X/d)=X^kK(X^\ell).
\]

The absolute envelope does not close the required sublinear signed estimate.
The forcing equation alone supplies no contraction at the critical exponent.
A control that adds (+1) beyond a very large arithmetic cutoff can pass every
finite test; its Mellin pole at one proves that its critical cofinal bound is
false. These controls are explicitly counterfeit arithmetic, not prime data.

The new source and proof are in `mellin_kernel_grammar.py` and
`mellin_kernel_proof.txt`; the strict loader is `mellin_kernel_report.py`.
The numerical pilot and its independently checked counts are scoped separately
from the existing ten-family catalogue. **All RH-strength uniform signed
estimates remain unproved.**

## What the next search must improve

The unresolved task is a proof of a signed arithmetic correlation, moment
defect or coupled parameter-family bound over every scale. The tool must infer such estimates from actual
arithmetic and discharge their universal premises with independently checked
arguments. More filters, finite matches, or operator safety certificates alone
will not finish the objective.

The representations should expose explicit two-index correlation kernels,
parameter jets and their quotient, residue and divisor relations, then learn recurring
signed structures or scale inequalities. Prime labels and factor queries belong
in the evaluator when the producer claims to use no oracle. Useful structures
should be promoted by frozen rules, with unsupported leads retained and fresh
final data after any outcome-driven revision. The earlier autonomous-language
stage supplies generic index, sequence and matrix constructions and its own
promotion ablation; no improvement claim follows merely from naming more filters.

The remaining design assumptions are explicit: the source operator search
uses six integer bases, degree at most four and rational coefficients. The
new fractional stage reuses eight sealed residuals and samples rational moment
orders under a declared denominator budget. Its machine protocols record fitting, rounding,
promotion, resource and selection rules. It is answer-independent within that
representation, not an assumption-free search. The coefficient/kernel search
independently varies its three parameters within finite declared budgets. The
parameter-jet identity recovery is guided calibration; its derivative operation
is general, while the recovered prime-error formula was nominated before its
independent numerical audit. The named global calibration imports a proved
signed estimate and does not count as discovery of that estimate.

## Complete signed correlations and squarefree density corrections

The new grammar searches quadratic observables of the complete inverse-kernel
responses. For two kernels at the same rational parameters, write
`F_i(X)=sum_(n>=1) mu(n)*(X/n)^k*K_i((X/n)^ell)`, with `k>1` and
`ell>0`. A rational symmetric matrix `H` produces the exact decomposition

`E_H(X)=F(X)^T H F(X)=D_H(X)+C_H(X)`.

`D_H` includes the actual squared inverse coefficients `mu(n)^2`; `C_H`
includes every signed pair with distinct indices. Both use the whole infinite
arithmetic sequence. Multiplying kernels creates arbitrary positive rational
rates `r+s`, retaining the signed cross coefficients. The producer computes
complete tails using absolutely convergent reciprocal-zeta and
`zeta(w)/zeta(2w)` moments at real `w>1`. No RH assumption enters those
numerical inputs. The verifier uses independently factored coefficients,
different prefixes, higher precision, extra Taylor terms and reverse summation.

An elementary all-scale certificate follows from square-divisor inversion:

`mu(n)^2=sum_(d^2 divides n) mu(d)`,

`|sum_(n<=x) mu(n)^2-x/zeta(2)| <= (5/2)*sqrt(x)`, for every real `x>0`.

Partial summation then proves a signed correction bound for every generated
diagonal, including indefinite ones:

`Z_H(X)=D_H(X)-A_H*X`,

`|Z_H(X)| <= V_H*sqrt(X)`, for every real `X>0`.

`A_H` is the exact continuous kernel integral divided by `zeta(2)`. Its
coefficients retain their signs; the variation constant `V_H` uses absolute
coefficients. This is actual arithmetic information over all scales, derived
without an imported prime-distribution estimate. It does not control the
signed off-diagonal contribution at RH strength.

The correlation target is, for fixed `H` and rational `rho`,

`for every q>=2 exists finite B_q: for every integer N>=1,`

`C_H(N) <= rho*D_H(N)+B_q*N^(2*(1/2+epsilon/q^nu))*log(e+N)^d`.

Positive semidefinite matrices are factored over the rationals into active
kernel combinations with strictly positive pivots. Singular matrices can
recover zeta through one effective combination. Every pivot and combination
amplitude is retained in the conditional Mellin cost. An exact all-height
certificate for the effective bank makes this cofinal target RH-equivalent.
Indefinite metrics remain signed numerical leads with a missing coercive
recovery method. Their upper bounds do not bound constituent absolute responses.

The density target asks for a stronger bound on `Z_H` itself:

`for every q>=2 exists finite C_q: for every integer N>=1,`

`|Z_H(N)| <= C_q*N^(1/4+epsilon/q^nu)*log(e+N)^d`.

The limit is one quarter because the raw diagonal Mellin transform contains
`W_H(s)*zeta(s)/zeta(2s)`. Its pole at one has residue `A_H`, which is removed
by the exact centering. A common-rate polynomial certificate can prove that
`W_H` does not cancel any relevant denominator zero, at every height and for
every multiplicity. Multiple rates and unsupported polynomials are retained
with missing certificates.

Possible cancellation by the numerator `zeta(s)` is included in the ordinary
zero argument. If a hypothetical zero `rho` has `Re(rho)>1/2`, holomorphy of
the quotient at `rho/2` would force a numerator zero there with at least the
same multiplicity. The functional equation and conjugation then force another
zero at `1-conjugate(rho)/2`, still right of the critical line, with half the
height. Iterating gives zeros accumulating at `2/3`, where zeta is nonzero.
This contradiction supplies an all-height RH bridge. Under RH, the parent's
named conditional Mertens bound and exponential Gamma decay give the converse
smoothed density estimate. Neither direction proves a new unconditional
quarter-power bound.

All positive rational approach powers `nu`, including fractional roots, are
allowed by the semantics. Each `q` has its own free constant; no common bound
or growth law for those constants is imposed. Finite parameter grids never
establish either global target. The density observer charges its local
integral, pole subtraction, unit increments, kernel Gamma factor and the
additional numerator-zeta factor needed to recover `1/zeta(2s)`.

The frozen pilot has 426 correlation programs, 80 density programs and 27,288
primary growth hypotheses; 29,376 hypotheses include the equal-slot ablation.
Generation learns rank-one combinations and positive covariance metrics from
anonymous training responses and promotes rational matrix congruences.
Eight singular energy programs have all-height recovery; 68 indefinite
programs remain in the primary archive of generated forms. Thirty density
forms have certified quarter-power recovery. The finite selected archive and
fresh results are in `kernel-correlation-results/pilot-002/report.txt`.
Promotion and random-slot ablation have the same best conditional cost in
this pilot; improved search performance from promotion is not established.

The generator receives only parent kernel forms and pair membership. It
cannot read parent outcomes, literature, network services or private final
cases. Candidates are frozen before validation. New `q` values are drawn
after selection, and their constants are calibrated only on the frozen
training scales and sealed before fresh scales are drawn. A checker
record-format failure in `pilot-001` is retained with its original sources and
final cases. The corrected run excludes those cases and parameters.

Negative controls include a counterfeit inverse tail beyond `2^200` and a
tiny but wrong density normalization. An uncancelled pole at one makes their
global sublinear targets false even when the finite comparisons pass. The
counterfeit's diagonal is explicitly the actual arithmetic comparator; no
counterfeit pair decomposition is asserted. Missing recovery certificates
and failed fitted constants are separately classified.

The new signed diagonal theorem has a square-root remainder. RH needs the
quarter-power density estimate or the critical signed correlation estimate.
Both uniform obligations remain open. The proof methods were supplied and
independently coded; this stage does not claim autonomous proof invention,
historical novelty, a new prime-distribution theorem or machine formalization.

## Typed lattice synthesis and complementary fractional dilations

The lattice stage expands arithmetic dilations to every rational `r>1`,
including fractional values between one and two. For a signed rational kernel
`Q(y)=sum c_m (R*y)^m exp(-R*y)`, define

```text
G(Y)       = sum_j (Y/j)^K Q((Y/j)^ell)
D_mu,r(X)  = sum_d mu(d) G(X/d^r)
Z_mu,r(X)  = D_mu,r(X) - I*X/zeta(r),   I = integral g(u) u^(-2) du
```

The complete arithmetic positions are `j*d^r`. Integral `r` recovers the
`r`-free integer indicator. Fractional `r` gives a generalized signed measure;
its positivity is not assumed. Exact rational comparisons select the finite
prefix, and rigorous Taylor tails enclose every remaining position. The
Mellin profile of the actual arithmetic is `W(s)*zeta(s)/zeta(r*s)`.

A separately typed reference substitutes coefficient one for `mu(d)`, with
profile `W(s)*zeta(s)*zeta(r*s)`. The detector learns signed rational kernel
coefficients from anonymous raw reference-response tables. The learner receives
neither pole locations nor Gamma residues. A later exact validator determines
whether a proposal annihilates either or both residues. Such annihilation is
recorded as a discovery result only when the rational coefficients give exact
zeros, rather than merely a small numerical residual.

The global proof grammar can certify estimates itself in the reference model.
For any positive rational `a`, after subtracting its exact residues at `1` and
`1/r`, the reference response satisfies `|R_1,r(X)|<=C_a X^(-a)` at every real
positive scale. The detector chooses among a frozen grammar of Gamma-integral
rotation angles. Each choice has an explicit bound on the entire vertical
contour, including a polynomial height factor and its complete integral. The
constant comes from the proof, not from a finite regression.

These reference theorems have no RH consequence. A proof certificate records
its arithmetic model, and the detector rejects an attempt to apply a unit-model
certificate to the inverse model. The actual reciprocal denominator introduces
the unknown-zero obstruction that the reference model lacks.

The actual arithmetic does have an elementary all-scale weak estimate,
`|Z_mu,r(X)|<=V X^(1/r)`. Its exponent normalized to ordinary zeta is always
`r*(1/r)=1`. Choosing a larger `r` makes the displayed power smaller without
strengthening the ordinary-zeta conclusion. The critical target remains

```text
for every q, there exists a finite C_q, for every integer N>=1:
|Z_mu,r(N)| <= C_q N^((1/2+epsilon/q^nu)/r) log(e+N)^d.
```

Each `q` and each bank member has its own free constant. Positive rational
`ell`, `nu`, decay orders and arithmetic dilations have no semantic denominator
ceiling; the particular enumeration and Taylor budgets are declared resources.
An independently certified derivative bound extends integer estimates to real
scales. It includes a separate small-scale majorant because the infinite
dilation sum samples `X/d^r<1` even when `X` is large.

The detector also certifies a useful limitation of an entire proof method.
The exact actual rewrite is
`Z_mu,r(X)=sum_d mu(d)*(G(X/d^r)-I*X/d^r)`.
For every nonzero common-rate kernel, taking absolute values on the right
produces an expression bounded below by a positive multiple of `X^(1/r)`.
The obstruction persists when the actual squarefree support `|mu(d)|` is
retained, and when both reference residues vanish. A local leading-term
certificate and the elementary squarefree count prove this globally. This
rules out the supplied absolute-norm proof method at critical strength; it
does not refute the signed estimate. A successful backend must exploit the
orientation of the actual Möbius signs.

Recovery is broader than demanding a zero-free multiplier halfplane.
All real roots of the finite Mellin polynomial are safe: they cannot mask
nonreal ordinary zeros. The producer supplies an exact Hermite matrix
factorization, while the independent checker counts real roots using Sturm
sequences. Complex operator roots can also be safe. Exact strip exclusions or
complete disjoint Rouché disks and native zeta enclosures establish their
noncoincidence with any right-half ordinary zero. This covers every operator
root and all possible zero heights, rather than sampling known zeta zeros.
An unavailable certificate remains an unresolved recovery obligation.

For `1<r<2`, a zero-preserving critical estimate implies that any possible
right-half ordinary zero has its real part in the finite exact set
`E_r={r^j/2 : j>=1 and r^j<2}`. The cancellation chain divides a right-half
zero by `r`, or reflects the resulting left-half zero, retaining multiplicity.
Outside those exceptions, heights contract to zero and real parts contract to
`r/(r+1)`, where zeta is nonzero. The critical-line numerator can mask a
denominator zero at an exceptional real part, so an individual fractional
constraint is not automatically RH.

The detector assembles banks by intersecting independently complete exception
sets. An empty intersection would imply RH if every member's actual cofinal
bound were uniformly true. The dilation factors are drawn from a frozen
rational enumeration before response data; the generator contains no nominated
winning pair. Bank assembly proves the conditional implication, not its signed
arithmetic premises. The run retains every member, its free constants, and all
observer costs; an unavailable observer cannot be silently dropped.

The stage includes a fixed baseline, anonymous response learning, automatically
promoted Euler derivatives, and an equal-slot random-shape ablation. Its
protocol and source hashes precede evaluation. Discovery and parameter
calibration processes are denied parent outcomes, full parent candidate data,
literature, network access, subprocesses and private final scales. Fresh-`q`
constants use only sealed training data and are sealed before fresh scales.
Independent verification changes prefix cutoffs, Taylor lengths, precision,
summation order and root methods; deterministic producer replay runs separately.

The supplied proof grammar, linear common-rate language, sampling resources
and ranking criteria remain design assumptions. Reference-model theorems,
weak actual estimates and complementary conditional bridges supply no new
uniform prime-distribution estimate. RH-strength signed estimates remain open.
The source proofs and current scoped results are in
`lattice_synthesis_proof.txt` and `lattice-synthesis-results/latest.json`.

The verified `pilot-002` contains 551 primary programs and 19,836 primary
growth hypotheses (22,500 with the equal-slot ablation). All 17 independent
checks and the 16 public contracts pass. It supplies 2,204 proved reference
negative-power estimates and 551 actual-support sign-loss barriers. Six
complementary fractional banks were selected; three pass the fresh finite
tests. Twelve individual RH-if-uniform hypotheses and three quasi-RH
hypotheses also survive the fresh checks. These counts concern illustrative
fitted constants; they do not settle the existence of a uniform critical
bound. The weak actual frontier has a separate proved constant witness.

The anonymous learner made 24 proposals and recovered no exact two-pole
annihilator in this pilot. All 96 promotion slots were admitted, but the best
fully charged conditional observer cost equals the random-slot ablation's
cost. This run shows no improvement from promotion. These limitations are
retained alongside the successes. The failed first run preserves its original
source and final data; the corrected run excludes its final scales and `q`
values. The correction concerns comparisons of precision-dependent native
bound endpoints, not the candidate formulas or search rules.

A separate post-run generic calibration independently evaluates complete
arithmetic for `ell=1/2,1/3,1/6,1/10007`. It verifies square, cube, sixth and
10007th-root semantics, plus a reference decay order `1/37`, with no change to
selection or fitted constants and no new fresh-discovery claim. The root
calibration does not prove an actual critical arithmetic estimate.

## Normalized arithmetic roots and signed profile learning

The root-lattice stage supports every positive rational arithmetic dilation
`r`, including `1/2`, `1/3`, and `1/6`. Smoothing exponents and approach rates
are positive rational parameters too. There is no semantic denominator cap;
the bounded pilot and numerical certificate resources are recorded separately.
Convergence requires `K>max(1,1/r)` and `ell>0`. Its pure-power kernel is

\[
g(u)=e^R u^K e^{-R u^\ell}\sum_m c_m u^{\ell m},\qquad R=K/\ell.
\]

The moment-zero peak is at `u=1`. Set

\[
D_r(X)=\sum_{j,d\ge1}\mu(d)g\!\left(\frac X{j d^r}\right),\qquad
V_r(M)=D_r(M^r)-A M^r.
\]

Here `M` means the positive arithmetic-index scale, not the Mertens sum used
earlier in this document. Comparing the same `M` across different `r` keeps the
ordinary-zeta exponent fixed. An apparently smaller power caused by changing
the scale variable is not stronger arithmetic control.

Complete moments `zeta(K+ell*h)/zeta(r*(K+ell*h))`, all evaluated strictly to
the right of one, give convergent whole-response Taylor sums with explicit
full-tail enclosures. The independent checker evaluates a separately factored
integer arithmetic rectangle using a prime sieve and a complete remaining
tail, with different Taylor length, precision and summation order. Thus a
sixth-root experiment does not enumerate a lattice of size `X^6` or replace
the actual arithmetic with a finite prefix.

If `W(s)` is the Mellin transform of `g`, the ordinary-index profile is

\[
\frac1r W(z/r)\frac{\zeta(z/r)}{\zeta(z)}.
\]

For `r!=1`, the known center is `A=W(1)/zeta(r)`. At `r=1`, exact arithmetic
factor cancellation gives `A=0`; this does not substitute a numerical infinite
value for `zeta(1)`. The observer charges the Jacobian `1/r`, normalized Gamma
and kernel polynomial, numerator zeta, the main pole, local integral, unit
increments and every positive approach-to-line gap.

For `0<r<1`, a certified cofinal bound

\[
\forall q\ \exists C_q<\infty\ \forall M\ge1:\quad
|V_r(M)|\le C_q M^{1/2+\epsilon/q^\nu}\log(e+M)^d
\]

would imply RH when the kernel preserves every possible ordinary right-half
zero. A denominator zero at `rho` would force a numerator zero at `rho/r`,
with at least the same multiplicity. Repeating division increases its real
part past one. The exact finite certificate `r^J<=1/2` covers every height;
no critical-line exception or zero-grid sampling is needed for these roots.
The uniform signed estimate is still an open premise. The supplied unsigned
count method proves only ordinary exponent one, with a bounded derivative in
the common arithmetic-index variable. Exhausted zero or Taylor resources
mean missing coverage, not a counterexample to an estimate.

The anonymous moment learner fits short recurrences on eight moments and
validates on held-out moments. It receives no arithmetic names, dilation,
factor ledger or expected relation. Only afterward can an exact supplied
factor-ledger certificate promote a recurrence to a universal operation and
compile its arithmetic support. Other fitted relations remain numerical
leads. Actual-centered response learning separately sees only numeric columns
and scales; it receives no pole locations. Frozen Euler-derivative promotions
are compared with an equal-slot random-shape ablation.

At `r=1`, the exact signed identity `mu*1=delta_1` makes the actual response
equal to `g(M)` over every positive real scale. The supplied signed proof
backend then proves `|g(M)|<=C_a*M^(-a)` for every rational `a>0`. This retains
the actual Möbius signs before estimating the remaining finite response.
It is a known signed-cancellation calibration. Its arithmetic profile cancels
ordinary zeta identically, so those true global estimates have no RH
consequence, even if a kernel-only zero-preservation certificate passes.

Two controls keep those distinctions visible. A counterfeit coefficient tail
starting beyond `2^8192` has a complete nonzero enclosure while remaining
invisible in the pilot's finite comparisons. An uncancelled ordinary pole at
one proves its critical global target false. Such a pole is not a
counterexample to the actual Möbius arithmetic. Separately, true signed rapid
bounds at `r=1` reject the false inference that kernel preservation alone
proves RH after ordinary zeta has been erased.

The proof methods, finite moment dictionary, kernel language and resource
budgets are supplied assumptions. A successful behavioral calibration is not
autonomous proof invention or new prime-distribution information. The source
argument is `root_lattice_proof.txt`; scoped results are loaded strictly from
`root-lattice-results/latest.json` after independent verification.

The verified `pilot-002` contains 243 primary programs and 8,748 primary
growth hypotheses (11,772 including ablation). All 16 independent audit groups
and 14 public contracts pass. Its 15 contexts use `r=1/6,1/3,1/2,3/4,1` with
`ell=1/6,1/3,1/2`; the additional `3/4` is selected by the pre-data seed.
There are 194 recovering root programs, 48 zero-erasing calibration programs,
and one unavailable root certificate. The anonymous moment learner records
90 attempts and validates three exact signed recurrences, one for each
`r=1` context. Those three are automatically compiled; their known
`mu*1=delta_1` identity is reported as calibration. Fifteen additional shapes
are learned from actual centered responses.

All 24 archived hypotheses pass the fresh finite tests at arithmetic indices
`1393,1885,1932`, their `1/3` offsets, and boundaries `1,2`, including fresh
`q=157,177,178`. Twenty are RH-if-uniform targets; three have globally proved
signed decay but erase ordinary zeta, and one has a proved weak exponent-one
witness. The primary grammar certifies 144 signed rapid-decay estimates for
the zero-erasing calibration. No recovering critical uniform estimate is
proved. The verifier also checks 20 finite-passing counterfeit tails whose
ordinary poles prove their critical global targets false, and rejects three
false RH inferences from true signed cancellation.

Of 60 derivative proposal slots, 57 are admitted. The best charged conditional
log cost is `56.984704125776354` for promotion and
`55.4098621826308` for the random-slot ablation. Promotion performs worse by
this measure; no benefit is claimed. The first failed run retains all sources
and data. Its verifier wrongly required a finite native zeta value and a
successful exclusion from a box containing the pole at one, although the
producer had honestly marked the certificate unavailable. The corrected
checker retains missing coverage as missing, and the new run excludes the
first run's final indices and `q` values. The mathematical candidates,
learner, fitting rules and selection criteria were not retuned.

The next proof-method expansion must retain actual arithmetic signs and
ordinary-zero information together. More finite passes or more rapid bounds
after zeta has been cancelled cannot satisfy the research objective.

## Divisor preconditioning with the signed remainder retained

The divisor-preconditioner stage adds arithmetic operators

\[
\lambda_a(n)=\sum_{d\mid n}\mu(d)\bigl(\log(n/d)\bigr)^a,
\qquad T_a(x)=\sum_{n\le x}\lambda_a(n),\qquad a>0.
\]

It supports every positive rational logarithmic order, including square,
cube and sixth roots. The producer uses constant-one divisor inversion and
logarithmic weights without a prime oracle. The independent evaluator factors
actual integers and checks the whole prime-factor finite difference.

For integer orders, the supplied differential algebra has
`lambda_(k+1) = D(lambda_k) + lambda_1*lambda_k`, where
`D f(n)=log(n)*f(n)`. The feature learner receives anonymous numeric
convolution columns, indexed by integer partitions; it receives no expected
coefficients. The exact generic Bell completion is applied only afterward.
The second order recovers the familiar weighted prime-power and prime-power
convolution identity `lambda_2 = Lambda*Lambda + log(n)*Lambda(n)`.
These identities also hold for jets of unrelated unit-normalized generic
coefficient sequences, but their prime-support interpretation requires the
actual constant-one input.

The new global proof method preconditions a component rather than erasing the
whole arithmetic object. Let `u h(x)=sum_(n<=x)h(x/n)`. An anonymous fit proposes
`h(x)=x*P(log x)+b`. A frozen triangular constraint solver uses the harmonic
Euler constants to create a new completed candidate `h_k`, with a retained
remainder `R_k`. It proves, for every real `x>=1`,

\[
\sum_{n\le x}\log^k n=(u h_k)(x)+R_k(x),\qquad
T_k(x)=h_k(x)+\sum_{d\le x}\mu(d)R_k(x/d).
\]

Only the `u h_k` component collapses under the arithmetic inverse. The actual
Möbius remainder remains and carries the ordinary-zeta denominator. Complete
harmonic error envelopes give

\[
|R_k(y)|\le C_R(1+\log y)^k,\qquad
|T_k(x)-h_k(x)|\le C_k x
\]

at every real scale. This is actual signed arithmetic control with retained
zeta information. It remains ordinary exponent one. The independent checker
computes harmonic constants by Cauchy contour integrals and separately checks
the full Mellin principal part by Laurent inversion; it does not import the
producer's mathematical code. Explicit constants are derived in
`divisor_preconditioner_proof.txt`. The known Selberg symmetry formula is a
calibration reference, not an imported new prime-distribution estimate:
https://terrytao.wordpress.com/2014/10/25/a-banach-algebra-proof-of-the-prime-number-theorem/

Fractional logarithmic orders have a distinct universal sign law. If `n` has
`r` distinct primes, their exact coefficient is an iterated finite difference
of `t^a`, with sign given by the falling product
`a*(a-1)*...*(a-r+1)`. The associated positive integral remains finite at the
zero endpoint for every real `a>0`. Integer order `k` vanishes when `r>k`.
Noninteger order in `(m,m+1)` is positive through `r=m+1` and then alternates
forever. In particular square, cube and sixth logarithmic roots have alternating
support across arbitrarily many distinct primes; they are not truncated
almost-prime indicators. This is all-index signed prime-factor information,
not a global prime-distribution error estimate.

The ordinary-zero gate remains separate. The first integer jet is
`-zeta'/zeta`; every ordinary zero has a nonzero logarithmic-derivative residue,
regardless of multiplicity. A cofinal square-root bound for its exactly
centered signed sum would imply RH. The proved bound is `C*x`. Higher derivative
numerators can mask zeros, so no automatic RH gate is certified for those jets.
For fractional orders the Mellin numerator has a fractional branch at one;
an integer polynomial center does not remove it. Full fractional centers and
their ordinary-zero recovery are unresolved requirements, while their exact
coefficient sign certificates remain valid.

The verified `pilot-001` samples orders `1/6,1/3,1/2,1,2,3,4,5/2`; the last
is selected by a pre-data seed. It records 20 anonymous fitted preconditioners,
four new completed-candidate promotions, four learned universal convolution
relations and eight learned universal sign signatures. Completion replaces
an approximate candidate by a new constrained candidate; it is not falsely
labelled a semantics-preserving compression of the original approximation.
The original rational proposals remain and have separately proved, conservative
global bounds. The equal-slot random ablation has best log losses `0,1,2,3`
for orders `1,2,3,4`; completion achieves `0,0,0,0`. This is a logarithmic
improvement in three contexts, with no improvement of the ordinary power one.

All 13 public contracts and 12 independent audit groups pass. Fresh real-scale
checks use integers `2347,2687,3615`, their `1/3` offsets and boundaries `1,2`.
The checker verifies 28,920 complete prime-factor arithmetic coefficients,
69,204 retained signed remainder terms, 32 full real-scale rewrites, ten
harmonic constants, ten Mellin principal coefficients, 24 original-proposal
global bounds, 304 fresh convolution-relation witnesses, 212 unrelated
generic-sequence witnesses and 64 fresh difference geometries. The archive
and every source hash precede fresh final cases; isolated replay reproduces
the complete sealed files exactly.

An early development audit found and fixed an alternating-sign error in the
harmonic-constant expansion before freezing the pilot. A harmonic-limit
regression and the separate Mellin principal-part audit now cover that issue.
No frozen source or final data was revised. Proof backends, polynomial and
partition features, signature classes and finite sampling remain supplied
design assumptions. No RH-strength signed estimate or RH proof is obtained.

## Complete fractional centers and cofinal signed parameter families

The next separately frozen stage closes the fractional-center and collective
ordinary-zero recovery gaps for logarithmic orders `0<a<1`. It does not close
the critical signed-estimate gap. Its successful run is
`branch-center-results/pilot-002`; the failed first run and its exact original
sources and evaluation data remain retained.

The arithmetic remains
`lambda_a = mu * (log n)^a`, with the weight at `n=1` set to zero, and
`T_a(x) = sum_(n<=x) lambda_a(n)`. The producer uses the divisor inverse of
the constant-one sequence and complete point support, without a prime or
factorization oracle. Bernstein's fractional-power integral proves, for every
integer `n>1`,

`|lambda_a(n)| <= (log p_min(n))^a <= (log n)^a`.

Together with the previously proved alternating prime-factor sign law, this
supplies exact signed coefficient information across every integer. It does
not supply RH-strength cancellation or a new prime-distribution theorem.

Write `Z(u)=(u-1)zeta(u)`, with its removable value `Z(1)=1`, and
`c_a=a/Gamma(1-a)`. The full branch center is

`A_a(x) = c_a * integral_0^1 (x^u-1)/(u*Z(u)) * (1-u)^(-a) du`.

It subtracts the entire fractional branch on the positive real cut. Its
Mellin transform is holomorphic at every nonreal ordinary zeta zero; actual
Möbius arithmetic and possible ordinary-zero poles remain. A paired eta
integral proves `Z(u)>=1/(4 log 2)` on `[0,1]`, and hence
`0<=A'_a(x)<=4 log(2)c_a/(1-a)` at every real `x>=1`.

Direct repeated quadrature was too slow for large arithmetic scales. The
producer now integrates a reusable analytic Taylor expansion, with a full
Cauchy tail and a Rouché certificate on a disk of radius `5/4`. The checker
uses independent coefficient division at higher precision, a separately
certified disk of radius `6/5`, and direct original-variable integral anchors.
Every stored center contains the sharper independent enclosure. Arbitrarily
large rational denominators have semantics; an explicit accuracy or work-cap
failure is missing evidence. A denominator-30,021 development check and the
public rational-denominator contracts do not become selected discoveries.

For distinct positive rational bases `b_i<1` and nonzero signed rational
weights `w_i`, define parameter moments `p_m=sum_i w_i b_i^m`. If `m0` is
their first nonzero moment, the tested operator is

`R_q(x) = sum_i w_i*(T_(b_i/q)(x)-A_(b_i/q)(x)) / (p_m0/q^m0)`.

This normalization exposes the first nonvanishing parameter response and is
charged throughout the arithmetic, center, interpolation and observer costs.
It prevents apparent improvement from a vanishing high-pass amplitude.
For every fixed positive integer `q`, a true all-real-scale certificate gives
`|R_q(x)|<=C_q*x*(1+log x)`. Its ordinary power is one, with logarithmic
loss one; it is not an RH-strength signed estimate.

The collective zero bridge also works when `sum_i w_i=0`. Euler summation
shows that the complete numerator `F_a(s)=sum_(n>=2)(log n)^a n^(-s)`
is entire in the exponent parameter at each fixed nonreal `s` with positive
real part. If a cofinal critical signed premise held, every ordinary zero
`rho` with `Re(rho)>1/2` would force
`sum_i w_i F_(b_i/q)(rho)=0` at a cofinal sequence of `q`. The entire
parameter function would then vanish identically. An exact eventual moment
dominance certificate would make `a -> F_a(rho)` a polynomial. Since
`F_k(rho)=(-1)^k zeta^(k)(rho)` at positive integers, this would give
the Taylor series of zeta infinite radius, contradicting its actual pole at
one. This covers all ordinary heights and multiplicities without requiring
an individual numerator to avoid every ordinary zero.

Consequently, for fixed `epsilon>0`, `nu>0`, and finite `d>=0`,

`for every q there exists finite C_q such that for every real x>=1,
 |R_q(x)| <= C_q*x^(1/2+epsilon/q^nu)*log(e+x)^d`

would imply RH. Constants may depend arbitrarily on `q`; a cofinal
subsequence is sufficient. The universal signed premise remains unproved.
Finite sampled parameter levels and scales cannot replace its quantifiers.

The frozen anonymous-response pilot produces 30 programs, four learned
signed combinations, four new parameter-moment promotions, 1,620 growth
hypotheses and 60 archived estimates. All 30 families receive conditional
recovery certificates; ten have zero total weight. The pilot's highest
initial nonzero moment is one; a second-moment family is a separate public
contract rather than an asserted discovered answer. The automatic promotion
rule creates `P(t)-2^m0 P(t/2)`, skips already present child semantics, and
rechecks the resulting family. Its comparison uses four seeded random slots
and the same predeclared root-response data budget.

After selection closed, new parameter levels 39 and 40 were generated.
Their fitted constants used only the frozen training scales and were sealed
before generating fresh scales 1,487 and 2,022 and their fractional offsets.
Sixty critical finite fits passed across 30 programs. The best validated
charged conditional observer cost is about 158.463 in both the promotion
and equal-slot ablation modes. No improvement in that best cost is claimed.
All numerical leads and missing certificate outcomes remain retained.

The independent audit passes ten groups plus exact isolated replay and
16 public contracts. It checks 25,800 complete arithmetic coefficients and
Bernstein witnesses, 144 complete centers, two direct integral anchors,
60 all-real-scale weak certificates, 360 normalized signed witnesses,
12 complete continued numerators, 60 full family observers, 120 fresh
estimate evaluations, and six leading-only branch obstructions. Whole
numerators are independently checked by fractional integrals of ordinary
zeta, with complete endpoint and infinite-tail bounds.

Some selected targets have no positive Mellin gap at the finite query line;
their costs are missing, not silently omitted. A separate post-run audit
checks all 450 positive-gap costs in the full frozen validation set and
23 promotion-ranking costs, using six independently continued Taylor
composition profiles. It changes no candidates, cases, constants, or
selection. All normalization, full-center, real-scale guard and gap costs
are included.

The failed first run exposed an observer serialization issue: an exact
native modulus endpoint was tighter than the subsequently printed complex
ball. The corrected source recomputes the lower bound from the serialized
ball and rounds it downward on a 160-bit dyadic grid with an extra grid unit
of guard. A new public contract covers the strict outward margin; the fresh
run excludes the first run's final scales. No frozen artifact was repaired
in place.

Leading-only centering is a proved false control: it leaves a nonzero
`(s-1)^(1-a)` branch at one, so no all-scale exponent below one can bound
that error, even assuming RH. This obstruction does not reject the full
centers. Generic arithmetic aliases and the zero operator receive no
ordinary-zeta recovery certificate. The actual fractional critical signed
premises and RH remain open; the research goal is active.

An additional callable numerical layer,
`rational_fractional_evaluator.py`, removes a discovered native interface
limit without altering the frozen search. The older native nth-root routine
requires an unsigned 64-bit denominator. The general evaluator instead
uses `exp(a*log x)` with an exact-rational enclosure of `a`; all positive
rational logarithmic orders have semantics. Native precision and complete
continuation-tail resources are explicit. Serialization scales with native
precision so tiny parameter differences survive normalization. Integer
bound guards use the exact native ceiling of the serialized enclosure,
rather than an insufficient fixed number of decimal digits.

Separate independent contracts verify denominators `2^64+1`, `10^100`
and `2*10^100`: 96 complete prime-difference coefficients, three whole
fractional-zeta integrals, three full centers, a normalized tiny-root
high-pass observer, and a 201-digit outward weak-bound guard. They use no
new search selection, growth fits or protected search cases. These API
regressions are additional verification, not claimed numerical discoveries.

Run a new independently frozen search with
`../.venv/bin/python run_expanded_probe.py --branch-centers-only`, or reuse
the portable evaluator directly from Python. Existing runs and integration
snapshots are retained.

## Current bounds strategy: the full signed energy defect

The main proof target is now the inequality itself. For the actual step
Mertens sum \(M(x)=\sum_{n\le x}\mu(n)\), define

\[
A(X)=\int_X^{2X}M(t)^2\,dt,\qquad
\Delta(X)=A(2X)-4A(X).
\]

We seek, for **every cofinal positive \(\varepsilon\)**, a finite
\(B_\varepsilon\) such that **every dyadic \(X\ge1\)** satisfies

\[
\Delta(X)\le B_\varepsilon X^{2+\varepsilon}.
\]

The constant may depend on \(\varepsilon\), but never on \(X\). Only an
upper bound is needed; large negative defects are allowed. Induction gives
\(A(X)=O_\varepsilon(X^{2+\varepsilon})\). Dyadic Hölder then proves
Mellin convergence on \(\Re s>1/2+\varepsilon/2\). The exact identity
\(\int_1^\infty M(x)x^{-s-1}dx=1/(s\zeta(s))\) excludes ordinary zeros
there, and cofinal \(\varepsilon\to0\) gives RH by functional symmetry.
The recovery argument covers all ordinary heights and off-critical
multiplicities. **The uniform arithmetic premise remains unproved.**

This target avoids an unnecessary strengthening. At exactly
\(\varepsilon=0\), the fixed recurrence gives \(A(X)=O(X^2\log(eX))\).
For unfiltered \(M\), its Mellin bound near a critical zero grows at most
\(h^{-3/2}\), so it would also imply that every critical zero is simple.
That implication is proved as a conditional statement; simplicity is not
assumed and the earlier fixed-critical recurrence theorem remains valid.
The positive-epsilon family can pursue RH without that extra requirement.

The new exact kernel is
\(K_X(n,m)=(2X-\max(X,n,m))_+\). Expanding the whole energy retains
every signed pair. The diagonal has a sharper every-scale defect bound
\(O(X^{3/2})\): elementary squarefree density gives its leading
\(3X^2/(2\zeta(2))\) term, which cancels between the two scales.

For each pair write \(n=ga<m=gr\), with \(\gcd(a,r)=1\). The actual
prime arithmetic obeys the exact identity

\[
\mu(ga)\mu(gr)=\mu(a)\mu(r)\mu(g)^2
                 \mathbf1_{\gcd(g,ar)=1}.
\]

Let \(C_B(X)\) retain pairs with \(r\le B\). The uniform elementary
bound for coprime squarefree counts proves

\[
|C_B(2X)-4C_B(X)|
 \le C X^{3/2} B^{3/2}(1+\log B)^2.
\]

The **same cutoff \(B\)** must be used in both terms. The frozen rational
grammar contains 47 cutoff laws \(B=\lfloor X^\beta\rfloor\). Its rule
selects the largest coverage with proved component power at most two;
it selected \(\beta=1/3\). Thus a cube-root-growing common-factor part
has a true every-scale \(O(X^2\log^2(eX))\) defect bound. Square, cube
and sixth-root cutoffs, and denominators as large as \(10^{100}\), have
separate public numerical contracts. Native cutoff resource exhaustion is
missing data, never a semantic cap or a changed cutoff.

This does **not** bound the whole defect. Define the dense remainder
\(R_B(X)=C(X)-C_B(X)\). At each scale, with \(B=B(X)\) fixed within
that pair of terms, the exact outstanding obligation is

\[
R_{B(X)}(2X)-4R_{B(X)}(X)
 \le K_\varepsilon X^{2+\varepsilon}
\]

at every dyadic \(X\), for cofinal positive \(\varepsilon\) and finite
scale-independent \(K_\varepsilon\). Proving this would finish the full
target because the other two pieces already have suitable bounds.
Absolute pair estimates still give ordinary energy power three. Further
operator search should be judged by whether it proves this remaining signed
control, rather than only improving a normalization or logarithmic cost.

The independently verified pilot is `critical-defect-results/pilot-001`.
Its fresh dyadic scales are 4096 and 8192. All four archived fitted residual
constants failed there. Their training residuals were nonpositive, yielding
effectively zero fitted constants; fresh positive residuals reject those
particular finite extrapolations. This does not disprove the existence of
larger uniform constants at the same growth rates. The fresh residuals are
retained exactly, without changing the fit after seeing them.

The audit checks 40,960 complete inverse coefficients, 1,040,909 primitive
prime-product identities, 204 component-bound witnesses, 373 exact retained
residuals, ten whole-energy defects and twelve fresh coprime-density cases.
All ten audit groups and fifteen public contracts passed, including exact
isolated replay. A positive-coefficient control has a controlled sparse
projection and full defect \((28X^3-X)/3\). A delayed positive tail agrees
with every development coefficient but has eventual cubic growth. These
counterfeit inputs explicitly reject inferring full control from sparse
control or finite observations.

The common-factor construction and elementary proof method were supplied.
This is a guided bound-decomposition audit, not anonymous mathematical
invention or a new prime-distribution theorem. It establishes proved
components and a precise unresolved signed obligation. No RH-strength full
inequality has been verified. The earlier parameter-cancellation prototype
in `parameter_cancellation_*` remains development code and is not frozen,
verified or integrated into this result.

Run a new frozen audit with
`../.venv/bin/python run_expanded_probe.py --critical-defects-only`.
Use `--summarize-only` to reuse the verified evidence without generating
new observations. Previous successful sources and integration snapshots
remain unchanged.

## Detector candidates followed by separate analytical proof attempts

The working cycle is now implemented: run the numerical detector, freeze its
exact selected formulas and proof queue, evaluate fresh cases, attempt
analytical proofs of those formulas, independently check the dispositions,
then apply the resulting feedback to a fresh search. The analytical review
cannot change an archived formula or retroactively replace the detector's
selection. Unsupported leads remain in the queue.

The first full-defect matrix pilot is `divisor-dual-results/pilot-001`.
It generates 72 exact programs, recovers a floor/lcm kernel from anonymous
divisor-Gram tables, and promotes the nonunit zero-forcing mask from generic
inverse responses. An equal-profile random-mask ablation uses the same
response data and scalar-profile budget. These index features and proof
methods were supplied; the expected winning formula was not supplied to the
fitter. The producer uses the complete divisor inverse without a prime or
factor oracle; the evaluator independently checks actual prime arithmetic.

For the full signed-defect matrix \(H_X\), each program tests

\[
S_{X,q}=D(X,q)I-H_X+Y(X)C_{4X}^{T}\operatorname{diag}(w)C_{4X}.
\]

If this is positive semidefinite, the actual inverse identity gives the
fully charged bound \(\Delta(X)\le 4XD(X,q)+Y(X)w(1)\).
All arithmetic pairs remain in the target. The unit-row cost is paid
whenever it is present. The nonunit Gram annihilates the actual Möbius
vector at every finite cutoff; that identity by itself supplies no signed
distribution estimate.

The 12 selected proof-queue templates were sealed before fresh evaluation
at \(X=30,32,64\) and levels \(q=9,10\). The fresh evaluations contain
32 positive matrices and 17 exact negative directions. All 1,346 matrix
cases were independently checked, including 29,488 exact positive leading
minors, 718 negative quadratic witnesses, and the actual inverse arithmetic.
All ten detector audit groups and 17 public contracts passed, including
deterministic isolated replay. These are finite matrix certificates.

The separate analytical review refutes six of the proposed uniform matrix
claims and retains six unresolved complete-nonunit-Gram templates. It proves
a general obstruction: if the mask leaves a positive-density set of rows
uncontrolled in \((2X,4X]\), a vector supported on those rows annihilates
the selected Gram and has cubic child energy. The matrix fails eventually
at every fixed \(q>1\), regardless of \(Y\). This rejects the particular
universal PSD route using residue, fixed-prime, sublinear-prefix or square
rows; it does not reject those arithmetic identities in other proof routes.
Even with all tail rows present, quadratic Gram coefficients below
\(4/3\) fail by an explicit full-tail vector. These analytic disproofs are
not counterexamples to RH.

For the six unresolved leads, congruence by the inverse divisor matrix
exposes the exact entry \(D(X,q)Q(4X)-\Delta(X)\), where
\(Q(N)=\sum_{n\le N}\mu(n)^2\). A uniform bound for this actual signed
entry remains necessary. The review derives an explicit conditional Schur
buffer for the remaining block, but its required arithmetic gap is
unproved. Increasing the Gram power cannot hide that gap.

All five analytical audit groups and six additional contracts passed. The
review and proofs are in `analytical-review-001` and
`divisor_dual_analytic_proof.txt`; the source detector queue is unchanged.
The arguments are ordinary mathematical proofs with independent exact
certificate checks, not machine-formalized proofs.

One grammar restriction emerged from the proof attempts: these templates
prescribe polynomial growth of the constant as \(q\) increases. The generic
RH-sufficient criterion permits an arbitrary finite constant for each
positive epsilon. A subsequent run should separate the shrinking exponent
from its constant law and allow additional growth programs or existential
per-level constants. The \(r=0\) templates impose an even stronger bounded
critical constant and retain their extra simple-critical-zero consequence.
The new obstruction and this coverage limitation are feedback for a fresh
run, not changes to the frozen pilot. No global critical inequality or RH
proof has been established.

Run the entire candidate-to-proof cycle with
`../.venv/bin/python run_expanded_probe.py --divisor-duals-only`.
Use `--summarize-only` to report existing verified results without creating
new cases or changing selections.

## Independent constants and direct tests of the actual signed gap

The next verified cycle is `signed-gap-profile-results/pilot-001`. It takes
the analytical feedback into a fresh frozen search rather than changing the
earlier candidates. It separates the exponent schedule from the constant
law and tests the actual missing arithmetic entry before another expensive
full matrix comparison. The exact target is

\[
\Delta(X)\le \tfrac12 D(X,q)Q(4X),\qquad
D(X,q)=C(q)X\lceil X^{\varepsilon(q)}\rceil
\lceil(1+\lfloor\log_2X\rfloor)^L\rceil.
\]

There are 384 profiles: eight cofinal exponent schedules, sixteen independent
constant laws, and logarithmic powers \(L=0,1/6,1\). Exponent denominators
include rational powers of \(q\), exponentials and factorials. Constants can
grow polynomially, exponentially, factorially, or as a power of that
denominator. The existential family allows an arbitrary finite constant at
each level. Its unseen constants remain missing rather than being fitted
to final cases and counted as predictions. These are sufficient candidate
routes to the unrestricted cofinal RH criterion, not a claim that the
finite collection of explicit growth programs covers every possible law.

Fresh scales are 60,026, 65,536, 77,416 and 524,288, with new levels 13 and 17.
The complete actual divisor inverse was independently checked against
prime-derived arithmetic through coefficient 2,097,152. All 704 available
half-gap predictions passed; 64 additional cases have unknown per-level
constants. Only one of these fresh signed defects is positive, so the finite
passes provide limited evidence about cancellation at future scales. All
48 exact selected all-scale signed-gap claims were analytically unresolved
at that initial review; the cofinal audit below supersedes three dispositions.
No constant is changed after evaluation.

A delayed positive tail agrees with every development coefficient through
131,072 and still has eventual cubic signed defect. It fails 609 of the
available counterfeit tests. Some rapidly growing constants also cover that
counterfeit at finite scales, which reinforces why finite success alone
does not establish an all-scale estimate. The counterfeit is explicitly
distinguished from the complete actual inverse; its failures are not RH
counterexamples.

The anonymous minimum-energy experiment inferred

\[
P(J)=J/6-J^2/2+J^3/3=J(J-1)(2J-1)/6.
\]

It was selected from sparse rational fits over a declared dictionary of
monomials in mass and dimension. The fitter was not supplied this coefficient
vector. After the selected relation and final data were frozen, the generic
backend checked \(P(0)=0\) and \(P(J+1)-P(J)=J^2\). An exchange argument
then proves it is the minimum binary-prefix square energy for every length
and mass. The inference and proof methods are supplied assumptions; this is
not autonomous invention of a proof method.

For any boolean divisor mask, \(J\) omitted rows in \((2X,4X]\) yield a
null Gram vector with energy at least \(P(J)\). Thus positivity necessarily
requires \(P(J)\le D J\), independently of the omitted rows' positions and
the Gram weight. This improves the previous positive-density obstruction:
cofinal critical diagonal growth cannot omit substantially more than
square-root many tail rows, up to its epsilon and logarithmic losses. This
is a proved global combinatorial restriction, not the needed actual prime
cancellation estimate.

The constant-law review also corrects the earlier simplicity scope. A
uniform defect family with \(B_\varepsilon=O(\varepsilon^{-\kappa})\) and
logarithmic degree \(L\) would bound critical-zero multiplicity by
\((\kappa+L+3)/2\). For \(\varepsilon=1/q\), polynomial constants
\(q^r\), and \(L=0\), every \(r<1\) still forces simple critical zeros,
even though the constants grow without bound. The earlier positive powers
\(1/6,1/3,1/2\) therefore imposed this additional consequence too. It was
incorrect to treat positive growth alone as removing every simplicity
restriction. The audit labels these conditional restrictions explicitly;
it does not assert anything about actual zero multiplicities. Factorial
parameter gaps and subpolynomial laws are recorded using limiting pole
exponents, with no unwarranted exact Big-O assertion.

All seven detector groups, four analytical groups and eighteen public
contracts passed. The ordinary global row-norm calibration still has
energy power three. The actual all-scale critical signed half-gap remains
unproved, and the research objective remains active.

Run a fresh cycle with
`../.venv/bin/python run_expanded_probe.py --signed-gap-profiles-only`.
Existing verified evidence can be reported with `--summarize-only`.

## Cofinal endpoint tests can refute an actual fitted arithmetic bound

The separate `cofinal-audit-001` reviews the unchanged 48 templates from
the preceding pilot. It uses their original independently checked arithmetic
cases, with no new holdout claim or refitting. It refutes three uniform
half-gap claims and the associated complete-dual PSD comparisons. Two
templates also fail their weaker, fully charged global defect majorants.
At this audit the remaining 45 half-gap claims were unresolved; the parallel
review below supersedes five additional dispositions.

The mechanism is exact. For fixed integer \(X\ge2\),
\(\lceil X^{1/d}\rceil=2\) whenever \(d\ge\operatorname{bit\_length}(X)\).
If \(C(q)=A\) is bounded and the exponent denominator tends to infinity,
the eventual diagonal is \(D=2AX\lceil\ell(X)^L\rceil\). The source claim
then requires \(\Delta(X)\le AX\lceil\ell(X)^L\rceil Q(4X)\).
A strict violation at one fixed dyadic scale persists for **every**
sufficiently large parameter. Thus the existential starting parameter
\(q_0\) cannot exclude it. A failure at one isolated parameter would not
automatically have this implication.

The three bounded-constant templates use exponent denominators
\(\lceil q^{1/6}\rceil\), \(\lceil q^{1/3}\rceil\), and
\(\lceil q^{1/2}\rceil\). Persistent half-gap witnesses occur at
\(X=16,384\), \(16,384\), and \(8,192\), respectively. Safe parameter
thresholds are 11,390,625, 3,375, and 196. Their exact actual signed defects
are 6,547,818, 6,547,818, and 2,978,976. Every endpoint margin is checked as
a rational number; displayed numerical approximations are not used as proof.

This is an actual Möbius-vector refutation of particular fitted inequalities,
unlike the earlier generic tail-vector obstructions. The three scopes are
kept distinct: a half-gap failure need not refute the weaker necessary
nullspace inequality, and a nullspace failure need not refute the fully
charged bound. Each is tested separately. These findings do not refute RH
or the existence of larger uniform constants for the same operator family.
A rescaled formula would be a new candidate requiring a fresh search and
its own all-scale proof.

All four independent audit groups and six public contracts passed. The
audit recomputes the actual arithmetic through 2,097,152 coefficients and
checks 64 exact endpoint cases plus nine illustrative native plateaus.
The universal parameter scope comes from the threshold theorem, not those
nine finite checks. Original source files, selected formulas and finite
outcomes remain frozen. Earlier reports retain their initial dispositions;
the combined report records the current cofinal refutations separately.

The complete candidate-to-proof cycle now runs this endpoint audit
automatically. An existing verified profile run can be reviewed with
`../.venv/bin/python run_expanded_probe.py --signed-gap-cofinal-only`.
No all-scale critical signed arithmetic inequality has been proved.

## Parallel analytical reviews preserve exact claims and require independent checks

The user authorized Sol 6.1 subagents to evaluate candidates in parallel.
`candidate-review-results/sol-6.1-round-001` assigns all 45 then-unresolved
formulas to three `gpt-6.1-sol` agents. Sorted stable IDs and round-robin
assignment cover each formula once. The reviewers focus respectively on
actual arithmetic, scale recurrence, and positivity/complex-analytic
constraints. Exact formulas and evidence are frozen before dispatch;
returned proof attempts are frozen before independent verification.

The reviews supplied five additional exact global refutations. Direct prime
factorization gives \(\mu(1),\ldots,\mu(8)=(1,-1,-1,0,-1,1,-1,0)\).
Thus \(A(2)=1\), \(A(4)=10\), \(\Delta(2)=6\), and \(Q(8)=6\).
For every integer denominator \(d\ge1\), \(\lceil2^{1/d}\rceil=2\).
Each of these five formulas has \(L=0\) and the exact constant
\(C=1478554275663870691771/45950839487610493075456<1/2\).
Its half-gap right side at \(X=2\) is \(12C<0.4\), below the actual defect
6 for **every** \(q\ge1\). An unknown \(q_0\) cannot exclude this witness.
The earlier audit only used recorded numerical scales and missed this small
dyadic boundary. Every future assignment explicitly asks reviewers to check
domain boundaries as well as larger scales.

There are now **eight refuted source half-gap claims and 40 unresolved
ones**. The original 704 available fresh numerical passes remain valid for
their tested cases. Growing constants may fail at finitely many small
parameters that a larger \(q_0\) can exclude; those failures are recorded
without globally refuting the claim. Unseen free-per-level constants remain
unknown. No coefficient is refitted after these analytical failures.

The independent certificate checker verifies actual tiny prime arithmetic,
the universal parameter argument, exact rational margins, source hashes and
complete assignment coverage. Four audit groups and eight public rejection
contracts pass. It checks 72 explicit small-scale parameter diagnostics from
the first review. Reviewer prose, conditional estimates and the auxiliary
large development sieve are retained as leads, with no independent upper
proof certification claimed. New global upper proofs will need a separate
mathematical checker suited to their arguments.

The conditional recurrence normalizes \(E_j=A(2^j)/4^j\) and
\(F_j=\Delta(2^j)/4^{j+1}\), yielding \(E_{j+1}-E_j=F_j\).
That identity still needs an actual bound on its signed forcing. Complete
divisor-Gram positivity has the same unresolved scalar gap on its exact
Möbius nullspace. The reviews supply no all-scale signed upper bound.

Prepare a new immutable round using `candidate_review_workflow.py plan`
with `--source`, `--cofinal-audit`, `--round-dir` and optionally
`--prior-review-round` to exclude independently refuted IDs. Dispatch the
prepared assignments through the collaboration tools with model
`gpt-6.1-sol`; the Python planner itself does not call a model. After the
reviews finish, run `run_expanded_probe.py --candidate-reviews-only
--candidate-review-round-dir <round>`. This freezes attempts, checks typed
certificates and publishes their dispositions. Completed rounds are retained
unchanged. Proof scope: `candidate_review_proof.txt`.

## Learned inverse compression feeds a separate signed potential search

The Sol 6.1 analytical routes now feed an operator search with exact inverse
prefix features and a separate grammar of nonnegative potentials. The supplied
basis is explicit: truncated inverse convolution powers, reference powers,
wrong-column alternatives and constants. Anonymous exact fitting receives no
expected binomial vector or recurrence. In `inverse-prefix-results/pilot-002`,
it learned five coefficient rows and one recurrence from 2,087 sparse supports.
A separate error-polynomial proof admits the discovered rule for **every positive
integer arity** and any unit reference, including nonmultiplicative references.

For a reference h with inverse a, its prefix through x is reconstructed from
inverse values through u whenever **x<(u+1)^k**. The exact error is
(a-a_u)^{*k}*h^{*(k-1)}. The strict endpoint cannot be replaced by equality.
Generic references generated after sealing passed 84/84 exact checks, including
arities six and seven; disabling recurrence promotion left 56 unseen-arity
responses missing. Actual Möbius reconstruction passed 32/32 full signed block
checks, with actual coefficients independently checked through 32,768.
Full reference data, divisibility geometry and tuple costs remain charged;
coefficient L1 cost is 2^k-1. Compression supplies an exact arithmetic
representation across scales, without establishing a cancellation estimate.

The potential grammar searches fixed nonnegative rational combinations of
component square energies, with full rational-power ceilings as normalizers.
Its 25 features include square-root normalizers and other fractional powers.
It searched 2,776 programs and sealed three leads, retaining one baseline and
one each with one and two terms. Final response values and seed-derived generic
references were withheld until sealing; the scale design was already visible
to the worker. Actual coefficients overlap prior development. All native
arithmetic stays within the pilot budget; generalized search missingness beyond
that budget remains an extension task. The arbitrary rational evaluator itself
has no semantic denominator cap.

The three leads passed only **6/24** fresh available inequalities; 24 cases at
new levels have unknown constants and remain missing. A separate backend proves
nonnegativity and the conditional telescope: if fixed V>=0 satisfies

    E(2X)+V(2X)-E(X)-V(X)<=C_q ceil(X^(1/q))

for every dyadic X and every sufficiently large q, with finite C_q independent
of X, then unfiltered Mellin recovery gives RH. The all-scale actual signed
innovation inequality remains unproved. Moving cutoffs are evaluated separately
at X and 2X. Individual component envelopes do not establish this inequality.

Three Sol 6.1 agents reviewed the exact sealed leads in parallel. Narrow native
certificates admit the sharper slot-one identity
B_(k,1)(X)=X M(floor((4X-1)^(1/k)))^2 and its global envelope. Power p>=1+2/k
makes this feature bounded. The selected nonempty potentials even tend to zero,
but a bounded V merely changes the free-constant baseline innovation inequality
by an additive constant. It does not supply the missing signed arithmetic bound.

Independent actual witnesses at X=2 for the baseline and X=512 for each
nonempty potential refute all twelve stored-level inequalities with the original
C_q=2^-64. Extending that constant to every large q is also disproved. These
witnesses leave the original unknown-q0, existential-C_q claims unresolved.
Original fresh outcomes remain unchanged; reviewer arithmetic is analytical
development, not fresh validation. Full reviewer prose is retained, while native
checks certify only the typed envelopes, witnesses and scope distinctions.

The first operator pilot is retained as a failed access-guard attempt; it
produced no candidate or final records. The first separate review attempt is
retained as a JSON-serialization failure after arithmetic checking. Successful
runs use fresh directories and hash those failure records. Proof scopes:
`inverse_prefix_proof.txt` and `inverse_prefix_slot_review_proof.txt`.

Run a fresh detector stage with `run_expanded_probe.py --inverse-prefix-only`;
provide `--inverse-prefix-run-dir` with a completed run to republish its checked
summary without rerunning selection. Candidate reviews use
`inverse_prefix_reviews.py --source <run> --review-dir <fresh directory>` after
parallel agent attempts are complete. Native numeric audit groups: ten;
analytical groups: nine; separate parallel review groups: six.

## Workflow audit adds safety boundaries and a signed-bound calibration

The audit in `workflow-audit-results/audit-001` separates operational reliability
from demonstrated mathematical discovery capability. All successful old native
sources and results remain unchanged. New wrappers address bugs exposed outside
the original pilot contracts:

- `detector_safe_evaluation.py` makes unavailable exact normalizers explicit
  missing values. The raw native `Fraction(energy, None)` branch previously
  became unnormalized energy. No unavailable case can pass or contribute to a
  constant fitted from a partial dataset; unseen q constants remain unknown.
- `detector_safe_inference.py` preserves full sparse fitted vectors and their
  alternatives. Constant/distractor fits keep their finite semantics, and cannot
  be truncated into an inverse-polynomial macro. Absent/no-fit arities remain
  explicit, with universal admission separate.
- `detector_workflow_guard.py` rejects optimized Python and inherited nonzero
  `PYTHONOPTIMIZE`, refuses sealed worker destinations, and rederives refutation
  IDs from the frozen typed witnesses and validated predecessors. Counts and ID
  lists alone cannot exclude an unresolved candidate. The main root entry uses
  this guard before dispatch or publication.
- `detector_review_planner.py` supports generic sealed queues and arbitrary batch
  counts, validates complete review coverage before collection, and collects
  atomically. Model dispatch uses collaboration tools externally. Receipts bind
  observed task names and exact inputs; metadata alone does not independently
  authenticate the runtime model. Domain proof checking stays separate.

Use the project interpreter `../.venv/bin/python`, which includes the native
exact arithmetic dependencies. Raw frozen legacy helpers remain diagnostic
interfaces with their original finite contracts. Use the safe wrappers when
expanding grammars or resources; do not invoke raw worker code on a sealed run.

The signed-bound calibration learns anonymous digit, prefix and moment rules
from numeric responses in bases two through four. Its frozen coefficient rule
then transfers to genuinely different base-five and base-six functions without
moment refitting. New instances have declared numeric digit/prefix parameter
probes; these are sealed before generating the larger evaluation dimensions.
Exact coefficient witnesses establish differences from every training function.
For four unseen signed instances, analytical admission proves

    H(bN)-bH(N)<=K, and H(N)<=C*N, for EVERY integer N>=1.

Positive controls fail globally; four delayed positive-tail candidates pass
the finite probes but are rejected by their complete generator semantics.
The fully unsigned prefix energy grows faster than linearly. This demonstrates
signed estimate inference and all-scale admission in a tractable supplied
language. Six focused calibration contracts and the aggregate workflow
contracts are recorded with frozen code and exact input hashes.

The calibration's generator class, residue/moment feature dictionary and
induction/positivity proof method are supplied assumptions. Blindness is
function/data-flow separation in one process, without an adversarial OS sandbox.
An agent-authored generic calibration cannot demonstrate independence from
model-chosen representations or establish a probability of solving RH. It
proves no actual-prime/Möbius bound and is separate from the theorem registry.

Experimental diagnostics explain a weakness in the current actual-zeta pilot:
all three selected leads trained on negative-only innovations, so their tiny
constants never measured positive forcing. Earliest dyadic boundaries were
omitted from fitting an every-dyadic-scale claim. The selected bounded/vanishing
corrections also leave the asymptotic free-constant signed problem unchanged.
These warnings preserve the candidates; they are not global disproofs.

Future bound-search protocols should predeclare early boundaries, diverse
positive/negative forcing regimes, precision/resource checks and out-of-range
scales. Preserve all candidates and unsupported proof routes; promote changed
formulas as new proposals. A serious RH lead should expose a tractable signed
correlation/cancellation lemma for actual arithmetic, carry ordinary-zero
recovery, and survive independent global proof checking. Another exact identity
or bounded correction does not establish that missing mechanism.

Audit entry: `run_detector_workflow_audit.py --audit-dir <prepared audit>`.
Its contract suite tests safety boundaries, planner completeness, signed-bound
inference and deliberately false controls. The current audit preserves both
normal and optimized fault-injection evidence. The main research objective
remains active; verified RH-sufficient signed controls remain zero.

## Reviewable artifacts

- Current primary search: `mellin-search-results/pilot-001/report.txt`.
- Workflow reliability and signed-bound readiness audit: `workflow-audit-results/audit-001/report.txt`.
- Genuine unseen-generator signed-bound calibration: `workflow-audit-results/audit-001/signed-bound-calibration/report.txt`.
- Learned inverse-prefix compression and signed potential detector: `inverse-prefix-results/pilot-002/report.txt`.
- Separate Sol 6.1 component bounds and stored-fit counterexamples: `inverse-prefix-results/pilot-002/parallel-review-002/report.txt`.
- Standalone inverse-prefix and signed innovation figure: `inverse-prefix-results/pilot-002/inverse_prefix.pdf`.
- Parallel Sol 6.1 analytical attempts and checked counterexamples: `candidate-review-results/sol-6.1-round-001/report.txt`.
- Stronger audit of earlier pilots: `signed-mellin-results/audit-002/report.txt`.
- Full conditional analytic argument: `signed_mellin_proof.txt`.
- Exact operator stability and inverse argument: `stable_scale_proof.txt`.
- Explicit correlation identity and diagonal argument: `signed_correlation_proof.txt`.
- Logarithmic recurrence transfer: `signed_recurrence_proof.txt`.
- Learned recurrences: `signed-defect-results/pilot-001/report.txt`.
- General rational power domains and fractional moment transfer: `rational_power_proof.txt`.
- Fractional-moment pilot: `fractional-moment-results/pilot-001/report.txt`.
- Fractional-zeta pole and zero branch gate: `fractional-branch-results/audit-001/report.txt`.
- Fractional coefficient/kernel search: `pole-neutral-results/pilot-001/report.txt`.
- Coefficient-power and log-kernel bridge: `pole_neutral_proof.txt`.
- General parameter jets and exact prime recovery: `parameter_jet_proof.txt`.
- Guided jet calibration: `parameter-jet-results/calibration-001/report.txt`.
- Signed prime-error filter search: `prime-error-results/pilot-001/report.txt`.
- Logarithmic zero-faithfulness and whole-unit transfer: `prime_error_proof.txt`.
- Floor-density and signed prime-correlation search: `prime-discrepancy-results/pilot-001/report.txt`.
- All-scale prime/diagonal bounds and signed pair obligations: `prime_discrepancy_proof.txt`.
- Fractional prime-twist search and exact signed centers: `prime-twist-results/pilot-001/report.txt`.
- Signed harmonic and fractional reciprocal-tail proofs: `prime_twist_proof.txt`.
- Standalone signed decay and density-matched control figure: `prime-twist-results/pilot-001/prime_twist_evidence.pdf`.
- Exhaustive frozen-candidate and complete-window coverage: `prime-twist-coverage-results/coverage-001/report.txt`.
- General oscillation compatibility and automatic log-loss repair: `prime-oscillation-results/audit-001/report.txt`.
- Eventual inverse/Stieltjes consequence and named external import: `prime_oscillation_proof.txt`.
- Fractional discrete/continuous family search: `fractional-remainder-results/latest.json`.
- Entire numerator, parameter-pole recovery and weak signed-family proofs: `fractional_remainder_proof.txt`.
- Small-order inverse compatibility and source-batch log repairs: `mertens-limit-results/latest.json`.
- Derived limit/Volterra argument and named external extremum import: `mertens_limit_proof.txt`.
- Complete infinite arithmetic tails and cofinal kernel search: `mellin-kernel-results/latest.json`.
- Exact bank recovery, signed forcing and cofinal quantifiers: `mellin_kernel_proof.txt`.
- Complete signed correlation and density search: `kernel-correlation-results/latest.json`.
- Signed squarefree correction and ordinary-zero reflection proof: `kernel_correlation_proof.txt`.
- Standalone Gram, density and conditional-cost figure: `kernel-correlation-results/pilot-002/kernel_correlation_evidence.pdf`.
- Typed lattice estimate synthesis and complementary fractional banks: `lattice-synthesis-results/latest.json`.
- Global contour, actual-support sign barrier and fractional zero-chain proofs: `lattice_synthesis_proof.txt`.
- Complete-arithmetic fractional-root semantic calibration: `lattice-synthesis-results/pilot-002/fractional_root_calibration.json`.
- Standalone typed-lattice evidence figure: `lattice-synthesis-results/pilot-002/lattice_synthesis_evidence.pdf`.
- Normalized arithmetic roots and signed profile learning: `root-lattice-results/latest.json`.
- Complete root moments, signed profile proof and finite zero escape: `root_lattice_proof.txt`.
- Standalone normalized arithmetic-root evidence figure: `root-lattice-results/pilot-002/root_lattice_evidence.pdf`.
- Divisor preconditioning retaining actual signed arithmetic: `divisor-preconditioner-results/latest.json`.
- Harmonic completion, every-scale signed bounds and fractional sign proof: `divisor_preconditioner_proof.txt`.
- Standalone retained-remainder evidence figure: `divisor-preconditioner-results/pilot-001/divisor_preconditioner_evidence.pdf`.
- Complete fractional centers and signed cofinal parameter families: `branch-center-results/pilot-002/report.txt`.
- Entire exponent parameter, full-cut center and conditional all-height recovery proof: `branch_center_proof.txt`.
- Independent positive-gap observer costs without search changes: `branch-center-results/pilot-002/positive_gap_observer_audit.json`.
- Standalone fractional-center evidence figure: `branch-center-results/pilot-002/branch_center_evidence.pdf`.
- Arbitrary-denominator and exact-integer numerical API: `rational_fractional_evaluator.py`.
- Independent arbitrary-denominator and tiny-parameter contracts: `branch-center-results/pilot-002/rational_fractional_contract_verification.json`.
- Current RH signed-defect target and common-factor proof: `critical_defect_proof.txt`.
- Verified signed-defect components and exact unresolved residual: `critical-defect-results/pilot-001/report.txt`.
- Standalone full-defect and retained-residual figure: `critical-defect-results/pilot-001/critical_defect_evidence.pdf`.
- Exact detector-selected full-defect candidates: `divisor-dual-results/pilot-001/proof_queue.json`.
- Detector evidence and independent matrix audit: `divisor-dual-results/pilot-001/report.txt`.
- Separate analytical dispositions on those unchanged candidates: `divisor-dual-results/pilot-001/analytical-review-001/report.txt`.
- Universal coverage and Gram-coefficient barriers: `divisor_dual_analytic_proof.txt`.
- Standalone matrix-candidate evidence: `divisor-dual-results/pilot-001/divisor_dual_evidence.pdf`.
- Independent exponent/constant profiles and actual large-scale gap evidence: `signed-gap-profile-results/pilot-001/report.txt`.
- Exact frozen signed-gap and anonymous estimate proof queue: `signed-gap-profile-results/pilot-001/proof_queue.json`.
- Separate analytical dispositions and constant-growth restrictions: `signed-gap-profile-results/pilot-001/analytical_review.json`.
- Generic minimum-energy proof and critical-multiplicity scope: `signed_gap_profile_proof.txt`.
- Standalone actual signed-gap evidence: `signed-gap-profile-results/pilot-001/signed_gap_profile_evidence.pdf`.
- Exact persistent actual-arithmetic counterexamples: `signed-gap-profile-results/pilot-001/cofinal-audit-001/report.txt`.
- Cofinal root-plateau proof and distinct bound scopes: `signed_gap_cofinal_proof.txt`.
- Complete-window prime-cancellation evidence plot: `prime-discrepancy-results/pilot-001/prime_discrepancy_evidence.pdf`.
- Named imported global signed calibration: `signed-global-results/calibration-001/report.txt`.
- Finite correlation data: `mellin-search-results/pilot-001/correlation_obligations.json`.
- Standalone evidence plot: `mellin-search-results/pilot-001/signed_control_evidence.pdf`.
- Combined current objective and results: `root-results/candidate_registry.json` and `root-results/report.txt`.

The failed first analytic-audit attempt is retained with its original sources
and explanation: it serialized archived records in candidate-batch order while
the independent checker required archive order. The corrected audit used a
fresh audit directory; it did not consume or retune new finite evaluation data.

## Typed signed arithmetic preserves coupled cancellation

The separate `signed_arithmetic_search.py` stage explores exact signed sequence
programs and complete combinations of actual Mobius block energies. Its typed
language includes complete divisor inversion, Liouville square lift, convolution,
point products, signed rational weights, prefixes, index shifts/dilations/roots,
residue and coprimality masks, and rational power normalization. Finite resource
exhaustion remains an explicit missing result. Formal logarithmic atoms and
complex character kernels remain outside this first rational implementation.

A seeded recursive sampler records every generated program, duplicate, missing
computation and exploratory score. Those scores do not imply an ordinary-energy
bridge. A separate exact learner fits signed dilation stencils from anonymous
kernel moment responses, freezes all fitted constants and candidates, then tests
post-seal scales and parameters. The coefficient grid, polynomial moments, proof
methods and sampling literals are disclosed assumptions. Historical coefficient
prefixes and standard stencil responses can overlap these evaluations.

Every energy stencil retains its diagonal, one shared primitive-pair projection,
and complete dense signed residual. The reusable polygon-kernel certificate
proves zero density integral and a rational upper bound for weighted variation;
the supplied squarefree-discrepancy lemma then proves actual all-scale component
cancellation, charging every modulus. It supplies no critical bound on the dense
residual. Shared-cutoff Mobius reconstructions retain both signed cross moments
and the negative low-prefix square credit.

Higher vanishing moments have an explicit failure control: they can annihilate
cubic energy growth. Such small filtered responses do not by themselves control
the unfiltered Mobius energy. Nonnegative critical recurrences have a conditional
bridge, whose full all-scale signed inequality is still a premise. Mixed-sign
recurrences need an independently established recovery theorem. The filtered
Liouville squarefloor identity is a separate all-integer calibration.

Run `../.venv/bin/python run_expanded_probe.py --signed-arithmetic-only
--signed-arithmetic-run-dir signed-arithmetic-results/NEW_DIRECTORY` on one line.
An existing verified directory can be republished without rerunning its producer.
All failed runs and earlier successful source snapshots remain retained. The
research objective is still open: no RH-sufficient complete actual signed bound
has been established by this stage.

The subsequent parallel reviews sharpen this reduction without changing the
sealed pilot. They establish the explicit component charge
`U(w)*(11+16*q^2/9)*X^2*ceil(X^(1/q))` for every `q>=1`, with shared
`B=floor(X^(1/3))`. Thus a full signed upper bound is equivalent, after charging
this constant, to a bound on the complete dense signed remainder. The proof
and exact stored-constant counterexamples are in
`signed_arithmetic_review_proof.txt` and the separately verified review report.
Every zero-quadratic-moment scale polynomial also factors as `(T-4)B(T)`;
nonnegative coefficients of `B` give a broader conditional recovery rule via
a nonnegative transformed energy. They supply no new actual signed inequality.

## Complete convolution potentials

The separately verified `convolution-control-results/pilot-001` explores the
sampled convolution target `c=mu*lambda` using 54 nonnegative potentials that
retain signed mixed moments, complete divisor channels, and exact square/cube/
sixth-root scale selectors. The search compares 178 proposals, retaining 167
distinct programs and all 11 aliases. Forty contracts and 16 independent audit
groups pass; the sealed worker outputs replay byte for byte.

Five selected programs were evaluated at scales 8192, 11083, and 16384. There
were 27 finite passes, three dyadic failures of stored constants, and 30 missing
constants at unseen exponent levels. Both selected learned combinations failed
at X=8192,q=12; the baseline and one moving-square-root potential survived the
available cases. Every existential global signed estimate remains unresolved.

For `E=A_C/X^2` and any declared nonnegative potential `V`, a complete cofinal
bound on `E(2X)+V(2X)-E(X)-V(X)` would imply ordinary RH. Conversely, critical
C-energy makes every feature in this finite dictionary subpower. This expands
the possible form of a proof without supplying the missing prime information.
The exact identities and conditional argument are in `convolution_control_proof.txt`;
the experiment, limitations, and next pairing-language priority are documented
in `CONVOLUTION_CONTROL_HANDOFF.txt`. This is a separate research stage, with
no change to the prior native theorem count or RH-sufficient admissions.

The subsequent `arithmetic_filter_pole_budget.py` extension admits a broader
conditional bridge. For actual `mu^{*r}*lambda^{*l}`, put `k=r+l`. A nonzero
fixed filter with `m<=k` distinct dilation terms cannot erase an ordinary
off-critical zeta pole: its exponential-polynomial multiplier has zeros of
order at most `m-1`, whereas the target has poles of order at least `k`.
Thus critical filtered energy alone would imply RH without requiring a bounded
inverse of the filter. The Vandermonde/Mellin proof, independent analytical
review and five passing contracts are preserved in
`convolution-control-results/pole-budget-001`. The required filtered energy
bound is unproved. This extension was not used to select the prior pilot.
