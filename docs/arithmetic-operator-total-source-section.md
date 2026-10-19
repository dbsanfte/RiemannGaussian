# Total determinant source and native sextic section

Local research checkpoint, 2026-10-19. The Banks interpolation review
continues through four source/applicability tests. Three isolated Lean
leaves pass; no independent signed endpoint estimate has been obtained.
The imported strict `Re(s)>7/8` result is unchanged. The current target
remains `1/2<beta<=7/8`.

## 1. Growing determinant size does not rescue this ordinary logarithm

The previous fixed-construction logarithmic audit left growing matrix
size open. We tested the actual rank-`N` Gaussian Jacobi–Trudi determinant
for an `N` by `N` by `N` plane-partition box, at a fixed integer base
`b>=2`. Its exact ordinary logarithm is

\[
\log D_N(b)=\frac{3N^3-N^2}{2}\log b+F_N(1/b).
\]

For `0<q<1`, the entire finite boundary sums exactly to

\[
F_N(q)=\sum_{k\ge1}\frac{q^k}{k(1-q^k)^2}(1-q^{kN})^3,
\qquad
0\le\Lambda(q)-F_N(q)\le3\Lambda(q)q^N,
\]

where `Lambda` is the same sum with its last factor replaced by one.
[ArithmeticOperatorGrowingQBoxAudit.lean](../scripts/ArithmeticOperatorGrowingQBoxAudit.lean)
proves the finite product/logarithm bridge, reciprocal cubic height,
Lambert expansion, geometric defect, and summability of all polynomial
absolute residual moments.

The determinant identification is paper-level: [Krattenthaler, Theorem 26,
equation (3.11)](https://arxiv.org/abs/math/9902004), together with
[Lai, equation (1.2)](https://arxiv.org/abs/1710.02241). It is not an
unproved Lean import. Exact integer regression checks the indexing, and
an independent Pascal/Bareiss calculation confirms it.

After removing the complete height and constant, the ordinary row
Dirichlet series is entire. Before centering, its only possible poles
are the elementary poles `4,3,1`. These refer to
`sum_N log(D_N)*N^(-s)`, not a differently normalized continuous Mellin
integral. Thus this particular growing-rank statistic fails the zero-source
test. Freeze it before building estimates. Moving bases, other growing
geometries, prime-depth phases and common-base correlations remain outside
this result.

## 2. The total unsaturated trace needs a growing-divisor source theorem

The actual cyclotomic product `C_N(b)=prod_(2<=n<=N) Phi_n(b)` has prime
complete-base trace

\[
W_N(p)=\frac{1}{p}\left(\mathbf1_{p\le N}
 +\sum_{\substack{d\mid p-1\\2\le d\le N}}\varphi(d)\right).
\]

[ArithmeticOperatorQDetTotalKernelAudit.lean](../scripts/ArithmeticOperatorQDetTotalKernelAudit.lean)
proves its finite reindexing for arbitrary weights on literal primes and
its saturated endpoint. The preceding actual cyclotomic leaf supplies
the integer-product-to-trace bridge.

With `N=floor T`, `X=T^kappa`, the **total** prime-layer Mellin transform,
initially for `Re(s)>1`, is

\[
sM_\kappa(s;y)=D_P(s+1+iy)+
\sum_p\frac{\log p}{p^{1+iy}}
 \sum_{\substack{d\mid p-1\\d\ge2}}
 \frac{\varphi(d)}{\max(d,p^{1/\kappa})^s}.
\]

Here `D_P` is the ordinary-prime logarithmic series. The max cutoff is
literal. Divisor switching leaves `p=kd+1` prime and the boundary
`kd+1<=d^kappa`; neither can be removed for free.

Every fixed-`d` sector is holomorphic for `Re(s)>0`. This does **not**
make the whole sum holomorphic there. Indeed the actual `kappa=1`
endpoint equals `[D_P(s+iy)-D_P(s+1+iy)]/s` and retains the matched
zero source. Any positive source at `kappa>1` must arise from the
nonuniform growing-divisor tail. Its continuation and nonzero residue
are unproved; the principal reference alone does not decide them.

The checked Titchmarsh literature includes a zero-explicit formula, so
the obstruction is not absence of all such formulas. Its actual weights,
moving cutoff, conductor range and error do not furnish the needed
source-scale theorem here. These analytic conclusions are paper-level.
The prior proper-prime-power payment, finite-base discrepancy and height
costs remain intact. Complete-base averaging is still not one common base.

## 3. Native calibration is fixed; the section normalization is now explicit

The actual `SourceData` chooses its finite calibration set before the
limit `Z->infinity`. Its good-prime factors assemble into a fixed
numerator multiplier `M_C`, with `N M_C <= K_C^4`. The previously proved
actual sixth-power symmetry permits the required finite bad-ray character
expansion; arbitrary period-72 invariance is not substituted for it.

The necessary Fourier extraction is, at paper level,

\[
(N M_C)^{5/12}U_{-M_C}f,
\qquad
\rho_{U_bf}(m)=(Nb)^{-5/12}\rho_f(bm).
\]

It preserves the normalized infinity constant. This identifies the exact
operator and factor that were missing from a bare `rho(M_C*m)` notation.
It still requires the actual inverse-Kubota lifts, cusp/scattering vector,
Fourier normalizer and physical-mask identification. The nonzero infinity
constant is not a source theorem for the original detector: its physical
weight excludes zero numerator. No new Lean automorphic bridge is claimed.

## 4. Automatic residual projection does not supply cancellation

[QuasiRHResidualProjectionAudit.lean](../scripts/QuasiRHResidualProjectionAudit.lean)
proves on the actual good odd maximal Eisenstein quotient that the
principal zero-frequency unit sum is nonzero, while the canonical sextic
one vanishes. The complete profiles differ. Thus the native principal
Ramanujan profile cannot be replaced directly by a sextic Kloosterman
profile. A standard nonzero-frequency formula also cannot simply be
evaluated at a zero slot.

Conditionally on constructing the native automorphic pairing,
subtracting its residual projection removes the **entire** unpaid theta
covariance. The projection coefficients are full Fourier covariances,
not just cusp constants or the already-cancelled Mellin moment. No
identity makes the scalar Patterson model that projection. Source
retention after centering therefore needs an additional exact theorem.
This freezes the automatic substitution/projection shortcut, not every
possible coupled spectral estimate.

## Validation and next gate

The three strict leaves have 76 local declarations / 62 theorem
declarations including helpers, 15 namespace linters each, and only
`propext`, `Classical.choice`, `Quot.sound`. Root reran them and the
three exact regressions. The growing-box test has 5,760 exact checks,
the total kernel 1,018, and the fixed section extraction 40; a separate
review adds 20 independent determinant checks. Finite probes do not
certify the paper-level analytic statements.

Detailed preflights, primary PDFs, commands, axiom reports and preservation
hashes are indexed by
[the checkpoint manifest](arithmetic-operator-total-source-section-gates.json).
All 269 preceding pins and 57 additional agent pins matched before
shared notes changed. No root/public registration, broad CI, commit or
push was performed.

The next useful results remain a genuine growing-divisor source/covariance
theorem, or a native sextic section/projection identity that demonstrably
retains the original detector source. Repeating fixed-sector or ordinary
row-log estimates cannot discharge either requirement. Eight Tier-1
families have been visited; none is declared exhausted.
