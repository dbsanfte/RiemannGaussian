# Full central payment and three arithmetic shortcut audits

Local research checkpoint, 2026-10-19. This continues the
[integral/primitive/native-moment checkpoint](arithmetic-operator-integral-primitive-moment.md)
and the [Siegel interpolation review](siegel-interpolation-review.md).
The imported strict `Re(s)>7/8` endpoint is unchanged.

## A full central estimate is now checked below the final imported wrapper

[QuasiRHFullCentralBelowBoundaryAudit](../scripts/QuasiRHFullCentralBelowBoundaryAudit.lean)
proves a bound for the **actual entire finite central contribution**, including
floor bins. If the actual Hecke zero supremum satisfies

\[
\frac{8749}{10000}\le\beta_\star\le\frac78,
\]

there are native fine data, with independent auxiliary gap `Delta=1/10000000`,
such that every compatible fixed source datum admits actual buffered bins and
a positive moving-height exponent for which

\[
\left|\frac{F_{\mathrm{all}}(Z)}{\mathcal N(Z)}\right|
\le C\,Z^{\beta_\star-11/16-1/250000}
\quad\text{eventually}.
\]

The original normalizer is nonzero. Selected marks, cube powers and overlaps,
calibration, physical slots, and both floor/nonfloor populations are retained.
The theorem constructs the genuine detector bins and their inequalities; it
does not assume a favorable partition. It accepts every compatible fixed
`SourceData`, including rebuilt finite exclusions. Constants and the chosen
height exponent may depend on that fixed datum and character.

The proof combines the previously checked four-field native moment producer
with the original nonfloor collection, floor estimate and exact supported
split. The finer data construction exposes positive costs bounded by `20t`
and `5t`, respectively. It uses the original `49/440640` nonfloor margin,
not an unproved substitution of the newer `1/5000` scalar certificate.
At the worst permitted parameters, the final exponent inequality has exact
spare `359/400000000`. The stronger interval beginning above `0.8748` remains
the earlier paper calculation; this checked endpoint starts at `0.8749`.

This is a central-row payment, not a physical-probe estimate. The source
ledger remains

\[
\text{normalized physical probe}
-\text{normalized central rows}.
\]

Removing the central rows leaves the physical probe. A theta-only source
allocation still requires the complete stated continuous/exterior transport,
and the unknown prime/square-core correlation remains unpaid. No zero
exclusion follows from the central bound alone.

## The auxiliary Hecke partners miss each other's physical windows

[QuasiRHAuxiliaryHeckeCorrelationAudit](../scripts/QuasiRHAuxiliaryHeckeCorrelationAudit.lean)
proves the exact scaling of the actual corrected marked coefficient under
`m -> l^2 m`. It retains the factor

\[
\chi_I(l)^2\chi_J(l)^6,
\]

including its nonunit zero mask, all cube powers and `I,J` overlaps.
For `l` coprime to `J`, the sixth-power cube factor is exactly one.

The proposed sextic `j=1`/`j=3` relation, still a paper-level finite-section
input, pairs numerator sizes differing by `q^2`, where `q=N(l)>=7`.
The actual canonical cutoff has support inside `[1/2,8]`. Lean proves

\[
\Omega(x)\ne0\quad\Longrightarrow\quad\Omega(q^2x)=0.
\]

Thus the direct pair has no simultaneous support in the same physical
window. Its discrepancy is an entire annulus, not a small boundary.
The remaining paper phase is a genuine cubic phase involving the product
of the numerator and selected ideal; it gives no automatic signed estimate.
Adjoining `l` to the selected ideal to absorb the Gauss factor would instead
kill the literal character because `l` divides the numerator.

This closes the direct fixed-tuple pairing and automatic incidence-average
shortcut. It does **not** exclude a future cross-tuple identity: changing the
unselected tuple can rescale the physical window, but also changes its slot
weights, Gaussian scale and completed mark. Those changes need an exact
weighted comparison and an independent estimate.

## The unsaturated order sector has real absolute mass

[ArithmeticOperatorPrimitiveGCDSourceAudit](../scripts/ArithmeticOperatorPrimitiveGCDSourceAudit.lean)
proves the ordinary integer identity

\[
\gcd(b^d-1,b^e-1)=b^{\gcd(d,e)}-1
\]

at every prime-power depth, plus uniqueness of the retained primitive
cyclotomic parent. For a square base `b=c^2`, it constructs a literal
primitive index `2<=d<=M` for every allowed prime `p<=2M+1`.
Thus the first extra annulus contains every such prime, with arbitrary
complex weights retained.

For every fixed base, quadratic reciprocity supplies a positive-density
subfamily in that annulus. Applying the explicit fixed-progression theorem
of Bennett–Martin–O'Bryant–Rechnitzer gives on paper

\[
E_{b,\kappa}(M;0)\ge \frac{M}{2\varphi(8b)}
\quad\text{eventually},\qquad\kappa>1\text{ fixed}.
\]

Consequently its termwise absolute mass cannot be paid at a source scale
`M^beta` with `beta<1`. The exact finite square-base inclusion is checked;
the AP-PNT/asymptotic application is clearly separated as paper work.
This lower bound does not lower-bound the twisted sum or determine its
zeta-zero residue. Density subtraction and signed order cancellation remain
distinct obligations.

Very thin windows `X=T+O(T^alpha)`, `alpha<beta`, evade this first-annulus
obstruction. But their difference from ordinary twisted Chebyshev is bounded
by the short-window mass plus `sqrt(X) log X` on paper. They preserve an
already known source while collapsing back to the old uncoded statistic.
No new independent estimate results.

## Positive same-base cutoff words collapse exactly

[ArithmeticOperatorNextInteractionAudit](../scripts/ArithmeticOperatorNextInteractionAudit.lean)
handles arbitrary finite words in the actual nested integers

\[
C_n(b)=\prod_{2\le e\le n}\Phi_e(b),
\]

using multiplication, GCD and LCM. Every word has exactly the prime support
of one original cutoff row. Its effective cutoff uses `max` for products
and LCMs, and `min` for GCDs. The complete first-prime-layer identity holds
for arbitrary complex weights and masks. The theorem also covers actual
primitive prefixes and proves coprimality of distinct primitive factors.

With a shared bounded depth weight and literal cutoff `p^r<=X`, the remaining
proper-power difference has the paper bound `floor(sqrt(X)) log X`, without
a word-height or word-size cost. Any source comparison still refers to the
same effective row. Saturation to ordinary Chebyshev requires
`X<=effective(word)`; outer notation `X=N` alone does not ensure this.

Signed division and different bases are outside the theorem. The literal
examples `C_6(2)/(C_2(2) C_3(2))=155` and `R_3(2)=R_6(3)=7` show why.
This closes a positive same-base composition class, not the entire
cutoff/GCD family.

## Remaining decision and validation

The best-defined unpaid target remains the **original prescribed signed
theta/marked-row covariance on prime and square cores**. A useful theorem
must control that correlation with the full finite-section phases, current
exclusions, mark/cube masks, moving physical lengths and original source
normalization. Local Hecke rewrites and positive cutoff-word compositions
have now been tested at precisely those interfaces.

Four isolated strict leaves contain 98 module-local declarations and
58 theorem declarations, including generated helpers. Each passes 15
namespace linters and all-local standard-axiom checks. Root reran the three
agent leaves and all 257,188 exact regression checks; an independent review
also checked 3,584 physical-depth majorants. Probes do not certify analytic
residue identities or new zero-free statements. Two small paper-domain
corrections are archived with before/after hashes; strict proofs are unchanged.

See the [frozen evidence manifest](arithmetic-operator-auxiliary-order-central-gates.json).
All work remains local, without broad CI, public/root registration, commit
or push. Eight Tier-1 families have been visited; none is marked exhausted.
