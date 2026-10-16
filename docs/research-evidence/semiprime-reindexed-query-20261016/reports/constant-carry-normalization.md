# Paid constant-carry normalization for the direct scalar norm

2026-10-16. A constructive preprocessing reduction on the actual source; it does not acquire the remaining scalar norm or improve its known exponent. No frozen artifact is modified.

Let d=m², q=gamma^d, delta_j the literal source offset in [-3d,d], and z_j=gamma^(-N-delta_j). Compute Euclidean division

    delta_j = r_j+d kappa_j,  0<=r_j<d.

Then kappa_j belongs to {-3,-2,-1,0,1}. Set w_j=gamma^(-N-r_j). These values, all powers, all carries, and all factors below are acquired in soft O(J log N) bit-scaled ring work (or soft O(J) ring work with usual logarithmic power costs). No local order or discrete logarithm is used. The residue r_j is the ACTUAL full input residue modulo d, not just N modulo m and not a freely chosen lift.

For H_ell(x)=prod_(0<=i<ell)(1-xq^i), any integer k obeys the following polynomial identities, including zeros:

    k>=0: H_ell(w q^(-k)) prod_(ell-k<=i<ell)(1-wq^i)
          =H_ell(w) prod_(-k<=i<0)(1-wq^i);

    k=-h<=0: H_ell(w q^h) prod_(0<=i<h)(1-wq^i)
          =H_ell(w) prod_(ell<=i<ell+h)(1-wq^i).

For ell<|k| these products are still the stated integer intervals and the identities still hold, by cancellation of labeled factors before specialization. Thus ALL rows of a common length and origin can be normalized simultaneously, using at most six numerator/denominator endpoint factors per row. On the branch where these factors are units, one batch inversion gives an exact unit multiplier U and

    prod_j H_ell(z_j q^a) = U prod_j H_ell(w_j q^a).          (1)

The same formulas apply to arbitrary tag subsets and common seed subinterval [a,a+ell), without reconstructing a long coefficient array. Multiplicity weights are retained when tags coincide. The reduction does not require unit differences between distinct nodes.

Composite safety is explicit. Take gcds of the O(J) endpoint factors before dividing. A proper gcd is already a factor. A gcd N is saturation and must not be inverted; (1) as a ratio is then unavailable until a separate valid recovery resolves it. The unmultiplied polynomial identities remain true. For the full canonical rectangle on the actual retained majority, the existing endpoint-band theorem (constant width at least 6 suffices) guarantees that every normalization endpoint factor is a unit in both fields: rewriting w_j=z_j q^kappa_j places the compared endpoints within a constant of the original row endpoints. Thus this positive reduction for the full canonical rectangle is unconditional on that already constructed majority. Arbitrary restricted rectangles require their own endpoint-unit checks; the canonical endpoint theorem does not guarantee their interior endpoints. It is not asserted to handle arbitrary saturated boundary events for free. At a valid canonical leaf, existing native global phase recovery remains available as before.

The strongest resulting scalar-only target can therefore be stated without centered carries:

    G_r(X)=prod_(j in S)(1-gamma^(-N-r_j) X),
    acquire prod_(0<=i<ell) G_r(q^(a+i)) in soft O(|S|+sqrt ell),
    r_j = delta_j(N,m) mod m² in {0,...,m²-1}.

For common origin a, one may absorb q^a into all roots. Crucially, the r_j form the literal high-digit-dependent modular graph. Their low digits are N(t²-2t) modulo m, but the remaining input digit survives the normalization. Equation (1) is a paid simplification, not a certificate that arbitrary modular graph nodes admit fast multipoint products. It grants no replacement of r_j by that low quadratic, no m-th root of unity, and no artificial relation gamma^(m²)=1.

This makes one useful positive distinction: high centered carries and restriction stability do not themselves cause a Jb coefficient charge. They are removable with O(J) acquired boundary metadata on the unit branch. On the endpoint-unit branch, any future scalar algorithm for the actual residue graph immediately extends to the corresponding original full rectangle or restricted rectangle with the same soft complexity; other branches require paid proper-factor or saturation handling. The principal missing step is the residue-graph norm itself. The new actual high-digit energy theorem rules out certain small progression carriers, but is not a lower bound against this scalar contract or against an amortized many-seed norm evaluator.

A focused primary search for materially different q-resultant/q-difference norm and hypergeometric multipoint product algorithms did not identify an applicable new theorem. No old velusqrt/BFSS/fixed-degree q-holonomic theorem is presented as a new failure result here, and no new primary PDF is retained: the positive identities above are self-contained finite polynomial identities.

## Exact inherited source references

* Native literal offset/bounds and phase: /home/dbsanfte/riemann/formal/RiemannGaussian/SemiprimeGlobalPhaseCancellation.lean, SHA256 9e061d01e511f908a33256c229ca87aab1a3401077e63941f6fc2cf025720a1a, 31743 bytes.
* Existing constant-width endpoint-unit majority: /home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-canonical-query-20261015/reports/endpoint-band-counterfamily.md, SHA256 882bbf2500add5deec9f90e0e46630b55a8c0a3f8e5ad72e8bc7bd68d4e2269e, 10881 bytes. This supplies fixed canonical length and one prescribed padded-length family; no simultaneous free union over arbitrary length functions is imported.
