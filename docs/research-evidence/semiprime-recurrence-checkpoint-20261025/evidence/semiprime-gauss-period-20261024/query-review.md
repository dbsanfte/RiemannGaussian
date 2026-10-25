# Independent period query audit

2026-10-24. Verdict: **PASS**. No required fixes remain; the final source explicitly states raw/projected-point consistency and the palette-order distinction. Reviewed `/tmp/semiprime-gauss-period-20261024/period-query-attempt.md`, SHA256 `b876429f4ca01b324e5dec74d62a27706664942c023a5eb97487252df6152cb9`.

No repository or source edits. The exact algebra, initialized acquisition bound, and conditional folded recovery are valid. The condition concerns the separately acquired period-order guards; no raw period point inherits a projected-point order certificate automatically.

## Antipodes and three carry classes

For m=3 mod4, quadratic characters of opposite tags are opposite, a-values agree, and ell_j+ell_(m-j)=m²*t_j with t_j in {-2,-1,0}. Consequently T_j*T_(m-j)=q^t_j exactly. All carries are retained. The m=1 mod4 branch is explicitly left with the ordinary rank-two query; no character flip is assumed there.

Thus at most three carry classes need separate seeds, gauges and target polynomials. All O(m) rank-two row powers are paid by binary powering with O(log N)-bit exponents, so their total cost is soft m. This is a true constant-dimensional acquisition improvement over individually forming degree-m cyclic rows, but is not a shorter horizon or terminal evaluator.

## Hilbert 90 gauge with lawful units

For a=q^t, Norm(a)=1. Set C=T+a/T. Then bar(C)=a^-1 C. The first gauge v1=1+a has the same covariance and Norm(v1)=2+Tr(a). A proper scalar gcd gives a factor, a unit norm permits the conjugate-over-norm inverse, and gcd=N gives Tr(a)=-2 in R. In that last branch v=tau*(1-a) has the required covariance and norm -D*(2-Tr(a))=-4D, a certified unit. This works globally without choosing either hidden colour or a square root of a.

The ratios C/v and (q^i+a q^-i)/v are fixed by conjugation. Since 2 is a unit in R and {1,tau} is the free quadratic basis, their tau coordinates are zero, so these are genuine scalar targets/seeds. The stated Dickson recurrence and its two startup values follow directly from the two exponentials q^i and q^-i. All initialization is acquired; no recurrence boundary is assumed.

## Terminal polynomial, units and exact cost

For r targets in a carry class, G(Y)=prod(Y²-v*c_j*Y+a) has degree 2r and factors (Y-T_j)(Y-a/T_j). Its value at q^i is exactly v*q^i raised per target times the scalar product of s_i-c_j. Multiplication over i gives the displayed v and q prefactors in equation (2), including the exponent r*L*(L-1)/2. That exponent is an acquired integer, not modular division by two.

Constructing the length-b block polynomial costs soft(r b), including its degree 2r b. Geometric MPE at O(L/b) actual block starts and the short tail give soft(r b+L/b+r). The evaluation-point remainder tree is monic; no point difference or hit value is inverted. Optimizing b and summing the three class costs gives soft(m+sqrt(mL))=soft m^1.5. Pairing reduces target number while the conversion doubles terminal degree; no exponent reduction is claimed.

## Folded recovery, including split algebras

The factorization v(s_i-c_j)=(q^i-T_j)(q^i-a/T_j)/q^i is exact. In either hidden field, its scalar zero implies the product of the TWO scalar difference norms vanishes. A field has no zero divisors, so one difference norm vanishes; both compared points have norm one, hence the reviewed norm-one collision theorem forces equality in the ENTIRE local quadratic algebra, including the split case. The fold is therefore the OR of two ACTUAL row matches, not an uncontrolled componentwise zero. Its second root is exactly the antipodal original target at the SAME seed i; no extra seed outside the inherited horizon is needed.

After localizing a saturated scalar leaf, compute the two difference norms. A proper gcd factors N. Otherwise at least one difference norm has gcd=N and supplies a global collision of an actual original period row. On the separately paid surviving-point branch of period-recovery.md, its signed sum/difference decoder applies. A mixed direct/inverse orientation between P and Q already produces a proper gcd of one difference norm. This closes the fold-recovery gap conditionally; the report correctly does not import the original scalar beta decoder.

Raw/projected consistency: the point used to define T_j,q,c_j and the leaf norms must be the SAME point returned by the guarded controller when that decoder is invoked. Replacing raw W(x) by W(x)^M for a common known public M preserves all row/antipode identities and the dyadic W identity below. Applying different projection powers at the different scalar period points would require a new identity. The final reviewed source states this clarification explicitly, including that cheap palette-value acquisition does not pay for separate order screens. The earlier ambiguity is resolved without changing the mathematics or clock.

## Period-specific dyadic identity and palette costs

Each factor (x+zeta^r)(-x+zeta^r)=zeta^(2r)-x². Multiplication by 2 maps residues to themselves or the complementary set according to chi(2), proving U(x)U(-x)=U_chi(2)(-x²) with no omitted global sign. Taking conjugate quotients proves the W identity with exponent chi(2). It holds for signed exponent k because all W points are units.

For beta, -beta and -beta², the norm numerators/denominators listed in the source are correct. Odd local beta order excludes beta^a=-1, and the >16m² bound excludes beta^m=1, beta^(2m)=1, beta=1 and beta²=1. Dyadic positive powers preserve the odd order. Therefore every stated signed dyadic point has the certified scalar norm inverse. A requested K dyadic values is generated by K modular squarings/sign choices, and degree-O(m) Gauss polynomials are evaluated there by monic MPE in soft(m+K). This pays acquisition and every scalar unit guard, not all local-order certificates. K independent q-order screens would cost soft(Km); one may scan projected candidates using cheap gcd checks, select one surviving point, and screen that point once in soft m. A constant-size three-point dyadic family can each be screened within soft m, but an O(m)-point value palette is not an O(m)-point certified-order palette. Arbitrary scalar nodes do not inherit the unit guards, and O(Km) separate native row powers remain charged.

The exponentiated dyadic relation has a globally zero residual for every k, so cannot select a native hit. Its difference-product expansion is exact, but remains a product of sums of exponential sequences. Two ordinary geometric-product queries acquire the aggregate at the old soft sqrt(JL) scale. A single shorter difference, halved horizon, free scalar orbit closure or zero-support cancellation does not follow. The report makes these limitations explicit.

No new covered soft-m terminal query or all-input surviving-point theorem is supplied. The report's positive outputs are initialized scalar folding and the exact period-specific bridge, with conditional recovery and the old terminal clock.
