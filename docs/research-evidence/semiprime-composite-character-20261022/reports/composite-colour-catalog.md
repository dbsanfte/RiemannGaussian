# Composite odd-modulus square-colour catalog: paid construction

22 October2026. Verdict: PASS. For any odd public m>=3 with gcd(m,N)=1 and unit row tags, the full quadratic-colour palette catalog can be explicitly acquired in soft O(m) native bit work. This removes the requirement that the ROW/CHARACTER ORDER m itself be prime. It does not evaluate the resulting common long products, nor acquire all Gauss-derived row vectors in softm. An auxiliary public prime ell=3mod4 may be selected first and m=(ell−1)/2 taken afterwards, avoiding a prescribed-prime-progression search for ell=1modm.

## Exact native mask, including nonunit discriminants

Let every canonical row have a,j units modulo odd m and the retained quotient identity. Put

    Delta=b²−4ac, kappa=−Delta/(4aj) modm,
    c_j=(4aj)^(−1) modm.

The map h→b+2ah is a bijection of Z/m because2a is a unit. Thus existence of h satisfying the native quadratic congruence is EXACTLY

    I modm ∈ kappa+c_j Squares(Z/m).

This includes all zero divisors and the zero discriminant. It is not restricted to Euler/Legendre tests on units. Local valuation parity and the unit square class, rather than a single Jacobi value modulo composite m, determine square solubility. The native true index retains this condition by the original integer discriminant identity.

Write m=product_l p_l^e_l, all p_l odd. Unit square classes are indexed by independent signs at the p_l, so there are2^omega(m) colors. Choose two public local unit representatives for each sign; CRT gives one global unit representative u_c per color. Define the actual ordered palette

    R_c=u_c Squares(Z/m),

and assign each row the color of c_j via its Legendre signs modulo the known p_l. A square unit multiple preserves the whole square IMAGE, including nonunits, so this assignment supplies exactly c_j Squares, not just its unit portion.

## Prime-power count and exact disjointness

For n=p^e and either local color,

    |Squares(Z/n)|=1+(1/2) sum_(0<=v<e,v even) phi(p^(e−v)).

Every nonzero square has an EVEN valuation v, and its unit part is square modulo p^(e−v). Conversely each such residue is square by odd-prime Hensel lifting after extracting p^v. Multiplication by a unit nonsquare at p exchanges the two unit square classes at every even valuation. Hence the two scaled square images are DISJOINT EXCEPT0, even when e>1. Their combined descriptor count, retaining0 once in each color, is

    2|Squares(Z/n)|=2+sum_(v even<e)phi(p^(e−v))<=n+1.

The inequality follows because the sum is at most sum_(k=1..e)phi(p^k)=p^e−1. No nonzero odd-valuation residue appears in either image. Thus the union need not cover Z/p^e for e>1; no such coverage is required or claimed.

By CRT, for the TOTAL size T of all actual color/residue lists,

    T=sum_c |R_c|
      =product_l 2|Squares(Z/p_l^e_l)|
      <=m product_l(1+p_l^(−e_l))
      <=m H_m<=m(1+logm).

For the second inequality, expanding the product gives reciprocal products of selected prime powers; these products are divisors of m, so their reciprocal sum is bounded by the full harmonic sum through m. The estimate counts repeated zero residues in different colors and repeated partial zero-components. Such cross-color repetitions are real output descriptors and are already charged. Each within-color list is a SET, with no duplicate roots from multiple square roots.

## Explicit deterministic algorithm and complete output cost

Factor m by trial division through sqrtm; this costs soft O(sqrtm) small-integer operations, within softm. Compute all prime powers n_l. Their sum is at most m for odd pairwise-coprime factors (induct on products of integers>=3); for a single factor equality holds.

For each n_l enumerate t=0,...,n_l−1 and mark t² mod n_l in an n_l-entry Boolean array. Collect the marked residues for the plus palette; multiply these by one acquired unit nonsquare to obtain the minus palette. Find a nonsquare by scanning p_l residues and using modular powering or the square table; the total scan cost is bounded by sum n_l<=m. Store each local list once, with its color label. The two lists share0 as separately charged colored entries.

Form their CRT Cartesian product, retaining both the color tuple and residue. CRT constants are public and cost logarithmic inverses modulo coprime integers. At each stage combine every partial colored residue with each entry of the next local colored list, using the standard two-modulus CRT formula. The final T entries are precisely every(color,residue) pair; no hidden factor or subgroup is used. Intermediate list sizes are bounded by the final T (indeed grow by factors at least4), so all stage work is soft O(T). Sort each final palette by integer residue. Deterministic sorting across all palettes uses soft O(T logm) bit work. Representatives and color labels use O(logm) bits apiece, and full output size is soft O(m), not merely an implicit catalog description.

For J native rows, modular inverses and the omega(m) Legendre signs of c_j cost soft O(J), with logarithmic factors. The number of colors is at most T, and palette IDs can be packed into omega(m) bits. Hence all catalog construction and row assignment costs soft O(m+J). For m=1 handle the degenerate one-residue/no-character case separately; it is irrelevant to the large native regime.

## All translations and boundary values remain paid

For each color use the SAME scalar common polynomial

    H_c(X)=product_(r∈R_c,n<K)(X−q^(r+mn)).

Write L=mK+t, set y_j=x_j q^(−kappa_j). The exact A/B/C index corrections in the two-prime-palette report depend only on an ordered residue subset R, not on primality or equal palette size. They therefore apply unchanged to every R_c. The row count is now D_j=K|R_c|+degA_j+degB_j−degC_j, and the q^(kappa_j D_j) normalization remains exact. K=0 uses the same symbolic A/C cancellation before evaluation.

Build the constant number of boundary channel product trees for every palette. At a fixed tree depth the TOTAL polynomial degree over ALL colors is O(T)=softm, not m times the number of colors. Every row requests O(1) nodes per depth in its one assigned palette, giving O(J) total requested evaluation points per depth. Batched monic MPE therefore acquires ALL boundary values in soft O(T+J)=soft O(m+J), with logarithmic depth overhead. Actual scalar root powers for the boundary channels are acquired in softm; catalog lookup does not require regenerating one power per color occurrence. All degree/output charges include unequal palette sizes and shared zeros.

No root-difference inversions occur. A proper boundary gcd factors. A saturated boundary product is localized once through its requested polynomial tree at soft degree<=softm cost. Its scalar leaf retains the original gamma exponent gap. The earlier uniform bound E_j>m²(L+m), derived from E_j>=N−3m², P,Q>16m², L<=4m², guarantees every native and denominator auxiliary leaf has a positive O(log N)-bit ledger. The composite catalog does not change those index ranges. This recovery statement assumes those retained canonical size/order hypotheses are established for the selected composite m; it does not assert them merely from the existence of the catalog. Unit a,j,4aj follow from gcd(N,m)=1 and a j²=N modm.

## Selecting ell first: what is repaired and what is not

Choose an arbitrary public prime ell=3mod4 in a constant-factor interval at the desired native scale, and set m=(ell−1)/2. Then m is odd and m|ell−1 automatically. A primitive character of order m modulo ell and its table can be acquired by the reviewed O(ell) public enumeration; ell=Theta(m). Thus the old additional requirement “find a small prime ell=1mod a PREASSIGNED prime m” is avoided. m is no longer required prime, so the composite catalog above is needed.

A fixed-modulus PNT in progression3mod4 ensures an appropriate prime in a sufficiently large fixed-ratio scale interval; a paid sieve over that interval finds it in softm. This uses a fixed progression, not an unproved uniform least-prime theorem for growing modulus. Choose the interval constants to preserve required scale inequalities such as N<=m^6; taking m too small by an arbitrary factor is not harmless. Before the Gauss/catalog construction, screen EACH distinct known prime p dividing m and the auxiliary ell individually against N. For a distinct-prime semiprime, any nonunit such gcd is a proper factor; this avoids the combined-gcd saturation that can occur if different public primes account for P and Q. If arbitrary nonsemiprime inputs are allowed, N equal to a public prime is explicitly an input-equality outcome, not a proper factor. No source theorem is inferred solely from selecting ell. The independently reviewed native bound for ALL retained P<=Q with P,Q>16m² and N<=m^6 is 13<I<(17/16)m²+3<4m² (m>=3), so the original positive index window remains applicable to this composite-m supply; it is not restricted to balanced hidden factors.

The repaired supply gives character order m at total carrier size ell=Theta(m), but full JOINT additive/character carrier rank is still m(ell−1)=Theta(m²). The packed C_E/A_E primitive lives in rank m, and does not acquire O(m) rank-m native targets in softm. Composite m also requires using the reviewed exceptional-character projectors, not pretending every component character is primitive.

The common H_c palette menu is now explicitly acquired, with total base root descriptors softm and all row-dependent boundary values paid. Its long products remain uncomputed. Neither an H evaluator, a Gauss paired-component localizer, universal useful relation existence nor a sixth-rate all-input algorithm follows from this supply repair.

Only this allocated scratch report was written. No repository edits, new agents, backend, examples or finite success campaign. Counts and construction are elementary CRT/square arithmetic under the retained native contracts.
