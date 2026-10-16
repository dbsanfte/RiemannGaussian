# Actual canonical endpoint bands miss every local collision on the retained majority family

2026-10-15. New classical counting argument extending the frozen source arithmetic. No Lean theorem or acquisition algorithm is claimed.

## Statement

Use the previously retained actual balanced prime-pair supply, with scale X=M³, literal sixth-width B=ceil(N^(1/6)), and up to K(N)<=floor(B^.020) consecutive candidate primes m>=B. Fix an integer envelope K_*=O(M^.020) dominating this menu, and any nonnegative integer band width w=w(M)<=M^.970. For each candidate m let L_m=2m²+2 and test ALL first-seed tags j=1,...,m-1 at ALL indices

    i in [-w,w] union [L_m-w,L_m+w],

with the obvious integer interpretation (and w eventually <L_m/2). The actual projected gamma and public first-seed residual are

    A_(j,i)=gamma^(N+delta_j)-gamma^(m² i),
    delta_j=a_j+m b_j-2a_j j.

The number of original ordered input pairs on which ANY such residual is nonunit, at ANY allowed m and in EITHER hidden field, is

    O(K_* (w+1) M^5) = O(M^5.990)

(the +1 includes the two endpoints when w=0). Therefore deleting those inputs together with all frozen soft O(M^5.994) deletions still leaves Omega(M^6/log² M) actual inputs satisfying ALL prior obstructions and having EVERY endpoint-band residual a unit in BOTH fields. This is an infinite actual-family counterexample to the specified endpoint-only observations.

For polylogarithmic w the observations are paid soft O(m) atomic ring/gcd probes per candidate modulus. For w=M^.970 they are NOT paid nearlinear; this stronger width is granted for coverage only. A polynomial-size menu is likewise granted free for the coverage obstruction, as in the frozen menu theorem; only polylogarithmic menus preserve the soft O(B) whole-menu acquisition clock.

## Historical source inputs and provenance

Restored via archive verifier, with no mutation:

* docs/research-evidence/research-checkpoint-20261012/index.json entry original_path /tmp/semiprime-next-covered-acquisition-20261008/full-euclid-all-hit-obstruction.md. Its §2 equations (E5)–(E10) supply the actual prime bin, projection, local orders and literal-selector strip bounds; §4–§6 equations (E16)–(E22) supply the exact source lift and false-tag uniqueness mechanism.
* /tmp/semiprime-long-norm-frontier-20261008/charged-skipped-ray-obstruction.md §2 records that same original supply and confirms source-faithful use of the full-N lifts.
* Journal docs/semiprime-factorisation-investigation.md dated 2026-10-08 menu extension, around the displayed (J4)–(J5), supplies the first-K candidate envelope and prior joint loss soft O(M^5.994).

The restored copies are under ../restored-endpoint/. Their exact uncompressed SHA256 values are in endpoint-band-source-pins.json beside this report. These historical inputs are reused, not reproved from the primary prime-distribution papers in this turn.

Concretely, original ordered primes P,Q lie in one fixed multiplicative bin of ratio at most 3/2 inside [cX,X], with mass Omega(M^6/log² M). They have P-1=v_P R_P and Q-1=v_Q R_Q with unique large primes R_P>P^.677, R_Q>Q^.677, and the cross-order exclusions. At every retained candidate m the actual projected gamma has EXACT local orders R_P,R_Q, uniformly R_P,R_Q>16m². Also P,P-1,Q,Q-1 are units modulo m², and m~M, eventually B<=m<=2B.

Write G_m=m-p_(-K_*)(m). The necessary menu-selector envelope is

    p_(-K_*)(m)^6<PQ<=m^6.

At fixed P,m its Q strip has length O(m² G_m), covered by O(G_m+1) half-open boxes of width at most m². The frozen telescoping estimate is

    sum_m (G_m+1)=O(K_* M).

No assumption about primes in short residue-class intervals is used.

## Exact public source formulas

For each tag j define the canonical a=a_j in {1,...,m-1} by

    a j² = N (mod m).

Let I_j be the literal public inverse of j modulo m, D_j=(N-a j²)/m and b_j=centered(m,-I_j D_j). Put ell_j=m b_j-2a j and delta_j=a+ell_j. The frozen native seedOffset bound is

    -3m²<=delta_j<=m².

In the P-field a residual vanishes precisely when

    Q+delta_j-m² i = K R_P                         (1)

for some integer K, because gamma has exact order R_P and P=1 mod R_P. This reduction keeps the full seed lift; it does not replace delta_j by its low digit or assume a local orbit decomposition.

## False tags: O(m) possible Q states per box and fixed index

Fix an admissible P, m, one half-open width-m² Q box, and one publicly chosen integer index i. The magnitude of i is irrelevant. Across the WHOLE box and ALL source tags, Q+delta_j-m²i lies in an interval of length at most 5m². Since R_P>16m², equation (1) allows O(1) values of K, uniformly in P,m,i and all source tags. A large fixed shift changes the location of this interval but not its length.

Fix one such K and one slope a in {1,...,m-1}. Reducing (1) modulo m and using P Q=a j² gives

    a j²-2aP j+aP-P K R_P = 0 (mod m).            (2)

This has at most two tags j because a is nonzero in the field F_m. This counts actual source qualifications rather than granting independent free tags.

Fix a,K,j, with FALSE tag j!=P mod m. If two qualifying Q,Q' give the same state, their slope constraint implies Q-Q' is divisible by m. The actual full-N lift gives

    m(b_j(Q)-b_j(Q')) = -I_j P (Q-Q') (mod m²).

Subtracting (1) then yields

    (1-I_j P)(Q-Q') = 0 (mod m²).

Since j!=P mod m, the coefficient 1-I_jP is a unit modulo m². Thus Q=Q' mod m² and a half-open box of width at most m² contains at most one such integer Q. This proves at most O(m) false-tag Q states per box per fixed index.

The bound is uniform in the exact prime order R_P; there is no need to enumerate v_P or pay a cofactor sum. Once P is fixed, its actual R_P is fixed. There are O(X)=O(M³) possible INTEGER P values in the bin. Summing m~M slopes/state budget, selector boxes, candidate m and at most 4w+2 endpoint indices gives

    false-hit input count
      <= C (w+1) X sum_m m(G_m+1)
      = O(K_* (w+1) M^5).                        (3)

Restricting back to actual prime P,Q only decreases this bound. Reversing the roles of the two hidden fields costs a factor two.

## Own tags: every local hit is the exact seed index, which lies away from both bands

At j=P mod m, the source quotient relation gives an integer seed index

    I=(aP+ell_j+Q)/m².

For completeness its integrality follows by multiplying the numerator by P: modulo m² it is a(P-j)²+(N-a j²)+m b_j P, which is zero since P-j is a multiple of m and b_j P=-D_j mod m. P is a unit modulo m², so the numerator itself is divisible by m².

Equation (1) at this tag becomes

    m²(I-i)-a(P-1)=K R_P.

The exact order is prime R_P>m, so R_P divides I-i. Both I and all queried i are O(m²). More explicitly, the fixed ratio <=3/2 bin gives P,Q<=sqrt(3/2)*sqrt(N)<=sqrt(3/2)*m³. Using 1<=a<m and ell_j=delta_j-a gives

    I <= P/m+Q/m²+1
      <= sqrt(3/2)*m²+O(m),
    I >= Q/m²-3-1/m >= c_1 M-O(1).

Here Q~M³ and m~M uniformly over the candidate menu. Therefore, for w<=M^.970=o(M), eventually

    w < I < L_m-w.

Also |I-i|<4m²<R_P for every endpoint i in the two-sided bands (also for every i in the full canonical rectangle), so R_P dividing I-i forces I=i. This contradicts membership in either endpoint band. Thus there are NO own-tag hits at all, uniformly over the original balanced supply and all candidate m, once M is large enough.

These statements apply with P,Q swapped, even though only the smaller prime was needed for the original coverage witness. They use the fixed ratio bound and public m range, not the ordering of the hidden factors.

## Consequence for signed short-shift cancellation

The full canonical rectangle still has the native forced seed hit and therefore nontrivial gcd. Nevertheless ALL endpoint-band observations are units on the remaining majority family. Products, inverses and gcds formed solely from these observed unit residuals remain units and cannot yield a proper factor through collision support. This does not exclude arbitrary additions that manufacture a new residual or an unrelated factoring computation.

The conclusion applies simultaneously to ALL finite integer-weighted shifted length-L_m stencils with shifts s in [-w,w] and augmentation sum_s c_s=0. Their exact labeled-factor multiplicity vanishes on the common interior [w,L_m-w), and all remaining support lies in [-w,w] union [L_m-w,L_m+w]. Every remaining numerator and denominator atomic factor is a unit on this counterfamily, so every such multiplicative boundary observable is a unit, for every source tag and every integer choice of weights. This is a simultaneous assertion for all stencils, not a union bound over their coefficients. It includes negative shifts and the upper endpoint L_m itself. Stencils with nonzero augmentation retain the long common-interior factors and remain outside the cheap boundary-only evaluator. Boundary sets at unrelated public starts or shifts outside [-w,w] need a separate count. No claim is made about all scalar algorithms, arbitrary gcd-only algorithms, or the still-unpaid long product oracle.

## Corollary: one prescribed public padded length family

Fix in advance ANY prescribed public integer length function m -> L_m satisfying

    2m²+2 <= L_m <= 4m².

The same theorem and identical deletion bound hold for the TWO-SIDED bands [-w,w] union [L_m-w,L_m+w], with all other hypotheses unchanged. This is one prescribed length family at a time; there is NO free simultaneous union over all length functions or all O(m²) possible lengths. Uniform proof constants do not license that extra union.

Proof. For false tags, the fixed-index argument above is independent of the index's magnitude. Replacing 2m²+2 by this prescribed L_m changes only the location of its at most 4w+2 endpoint indices, so equation (3) is unchanged. For own tags, I<=sqrt(3/2)m²+O(m) remains separated from every allowed upper band since L_m>=2m²+2. The lower-band exclusion is also unchanged. For every index in the new bands, |I-i|<5m²<R_P eventually, using L_m<=4m² and w=o(m). Thus the same order-divisibility argument forces I=i and gives a contradiction. All integer-weighted zero-augmentation stencils with shifts in [-w,w] now have their support in the new two-sided bands; their simultaneous multiplicative-unit conclusion follows exactly as before.

In particular this applies to the CURRENT NATIVE PADDED length `SemiprimeSeedSumAcquisition.seedLength m`. Its already compiled `seedLength_bounds` theorem, at RiemannGaussian/SemiprimeSeedSumAcquisition.lean lines 42–43, states 2*m²+2<=seedLength m and seedLength m<=4*m² for m>=4. The exact native source SHA256 is recorded in endpoint-band-source-pins.json; this corollary changes no native source and claims no new Lean theorem. The main canonical statement above retains L_m=2m²+2 unchanged.
