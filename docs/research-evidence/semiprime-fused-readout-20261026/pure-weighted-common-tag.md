# Pure weighted torus rows with one common factor-residue tag

26 October 2026. Original-source audit and complete paper composition. No repository changes, tests, numerical campaign, implementation or Lean.

**PASS: a stronger uniform acquisition target.** The old weighted construction already uses ALL unit tags and fixed barpi, without chi_D(j). It therefore transfers to the independently licensed pure K=2·3^e preparation. In each correct nonsplit-factor bin, EVERY clock hit—including axes and nonprimitive rows—has the SAME factor residue modulo n*=3^ceil(e/2)~sqrt K. Two additive simple-pole coefficients for the whole bin consequently give (d,dr), with 1<=d<=J<R. There is no content-sector palette, unique-hit premise, row-separation prerequisite or hit-depth search. The coefficients are not acquired in soft K by this theorem. The old division-free row-value engine **does** complete factoring on this new pure bank at the retained soft K^(5/4) bound, with a new flag/tag consumer that needs no old chi-dependent saturated-leaf decoder.

## 1. Original sources and conductor removal

Read the original [signed-two-weight-query §§1–6](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-recurrence-checkpoint-20261025/evidence/semiprime-arithmetic-query-reuse-20261024/signed-two-weight-query.md), the [journal's complete signed-weight composition at line 43815](/home/dbsanfte/riemann/formal/docs/semiprime-factorisation-investigation.md:43815), and the current [pure-modulus original-supplier audit](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-projective-readout-20261026/pure-modulus-preparation.md).

The original weighted source §2 explicitly enumerates EVERY unit j modulo its k and constructs V_j=pi^ell_j*barpi^(a+bN). Its §3 Frobenius and §5 every-hit integer bound use no character of j. The old c0|k setup choice is therefore not a row/proof requirement here. Replace it with the fully rerun pure preparation:

    K=2·3^e~N^(1/6), e>=3, H=K²,
    N=PQ<=K^6, P<Q, P,Q>16H,
    D<0 fundamental, |D|<=K/2, Jacobi(D,N)=-1.

All actual scalar/torus suppliers, smooth killing and coupled q screen are rerun. They cost soft K and supply odd K-rough beta and W, pi=beta W, barpi=beta/W, q=pi^H, and global units 1-q^s for 1<=s<=16H. At the unique nonsplit prime R (either P or Q), the odd scalar/torus orders divide R-1,R+1 and are coprime, giving

    ord_R(pi)=ord_R(q)>256H².

Initial D discovery retains the old unconditional soft N^(5/32) scan, public |D| guard and explicit verified finite-exception fallback. No QRH orientation or new analytic threshold is imported. All factors of K are known. None of these suppliers needs c0|K once chi_D(j)-dependent old rows are not reused.

This is not an operation “erase chi from already acquired old roots”: acquire the new Gauss rows/phases at the new K. Relative to the closest **original weighted** source there is no colour-row expansion: it already had all units and fixed barpi. Relative to older half-colour canonical constructions, retaining both character signs is at most a factor-two count at the same conductor-aware modulus; that comparison does not identify roots across changed moduli. The present count is simply J=phi(K)=K/3 per bin.

## 2. All bins and actual weighted inputs are acquired in soft K

For every dyadic bin B0<=R<2B0, with public powers of two 1<=B0<=N, and every unit j in [1,K), compute s=[N j^-2]_K. Exact Gauss reduction of

    (K B0²,0), (s B0²,N)

returns a nonzero shortest lattice vector (a B0²,bN), with

    a*j²=b*N mod K,
    a² B0^4+b² N² <= (2/sqrt3)*K B0² N.          (1)

The determinant is K B0²N. Integer arithmetic and exact reduction have polynomial(log N) cost per row; all coefficients have O(log N) bits even in wrong bins. No local sign of D is used. There are O(log N) bins and J<=K rows each, total soft K acquisition.

Compute the integers

    D_j=(a j²-bN)/K,
    t_j=[D_j*j^-1]_K,
    ell_j=[-2aj+K t_j]_H centered in [-H/2,H/2),
    y_j=pi^ell_j*barpi^(a+bN).

For f_j(X)=aX²+ell_j X+bN, exactly

    f_j(j)=0 mod H, f'_j(j)=0 mod K.              (2)

All signed powers, inverses of unit j, integer labels and actual roots are acquired; no factor is an exponent input. Axes, both signs, ties of the deterministic shortest-vector routine and nonprimitive integer contents remain allowed. No integer-zero deletion or chi mask is needed.

In the correct bin, (1) implies for EVERY row

    |a|R+|b|N/R <4sqrt(KN).                       (3)

This is precisely the original weighted norm proof; changing K's factors does not change it. Let Dceil=ceil(sqrt(KN)) and set

    M0=ceil(4Dceil/H)+2, h=2M0+1,
    T_j=q^M0*y_j, 0<=t<h, i=t-M0.

The source proves h=O(1+sqrt N/K^(3/2))=O(K^(3/2)) and h<16H on K>16. All geometric start/endpoint powers are paid. Each row has at most one hit at any local field/component, by the actual q-order guard.

## 3. Guaranteed cover and EXACT provenance of every good-bin hit

At the own tag j=[R]_K, (2) gives f_j(R)=0 mod H and hence

    I=(aR+b(N/R)+ell_j)/H is an integer.

Equation (3) places it inside [-M0,M0]. Frobenius at the nonsplit field gives for EVERY row

    y_j=pi^[aR+b(N/R)+ell_j].                    (4)

Thus the own tag supplies a hit. The proof works whether R is smaller or larger and uses fixed barpi throughout.

Conversely a hit y_j=q^i in that same bin has ord_R(pi) dividing

    L=aR+b(N/R)+ell_j-H i.

The original every-row/every-index bound is

    |L|<8sqrt(KN)+(7/2)H+4<3H²<ord_R(pi),

so L=0 as an INTEGER. Consequently f_j(R)=0 mod H for every good-bin hit, not just the own tag. Wrong-bin aliases have no such tag guarantee; bin outputs must remain separately validated.

## 4. Contents and axes all reduce to one modulus

For a nonaxis row let g=gcd(a,K)=gcd(b,K). Equality follows prime-by-prime from a j²=bN mod K and j,N units. From (1), independently of the bin,

    |ab| <= K/sqrt3,
    g² <= |ab| < K.                              (5)

To prove the content tag, put x=R-j. By (2), for integers c,d,

    f_j(R)=a x²+K c x+K² d.

Fix a prime l^vK||K. If v_l(a)=v<vK and v_l(x)=u<vK-v, then the first term has valuation v+2u, strictly below the second's lower bound vK+u and below 2vK. It would be the unique lowest term, contradicting H|f_j(R). Thus K/g divides R-j. No inverse of a,b or g was used.

Write g=2^alpha*3^v with alpha=0 or 1. By (5), 3^(2v)<=g²<2*3^e, so 2v<=e and v<=floor(e/2). Therefore

    n*=3^ceil(e/2) divides K/g

for every nonaxis row. It is a divisor of K and lies between sqrt(K/2) and sqrt(3K/2). In particular n*>=K^(1/3) on the native e>=3 range.

For axes the shortest lattice vector must be (+/-K,0) or (0,+/-K), since a larger axis multiple is not shortest. If b=0, the stationary phase is ell=-a j mod H and

    f_j(R)=a R(R-j) mod H,

forcing R=j mod K. If a=0, ell=-bN/j mod H and

    f_j(R)=bN(1-R/j) mod H,

again forcing R=j mod K. Hence the axes carry the full K tag and certainly the same n* tag. They are not scalar accidental-alias axes: exact-integer provenance (4) is essential.

It follows that ALL good-bin hits across all contents and axes have

    w_j=[j]_(n*)=[R]_(n*)=:r.                    (6)

There is no sector splitting or root separation in this statement.

## 5. Whole-bin additive simple-pole target and its paid consumer

Normalize each leaf as a_jt=1-T_j q^-t and define the pair componentwise by finite Laurent coefficients:

    V_bin=[delta^0] delta*sum_(j,t) 1/(a_jt+delta),
    U_bin=[delta^0] delta*sum_(j,t) w_j/(a_jt+delta). (7)

At a local component a nonzero leaf contributes zero to this coefficient and a zero leaf contributes 1 (or w_j). These are additive hit counts, not cofactor amplitudes. At the good nonsplit field, coverage and (6) give

    (V_bin,U_bin)=(d,d*r), 1<=d<=J<R.             (8)

Multiplicity of repeated row roots is counted, and still d<=J because each row has at most one hit. Thus the denominator is nonzero without d-search or high Hasse depth. The Laurent definition is not a supplied algorithm for inversion with a nonunit constant term over B; acquiring (7) remains the new target.

Given an actual pair (7), the old norm/coordinate validator applies: a proper norm gcd of V factors; norm gcd N declines this attempt (it cannot occur for the good bin); a unit norm permits certified inversion of V. The tau-coordinate of U/V then yields a proper factor, a rejected attempt or a global base scalar, and the scan through 0<=r<n* yields a proper factor or a correct small residue on the good attempt. Wrong attempts may fail boundedly. Keep unit residues and complement by N/r mod n* to accommodate either factor. The restricted HH consumer uses beta^(n*²), whose local orders exceed the supplied beta^H orders since n*²|H. Its cost is soft K for a single correct residue at this n*. Running all O(log N) bin attempts retains soft K and must continue after any unverified wrong-bin candidate.

Thus one pair per WHOLE bin suffices, rather than content pairs, multiple-hit polynomial coefficients or a palette of lifted sector residues. The consumer is unconditional on orientation and root separation once the actual weak pairs are supplied. It is not a supplier for them.

## 6. Completed pure-bank baseline, without the old saturated-root consumer

The new bank also has a COMPLETE retained-bound algorithm, not just conditional coefficients. For every bin acquire ALL row values

    R_j=product_(t=0)^(h-1)(1-T_j q^-t)

with the old division-free shared row-value engine. Its block polynomial of degree d≈sqrt(Jh), all giant starts, every per-row accumulation and the clipped tail cost soft(J+sqrt(Jh)). Repeated roots and collision zeros are allowed.

Classify each actual R_j by norm and coordinates. Proper norm gcd factors. A unit norm certifies a global unit. For saturated norm, the nonsplit field forces BOTH coordinates divisible by R; therefore the common coordinate gcd is proper, or both coordinates vanish globally. There is no leftover ambiguous split-only branch because a nonsplit prime exists. On no-factor continuation every row value is consequently a **global unit or globally zero**, certified in soft J.

Set flag_j=0 or 1 accordingly. Each component has at most one clock hit in a row, so these are exactly its simple-pole hit indicators, including on every split coordinate. Therefore

    V_bin=sum_j flag_j,
    U_bin=sum_j w_j flag_j

are the ACTUAL coefficients (7), acquired by the row-value engine plus soft-J arithmetic. No annihilator is invoked on an additive zero, discriminant product, global row-value zero or its long product. In the correct bin all flagged weights are the same integer r; one can also directly retain that common tag. In either form (8) and the guarded HH validator complete factoring.

This replaces the old signed-weight saturated LEAF/root consumer for this completion: no chi-dependent canonical recovery, clock-index localization, original-beta root label or global-beta annihilator is needed. The method still attempts bins separately and accepts only verified factors. The correct bin is guaranteed to have d>=1; an incorrect bin cannot suppress its later attempt.

Charging setup, all bins, all row values, classifications, candidate scans and HH gives

    soft(K+sqrt(Kh))=soft K^(5/4)

at h=O(K^(3/2)), with the inherited finite setup fallbacks. This is the retained rate, not an exponent gain. The new positive result is a simpler whole-bin common-tag/first-pole interface, with an independently certified complete baseline on the pure bank. A soft-K acquisition of (7), or another correctly marked whole-bin statistic, remains the missing step for the sixth-rate goal.
