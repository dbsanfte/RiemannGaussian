# Full weighted-ellipse completion, M1 admissibility and exact orbit overlap

26 October 2026. Paper-only native arithmetic experiment; no frozen repository edits, code or tests. **A concrete covered completion remains admissible for the one-moment consumer even with soft-K multiplicity. Its literal q-orbit union does not give a better uniform query bound: a correct balanced bin already contains an order-K primitive bulk with disjoint formal orbit intervals.** This is scoped to the specified completion/merging route, not a general acquisition lower bound.

Prior material read and credited: frozen pure-weighted/common-tag; packed-residue one-moment consumer; torus-query; colourquery/rectanglequery coverage and native-boundary; the fixed-pair chirp completion in fused-readout/quadratic-lifts. In particular completing an acquired fixed pair to all colours and reducing its square strata to GP strings is OLD credit. It is not the new operation claimed below.

## 1. Execute a full coefficient-ellipse completion

For each public factor-size bin B<=R<2B, acquire ALL signed nonaxis integer pairs with |a|,|b|<=K satisfying

    a²B^4+b²N² <= (2/sqrt(3))*K*B²*N,            (1)

and all unit colours j modulo K satisfying a*j²=b*N modulo K. Keep the actual stationary phase from the frozen formula, centered modulo H, and roots y=pi^ell*barpi^(a+bN), with the original clock and shifted-root ledger. Axes are separately restricted to (±K,0),(0,±K), as in the covered bank, and are retained ONLY when the same ellipse test (1) holds; for each retained axis keep all actual colours. No larger axis multiples or out-of-ellipse axes are added. This filter is necessary for the every-hit provenance below.

This is an explicit overcover of the original shortest-vector bank, not equality with it. The irrational comparison in (1) is exact integer arithmetic: if Q=a²B^4+b²N², test 3Q²<=4K²B^4N². The AM-GM bound gives |ab|<=K/sqrt(3)<K. Thus pairs can be enumerated from the signed hyperbola list in soft K before filtering; a K-by-K scan is unnecessary.

For nonaxis g=gcd(a,K)=gcd(b,K), the number of possible pairs at fixed g is O((K/g²)log K). Divide the stationary congruence by g. Unit roots modulo K/g have at most two square-root branches; lift their public 3-power roots and parity to all valid colours, at most 2g per pair. Summation of K log(K)/g over divisors of pure K=2*3^e is soft K since sum 1/g is bounded. All actual phases, numeric roots and bin labels therefore cost soft K. This enumeration is concrete and keeps every sign, canonical carry, axis and original witness.

In the correct bin, (1) gives the same every-row physical exponent bound as the original weighted construction. Hence every added good-field hit has exact integer provenance and colour R modulo K/g. Since g²<=|ab|<=K/sqrt(3), all hit colours still have the common residue R modulo n=3^ceil(e/2), including the axes' stronger full-K tag. Every row has at most one hit at each local component by h<16H. Thus the enlarged table has the common canonical square tag u=[R²]_n at every good hit.

## 2. M1 survives soft-K multiplicity: a paid enabling theorem

Use the explicit completed-ellipse bound J*<23K from `completed-source.md`: for real ellipse semiaxes A,B, AB=(2/sqrt(3))*K, the nonaxis colour count is at most 8AB*sum_(g|K)1/g<12sqrt(3)*K<21K. Filtered axes add at most 4phi(K)=4K/3, hence total <23K. This count has no hyperbola logarithm or asymptotic finite guard. Let J* be the acquired number of incidences and use the NEW family moment

    M1*=[delta^-1]sum_(completed rows,i)
                      [j²]_n/(delta+1-T_j*rho^i).

This is not numerical equality with the original-bank M1: multiplicities have changed. At the good field it is c=d*u with 1<=d<=J*<23K, 0<u<n. The old sharper d<=3^floor(e/2) is not assumed. Put M*=23K*n. Since n<=K/6 on native e>=3,

    c<M*<4H, padded recovery range <=4M*<16H<P,Q.

Thus the ALREADY PAID prime bound supplies finite-safe bounded-integer recovery. No extra small-factor prepass, asymptotic total-count guard or batching is needed. Recovery and trial factorization of c cost soft K. The explicit linear count and this simplification are credited to `completed-source.md`; they strengthen the earlier soft-K hyperbola estimate rather than being counted as a new scalar acquisition here.

The divisor-palette construction from the one-moment consumer still applies with d<=J*: retain divisors u of c having 0<u<n and 1<=c/u<=J*, test public unit-square status, take the two Hensel roots and their complements, and invoke ONE shared HH palette search. With the uniform divisor bound tau(c)=O(c^(1/12)), its size is O(K^(1/6)) by the coarse finite bound c<4K². Choose the same actual interval parameter

    A=ceil(cuberoot(K^4)), t_HH=ceil(16A/n).

The baby alphabet has length<K from nt_HH>=16K^(4/3), and all giant starts cost soft(S*t_HH)=soft K. The native beta^(n²) order guard is unchanged because n²|H. Every wrong-bin attempt is bounded and checked; continue after failure. The correct bin is guaranteed to succeed IF M1* is actually acquired.

This is an enabling theorem for this specific covered completion: the ORIGINAL small hit-count bound is unnecessary for moment ONE. It does not automatically extend to higher moments or arbitrary unit Lambert amplitudes, and it does not acquire M1*. Its old full acquisition still costs soft(J*+sqrt(J*h))=soft K^(5/4).

## 3. Exact literal q-overlap law with all carries

Before any numerical group specialization represent a row leaf by the formal exponent pair

    (A,L)=(a+bN, ell+H*M0-H*i),
    T_j*rho^i=barpi^A*pi^L.                    (2)

Two canonical rows are on the same LITERAL q orbit only if their A coordinates agree. Since |a|,|b|<=K and N>2K, equality a+bN=a'+b'N forces a=a', b=b'. Within that fixed pair, canonical phases lie in the same half-open length-H interval. Hence ell−ell'=H*t forces ell=ell', t=0. Distinct colour descriptions of that identical pair/phase may be deduplicated; their multiplicity is not a new orbit.

Thus full coefficient completion supplies no literal q-shift chain between distinct pairs, or between distinct canonical phases of one pair. Its higher-content GP-string contraction is the OLD chirp operation, using fractional smooth-power clocks and actual endpoint gates; it does not change this original canonical-orbit statement.

For a same-colour adjacent lattice basis, the exact canonical carry law is

    y_(v+w)=y_v*y_w*q^(-carry).

It changes A by addition, not by an integer q shift. An overlapping cone or Farey edge therefore provides a multiplicative character relation; it is not a shared q-clock interval whose bulk can be removed. Canonical carries in the L coordinate do not remove the A coordinate.

This is a formal-support statement only. Local modular root overlaps may occur and are precisely the interesting collisions; they are NOT excluded. A NUMERIC tested relation y_v=q^t*y_w has a nontrivial short mixed beta/W label unless the formal pairs in (2) coincide. The new consumer can factor from an actual localized such relation. That is not a free certificate of their absence, nor a way to acquire all shifts simultaneously. The supplied-fixed-shift factor-or-literal routine is prior credit; repeating it for h shifts is not soft K.

## 4. The primitive bulk blocks this particular literal-union strategy

Consider a correct balanced-size branch with B/sqrt(N) in [1/2,2]. Set L=floor(sqrt(K)/4). For all sufficiently large native K, consider positive pairs 1<=a,b<=L, a,b odd and prime to 3, with a*N=b modulo 3. These form an order-K subset: the admissible two residue classes modulo 6 each give order-L choices independently.

Every such pair satisfies (1), since

    (a²B^4+b²N²)/(B²N)
       =a²*(B²/N)+b²*(N/B²)<=8L²<=K/2.

Its content g is one. The unit b*N/a is 1 modulo 3 and odd, so it has exactly two unit square roots modulo K=2*3^e. Both associated canonical stationary phases are supplied. They are distinct: phases for j and −j cannot coincide modulo H, because their reduction ell=-2aj modulo 3 is nonzero and changes sign. Thus the completion contains order K DISTINCT primitive pair/phase orbits even in this small box.

Each such orbit has a full clock interval of length h. By §3 none of these intervals can merge literally with another orbit. Consequently their formal union mass is Omega(Kh). At the actual sixth-root scale N=Theta(K^6), h=Theta(K^(3/2)), giving Omega(K^(5/2)) mass. Inversion can only pair with negative A; it cannot merge distinct positive pairs of this bulk. Including the negative sector and folding inverses changes only a constant factor. The primitive g=1 chirp strata have m=1 and do not change their clock length.

This is a native conditional-branch count for the full ellipse, not a claim that every input is balanced or that arbitrary scalar circuits require that many operations. It also does not assert a numerically separated spectrum. It shows that THIS covered completion, followed only by literal orbit union/inversion and the inherited query engine, does not force the desired S_union=soft K². Cheap-first scheduling may exploit other actual bins; this count does not prevent that adaptive success on inputs where a correct bin has a smaller support statistic.

## Result and remaining constructive operation

The full ellipse is a soft-K acquired, coverage-preserving family whose M1 remains an adequate soft-K-recoverable output despite soft-K multiplicity. Its exact overlap law is now explicit and includes the phase carries. Adjacent-basis addition is not a q translation, and a correct balanced ellipse already has order-K primitive disjoint literal orbit intervals. Therefore no new uniform query rate follows from this completion/union execution.

A genuinely useful next operation would jointly contract the primitive positive-pair bulk with varying a+bN, or acquire localized numerical shift relations without running h separate fixed-shift tests. Alternatively a different public subfamily must retain coverage while reducing that primitive bulk or its actual windows. The statement here does not rule out either operation; it identifies the exact family and overlap structure they would have to exploit rather than claiming another decoder as acquisition.
