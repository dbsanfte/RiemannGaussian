# A cubic-in-P covering construction with fixed-rank lattice initialization

24 October2026. Scratch mathematical report. This is separate from native-lattice.md's small-root audits. Root proposed the cubic weight, its congruence lattice and derivative-volume ledger; this report checks and initializes the cover, centering, zero-exponent branch and scalar recovery.

Under the previously paid scalar-controller input, the construction below gives a complete soft-O(N^(2/9)) factor-cover acquisition and recovery route, equivalently soft-O(k^(4/3)) at k=Theta(N^(1/6)). It uses a LARGER row family and a shorter clock than the old k-row/k²-clock query. It does not solve that original fixed-input endpoint in soft k, does not reach one-sixth, and is slower than the known one-fifth factoring bound. No absolute novelty or best-known factoring rate is claimed. The proof uses a dimension-three short-vector guarantee, not heuristic independence of multivariate small-root polynomials.

## 1. Paid input and exact scalar consumer

Let N=PQ, P<Q, N<=k^6, k=Theta(N^(1/6)), H=k², and suppose the continuing branch has P,Q>16H. The actual supplied scalar beta is a unit modulo N, with both local orders odd, k-rough and >16H. It may be the already paid rough scalar controller; no norm-one W or character colours are needed for this NEW scalar covering family. The new seed will be q_c=beta^(k³), not the old coupled quadratic seed. Roughness implies gcd(k³,ord_P(beta))=gcd(k³,ord_Q(beta))=1, so q_c has the SAME local orders as beta.

For a supplied nonzero integer K of O(log N) bits with beta^K=1 modulo N, use the existing general short-annihilator extractor, NOT the bounded factor-sum theorem. Its exact source is

`/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/unbalanced-extractor.md`, SHA256 `a7765a14e4d0bc82339229f5f3bb445ad8f1f95bd22c49d631259d4e039195be`.

That theorem assumes odd local orders>16k², explicit nonzero polylog-bit K, and returns a factor in soft-O(k), with no balance or local-order factorization assumption. It has an asymptotic finite-input fallback. The present report ACQUIRES such K or a proper factor; it does not pass a local certificate or zero K into that theorem. Coprimality between the two local beta orders is not needed for this consumer, though the existing controller may supply it.

The report concerns this stated paid input branch. Composing the previously proved factor-or-controller preparation of soft-k cost does not alter its bound. It does not newly prove that preparation or the global executable/Lean bit theorem.

## 2. An actual rank-three congruence lattice for each tag

Fix any public unit tag1<=j<k. For integer coefficients a,b,c impose

    b+3aj=0 modulo k,
    cN-2aj³-bj²=0 modulo k².                      (1)

This is a full-rank sublattice Lambda_j of Z³ of determinant EXACTLY k³. To initialize it, write b=-3aj+ks; then

    c=N^-1(-a j³+k s j²) modulo k².

Let c0=[-j³N^-1]_(k²), c1=[k j²N^-1]_(k²). The three column vectors

    (1,-3j,c0), (0,k,c1), (0,0,k²)

are an actual basis, of determinant k³. N^-1 modulo k² and j^-1 modulo k³ are public modular inversions; if gcd(k,N)>1 it is already a proper factor. No hidden factor or finite-field oracle is used.

After a nonzero lattice vector (a,b,c) has been acquired, define an initial ell0 modulo k³ by

    ell0=-a j²-bj-cN j^-1 modulo k³.               (2)

Then f(X)=aX³+bX²+ell0 X+cN satisfies

    f(j)=0 mod k³, f'(j)=0 mod k², 3aj+b=0 mod k.

Expansion at j proves k³ divides f(j+kx) for EVERY integer x. In particular, at the own tag j=P modulo k, dividing f(P) by P is legitimate modulo k³ and gives the integer

    I0=(aP²+bP+cQ+ell0)/k³.                       (3)

This congruence is exact even if a=0. The dimension-three short-vector theorem alone does NOT guarantee a nonzero a. Degenerate vectors are retained with the same divisibility and recovery proof; no unproved genuine-cubic coefficient promise is inserted.

## 3. Choose weights by actual public short-vector computation

Take a public factor bin P near an integer centre P0>0, with |P-P0|<=Delta<=P0/2. Define

    F(X)=aX²+bX+cN/X.

The following rational linear map of (a,b,c) measures its variation:

    w1=Delta*(2aP0+b-cN/P0²),
    w2=Delta²*(a+cN/P0³),
    w3=Delta³*cN/P0^4.                            (4)

Its determinant has absolute value N Delta^6/P0^4. Therefore the image lattice has covolume

    det L=k³ N Delta^6/P0^4.                      (5)

It is initialized by applying (4) to the three basis vectors above. Clearing the common rational denominator gives a rank-three integer lattice with O(log N)-bit entries for the polynomially bounded parameters below. Apply ordinary LLL and rescale. The first reduced vector satisfies

    ||w||_infinity <= ||w||_2
             <=sqrt(2)*(det L)^(1/3)
             =sqrt(2)*k N^(1/3)Delta²/P0^(4/3).  (6)

This is the usual determinant first-vector bound in dimension3. Fixed dimension and O(log N)-bit entries give polylogarithmic bit cost per bin/tag. A nonzero image vector gives a nonzero(a,b,c) because (4) is invertible. No nearest-vector oracle, algebraic-independence assumption or numerical sampling is used.

For t=X-P0 the remainder identity is EXACT:

    F(P0+t)-F(P0)
      =F'(P0)t+(a+cN/P0³)t²
                   -cN t³/[P0³(P0+t)].          (7)

For |t|<=Delta<=P0/2, (7) and max|wi|<=T give

    |F(P0+t)-F(P0)|<=4T.                         (8)

The rational coefficient heights are controlled explicitly by (4):

    |c|<=T P0^4/(N Delta³),
    |a|<=T/Delta²+T P0/Delta³,
    |b|<=T/Delta+2|a|P0+|c|N/P0².

Thus a,b,c, and every later exponent have O(log N) bits when P0,Delta,T are polynomially bounded and Delta>=1. The tangent vector(a,b,c)=(N,-3NP0,-P0³), when integral and congruent, illustrates an exact cancellation direction but is NOT assigned a cheap height; the actual lattice bound(6) is what is used.

## 4. Explicit public floor centering, including the signed interval

Choose ell0 as its least nonnegative representative. Form the actual RATIONAL number

    Z=[ell0+F(P0)]/k³
      =[P0(ell0+aP0²+bP0)+cN]/(P0 k³).

Compute nu=floor(Z+1/2) by exact integer floor division, including when Z<0. Put ell_c=ell0-k³ nu. Then

    -1/2 <=[F(P0)+ell_c]/k³<1/2.

Let U=ceil(1/2+4T/k³), where T is a public bound from(6). The own centred integer I_c=I0-nu lies in[-U,U]. The entire SIGNED width, not just U, must be guarded. To query ordinary nonnegative indices, set

    ell=ell_c+k³ U,
    E=a+b+ell+cN,
    V=beta^E, q_c=beta^(k³), h=2U+1.              (9)

The actual own index is i=I_c+U in[0,h-1]. Targets in(9) use the actual signed exponent E; negative exponents are acquired using the known unit inverse of beta. Equivalently the centred target is beta^[a+b+ell0+cN-k³nu] before the final shift by U. No raw rational Taylor exponent or omitted carry is substituted for it.

At that own index the exact difference is

    E-k³ i=(P-1)[cQ-a(P+1)-b].                   (10)

Hence V=q_c^i modulo P, as a scalar equality, regardless of character colour. This is a NEW scalar cover over all unit tags; no subset of the previous plus/minus family replaces its own coverage theorem.

## 5. Repair ZERO integer exponents before taking any product

The nonzero triple(a,b,c) gives the nonzero integer polynomial

    J(X)=aX²+(a+b)X-cN.                          (11)

Before acquiring the query rows, isolate all INTEGER roots of(11) and test whether any is a proper divisor of N. For a!=0 use its actual integer discriminant and divisibility by2a; for a=0,b!=0 test the linear rational root exactly. If a=b=0,c!=0, (11) is a nonzero constant. This takes polylogarithmic bit cost and needs no multivariate resultant independence.

If the own exponent(10) were ZERO, then J(P)=0 and this preprocessing would already factor N. On the continuing branch, the own exponent is nonzero.

For EVERY acquired row also detect the purely public integer-zero position: E=k³ z with0<=z<h. Remove that ENTIRE row after the preprocessing above. This is coverage safe provided h<ord_P(q_c): if that row were the own row, (10)'s local collision and V=q_c^z would imply q_c^(i-z)=1 with |i-z|<h, forcing i=z and E-k³i=0. The quadratic precheck would already have factored. Therefore no surviving correct own row is removed. Rows with a zero position outside the queried interval need not be removed.

Every retained leaf consequently has a NONZERO integer K=E-k³ i of O(log N) bits. A proper gcd of beta^E-q_c^i with N factors. A saturated gcd proves beta^K=1 modulo N, and the general short-annihilator extractor in Section1 applies. It is NOT a near-N factor-sum witness; cN and the centred exponents may be large. No bounded-sum decoder is invoked.

## 6. Actually acquire bins, targets, clock polynomial and witnesses

Run over O(log N) public dyadic factor bins S<=P<2S, from S>=8H through S<=sqrt N, clipping the last bin. The actual smaller prime lies in one such bin. For that bin choose an integer Delta within a fixed factor of

    Delta_star=k S^(7/9)/N^(1/9),                 (12)

and cap it at S/4, with Delta>=1. Integer powers and a ninth-root computation compute these cutoffs without floating point. Cover the bin by O(1+S/Delta) public integer centres whose radius-Delta intervals cover every integer in it. Centres can be kept comparable to S, so the variation estimates are uniform. For each centre and each unit tag modulo k, acquire the rank-three lattice vector and its metadata. There are

    J_S=O(k(1+S/Delta))

such rows. For one common horizon use, for example, an integer T>=2(k³N Delta^6/S^4)^(1/3), rounding upwards. This bounds(6) for all centres>=S. Computing the common U and h by(9) makes every row and interval actual. Each row uses its own public nu but the SAME q_c and U.

Uniformly in these bins, Delta_star/S tends to0 and Delta_star tends to infinity, so the cap and lower cutoff affect only an absolute finite-input range. Moreover

    J_S=O(N^(1/9) S^(2/9)),
    h=O(1+N^(1/3)Delta²/(k² S^(4/3)))
      =O(N^(1/9) S^(2/9)).                       (13)

Both are at most O(N^(2/9)) since S<=sqrt N (fixed bin constants are harmless). In particular h<16H for all sufficiently large N, UNIFORMLY across bins. The implementation publicly checks this guard. If the asymptotic parameter conditions/guard fail, use deterministic trial division; the proven uniform asymptotics restrict this fallback to a finite set of N. Thus all local orders of the NEW q_c exceed the ENTIRE positive horizon h; this is order preservation from actual beta roughness, not an unsupported transfer from a coupled seed.

For a bin, acquire the actual polynomial

    P_h(Y)=product_(0<=i<h)(1-q_c^i Y)

by a product tree in soft-O(h) arithmetic. Acquire every retained target inverse V^-1 by signed binary powering, then monic multipoint evaluation of P_h at all those actual arguments costs soft-O(h+J_S). No target separation, q-log label or hidden field is required for this monic evaluation. The row values are acquired, not merely their known nonunit product. Scan their gcds; proper factors end the computation. On a saturated row, enumerate its h actual scalar leaves until finding a nonunit gcd, at extra soft-O(h). Proper gcd factors; saturation gives the nonzero K from Section5 and calls the general extractor. If a bin has no nonunit, continue. The correct bin has a surviving own row, so eventually a factor or consumable global annihilator is found.

All row, centre, signed-centering and original i metadata are retained. No polynomial pivot or lattice coefficient is itself assigned a factor witness. Row/interval restrictions may be rebuilt with the same stored labels; the completed factor algorithm already acquires every row value and explicitly localizes a leaf. The two-stage localisation handles different hits at the two primes, since any proper gcd ends the computation and a saturated scalar LEAF is the supplied global annihilator.

The complete bit ledger is therefore

    soft-O(sum_bins(J_S+h)+k)
                       =soft-O(N^(2/9))=soft-O(k^(4/3)), (14)

including fixed-dimensional LLL, integer root prechecks, exponents, gcds, actual clock coefficients/starts/outputs and one general recovery call. This is a larger-cover/smaller-clock algorithm, not an oracle for the original degree-k/length-k² polynomial. Its last step need not evaluate a long recurrence at all.

## 7. Scope, primary input and comparison

The exact lattice determinant and derivative coordinates were proposed by root and independently derived here. The algorithm uses the ordinary fixed-rank LLL guarantee, not Coppersmith root extraction. Primary: A.K.Lenstra,H.W.Lenstra Jr.,L.Lovasz, *Factoring Polynomials with Rational Coefficients*, Math.Ann.261(1982),515--534, Section1: [primary paper](https://www.math.ucdavis.edu/~deloera/MISC/LA-BIBLIO/trunk/Lovasz/LovaszLenstraLenstrafactor.pdf). Clearing rational denominators before lattice reduction is exact, and fixed dimension makes its bit cost polynomial in the coefficient bit length. The source's polynomial-factorization theorem is not being used as an integer-factorization oracle.

The prior journal's cubic Lehman descriptors near33998 expand in a MULTIPLIER variable and retain a separate carry; this construction instead uses the actual factor P, all residue tags, an index-k³ integer congruence lattice and real derivative weights. General lattice/Lehman and Taylor-cancellation ideas are old credit. No absolute novelty of an N^(2/9) intermediate factoring algorithm is claimed, and this is slower than the known fifth-bound route. The gain here is a checked alternative native-cover clock from k^(3/2) to k^(4/3), conditional only on the previously paid controller/recovery packet, with all newly required acquisition and zero-exponent branches supplied.

It does NOT give soft k, avoid all root/clock output acquisition, prove a lattice minimum lower bound, or complete the executable/Lean bit-complexity theorem. Higher-order weights might permit another parameter balance, but no such conclusion follows from the determinant of this one construction.

Primary cache: `sources/lll-1982.pdf`, SHA256 `dabefb8bcfb5dbb8b36a43745081f8ab6f18aadc85b1e252fd7c85abefc5f704`. The actual inherited general-annihilator report pin is stated in Section1. No repository/source edits or finite numerical examples were used.
