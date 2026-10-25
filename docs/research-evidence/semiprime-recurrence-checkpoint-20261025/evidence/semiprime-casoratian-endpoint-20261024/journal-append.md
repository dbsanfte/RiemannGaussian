
## Initialized boundary states and native square lifts, 2026-10-24

No full-query exponent improvement was obtained in this pass. The
complete prepared query remains soft sqrt(JL)=soft k^(3/2), and the
all-semiprime sixth-rate algorithm, unconditional orientation and Lean
bit-complexity theorem remain open. The following are executed finite
candidates with their missing acquisition identified, not new backend
lemmas or numerical coverage evidence.

For the acquired short Casoratian normalizer R and unknown long matrix
M=diag(a_i)R, a_i=P_L(z_i), acquire u=1 and v^T=1^T R. Over the actual
commutative algebra, without any a_i inversion,

    det(M+epsilon*u*v^T)=det(R)*(Z+epsilon*S),
    Z=prod_i a_i, S=sum_i prod_(j!=i) a_j.

A global rank-one perturbation of the block family gives the sum of
all elementary cofactors. Weighting its right-vector segment by the
coarse class label gives a second coefficient. At the unique good
collision their ratio is the desired coarse label. Both perturbing
vectors and every normalizer are actually acquired in soft k; the two
long determinant coefficients are not acquired by this identity.

The full-r finite window test transports BOTH necessary states. Put
Z_t=prod_(h=t)^(t+r-1) a_h and S_t its elementary cofactor sum. Then

    a_t Z_(t+1)=a_(t+r) Z_t,
    a_t S_(t+1)+Z_(t+1)=a_(t+r) S_t+Z_t.

With unit endpoints and c_t=a_(t+r)/a_t, the actual transfer matrix is
[[c_t,0],[(1-c_t)/a_t,c_t]]. Its endpoint coefficients are acquired by
the earlier cheaper batch. At an interior hit, Z_t=0 and S_t!=0, so
the transfer only rescales the unacquired S_t. The normalized subtraction
again removes the desired signal. No periodic boundary is supplied by
E^(r²)=q^a, and the known zero-parameter state (1,r) belongs to a
different multiplicative orbit. This calculation uses full-r windows;
deduplicated determinant classes are not silently put in their place.

A separate local arithmetic test finds a genuine square relation in
DISTINGUISHED INTEGER exponents. Write k=d r³, m=d r², H=m²r²,
A=A_c, A J0²=N mod H, and theta=pi^(m²). Known centered carries give
ell0=-2A J0+H u0 and ell1=-2m J0+H u1. The known phase exponent is
a=-ell2/m²=-J0/A mod r², a unit. At the good smaller nonsplit P in
this class, t=(P-J0)/m and

    c=-(A P+Q-2A J0)/m²

are integers, and the actual local values satisfy

    C=q^(-B-u0)theta^c, D=q^(-u1)theta^(-2t),
    c=t²/a mod r², B=r²+r+12.

Indeed Pc=-A t²-r²*(N-AJ0²)/H. Integer divisibility is established
before reduction modulo r²; no inverse modulo ord(pi) is misused.
The quadratic c-2th+a h² is therefore a(h-t/a)² mod r². Its relevant
exponents c,t have not been acquired.

The attempted character implementation does not extract this relation.
Actual rough orders are coprime to k, so <theta>=<q>=<pi> locally.
The proposed quotient by <q> is trivial, and exponent residue mod r²
is not a character of the supplied group value. The constructible
rank-r² algebra B[T]/(T^(r²)-q) does not repair this: constant lifts
of C,D do not supply T^c,T^(-2t) with the unknown required carries.
The earlier Tate, cyclotomic and auxiliary-input DLP audits are credited.

For comparison, a complete bounded detector CAN be initialized:
T_c=Dq^u1=pi^(2mJ0)barpi^(-2m), g=pi^(-2m²). Compare T_c with g^t
for 1<=P'=J0+mt<=k³. At good P a hit forces
pi^[2m(P'-P)]=1; the exponent magnitude is below2k^4 and the local
order exceeds256k^4, hence P'=P. Saturated leaves therefore have the
explicit proper-factor consumer gcd(P',N). All starts are acquired.
But M<=m class intervals of length O(1+k³/m) give only the old
soft k^(3/2) uniform acquisition bound. No power saving in the actual
class count is proved, and the square relation has not reduced this cost.
On other orientation labels, accept only verified proper gcd factors
and otherwise return bounded failure.

Two primary endpoint-solver contracts were checked explicitly.
[Abramov's rational q-system solver](https://fpsac-archive.github.io/FPSAC99/ARTICLES/abramov.pdf)
assumes characteristic zero, a non-root-of-unity q, and a q-suitable
field supporting the search for powers at which a polynomial vanishes
(Introduction, printed pp2–4). It is not an endpoint oracle for our
finite algebra. Even bypassing that assumed search using the known
class product, the initialized equation

    A(X)Z(qX)=A(q^L X)Z(X), Z(0)=1

has product degree rL. Literal coefficient reconstruction costs
O(r²L) per class; dense product construction costs soft rL. Neither
gives the desired endpoint bound, and q denominators beyond16H need
actual additional classification rather than the short guard alone.
[Ardehali–Rosengren's 2026 gamma-product identity](https://arxiv.org/abs/2602.11329)
is analytic and infinite. Forming its finite quotient does not supply
an exact finite-ring circuit or a justified modular truncation.

Exact proofs, primary caches, independent reviews and the preservation
validator are in /tmp/semiprime-casoratian-endpoint-20261024/. The next
algorithmic target remains an acquired interior selector or a method
that actually uses bounded exponent lifts. Short perturbation vectors,
transfer matrices, germs and formal characters are not that acquisition.
No broad build, finite success campaign, commit or push was used.
All previous document prefixes, 270 frozen entries, HEAD and concurrent
RH work are preserved.
