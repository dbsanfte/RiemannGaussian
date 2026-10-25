# Teichmuller norm and two-geometric-progression acquisition attempt

22 October 2026. Read the frozen Fermat multiplier packet, the paid sparse dyadic norm constructor, and the current 208-entry preservation instructions. No repository edits, build, or coverage campaign. Coordinated the dyadic calculation with the sibling randomized_circuit_space investigation. The norm constructor is inherited. **No new soft-O(r) restriction-safe collision query is acquired here.** The exact changes of representation and the remaining constructive target are below.

## 1. Provenance correction: the coverage principle alone is elementary

For every unit P modulo r^2, the r points 0,P,...,(r−1)P on the circle Z/r^2Z have a circular gap at most r. Equality for every gap would make their set an additive coset of rZ/r^2Z. Since it contains0 and P, that would imply r divides P, impossible. Hence some circular gap is strictly between0 and r. Taking the corresponding difference of indices, with sign if necessary, gives

    1<=c<r,  cP = ±d mod r^2,  1<=d<r.

Thus the explicit catalog {±1,...,±(r−1)} already gives O(r) small-multiple coverage. An even simpler catalog is {1+rj:0<=j<r}: choose the existential multiplier c=P^(-1) mod r in [1,r). Neither construction selects the hidden multiplier algorithmically.

Consequently the Fermat packet's useful additional object is its *structured quotient-layer representation and its acquired labels*, rather than a new principle that O(r) small-multiple catalogs exist. This observation does not edit or invalidate the frozen construction and its soft-bit proof.

## 2. Exact Teichmuller norm embedding, including integer carry

Let H=r^2 and q=beta^H. For a catalog label (b,c), write

    bc=t+H*kappa,

with a fixed canonical residue t. The literal collision factor is exactly

    beta^(N+bc)−q^sigma
      =q^kappa [beta^(N+t)−q^(sigma−kappa)].

The scalar q is a unit, and the prefactor is harmless for local support. The shift of sigma is NOT harmless unless its permitted interval is transported with the same label. The selected (s,c) labels biject all units x=s/c modulo H; because b=−N/s, their residues t=bc=−N/x also biject all units modulo H. An unrestricted quotient-layer transform therefore does not leave a sparse set of t.

A correct universal algebra for the carry is

    K[X,X^(-1),Y,Y^(-1)]/(X^H−Y),  followed by X=beta,Y=q.

There X^(bc)=X^t Y^kappa. Exponent substitution X->X^a must also send Y->Y^a. Taking a modulo H while fixing Y is not an automorphism of this source algebra. For Teich representatives a_j,a_k, their product is a_(jk)+H*lambda, and the extra Y^lambda cannot be erased. Thus the desired finite Teich permutation is a semilinear operation with moving Y powers, rather than the scalar-ring Galois action required by an ordinary rank-(r−1) norm.

The familiar cyclotomic norm at Y=1 is a different specialization. In fact, for a primitive Hth root zeta and N a unit modulo H,

    product_(t unit mod H) (zeta^(N+t)−1)=0,

because t=−N is among those units. This zero is automatic and contains no factorization information. Restoring Y=q removes that automatic root and restores precisely the carry-dependent phases. This pinpoints the source error in a root-of-unity replacement; it does not rule out a new carry-aware norm algorithm.

Multiplicative Fourier transformation over the Teich index can be applied to any ONE supplied length-(r−1) list. But b->beta^b is an additive exponential with integer carries, not a multiplicative character of that index group. Taking its cth powers does not become multiplication by one scalar character. A proposed Fourier consumer must therefore pay the transformed c-dependent data or give a new shared contraction; changing basis alone has not supplied it.

## 3. Dyadic alternative: explicit arithmetic layers and two quotient cosets

Here is a completely constructive dyadic replacement that exposes simpler rows. Let m=2^k, k>=2, H=m^2, and, for odd x, define

    ell(x)=((x^(m/2)−1)/(2m)) mod m.

It can be computed using a power modulo2m^2. It is well-defined on units modulo H and is a homomorphism to Z/mZ: the product correction is divisible by m. LTE at5 gives ell(5) odd, so it is surjective. Its kernel is exactly x=±1 mod4m, with size m/2. Therefore a layer is two arithmetic progressions of length m/4.

The odd multipliers 1<=c<m have distinct ell(c), so their image Q_C has size m/2. Moreover Q_C and Q_C+m/2 are disjoint. Indeed ell(c/d)=m/2 implies c/d=±(1+2m) mod4m, hence c=d+2m or c=2m−d mod4m; neither is possible for positive odd c,d<m. Thus

    A={0,m/2},  A−Q_C=Z/mZ.

The combined two-layer catalog is simply x=±1 mod2m, of size m. This also has a direct elementary proof: the inverse of odd P modulo2m is odd; choose it or its negative so that its representative c is odd and <m. Then cP=±1 mod2m.

This replaces analytic quotient-image estimates by a finite identity and supplies an additive-progression catalog. It is not a new factoring exponent. With b=center(−N/s modH), its b values lie in two progressions b=b0+L*j, where L=2m, M=m/2, H=L*M and j runs through M consecutive integers. All rows and endpoints are acquired in soft O(m).

## 4. Exact fixed-GP consumer reduction and the Euclidean test

For one such progression, c is odd and hence permutes residues modulo M. Write

    c*j=M*u_c(v)+v, 0<=v<M.

Then

    beta^(N+(b0+L*j)c)−q^sigma
      =q^u_c(v) [beta^(N+b0*c+L*v)−q^(sigma−u_c(v))].

Enlarging the sigma interval by the public O(m) carry bound gives a sufficient fixed-GP query

    beta^(N+b0*c) = (beta^L)^z,

with O(m) supplied c indices and a common z interval of O(m^2) integers. A hit still has a valid original linear exponent N+b*c−H*sigma after retaining the corresponding labels; alternatively the enlarged query needs its own bounded factor-sum recovery bound with the enlarged constants. No equality is inferred after discarding a carry.

For the public b0=−N modL, write N+b0=L*kappa, and c=2d+1. The equality is equivalent, since the prepared beta has odd local orders, to

    beta^(b0*d) = beta^(m*(z−kappa)).

The exponent kappa can be very large (order m^5); it is a known center and cannot be silently replaced by a short interval centered at0. Reorigining z transports that center exactly.

I tested an integer Euclidean reparameterization of the two short coefficients b0 and m. Reduce b0 modulo m and update the second index by the exact corresponding multiple of d. A subsequent Euclidean division m=q*a+r replaces

    a*d−m*t  by  a*(d−q*t)−r*t.

This is an exact unimodular transformation. However the new d coordinate has width about q*m^2, rather than O(m), unless its parallelogram boundary is retained. Continuing with that boundary gives a periodic residue mask on an ordinary interval of length O(m^3); it has not produced a shorter geometric factorial. For consecutive d<m, coprimality of a,m makes the exponent projection injective, so the exact mask is determined by e modm belonging to a times the original short d interval. This is a precise intermediate representation for further work, not an operation lower bound.

In particular a compressed Euclidean word describing that mask would not by itself give a cheap product evaluator: the all-one word already describes an ordinary long q-factorial, whose standard block evaluation costs the square root of its length. I obtained no Euclidean recurrence whose *arithmetic evaluations*, including shifted arguments, sum to soft O(m). The actual generic monic-product consumer remains soft O(m+sqrt(m*m^2))=soft O(m^(3/2)).

## 5. Curvature-preserving next target in the original source

The linear cover's bijection restores all candidate cofactor residues. The original quadratic rows retain a weighted term a_j P+Q and can avoid this particular linear relabeling loss. A concrete next acquisition target should preserve their canonical small coefficient a_j<m.

For an original unit tag j modulo dyadic m, let

    a_j=N*j^(-2) modm in [0,m),
    D_j=(N−a_j*j^2)/m,
    b_j=center(−j^(-1)*D_j modm),
    delta_j=a_j+m*b_j−2*a_j*j,
    E_j=N+delta_j.

Take u_j=j^(-1) modulo m^2 and define the acquired lift defect

    h_j=(a_j−N*u_j^2)/m modm.

A direct cleared calculation gives

    E_j = N*(1−u_j)^2 + m*(1−j)*h_j modm^2.

Indeed m*b_j=−(N−a_j*j^2)*u_j modulo m^2, so E_j=N+a_j−a_j*j−N*u_j modulo m^2. Substituting a_j=N*u_j^2+m*h_j gives the displayed identity. This is a potentially useful curvature presentation: a quadratic square phase plus one explicit coefficient-lift defect. Its defect must remain coupled to the native row and the original seed interval. Replacing a_j by its full m^2 lift removes that defect from the displayed congruence but can make a_j P/m^2 as large as O(m^3), instead of the original O(m^2) index. Thus that simplification spends the rate.

The concrete sufficient algorithm target is now: apply the paid sparse dyadic norm/tangent machinery to the quadratic phase AND its actual acquired h_j mask, with a shared carry transport preserving a_j<m and the original O(m^2) seed interval. It must acquire the restriction-safe product of original differences, rather than only a trace of the phase. The first norm fold and ordinary fixed-direction propagation are inherited and do not instantiate this joint input contract. I did not derive a bounded-total-support recurrence for the lift-defect masks; their existence as O(m) scalar input data alone is insufficient.

## Outcome

This pass supplies exact source-preserving Teich carry algebra, an elementary provenance comparison, an explicit two-coset dyadic alternative, and a fully specified Euclidean/mask intermediate. None acquires the desired product in soft O(r). The next active target is the original curvature plus its canonical lift defect, rather than another unqualified cyclotomic norm or a linear cover that merely relabels the whole cofactor interval. All 208 frozen entries remain untouched.
