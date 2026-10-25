# Paid weighted rational power traces in the cyclic algebra

**Verified positive primitive.** For fixed arbitrary explicit B in A=(Z/NZ)[X]/(X^m−1), all m values Tr_A(B R^a), 0<=a<m, can be acquired in soft O(m) bit work (O(log N) arithmetic factors suppressed), where

 W=t(1+gamma X)/(X+gamma),   R=W/X.

This does not acquire the full native collision query: its weight varies with a through an automorphism, rather than being one fixed B.

## Hypotheses and exact output

N is odd, m is odd, gcd(m,N)=1, gamma,t are public scalar units, t²=gamma, and 1+gamma^m is a scalar unit. These hold on the retained prepared input: gamma has odd local orders, hence gamma^m cannot equal −1 in either hidden field. B has its canonical degree <m representative. Tr_A denotes the regular algebra trace, equal to m times the constant coefficient in A; it is also the sum over the m roots after an etale splitting extension. No such extension is computed.

The coefficient of z^a in

 F(z)=Tr_A(B/(1−zR))

is exactly Tr_A(BR^a). It suffices to compute F modulo z^m.

## Formula reducing the problem to a quadratic algebra

Put

 g=X(X+gamma),
 h=g−zt(1+gamma X)=X²+cX+d,
 c=gamma(1−zt),  d=−zt.

Let U=U0+U1 X be the remainder of Bg on division by the MONIC polynomial h. Write Bg=hV+U only for the proof; the algorithm never constructs V. Since deg(Bg)<=m+1, deg_X V<=m−1, and summing V on the m cyclic roots gives m V(0). The constant coefficients of Bg and h are 0 and −zt, so

 U0=zt V(0),

in the exact polynomial ring. In particular U0 is divisible by z, and V(0)=t^(-1)(U0/z). This is an exact shift of a polynomial/series, not inversion of z.

In the quadratic algebra C=(Z/NZ)[[z]][X]/(h), put

 l=1−X^m,   H=X^(m−1).

Then the complete generating function is

 F(z)=m t^(-1)(U0/z) + m [X](U H l^(-1) mod h).                 (1)

Here [X] means the coefficient of X in the degree-one representative. All powers and products in the second term take place in C, not in the original m-dimensional algebra.

## Proof of the quadratic residue identity and its sign

Let f=X^m−1. Initially over a splitting field with simple roots and nonvanishing denominators, consider U f'/(h f). Its residue at a root omega of f is U(omega)/h(omega). Its residue at a root beta of h is U(beta) f'(beta)/(h'(beta) f(beta)). The rational function has zero residue at infinity because deg U<2. Since f(beta)=−l(beta), summing residues gives

 sum_(omega^m=1) U(omega)/h(omega)
 =sum_(h(beta)=0) U(beta) m beta^(m−1)/(h'(beta) l(beta)).

For any monic quadratic h and degree-one remainder K, sum_(h(beta)=0) K(beta)/h'(beta)=[X]K. This proves the POSITIVE sign in (1). One may clear the resultant denominator to obtain a universal polynomial identity over the integer coefficient ring, then specialize to Z/NZ. Thus the argument does not require numerical roots, a hidden factor, or division by a discriminant in the algorithm. Equivalently, this is a universal algebraic residue identity in monic quotient algebras.

At z=0, h=X(X+gamma). The norm of l in C is its value at 0 times its value at −gamma, namely

 Norm_C(l)|_(z=0)=1+gamma^m.

This is a unit, so l is invertible as a formal series. Explicitly, for l=l0+l1X,

 l_conj=(l0−c l1)−l1X,
 Norm_C(l)=l0²−c l0l1+d l1²,
 l^(-1)=l_conj/Norm_C(l).

Only the inverse of a scalar series with checked unit constant coefficient is required. No field polynomial gcd or unguarded coefficient division occurs.

## Algorithm and full degree/bit charge

1. Check gcd(m,N), gcd(t,N), gcd(gamma,N), and gcd(1+gamma^m,N) as applicable to the supplied contract. A proper gcd is already a factor; the present theorem assumes the unit branch. Compute Bg, a scalar-coefficient polynomial of degree <=m+1, in linear work.
2. Compute U=Bg mod h using a balanced evaluation tree in the quadratic algebra, with scalar coefficient blocks. Precompute X^(2^r) mod h by squaring. Evaluate a block P_low+X^k P_high by combining its two remainders with the shared remainder of X^k. At a node of length s, every z-degree is O(s), because the quadratic companion matrix has entries of z-degree <=1. A level has O(m/s) such nodes, hence O(m) total polynomial degree. With fast polynomial multiplication, all levels together cost soft O(m). This is not m evaluations of length-m objects.
3. Retain precision z^(m+1) in step 2, so that the EXACT z-divisibility of U0 gives V(0) modulo z^m after shifting. Dividing by z without this extra coefficient would lose the highest requested moment. Alternatively the complete U has only O(m) scalar coefficients and can be retained exactly.
4. Compute X^m and X^(m−1) modulo h by binary powering to precision z^m. The number of algebra operations is O(log m), each polynomial product has length O(m), so this costs soft O(m). Form l and its conjugate/norm. Invert the scalar norm series modulo z^m by Newton iteration using only the unit constant inverse. Compute the second term of (1) modulo z^m.
5. Add the shifted quotient term and output its m coefficients.

A multiplication in the quadratic algebra uses a constant number of scalar polynomial multiplications, plus reduction using c,d of degree one. The evaluation tree has total O(m) coefficient data per level; retaining all levels uses soft O(m) space, or O(m) active data with recursive release. Input and output have O(m log N) bits. All arithmetic is modulo N, so coefficient bit sizes never grow with the symbolic degree. Monic division, series inversion with a unit constant, scalar gcd/exponentiation, and soft-linear polynomial multiplication over Z/NZ suffice. Neither m² coefficient output nor an implicit full quotient V is charged as free.

This proof uses generic fast polynomial arithmetic, not a claim that a Python schoolbook implementation has the same bound. It gives an implementation-ready algorithm without invoking hidden-field routines.

## Exact native limitation

Taking B=W^N is paid in soft O(m), since binary exponentiation uses O(log N) cyclic-algebra operations. Therefore all fixed-weight traces Tr(W^N R^a), a<m, are genuinely paid. A fixed constant number of other weights is also allowed.

However, after applying the native rho_(j²) substitution to a coefficient extraction and using a_j=N j^(-2) mod m, the weight becomes rho_(a_j/N)(B), not B. In addition the actual corrected row retains its own W_j^ell factor. Formula (1) cannot silently absorb either dependence. Applying the theorem separately to m different weights would cost soft O(m²). The theorem is a new paid mixed POWER piece with arbitrary fixed packed weight, not coverage or completion of the native long query.
