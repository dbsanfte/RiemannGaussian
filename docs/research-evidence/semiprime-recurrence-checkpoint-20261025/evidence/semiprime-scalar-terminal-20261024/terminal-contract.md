# A known zero endpoint and the actual localization contract

24 October 2026. The complete scalar aggregate is provably zero modulo N before evaluation. Its scalar evaluation is therefore vacuous; the nontrivial algorithmic task is to acquire a factor or a labelled collision. The short interfaces below are sufficient and mutually convertible up to soft k work. Neither an acquired kernel nor a faster localization algorithm is inferred from singularity.

Use /tmp/semiprime-paired-weighted-query-20261024/scalar-catalogue.md SHA256 `9ded79850c2f200069a7da67502d0de579d1df0457cb06c865fb3d39c9654058`, independent review `ce4d15b225d546c8008efaf5e6bdb2d2c0923b2b99d8603d3e1e24273efc6c27`. All its actual setup, catalogue, public zero-row deletion and finite fallback are retained. In particular N=PQ is squarefree, H=k², q=beta^H, both beta orders are odd and>16H, both q orders>16H, and P,Q>16H+1. The retained J=soft k rows have E_j=a_j+b_j N+lambda_j, with (a_j,b_j)!=(0,0), |a_j|,|b_j|<=k. Let

    M=ceil(4ceil(sqrt(kN))/H)+2, h=2M+1<16H,
    T_j=q^M beta^(E_j),
    F(X)=prod_(j<J)(X-T_j), f_s=F(q^s),0<=s<h.

The monic F and all roots/labels are actually acquired in soft k; no f_s values are assumed supplied.

## 1. Both-prime theorem: the complete endpoint is zero

For EACH R in{P,Q}, put S=N/R and choose its own virtual Gauss bin and tag j=R modk as in the scalar source. The complete bounded catalogue contains that Gauss row. Its uncentered phase has an integer I in[-M,M] with

    E_j-HI=(R-1)(b_j S-a_j).

The right side is nonzero: if b_j=0 then a_j!=0; otherwise |b_j S|>=S>16H>k>=|a_j|. Thus the witness survives the PUBLIC deletion of an entire row whose integer E_j/H lies in[-M,M]. Indeed deletion would give a second local q index in the same length-h interval, forcing equality of indices because ord_R(q)>h, and hence a zero right side, contradiction.

Consequently, for each R some retained row has T_j=q^s modR for an s in[0,h). Therefore

    C=prod_(0<=s<h)F(q^s)=0 modP and modQ,
    C=0 modN.                                   (1)

The witnesses need not share a row or index. In particular (1) does NOT promise an index s for which f_s=0 globally; it only promises a nonunit f_s somewhere at each prime. A proper gcd at any such index already factors. Many hits are allowed; localization also handles an active subinterval whose every value is zero.

## 2. Sufficient output: one index, or one kernel coordinate

An adequate algorithmic interface on these actual inputs is:

    return a verified proper factor of N; OR
    return0<=s<h with gcd(F(q^s),N)>1.            (2)

One returned s costs only soft k to complete recovery. Acquire all J original scalar leaves beta^(E_j)-q^(s-M) at that ONE index and scan their gcds. A proper gcd factors. If gcd(F(q^s),N)=N, either some leaf has a proper gcd or at least one leaf is saturated. For a saturated leaf the actual nonzero integer K=E_j-H(s-M) has O(logN) bits by the catalogue bounds and deletion. Then beta^K=1 GLOBALLY and the pinned short-annihilator extractor factors within soft k. A cross-leaf product zero is never itself passed to that extractor.

Define an h-dimensional cyclic weighted shift by

    T e_s=f_s e_((s+1) modh).

A second sufficient interface is to return a verified proper factor OR a labelled nonzero coordinate w_s of an ACTUAL vector w in ker(T). Since f_s*w_s=0, a proper gcd(w_s,N) factors; if w_s is a unit then f_s=0 globally and(2) applies. A nonzero canonical coordinate cannot have gcdN. Conversely a supplied index from(2) either factors immediately or has f_s=0 globally, in which case e_s is an actual nonzero kernel vector. Thus these output interfaces are equivalent up to soft k work, allowing the direct-factor branch. No full length-h output is required; a labelled nonzero annihilating coordinate suffices. Merely asserting that a kernel exists or returning the zero vector does not satisfy this contract.

## 3. Exact unit regularization, with its remaining acquisition

Equation(1) gives the actual identities over Z/N:

    T^h=C*I=0,
    det(I-T)=1-C=1,
    (I-T)^-1=I+T+...+T^(h-1).                   (3)

Thus there is a collision-safe unit system with a trivial inverse denominator. These facts do not supply its coefficients or a nonzero kernel coordinate. Powers T^r have cyclic-shifted interval products of the f_s as weights; the inverse in(3) contains the same interval products. An explicit scalar graph has Theta(h) coefficients f_s, not soft k supplied coefficients. A fast representation of F is not by itself those evaluated weights.

There is an initialized localization using the known endpoint without evaluating C. Maintain an interval whose product of f_s is0 moduloN, initially[0,h) by(1). Evaluate only its first half using the old zero-safe restricted q-product routine. A proper gcd factors. A saturated half retains that half; a unit half forces the OTHER half's product to be0 moduloN. Repeat until a single index. This is correct even with hits at different primes or all values zero. Its largest acquired interval is still of length about h/2; the old cost is soft(J+sqrt(Jh)), with no exponent saving. Removing the full initial aggregate call saves a constant, not its localization scale.

In fact the COMPLETE signed catalogue guarantees at least TWO distinct hit indices at EACH prime. For a witness(a,b,lambda,I), its stored opposite(-a,-b,lambda') with lambda'=(-lambda modH) has I'=kappa-I, where kappa=(lambda+lambda')/H is0 or1. The slack M>=4sqrt(kN)/H+2 puts I' in the same window. Its Fermat integer is the negative of the original nonzero one, so public deletion cannot remove it. If kappa=1 the integer indices cannot coincide. If kappa=0, coincidence would give I=0 and aR+bS=0; coprimality of R,S and |a|,|b|<=k<R,S would force a=b=0, impossible. Distinct indices remain distinct clock points since ord_R(q)>h.

Every length-(h-1) cyclic weight product therefore contains a zero at P and a zero at Q. Consequently T^(h-1)=0 GLOBALLY in this actual family. In particular the highest-power or adjugate shortcut does not produce a nonzero kernel coordinate. The determinant inverse, spectral singularity promise and zero endpoint alone still do not supply the required labelled NONZERO output.

The precise remaining operation is faster acquisition of a labelled nonunit f_s, or a labelled nonzero coordinate killed by this implicitly specified weighted shift. A structure-aware singular-coordinate algorithm could solve the remaining task; none is supplied by(3) or by the tested interval procedure. The original complete soft k^(5/4) bound and known global fifth-rate comparison are unchanged; the soft k factoring/Lean goal is not complete. No shared/frozen source or numerical campaign was used.
