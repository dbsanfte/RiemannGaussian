# A paid packed Gauss-power quotient over an unfactored modulus

22 October 2026. Constructive primitive, not a factor-residue extractor. For a public auxiliary prime m, any k|m-1, and unfactored odd semiprime N=P Q with gcd(N,mk)=1, this computes ONE degree-<k polynomial encoding the Gauss-power quotient for EVERY character of order dividing k. It costs soft O(m+k) in the native polynomial-size bit regime. It never constructs the degree ~(m-1)k joint Gauss carrier. The remaining native Frobenius/tag issue is retained explicitly below.

## Public algebra and exact input

Let R=Z/N and A=R[X]/(X^k-1). Fix a public primitive root g modulo m, and let ell(t) be its discrete-log TABLE for t in F_m*. This is acquired by walking g's powers, not a hidden-prime discrete logarithm. Put ell(-1)=(m-1)/2. Conceptually adjoin a primitive m-th root Z only for the proof, and write

    G_a(X,Z)=sum_(t in F_m*) X^(a ell(t)) Z^t,
    J_ab(X)=sum_(t≠0,1) X^(a ell(t)+b ell(1-t)),

with exponents of X reduced modulo k. Evaluating X at a k-th root xi gives the usual Gauss/Jacobi sums for the character t→xi^ell(t). No prime divisor of N, finite field of hidden characteristic, root of unity modulo N, or factor-indexed table is an input. The auxiliary field F_m and its complete enumeration ARE public and paid.

One J_ab is a histogram of m-2 public terms in k bins, acquired in O(m) small-integer operations and O(k) coefficient storage. The joint Z-algebra is never represented by the production algorithm.

## Exceptional characters: explicit projectors make ALL characters packable

For a modulo k let h_a=k/gcd(a,k), with h_0=1, and form

    E_a(X)=h_a^(-1) sum_(t=0)^(h_a-1) X^(a t) in A.

All inverses exist because h_a|k and gcd(k,N)=1. E_a is an idempotent. At every character specialization xi it equals one precisely when xi^a=1, and zero otherwise. This follows either from the finite geometric sum or group averaging. To justify simultaneous specialization over the composite ring, base change separately to algebraic closures of F_P and F_Q: X^k-1 has distinct roots since neither characteristic divides k. Equalities at all these roots imply equality in A by reducedness/CRT; the production algorithm does not use this decomposition.

Set

    P_00=E_a E_b,
    P_cancel=E_(a+b)-P_00.

These project respectively onto both characters trivial, and both nontrivial with their product trivial. Define the following fully acquired polynomial:

    c_ab = J_ab + (m-1) P_cancel J_ab - (m-1) P_00.        (A)

Then in the conceptual joint Gauss algebra,

    G_a G_b = c_ab G_(a+b).                              (B)

Here all a,b subscripts are modulo k. Verification at each xi has four exhaustive cases:

* Neither character nor its product is trivial: the ordinary double-sum change of variables gives G_a G_b=J_ab G_(a+b), so c_ab=J_ab.
* Exactly one character is trivial: its Gauss sum is G_0=-1, J_ab=-1, hence c_ab=-1.
* Both are trivial: G_0²=1=(-1)G_0 and J_00=m-2; (A) changes m-2 to -1.
* Both are nontrivial and cancel: G_a G_(-a)=X^(a ell(-1))m and J_a,-a=-X^(a ell(-1)); (A) multiplies this J by m, so c_ab=-X^(a ell(-1))m as required because G_(a+b)=G_0=-1.

All factors are units. G_0=-1 is a unit; a nontrivial Gauss sum is a unit because its product with the inverse-character Gauss sum is the unit m times a root of unity. Consequently c_ab is a unit in the joint algebra and in A. More directly, in nontrivial/noncanceling components J_ab J_-a,-b=m, while the exceptional displayed values are units. These facts prove unit safety, but the algorithm does NOT invert a Gauss sum or a Jacobi sum.

## Binary algorithm and its exact output

For any supplied E≥0, compute C_E in A with

    G_1^E = C_E G_(E mod k).                             (C)

C_0=-1 and C_1=1. Starting from the leading binary one of E>0, retain e modulo k and C_e. A doubling step is

    C_(2e)=C_e² c_(e,e).

If the next binary bit is one, follow with

    C_(2e+1)=C_(2e) c_(2e,1).

Thus at most 2 floor(log_2 E) acquired J histograms and O(log E) cyclic polynomial multiplications are needed. Formula (C) proves correctness by induction. All arithmetic occurs in A; coefficient reduction is cyclic, so no cyclotomic polynomial construction or field inversion is needed.

For a primitive k-th root zeta_k, the SINGLE output C_E(X) encodes

    C_E(zeta_k^r)=G(chi^r)^E/G(chi^(rE)), 0≤r<k,

including nonprimitive and trivial characters. The slash describes the already proved identity between units, not a production division. The trivial component is C_E(1)=(-1)^(E+1), hence one for odd E. For E=k this also acquires G(chi)^k=-C_k(zeta_k), an exact base-cyclotomic unit useful for homogeneous-line arithmetic.

Packing is literal and limited: the output has k coefficients, not k². Applying a supplied rho_s (X→X^s, gcd(s,k)=1) costs O(k) by permuting cyclic coefficients. All rho_s-conjugates are represented by this polynomial and their index tags, but MATERIALIZING k full conjugate vectors still has k² output size. No free arbitrary downstream all-pairs computation is inferred.

## Full construction and bit cost

Check gcd(N,mk). A proper gcd already factors; the stated primitive proceeds on the coprime branch. A public m can be certified by trial division through sqrt m within soft O(m). Factor m-1 by trial division in soft O(sqrt m) small-integer operations. Testing candidates for a primitive root using these known prime divisors and modular powering uses at most m candidates and soft O(m) work. Construct the complete ell table in O(m) modular multiplications modulo m. No logarithm oracle is used.

Each J histogram costs soft O(m log m) bits. Constructing E_a or E_b costs O(k) coefficient/index operations; one inverse of k modulo N suffices for every h_a inverse, since h_a^(-1)=gcd(a,k)/k. Multiplication in A uses cyclic convolution and integer packing, costing soft O(k(B+log k)) bits, B=ceil(log_2 N). O(log E) such operations give the conservative bound

    soft O(m log m + log(E+1)*(m log m+k(B+log k))).

Storage is soft O(m log m+kB) bits, plus O(log E) descriptor bits. Under m,k,E≤N^O(1), k≤m-1, this is soft O(m) when logarithms in N are suppressed, including the full packed output and every histogram. No construction cost is hidden in a supplied complete Jacobi sum. This is a deterministic N-only modular primitive with public m,k.

## What Frobenius information it actually gives

For a hidden prime P not dividing mk, TRUE Frobenius acts on BOTH root systems. If sigma_j sends Z→Z^j and rho_r sends X→X^r, then

    Frob_P = sigma_(P mod m) rho_(P mod k).

For one primitive character, direct substitution gives

    G(chi)^P = chi(P)^(-P) G(chi^P) modulo P,
    C_P(chi)=chi(P)^(-P) modulo P.                        (D)

The algorithm computes C_N, not the unknown-index C_P. For N=P Q, its actual reduction is

    C_N(chi) = chi(P)^(-N) C_Q(chi^P) modulo P.           (E)

The remaining C_Q term is not supplied and cannot be discarded. A prime-test congruence C_N=chi(N)^(-N) proves a property if it holds; its failure is not automatically a proper gcd or a recovered hidden character value. Primality certification and factor extraction remain different tasks.

For native row cancellation, replacing Frobenius by sigma_(P mod m) alone is invalid unless rho_(P mod k) fixes the starting element. Corrected candidate automorphisms sigma_j rho_r restore the Frobenius identity at j=P mod m,r=P mod k, but a paid coverage/routing theorem must retain that second tag. The packed C_N contains all character conjugates compactly; it does not yet prove that an m-by-k candidate family can be searched or aggregated in soft O(m). Thus the primitive is genuinely acquired, whereas the proposed seed-index residue extraction remains open.

## Literature and prior-audit boundary

The Gauss/Jacobi product identities and their use to replace the large joint cyclotomic carrier by a smaller character carrier are classical APR/CL ingredients. No first-discovery claim is made. The explicit all-character projector implementation and its native soft bit ledger above are supplied here to make the affordable interface precise.

* Schoof, *Four primality testing algorithms*, MSRI Publications 44 (2008), section 4: https://www.mat.uniroma2.it/~schoof/05rene.pdf . The cyclotomic algorithm certifies primality/compositeness through public auxiliary sums and residue constraints; it is not an all-input factor-residue acquisition theorem.
* FLINT's own APRCL source, `src/aprcl/unity_zp_jacobi_sum.c`, lines 14–47, explicitly constructs auxiliary-prime Jacobi sums from a public table: https://raw.githubusercontent.com/flintlib/flint/main/src/aprcl/unity_zp_jacobi_sum.c . Its implementation is prime-power-order specialized; formula (A) above is proved separately and does not rely on a library black box. The URL is a moving branch; title/path and check date 22 October 2026 identify the inspected source, without pretending it is an immutable commit pin.
* Berghoff, *Efficient computation of universal elliptic Gauss sums*, arXiv:1707.08610v1: https://arxiv.org/pdf/1707.08610 . Its application starts with an elliptic curve over a known F_p, an Elkies prime and Frobenius eigenvalue problem. It provides no theorem recovering a hidden semiprime component's Frobenius from N alone at the requested budget.
* Couveignes–Lercier, *Elliptic periods for finite fields*, arXiv:0802.0165v2: https://arxiv.org/pdf/0802.0165 . Its quasi-linear arithmetic is in constructed finite-field extension models; a fast supplied Frobenius action does not identify the two unknown local Frobenius actions over Z/N.

The repository's `semiprime-cyclotomic-row-cancellation-20261016` packet used u=1+zeta and an anti-invariant selector, which vanishes for every native tag. It does not already prove or disprove this Gauss-eigenline primitive. The `semiprime-twist-character-20261022` fast-Jacobi audit correctly charges the hidden field for van Wamelen's algorithm; the present sums are instead complete sums over the PUBLIC auxiliary F_m, enumerated and paid explicitly. These input contracts must not be conflated.
