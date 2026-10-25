# Quadratic period PRODUCT: paid rank-two and rank-three native row acquisition

2026-10-24. Scratch only; no repository edits, examples, backend expansion or query-rate claim. This proves and initializes the proposed quadratic-period PRODUCT. It acquires its nontrivial rank-two component, all native rank-two rows, and the full rank-three relative-norm rows in soft m. It does not acquire the long collision query or inherit a translated-base order/recovery theorem.

The root proposal was explicitly unreviewed input. The older cyclotomic-row-cancellation README was read; SHA256 992e31ea5ece408e448dba91771a1616228b4629668552960c15311c9aafad6e. Native row/own-index coverage is inherited from uniform-setup-and-query-interface.md, SHA256 4c4efaba5c3a09dd4ca1a87801e44212d5fcd2570ff26ec5f193f71589ec0d46. Character sums, period products and Newton identities are standard; no absolute novelty is claimed.

## 1. Correct ambient ring and universal Gauss identity

Let m be an odd prime, h=(m-1)/2, chi the quadratic character on F_m (chi(0)=0), and D=chi(-1)m. For the universal proof use

    S=Z[1/(2*m*h!)],
    C_S=S[Z]/Phi_m(Z),
    B_S=S[tau]/(tau^2-D).

Write zeta for Z in C_S and G=sum_(r=1)^(m-1) chi(r) zeta^r. In THIS cyclotomic quotient, sum_(r=1)^(m-1)zeta^r=-1. Define bar G by zeta->zeta^-1. Then bar G=chi(-1)G and

    G bar G = sum_(t!=0) chi(t) sum_(y!=0) zeta^((t-1)y)
            = (m-1)-sum_(t!=0,1)chi(t) = m.

The inner sum is m-1 at t=1 and -1 otherwise. The last equality uses sum chi=0. Therefore G^2=D, with the correct signed discriminant. Also sigma_j(G)=chi(j)G by permuting nonzero residues. These are integer polynomial identities in the cyclotomic quotient, not deductions in an unknown field.

Consequently tau->G defines B_S->C_S. The map remains INJECTIVE after ANY base change where 2 is a unit. Indeed, if A+B G=0, its degree-<m coefficient vector is (A,B chi(1),...,B chi(m-1)). Vanishing modulo monic Phi_m means this vector is constant. Since chi takes both signs, A=B and A=-B, so A=B=0. This proof works over rings with zero divisors and needs no splitting field or numerical square root of D.

The QR-invariant subalgebra of C_S is exactly this rank-two image. One proof uses representatives of degree <m: two representatives differ by a scalar multiple of Phi_m. Under sigma_q for q quadratic, the coefficient at exponent zero of their difference is zero; hence an invariant class has a representative whose nonzero coefficients are constant separately on QR and NR. Their two period sums satisfy eta_++eta_-=-1 and eta_+-eta_-=G, so 2 invertible gives the claimed span. The period product's coefficients belong to that span simply because QR permutes its factors.

IMPORTANT: in the FULL cyclic algebra S[Z]/(Z^m-1), G_full^2=D e1, not D*1. Here e0=(1/m)sum_(r=0)^(m-1)Z^r and e1=1-e0. The full QR-invariant algebra has rank THREE (orbits {0},QR,NR). Rank two is the nontrivial cyclotomic component only. Section 5 constructs the full rank-three object explicitly.

## 2. Power sums initialize the entire degree-h product

In C_S set

    C(T)=product_(r in QR)(1+T zeta^r),  degree h.

For 1<=k<=h, k is nonzero modulo m, and its power sum is

    p_k=sum_(r in QR)zeta^(kr)=(-1+chi(k)G)/2.

Hence in B_S[[T]], with tau mapping to G,

    log C(T) = sum_(k=1)^h (-1)^(k-1) p_k T^k/k  mod T^(h+1).

This formula uniquely determines C modulo T^(h+1) because its constant term is 1 and all 1,...,h are units. Since C has degree exactly h, computing this prefix acquires ALL its coefficients, not a tail-discarded approximation evaluated at a unit argument. That degree bound is what makes this operation unlike the failed formal prefixes of the long q-sum.

Now specialize the universal coefficient identities to R=Z/N, where the prepared primes satisfy P,Q>16m^2. All denominators in S map to certified units: 2,m,1,...,h are strictly below P,Q and nonzero. No hidden characteristic, field embedding, or quotient-algebra pivot is supplied.

The actual algorithm is:

1. Enumerate the nonzero squares modulo the PUBLIC prime m to acquire all chi(k) in O(m) small-integer work. Obtain chi(-1) from (-1)^h and define the explicit rank-two arithmetic tau^2=D.
2. Acquire 2^-1 and the inverses of 1,...,h in R (individually or by a batch unit inversion). Build the h logarithm coefficients (-1)^(k-1)(-1+chi(k)tau)/(2k).
3. Apply ordinary fast truncated power-series exponential through degree h. Its Newton inversion steps start from constant coefficient 1, and integration divides only by integers <=h. Rank-two multiplication uses a constant number of R operations. The total cost is soft m residue operations, including all coefficients and character metadata.
4. If C(T)=sum_(k=0)^h c_k T^k, acquire

       U(beta)=sum_(k=0)^h c_k beta^(h-k).

   A Horner evaluation or acquired scalar powers costs O(m). This avoids needing beta^-1, though beta is a certified unit anyway. The result maps EXACTLY to product_QR(beta+zeta^r) in C_R by the universal identity.

All acquired elements have O(log N)-bit residue coordinates. Intermediate polynomial lengths are O(m), not m^2. At no point are h degree-m cyclic factors multiplied explicitly or their m^2 coefficients acquired.

## 3. Unit and norm certificate

Conjugation on B sends tau->-tau and swaps QR/NR. Therefore, writing U=A+B tau,

    U bar U=A^2-D B^2
           =product_(r=1)^(m-1)(beta+zeta^r)
           =(beta^m+1)/(beta+1).

This is a universal polynomial identity: the apparent quotient is the exact polynomial (beta^m+1)/(beta+1) of degree m-1 for odd m. Algorithmically beta+1 and beta^m+1 are certified units because beta and beta^m have odd local order and cannot be -1. Compute their scalar inverses and the norm n_U by binary powering/scalar arithmetic. This is polylogarithmic work.

Thus U^-1=bar U*n_U^-1 is explicitly acquired with constant rank-two work, not by factoring B or inverting an unknown norm. This remains valid whether the local rank-two algebra splits or is a field. Norm computation/inversion is a lawful scalar operation; no claim about the order of U follows from it.

## 4. ALL rank-two native rows and own-tag coverage

Define sigma_j on B by tau->chi(j)tau. Its inverse is the same involution because chi(j^-1)=chi(j). Acquire once

    f=U^N, q_B=U^(m^2), U^-1.

Binary powering in rank two costs polylogarithmic residue work per supplied exponent. For each of the O(m) acquired native rows form

    T_j=U^ell_j (sigma_j U)^a_j sigma_(j^-1)(f).

This costs soft m TOTAL: constant-many rank-two signed powers per row, exponent bit length O(log N), plus O(m) character/row metadata. Equivalently T_j=U^ell_j(sigma_j U)^(N+a_j). No full degree-m row is an input or output. Explicit output is two R coordinates per row.

At either hidden prime p not dividing m, Frobenius acts on the universal Gauss image as

    G^p=sum_r chi(r) zeta^(pr)=chi(p)G.

The coefficients chi(r) are fixed in characteristic p. By the universally injective B_Fp->C_Fp map, Frobenius in B_Fp is exactly sigma_p, even when the rank-two algebra splits. In particular U^p=sigma_p(U). This is a direct proof; no unknown-prime algorithm or quadratic-reciprocity oracle is used.

At the ORIGINAL own label j=P modulo m and k=j^-1,

    sigma_j(U)=U^P,
    sigma_k(U^N)=(sigma_k U)^(PQ)=U^Q modulo P,

because (sigma_k U)^P=sigma_(Pk)U=U. Therefore

    T_j=U^(ell_j+a_j P+Q)=q_B^I modulo P,
    I=(a_j P+Q+ell_j)/m^2,  0<=I<2m^2+2.

The integer identity and interval are exactly the original native own-index theorem; the period product preserves that coverage. This is a local rank-two algebra equality, not a global equality modulo N. No lower bound or separation certificate for ord(q_B), no paid interval-membership query, and no saturated-leaf decoder for U are inferred. The original beta and metadata must remain available for any separately proved recovery bridge.

## 5. Full cyclic rank-three relative norm, also acquired soft m

Since m is a unit in R, the full cyclic algebra A_R splits as R times C_R by augmentation and the cyclotomic quotient. Let G_full=sum_(r!=0)chi(r)zeta^r in A_R. The rank-three invariant algebra consists of

    s e0+A e1+B G_full,   s,A,B in R,
    e0 G_full=0,  G_full^2=D e1.

Its compact representation is (s,A+B tau). The product

    U_full=product_(r in QR)(beta+zeta^r)

has augmentation (beta+1)^h and nontrivial component U=A+B tau. Thus acquire it as

    U_full=(beta+1)^h e0+A e1+B G_full.

The basis e0,e1,G_full has O(m) coefficients and is constructed once in soft m; U itself was acquired above. The augmentation is a unit, as is U, so the full relative norm is an explicit unit. This is the full QR relative norm of beta+zeta, not the rank-two element misidentified with a full cyclic element.

Automorphisms fix the scalar component and act on tau by chi(j). Native rank-three rows therefore have the already acquired rank-two T_j and scalar component

    (beta+1)^(h*(N+delta_j)).

Acquire the shared scalar power and O(m) signed row powers to get every rank-three row in soft m, represented by the one common basis and O(m) triples. If all m cyclic coefficients of all rows were explicitly requested, output alone would cost m^2; this theorem supplies their compact rank-three coordinates and coefficient access, not a free expanded table.

The full rank-three own equality follows either componentwise by Frobenius or by applying the multiplicative QR-relative norm to the original own equality. The subgroup automorphisms commute, so this norm commutes with every sigma_j. No information from the augmentation summand is silently dropped when asserting the full relative-norm identity.

## 6. Exact scope and primary reference check

The standard Gauss-square and Frobenius identities are also recorded in the primary Mathlib source/documentation, [Mathlib.NumberTheory.GaussSum](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/GaussSum.html), theorems gaussSum_sq and MulChar.IsQuadratic.gaussSum_frob. Those source formulations corroborate the signs and character action; the elementary universal quotient-ring proofs above establish the precise ring identities used here. No source theorem is claimed compiled into this repository.

Acquired: character table; the exact period-product coefficients; U and its certified inverse; f and q_B; ALL actual rank-two native rows; and compact full rank-three relative-norm rows, all soft m including initialization and all legal small denominators. This is a paid nontrivial character projection beyond augmentation.

Not acquired: the long native local-collision query, a shared support witness, an order certificate for U/q_B, or a factor decoder for translated/period saturation. These require separate proofs and algorithms. No factoring exponent gain is claimed from acquisition alone.
