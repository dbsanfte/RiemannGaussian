# T(2,4) unit-pattern repair: exact Fox calculation and infection factor

26 October2026. This verifies the root's proposed repair of the zero-torsion Borromean/unlink base. It closes that specific base gap. Unconditional results are the acyclic unit pattern, the unknotted axis construction, its odd-pair spectrum, and the explicit finite-ring determinant identity(13). Generic based-field infection multiplicativity is derived below. A literal infection Fox minor and a complete list of its elementary reductions to(12) are not supplied; identifying(12) with such a chosen raw minor at singular specializations remains conditional on that additional chain-level certificate. No remaining rank-m determinant is acquired in soft-k time.

Input: the full native acquired reciprocal K(T), represented by V of Seifert size2L; q=eta², eta=s0², s0=beta^(H/4), with H divisible by4. The hard branch has N=P Q squarefree and odd, and eta has both odd local orders>16H. Let

    r_i=2i+1, i=1,...,m,
    P_m=prod_i K(eta^r_i),

where r_i remains within the native small-order window. Empty prefix m=0 is handled separately by P_0=1.

## 1. Pattern group and actual representations

Let L0=T(2,4), the oriented closure of sigma_1^4 with two components. Its meridian presentation is

    pi(E_L0)=<a,b | (ab)^2=(ba)^2>.

Put c=ab, so b=a^-1 c. The same group has presentation

    <a,c | a c² a^-1 c^-2=1>.                         (1)

The regular Seifert fiber is h=c², which is central. The exterior is Seifert fibered over an annulus with one cone point of order2. Equivalently, start with a pair of pants times S1 and fill its third boundary torus by a solid torus with regular fiber equal to c². This also yields(1) by eliminating the fiber generator from <a,c,h | [a,h]=1,c²=h>.

Primary presentation verification: A. Cavicchioli and F. Spaggiari, *The character variety of one relator groups*, Extracta Math.38(2023),105–123, proof of Theorem3.1, p.110, https://dehesa.unex.es/bitstreams/96147daa-6c6b-4e73-b614-d9d38c8fe476/download . It identifies C(2n) with the closure of sigma_1^(2n), gives <a,b|(ab)^n=(ba)^n>, and displays the meridian generators. Our case is n=2.

For any unit z set

    A_z=diag(z,z^-1), B=[[0,1],[-1,0]],
    C_z=A_z B=[[0,z],[-z^-1,0]].

Then C_z²=(B A_z)²=-I, so these matrices **actually satisfy** the torus-link relation for every z; no root-of-unity condition on z is needed. For the native i-th odd pair use z=s0^r_i. Let rho_m be their direct sum, of dimension d=2m. Every generator has determinant1 and

    rho_m(h)=-I_d.                                    (2)

This representation is genuinely obtained from the normalizer-stable odd-weight subspaces of Sym^(2m+1)(diag(s0,s0^-1),B), with the +/-1 pair omitted. Each absolute-weight pair is invariant under the diagonal matrix and B. On an odd degree, B²=-I; a diagonal sign basis change normalizes its two off-diagonal entries to B as written. Thus omitting +/-1 is an actual direct-summand operation for this subgroup, with no division by K(eta) and no formal virtual representation.

## 2. Fox complex proves acyclicity and unit base torsion

Use relator R=a c² a^-1 c^-2 from(1). Evaluated under A=rho(a), C=rho(c), its Fox derivatives are

    F_a=I-A C² A^-1=2I_d,
    F_c=(A-I_d)(I_d+C).                               (3)

The Fox identity in the right-module convention is

    F_a(A-I_d)+F_c(C-I_d)=0,

since C²=-I_d. Also

    (C-I_d)^-1=-(C+I_d)/2.                            (4)

Because2 is a unit in R=Z/NZ, these are actual unit pivots. The C-I block makes the boundary C_1->C_0 surjective. Its kernel is parameterized by the a-coordinate; the derivative F_a=2I maps C_2 isomorphically onto that kernel. The resulting twisted pattern complex is therefore acyclic **over R**, not merely over an algebraically closed characteristic-zero field.

For one2-dimensional pair,

    det F_a=4, det(C-I)=2,
    tau(E_L0,rho_z)=4/2=2,

up to the ordinary orientation/basis sign. By block multiplicativity,

    tau(E_L0,rho_m)=+/-2^m.                           (5)

This scalar is cheaply acquired in O(log m) ring operations, and it is a certified unit. There is no eta-Pochhammer denominator to acquire in(5).

An independent topological calculation reaches the same result: the pair-of-pants times circle piece has torsion det(h-I)^(-chi(pants))=det(-2I)=2^(2m); the exceptional solid torus has torsion det(C-I)^-1=2^-m; their gluing torus has torsion1. Every torus involved contains the h=-I unit pivot. The product is again2^m. This calculation also shows why no uncharged homology-basis correction from the unlink case remains.

## 3. Unknotted commutator axis exists with fixed geometric cost

Take a based loop representing

    w=[a,b]=a b a^-1 b^-1=c a^-1 c^-1 a.               (6)

Its exponent sum in both meridians is zero, so it is null-homologous in E_L0 and has linking number0 with each pattern component. It admits an embedded representative by general position in dimension3. It can be chosen unknotted in S3: take a generic link diagram and change only the auxiliary loop's self-crossings to make its own diagram descending. Each crossing change is a homotopy of the auxiliary loop supported in a ball disjoint from L0, so its free homotopy class in E_L0 is preserved. No crossings of the pattern itself are changed.

One may route the four meridional petals and their connecting paths outside the fixed torus-link twist box. The self-crossing changes can also be confined there. Thus an axis disjoint from that box is available without changing the group word. It is not necessary to assume that the exact Borromean drawing survives a twist operation unchanged. The pattern has four crossings and the word has length4; one fixed auxiliary diagram can be constructed and stored once, with constant complexity independent of N,L,m. A literal crossing list has not been drawn in this note; the descending-diagram procedure is an explicit finite construction of it.

Primary precedent: T. D. Cochran, *Noncommutative knot theory*, AGT4(2004),347–398, Section8, p.377, https://msp.org/agt/2004/4-1/agt-v4-n1-p19-p.pdf . The infection construction explicitly notes that every group element has an unknotted representative. The source phrases this for a knot complement; the self-crossing-change proof above applies unchanged to a fixed link complement and is supplied here rather than treating the link version as a quoted theorem.

Let A_axis denote this unknotted representative, distinguished from the matrix A. For one pair,

    rho_z(w)=A_z²=diag(z²,z^-²).

Consequently its image G_m=rho_m(w) has precisely the eigenvalues

    eta^r_i,eta^-r_i, i=1,...,m.                       (7)

Changing the axis orientation replaces these by their inverses and leaves the reciprocal K-product unchanged.

## 4. Infection gluing, with every boundary factor retained

Infect the fixed pattern L0 along A_axis by the acquired knot K. This produces a genuine two-component satellite link S(K); it does not require m components. The representation on its group is the pullback of rho_m under the degree-one infection-collapse map. On the companion exterior it is the abelian representation sending a meridian to G_m and a longitude to I.

The peripheral meridian of the removed axis maps to I and its longitude maps to G_m. By the native local-order guarantee, each eta^r_i-1 and eta^-r_i-1 is a unit. Thus G_m-I is invertible. Put

    D_boundary=det(G_m-I)
      =prod_i(eta^r_i-1)(eta^-r_i-1).                 (8)

It is a certified unit. We do **not** claim its long numerical product has been acquired cheaply.

Let U be the punctured pattern exterior E_L0 minus the open axis solid torus. The common gluing torus has one nontrivial generator G_m with G_m-I invertible, so it is acyclic with torsion1. The removed solid torus has torsion D_boundary^-1. Since the original pattern is acyclic, U is acyclic too, and based multiplicativity gives

    tau(U)=tau(E_L0)*D_boundary.                       (9)

Over a formal coefficient field, where the companion evaluations are nonzero, its abelian twisted torsion is

    tau(E_K;G_m)=det K(G_m)/D_boundary,
    det K(G_m)=prod_i K(eta^r_i)K(eta^-r_i)=P_m².       (10)

The normalization det(V-T V^T)=T^L K(T) causes no extra factor here: det G_m=1, so its L-th power cancels exactly across reciprocal pairs. Gluing(9) and(10) cancels the entire boundary aggregate **symbolically**:

    tau(E_S;rho_m)=+/-2^m * P_m²                      (11)

where the left-hand side is being asserted as an ordinary nonzero torsion only on its acyclic generic locus.

The base calculation(5) is always acyclic under our unit hypotheses. **The infected target need not be acyclic at a collision.** At such a point the acyclic torsion on the left of(11) is not defined. The explicit matrix(12) below supplies a polynomial scalar extension of its generic expression. Identification with a selected raw infection Fox minor at that specialization remains unproved, as specified in Section5; no singular Alexander-order identity is being imported from the field theorem.

## 5. Finite-ring specialization and an explicit zero-extended matrix

Here is a direct integral determinant representative that makes the singular branches precise. Write V for the acquired integer Seifert matrix of K and define

    D_comp=V tensor I_(2m)-V^T tensor G_m,
    Z_m=diag(2I_m,D_comp).                            (12)

By the block spectra(7) and the Seifert determinant identity,

    det D_comp=prod_i det(V-eta^r_i V^T)
                         *det(V-eta^-r_i V^T)
              =P_m²,
    det Z_m=2^m P_m².                                (13)

These are finite Laurent-polynomial identities, with no inversion of K(eta^r_i). Matrix Z_m is the explicitly chosen **normalized determinant representative** of the generic gluing expression. It is not claimed to be the literal unreduced Wirtinger Fox matrix of a drawn satellite diagram. Its scalar is defined everywhere by the directly proved identity(13). The generic field gluing calculation identifies this scalar with a based torsion representative up to sign. However, an explicit raw infection Fox minor and the full finite-ring elementary reduction to(12) have not been written. The assertion that(12) is obtained from a selected raw infection minor using only the certified unit pivots should therefore be treated as a remaining chain-level construction, rather than as an already acquired certificate.

To justify specialization independently of a field theorem, work first over the universal Laurent ring in s0 and its inverse, with2 inverted. The fixed pattern pivots are2 and C-I with the explicit inverse(4). The only axis-boundary denominators additionally used in the gluing are factors s0^(2r_i)-1. Those are inverted temporarily for the based torsion proof, cancel between(9) and(10), and specialize to certified units on every native input. No companion K-value is inverted in deriving(12)–(13); the generic equality is cleared to the finite determinant identity before specializing to Z/NZ. Thus the explicit determinant identity(13) remains valid when a companion factor vanishes at one or both primes. This does not by itself construct or certify a raw infection Fox minor in the composite ring; that further identification is conditional as stated above.

Since N is squarefree and2 is a unit,

    det Z_m=0 mod N  iff  P_m=0 mod N.                 (14)

If P_m vanishes at exactly one prime, its square still vanishes at exactly that prime. Hence proper/nonunit behavior is also preserved. Ordinary powers of determinant images from changing lifts or bases are units: the representation is in SL_(2m), so only a sign remains for the unparameterized torsion, and(12) fixes a concrete sign convention for the scalar.

Primary gluing comparison: J. C. Cha and S. Friedl, *Twisted torsion invariants and link concordance*, https://arxiv.org/abs/1001.0926 , Section7.1, Lemma7.1 and its proof, https://arxiv.org/html/1001.0926 . It supplies the infection-collapse map, meridian/longitude interchange, rank condition, and companion eigenvalue factor for unitary field representations. Its stated torsion uses a norm quotient and requires nonzero companion evaluations for the multiplicative assertion. We do not treat that field/norm-quotient statement as an automatic finite-ring identity; the explicit pivots and finite determinant(13) above supply the specialization and retain the zeros instead of dividing them away.

## 6. Reproducible symbolic tests actually run

`check_unit_pattern.py` in this directory uses only the Python standard library and exact Laurent polynomials Z[z,z^-1]. Its captured output is `unit-pattern-validation.txt`. It checks:

- both(a,b) and(a,c) relators;
- C²=-I and the commutator spectrum diag(z²,z^-²);
- both Fox derivatives in(3), the Fox contraction identity, det F_a=4 and det(C-I)=2;
- three signed genus-one Seifert examples for det(V tensor I_2-V^T tensor diag(z²,z^-²))=K(z²)².

All checks passed. The symbolic variable z covers every odd-weight block, so this is a check of algebraic signs, not a numerical claim about native coverage or a selected semiprime.

## 7. What is repaired, and what remains unpaid

The fixed pattern/axis now has constant topological complexity, a genuine representation for every native eta, and cheaply acquired unit base torsion2^m. The former closed-unlink base-zero obstruction is removed. The +/-1 weight pair is omitted by an actual invariant summand; no accidental K(eta) boundary factor is introduced. Every axis-boundary normalization cancels before the zero test.

The representation rank is still2m. The normalized matrix(12) has order(4L+1)m and O(Lm) nonzeros when expanded. A one-knot template, fixed torus-link/axis template, and symmetric-power descriptor have O(L+log m) weighted description size, but no theorem here evaluates det Z_m in soft-O(L). Direct odd-pair evaluation costs O(Lm) ring operations; the inherited block product method retains its previous soft-O(L+sqrt(Lm)) scale. Expanding the geometric infected knot diagram can also multiply the fixed number of pattern strands by the size of an expanded K diagram and is not part of the small scalar acquisition.

Thus the proven positive result is a **unit-pattern repair and exact odd-pair determinant encoding**, valid on the entire native family: the base is acyclic with unit torsion, the axis has the right spectrum, and(13) is a globally valid finite-ring zero certificate. The satellite interpretation is exact on the generic based-field locus. Its promotion to a particular acquired raw infection Fox determinant at all singular composite-ring specializations still needs the explicit unit-pivot chain reduction described above. The outstanding fast operation is still the rank-m companion norm det K(G_m), or an equivalent small surgery Schur complement acquired without inverting its zero factors. No improved complete factoring bound is claimed.
