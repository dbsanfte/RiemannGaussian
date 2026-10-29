# Odd-character prefix: explicit symmetric-power and surgery constructions

26 October2026. Input is the genuine acquired knot polynomial K(T), with sparse Seifert matrix V of order2L, L=soft-O(k), and the native eta with eta²=q. Target:

    P_m=prod_(i=1)^m K(eta^(2i+1)), m=Theta(k^(3/2)).

The negative-only/half-rank construction is retained in L; it is not replaced by a special class of semiprimes or knots. K is reciprocal, K(1)=1, and

    det(V-T V^T)=T^L K(T).

Outcome: a one-knot symmetric-power descriptor of size O(L+log m) gives an exact determinant whose zero is precisely P_m's zero. The expanded determinant still has order2Lm. The explicit tensor and tridiagonal eliminations below did not supply a soft-k scalar computation. This is a concrete representation/cost audit, not a general no-go theorem.

Later in this investigation, the [unit-pattern construction](unit-pattern-infection.md) replaces the zero-base unlink in Section3 by T(2,4). It proves a unit base and a finite normalized determinant, with the raw singular Fox identification still conditional. The rank-m acquisition cost remains open.

## 1. Exact symmetric-power matrix, with no extraneous weight

For m>=1 set

    B=diag(eta,eta^-1),
    A_m=eta^(m+2) * Sym^(m-1)(B).

The monomial basis of homogeneous polynomials of degree m-1 diagonalizes Sym^(m-1)(B). Its eigenvalues are eta^(m-1-2r), r=0,...,m-1. Hence the eigenvalues of A_m are exactly

    eta^3,eta^5,...,eta^(2m+1),                         (1)

in reverse order. Unlike Sym^(2m+1)(B) alone, this construction does not insert the unwanted weights eta,+/-1 or require dividing by K(eta). For m=0, define P_0=1 separately.

It is a genuine abelian GL_m representation of the **same knot group**: send an element g to A_m^alpha(g), where alpha is integer abelianization. The scalar twist eta^(m+2) is a character, so the construction is a representation, not a change in the knot K.

Form the explicit block matrix

    D_m=V tensor I_m - V^T tensor A_m.                 (2)

Permuting the basis from Seifert-index-first to weight-first gives m diagonal blocks V-a_i V^T, a_i=eta^(2i+1). Therefore, over R=Z/NZ itself,

    det D_m=prod_i det(V-a_i V^T)
           =eta^(L*m*(m+2))*P_m.                       (3)

The exponent uses sum_(i=1)^m(2i+1)=m(m+2). The normalizing factor in (3) is a known unit and is acquired by binary powering with an O(log N)-bit exponent. Equation(3) is a finite polynomial determinant identity, requiring no eigenvalue extraction, field specialization, or inversion of a colliding K(a_i).

**Boundary normalization.** Native beta has odd local orders; eta=beta^(H/2) also has odd local orders, and squaring preserves them. Thus ord_P(eta)=ord_P(q), and likewise at Q, both>16H. Since2m+1 lies within the native short horizon, every eta^(2i+1)-1 is a unit. The usual meridian denominator det(A_m-I) in a Fox/twisted-torsion normalization is therefore a unit. Its full numerical value need not be acquired for **zero-only**: the explicitly normalized determinant(3) already avoids that denominator altogether. This is not permission to charge that long denominator product as one operation when an exact torsion value is requested.

The source conventions allowing multiplication by +/-det(rho(g)) introduce only powers of eta here, hence units. Equation(3) fixes a concrete determinant representative and removes any projective ambiguity from the zero decision.

**Paid size and cost.** The symbolic descriptor consists of the acquired O(L)-entry V, eta, m in binary, and the displayed Sym operation: O(L log N+log m) bits. A random diagonal entry of A_m is acquired by one modular powering. Expanding A_m takes Theta(m) entries. Expanding D_m has order2Lm and O(Lm) nonzeros because V has O(L) nonzeros. Evaluating the m small banded blocks or K(a_i) separately costs O(Lm) ring operations. The existing product/baby–giant method can recover the inherited soft-O(L+sqrt(Lm)) scale; no soft-L evaluator for the descriptor is derived here.

Thus (2) does remove the m-leaf **topology** of the keychain in favor of one fixed knot with a binary-described representation. It has not removed the rank-m arithmetic. Counting the Sym descriptor as an already evaluated determinant would be the unproved step.

## 2. Exact tensor circuit for powers of two, and its actual determinant recursion

For m=2^s, a still more explicit binary descriptor is

    A_m=eta^3 * tensor_(r=0)^(s-1) diag(1,q^(2^r)),     (4)

because its eigenvalues are eta^3 q^j, j=0,...,m-1. Its s two-by-two factors are acquired using repeated squaring in O(log m) ring operations. There is no hidden root-of-unity or group-order assumption.

For a variable U define the exact scalar function

    F_s(U)=prod_(j=0)^(2^s-1) K(U q^j).

Block elimination of the last tensor factor gives

    F_s(U)=F_(s-1)(U)*F_(s-1)(U q^(2^(s-1))).          (5)

This is an actual matrix/determinant recursion. A direct scalar evaluation of (5) has2^s leaves. Retaining F_(s-1) as a Laurent polynomial instead grows its width to2L*2^(s-1). The two calls use different U, so a previously evaluated scalar F_(s-1)(U) cannot be reused as the second scalar without an additional identity. The O(log m) tensor descriptor is not an O(log m) scalar evaluation circuit.

For general m, partition its interval into O(log m) dyadic blocks. Each block has a shifted copy of (4); total description is soft-O(log m), but direct-sum rank still totals m. This accounts for binary m without enumerating a negative test family.

The small SL2 matrix does make traces cheap. For example, tr Sym^(m-1)(B) is a geometric/Chebyshev sum and can be computed by binary powering. However det K(A_m) is a product of K at all weights, not tr K(A_m). Already for K(T)=1+c(T+T^-1-2), P_m is degree m in c with explicit leading coefficient prod_i(a_i+a_i^-1-2). A trace formula for a few chosen powers does not by itself evaluate that degree-m norm. No impossibility of a further determinant identity is inferred from this observation.

## 3. A genuine finite-component infection candidate: what works and what still needs proof

A null-homologous infection axis A is attractive because known satellite torsion formulas contain

    prod_(eigenvalues z of rho(A)) K(z).                (6)

There are two distinct issues: supplying the axis representation and evaluating (6).

**Concrete normalizer representation.** Native H is divisible by4. Put s0=beta^(H/4), so s0²=eta, and use matrices

    a=diag(s0,s0^-1), b=[[0,1],[-1,0]],
    [a,b]=diag(eta,eta^-1).                            (7)

They define an exact representation of the free group F2. For each odd r=3,5,...,2m+1, send the two free generators to

    a_r=diag(s0^r,s0^-r), b_r=b.

Their commutator has eigenvalues eta^r,eta^-r. The direct sum of these2-dimensional representations has rank2m and axis determinant1. It can also be described as the normalizer-stable sum of the weight-pair subspaces of Sym^(2m+1)(a,b), **omitting the +/-1 pair**. Omitting that pair is legal for this normalizer subgroup; there is no claim that an irreducible SL2 symmetric power has such an SL2-invariant quotient.

Take the standard Borromean infection picture: the two uninfected components form an unlink with free meridians a,b, while the unknotted third axis represents their commutator, up to orientation/conjugacy. Equation(7) therefore supplies a fixed-component axis with the required odd reciprocal weights. For this representation, the infection factor(6) would be

    prod_(i=1)^m K(eta^(2i+1))*K(eta^-(2i+1))=P_m².     (8)

Because N is squarefree on the hard branch, P_m²=0 iff P_m=0. Thus reciprocal pairing genuinely suits the requested zero-only goal; it does not require acquiring another full row family or inverting an excluded K(eta) factor.

**Why this is not yet a successful small surgery scalar.** The ordinary Alexander polynomial of the closed two-component unlink is zero. Applying a closed-link torsion product formula with that zero base factor cannot make (8) an observable nonzero-normalized determinant. One must use a based **relative** string-link/cobordism invariant, with a specified boundary homology basis, rather than silently discard the base factor. The trivial two-string-link exterior relative to its top punctured disk is a natural unit-base candidate. A complete new construction must identify the infected relative chain complex and all boundary maps and prove that its scalar determinant is a unit times(8), including the singular local branches.

Even granting that relative gluing construction, the explicit axis representation still has rank2m. Its symmetric-power descriptor has size O(log m), but its Fox matrix uses2m-by-2m blocks, and its infection determinant remains (8). Neither the relative construction nor the source formula alone supplies a soft-L scalar evaluation. This is a precise candidate with a missing boundary realization/evaluation step, not a claimed completed infection theorem over R.

## 4. Explicit cyclic/tridiagonal elimination test

Suppose one tries to handle-slide the diagonal factors d_i=K(a_i) into a scalar tridiagonal surgery matrix with off-diagonal products c_i e_i. Its determinants obey

    T_0=1, T_1=d_1,
    T_j=d_j T_(j-1)-c_(j-1)e_(j-1)T_(j-2).            (9)

The desired product is recovered when the extra coupling terms vanish. With a unit coupling, already

    det[[d_1,c_1],[e_1,d_2]]=d_1d_2-c_1e_1.

At any native local hit d_1=0, the original two-factor product vanishes there, whereas this determinant is the unit -c_1e_1. Thus this concrete coupling erases, rather than preserves, the hit. Closing the chain cyclically adds further boundary/cycle terms. Those terms must be retained or cancelled by a proved correction; they are not harmless units multiplying the product.

Unimodular handle slides can of course preserve the determinant exactly. But then a proposed reduced matrix must exhibit the full Schur complement and certify its pivots as units. A pivot d_i cannot be inverted precisely at the collisions sought. Equation(9) isolates a narrow failure of the naive “connect the keys into a short continued fraction” construction, not a general obstruction to all surgery reductions.

## 5. Primary-source audit and its exact limits

1. **T. Kitano**, *Twisted Alexander polynomial and Reidemeister torsion*, Pacific J. Math.174(1996),431–442, https://msp.org/pjm/1996/174-2/pjm-v174-n2-p06-s.pdf . TheoremA identifies twisted Alexander invariants with Reidemeister torsion; Proposition3.1 supplies the Fox determinant/meridian denominator formula under its nonvanishing hypotheses. The source works over fields/linear representations. We use it to identify the interpretation of(2); the composite-ring zero identity(3) is proved directly, and does not import an acyclicity assumption at collisions.

2. **H. U. Boden and S. Friedl**, *Metabelian SL(n,C) representations of knot groups IV: twisted Alexander polynomials*, https://arxiv.org/abs/1209.4244 ; full text https://arxiv.org/html/1209.4244 . Section1.1 gives multiplicativity for direct sums. Lemma7 gives(6), multiplied by the pattern's twisted Alexander invariant, for a null-homologous infection axis in a knot exterior and a GL_k(C) representation. This is exactly why an axis spectrum is relevant, but also why one cannot omit the pattern factor or apply the lemma to the relative Borromean candidate without additional proof. An abelian representation of a knot group sends any null-homologous axis to I, so using(1) as that axis's image would violate the hypothesis structure.

3. **A. T. Tran and Y. Yamaguchi**, *Higher dimensional twisted Alexander polynomials for metabelian representations*, https://arxiv.org/abs/1608.05525 ; full text https://arxiv.org/html/1608.05525 . Proposition3.1 decomposes even symmetric powers of an irreducible metabelian SL2 knot representation into2-dimensional odd-weight summands. Their diagonal commutator eigenvalues are roots of unity of order dividing K(-1), while the meridian has fixed matrix[[0,1],[-1,0]]. Theorem3.2 exploits a supplied finite period for asymptotics. This decomposition supports the weight-pair algebra used in(7), but its periodic evaluation theorem is not available for the native large-unknown-order eta. It is not an algorithm for binary-described arbitrary symmetric-power torsion.

The norm-quotient nonacyclic torsions used in some related link-concordance work are particularly unsuitable as a shortcut here: the reciprocal factor P_m² can itself become a norm, while an “always nonzero” homology-basis torsion has already removed the singularity we need to detect. A based integral determinant representative, with its boundary normalization fixed before specialization, is required.

## 6. Constructive interface remaining

The exact small descriptor is now explicit: either the one-knot matrix(2) with the binary tensor formula(4), or the fixed Borromean infection with the normalizer axis(7). A useful next theorem must do more than define their representation:

    Given the O(L)-entry V, eta, and binary m,
    acquire a scalar A in soft-O(L) bits such that
    A=known_unit*P_m, or A=known_unit*P_m²,
    or prove the corresponding exact zero-equivalence on every native input.

It must operate directly on the symmetric-power/tensor descriptor, or exhibit an O(L)-size surgery Schur complement whose boundary corrections are acquired at the same cost. It cannot expand rankm, invoke a known eta order, invert a collision factor, discard the closed pattern's zero torsion, or assume an analytic approximation preserves zero. The current formulas give precise matrix targets and valid normalizations, but do not yet give that fast scalar operation.
