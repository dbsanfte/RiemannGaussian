# Norm doubling on the actual odd-order source: a valid gcd transform and a branching obstruction

2026-10-15. New classical route analysis. No repository edits/builds. No nearlinear whole-query algorithm is obtained, and no arbitrary scalar lower bound is claimed.

## A genuine useful identity: squaring is collision preserving here

Write P_L(z;q)=prod_(0<=i<L)(1-z q^i). On the retained actual semiprime source, gamma has exact odd prime local orders R_P,R_Q, q=gamma^(m²), and z_j=gamma^(-E_j), E_j=N+delta_j. Therefore z_j q^i belongs to an ODD-order subgroup in each hidden field. Since -1 has order two, every 1+z_j q^i is nonzero in BOTH fields. Its lift to Z/N is a unit.

The division-free identity

    P_L(z;q) P_L(-z;q)=P_L(z²;q²)                         (1)

thus implies, with N squarefree,

    gcd(N,prod_j P_L(z_j;q))
      =gcd(N,prod_j P_L(z_j²;q²)).                        (2)

No collision factor is inverted, no negative-complement product is acquired, and no hidden order is an input to this algebraic identity. Squaring public targets and q costs O(J) ring operations. The odd local-order hypothesis is substantive: for arbitrary even-order source groups, negative complements can create spurious collisions.

Equation (2) is a GCD/zero-support equivalence, not equality of the desired scalar product. Exact scalar recovery would still need the complement unit product. Moreover J and L are unchanged. Iterating replaces z_j,q by their common 2^k powers without shortening the interval. Thus this positive transform alone does not acquire the long query.

## Why the time split does not collapse into the sign norm

Time splitting is the separate exact identity

    P_(2n)(z;q)=P_n(z;q²) P_n(z q;q²).                   (3)

The children z and zq are translates, whereas (1) needs the pair z,-z. On the actual source all translated targets are in the same odd subgroup and all their negatives are outside it. Thus the two child sets contain NO opposite target pair in either hidden field. Existing actual target families cannot simply be paired by the sign involution.

One may adjoin each missing negative child, justified as unit support above. But this yields

    P_n(z²;q⁴) P_n(z² q²;q⁴)
      =P_(2n)(z²;q²),

which is just the squared-target length-2n query again. It has not halved the number of time factors. Introducing the negative complements does not identify the time children.

More generally, if a complete 2^k-th root-of-unity family is adjoined in an extension where it splits, then

    prod_(omega^(2^k)=1) P_L(omega z;q)
      =P_L(z^(2^k);q^(2^k)).                            (4)

Every nontrivial omega factor is a unit in every hidden residue extension field because its nontrivial power-of-two order cannot lie in the odd source subgroup. Consequently this completion preserves collision support but still leaves L unchanged. Such roots/towers must themselves be acquired if an implementation uses them. Odd-order completions that intersect the source subgroup do NOT have this automatic safety: adding a root that makes omega z q^i=1 can manufacture a zero not in the original valid interval.

## An actual-source explicit-branching floor

This statement is about explicit transformed target packets, not all implicit scalar programs. It uses the ACTUAL low-digit relation and global order, rather than generic polynomial degree alone.

Assume the canonical first-current family J=m-1, delta_j in [-3m²,m²], gamma global order D>16m^4, and m an odd prime not dividing N. For 1<=T<=4m² define branch nodes

    B_(j,r)=z_j q^r=gamma^(-N-delta_j+m²r),
    1<=j<m, 0<=r<T.

If two branch nodes agree modulo N, D divides

    -delta_j+delta_k+m²(r-s).

Its absolute value is at most 4m²+m²(T-1)<=4m^4+3m²<16m^4<D (eventually, and directly for m>=2). Hence that integer difference is ZERO. Reducing modulo m gives equality of delta low digits. The actual source formula is

    delta_j=N(t²-2t) mod m, t=j^(-1).

For each low digit this is a nonzero quadratic in t, so at most TWO tags have it. For any fixed tag, equality of integer exponents forces r=s. Therefore every numerical global branch-node value has multiplicity at most two, and

    #{B_(j,r)} >= J T/2.                                (5)

This is numerical equality MODULO N, proved using the global order. It does NOT assert disjoint local q-orbits; gamma and q generate the same local subgroup. Nor does global distinctness imply pairwise unit differences or a polynomial-degree root bound over the composite ring.

After k ordinary even/odd time splits, T=2^k, the packet consists exactly of these J T targets at base q^T, each with length about L/T. For L~m², at depth T~m, any contract explicitly acquiring/deduplicating the transformed target array still exposes Omega(m²) distinct residue words by (5), exceeding soft O(m). The same floor applies if each level also uses sign completion/squaring: at depth k the nodes become (z_j q^r)^(2^k), with common base q^(4^k); raising to 2^k is injective in the actual odd-order global gamma subgroup, so their distinctness is unchanged. Ragged final lengths/odd endpoints remain charged.

The floor concerns a specified recursion that materializes its full branch packet. It does not forbid a smaller aggregate cocycle, a compressed scalar resultant, sharing among unevaluated circuits, or stopping early and switching to another algorithm. Such a different interface needs its own acquisition proof.

## The source carrier has no sign norm tower for free

Over either hidden field the source roots all lie in an odd subgroup, while their negatives lie outside. Thus the root multiset of H(X)=prod_j(X-z_j) is disjoint from its negative. Substitution X->-X is not an endomorphism of that source quotient: H(-X) cannot be a scalar multiple of H(X). Completing H to H(X)H(-X) first DOUBLES its rank. Taking the sign norm then gives the squared-root carrier of degree J, not J/2. Squaring is injective on the local subgroup, so the number of distinct source roots does not decrease either.

This contrasts with a genuine smooth-degree cyclotomic tower, where the ambient carrier already has a known sign automorphism and the relative norm reduces a known field degree. Replacing the source carrier by that carrier would require a paid exact embedding/selection construction, including ANY semantics and collision-safe denominators. Merely labeling the source resultant a norm does not supply it.

## Primary literature checked

Daniel J. Bernstein, *Fast norm computation in smooth-degree Abelian number fields*, Research in Number Theory 9, article 82, November 10, 2023:
https://doi.org/10.1007/s40993-022-00402-0
Primary journal PDF saved as bernstein-norm-2023.pdf. The introduction explicitly illustrates g(X)g(-X), reduction into a known cyclotomic subfield, and recursive norm transitivity. Its n(log n)^(3+o(1)) bit bound is for explicitly represented integral inputs in known smooth-degree Abelian number fields with tower-compatible bases and stated coefficient/weight regime. It is not a theorem acquiring an implicit P_L modulo an arbitrary source H over Z/N. The source carrier above lacks its required sign symmetry.

Bostan–Yurkevich, *Fast Computation of the N-th Term of a q-Holonomic Sequence and Applications*, JSC 115 (2023), 96–123:
https://arxiv.org/abs/2012.08656
The previously inspected expanded primary Algorithm 3 / Section 3.4 retains degree J and gives soft O(J+sqrt(JL)). The doubling identity builds a growing polynomial or branches over changing arguments; a sign norm by itself does not remove that acquisition.

Adamczewski–Bell–Delaygue–Jouhet, *Cyclotomic valuation of q-Pochhammer symbols and q-integrality of basic hypergeometric series*:
https://arxiv.org/abs/2209.11075
The primary abstract states cyclotomic valuation formulas and q-integrality criteria, not a nearlinear composite-ring scalar evaluator. No applicable later improvement surfaced in this focused search; this is not a literature-completeness claim. The current 2026 modular-composition and cyclic-q-dilog results inspected in the previous bundles remain separate interfaces and are not used as an uncharged scalar oracle here.

## Precise remaining positive target

The new safe identity (2) is compatible with target-subset and contiguous-interval restrictions: absorb the interval start into z_j, which remains in the odd subgroup. Thus it is a genuine restriction-stable collision transform. It does not meet the requested soft O(J+sqrt L) clock because it preserves the long-query dimensions. To progress, an additional exact identity must aggregate its time branches without exposing the Omega(JT) packet, or supply a new paid norm carrier whose acquisition already encodes those branches. No such identity/algorithm was found here.
