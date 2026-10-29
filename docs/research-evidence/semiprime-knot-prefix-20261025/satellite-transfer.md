# Satellite, cabling, and twist-surgery audit for the native zero-only prefix

25 October2026. Uses the already acquired native Alexander polynomial and sparse Seifert realization. No repository edits. No new fast prefix algorithm established.

Target over R=Z/NZ:

    P_m=prod_(i=1)^m Delta(q^i),

or exactly its zero decision, for the native q=beta^H and m=O(k^(3/2)). All native rows and existing prefix-consumer coverage are retained. A known unit multiple of P_m is fully sufficient; a topological expression with an unproved zero divisor prefactor is not.

## 1. Concrete positive encoding: a knotted keychain gives exactly the prefix

Primary source: D. Cimasoni, *The Conway function of a splice*, Proc. Edinburgh Math. Soc.48(2005),61–73, https://arxiv.org/abs/math/0407130 ; full text https://arxiv.org/html/math/0407130 ; author PDF https://www.unige.ch/~cimasoni/splice.pdf . Theorem3.1 gives the splice product formula; Corollary3.8 gives connected sum along a component:

    nabla_(L' # L'')(t1,...)
      =(t1-t1^-1)*nabla_L'(t1,...)*nabla_L''(t1,...).

The proof explicitly uses the normalization nabla_positiveHopf=1. The reduced function is Omega_K(t)=(t-t^-1)nabla_K(t); for a knot, Omega_K(t)=Delta_K(t²) in the symmetric normalization. Corollaries3.2–3.6 give the accompanying satellite/cabling formulas.

**Our construction from those exact identities, for m>=1.** The empty prefix m=0 is handled separately by P_0=1 and requires no link construction. Start with m positive Hopf links and take their connected sum along one chosen component. The result is a keychain C_m with central component0 and leaves1,...,m. Induction using Corollary3.8 gives

    nabla_Cm(t0,t1,...,tm)=(t0-t0^-1)^(m-1).

Tie a copy of the acquired knot K into each leaf by connected sum along that leaf. A leaf sum introduces the multiplier

    (tj-tj^-1)*nabla_K(tj)=Omega_K(tj)=Delta_K(tj²).

Thus the resulting actual colored link L_m has

    nabla_Lm(t0,...,tm)
      =(t0-t0^-1)^(m-1)*prod_(j=1)^m Delta_K(tj²).     (1)

Every cancellation here occurs first in the formal Laurent polynomial identity. The source uses oriented ordered links in integral homology spheres and the sign-determined Conway function, rather than an arbitrary projective representative. Positive Hopf links and connected sums along the specified consistently oriented components meet those hypotheses in S^3. There is no division by Delta_K and no assumption that an evaluation is nonzero. If one instead starts from an Alexander representative defined only up to +/-monomials, that ambiguity specializes to a certified unit because every color is a unit; it cannot introduce an accidental nonunit factor.

In the actual native setup k=2*3^e, so H=k² is even. Acquire

    eta=beta^(H/2), eta²=q,
    t0=eta, tj=eta^j.

Equation(1) then becomes, directly over R,

    nabla_Lm(eta,eta,eta²,...,eta^m)
      =(eta-eta^-1)^(m-1)*P_m.                         (2)

The boundary multiplier is a certified unit:

    eta-eta^-1=(q-1)/eta.

Both eta and q-1 are units by the native setup. Equation(1), after the formal knot denominators have cancelled, is a finite Laurent polynomial identity over the integers; specialization therefore uses only addition, multiplication, and inverse powers of the unit colors. No field torsion specialization, generic acyclicity assumption, or analytic continuation is needed. Consequently (2) preserves **global zero exactly**, and also preserves proper/nonunit behavior. For a q-only interface lacking beta,H, adjoining eta²=q is a free rank-two extension, so the same construction remains exact with a constant representation overhead; the native API does not need that extension.

**Acquisition cost, not omitted:** L_m has m+1 actual components. Its explicit keychain skeleton and leaf colors cost Omega(m) entries even if a single K-template is shared; writing eta^j sequentially costs O(m) ring operations. Copying the actual2J sparse Seifert data into every leaf costs O(mJ) without template sharing, and expanding K's binary twist coefficients into crossings can cost much more. Keeping K as a shared template reduces description to O(J+m), still above soft-k since m=Theta(k^(3/2)). The formal macro “m identical knotted keys, geometric colors” has O(J+log m) description, but evaluating its invariant through (1) returns precisely the unknown prefix product. The source proves no fast invariant algorithm for that macro.

This is a genuine order-free **representation** of the full native zero-only query by an actual link, with the boundary correction and every unit accounted for. It is not yet a compressed-acquisition solution.

## 2. Morton: an actual binary twist computation, but it gives a geometric sum

Primary source: H. R. Morton, *The Alexander polynomial of a torus knot with twists*, JKTR15(2006),1037–1047; author PDF https://www.liverpool.ac.uk/~su14/papers/torusknottwist.pdf ; repository https://livrepository.liverpool.ac.uk/3000530/ . Sections2–3 give a two-strand Burau recurrence and an explicit four-component link polynomial

    A(x,y,t,w)=(1-t²)(1-xw)-(1-t)(1-w)(yt+xy^-1).

Full twists induce w->w*t^(2m). Torres deletion sets w=1 and divides by1-t², yielding

    D_m=1-x*t^(2m)-(1-t)*G_m(t²)*(yt+xy^-1),
    G_m(z)=1+z+...+z^(m-1).                            (3)

This follows directly from A and works with the stated orientation conventions. This audit uses the displayed final four-component surgery identity in Section3; no claim about intermediate summation conventions is needed.

**Our acquisition proof.** Powers and G_m can be acquired together without division in O(log m) ring operations:

    z^(2r)=(z^r)²,
    G_(2r)(z)=G_r(z)*(1+z^r),
    G_(2r+1)(z)=G_(2r)(z)+z^(2r).

Consequently the fixed four-component formula really can process binary twist count m in O(log m), once x,y,t are supplied units. Ordinary diagrams expand to Omega(m) crossings, but (3) avoids their acquisition. This is an example of the type of exact succinct-topology calculation we need.

**Narrow failure for our prefix:** The output's m dependence is t^(2m) and a geometric **sum**, not a product of the acquired Delta(t^i). It can evaluate a fixed link under one monomial substitution, or introduce one companion value via a satellite. It does not introduce the independently shifted companion factor for every earlier i.

At t=q, the native range ensures1-q² is a unit, and where2m<16H also1-q^(2m) is a unit. Thus G_m(q²)=(1-q^(2m))/(1-q²) is itself a unit. This range holds for the actual asymptotic native horizon (the packet's explicit h bound and k>16 give2h<16H). Such a pure Torres/geometric-sum factor cannot be the source of the guaranteed native collision. The remaining Delta-dependent coefficient would need a separately proved zero-equivalence to P_m; the surgery identity gives none. This is a failure of candidate(3), not a theorem about all surgery constructions.

The correction1-t² in deriving (3) can be eliminated symbolically by G_m. For other Torres applications, the corresponding division must remain explicit and unit-tested after specialization. Symbolic divisibility over the Laurent polynomial ring does not license dividing by an arbitrary zero divisor in R.

## 3. Parallel colored cabling: collapse is to the product color

Primary source: M. Harper, *Seifert–Torres Type Formulas for the Alexander Polynomial from Quantum sl2*, Topology Appl.320(2022),108238, https://arxiv.org/abs/1911.00646 ; full text https://arxiv.org/html/1911.00646 . The published numbering differs from the arXiv HTML restatable environments; Section6's knot-parallel formula is Corollary6.8 in the current arXiv text (Corollary6.10 in the journal text):

    nabla_(K parallel n)(t1,...,tn)
      =(tau^w-tau^-w)^(n-1)*nabla_K(tau),
    tau=t1*...*tn,

where w is the diagram writhe/framing. The cabled crossing relation in Section7 is

    R_cable²+R_cable^-2=(tau²+tau^-2)*I.                 (4)

Theorem2.10 and Convention2.12 impose nondegeneracy on the representation decompositions; the final link identities agree with the classical splice formulas.

**Our precise candidate test.** Coloring the n=m parallel strands by eta,eta²,...,eta^m gives tau=eta^(m(m+1)/2). The entire companion dependence collapses to **one** value Delta_K(tau²), hence Delta_K(q^(m(m+1)/2)), after the one-knot normalization. It does not give prod_i Delta_K(q^i). The degree-two cabled skein relation allows powers of the cabled crossing to be reduced with O(log twistcount) scalar arithmetic, but it retains this aggregate-color behavior.

Zero-only is especially delicate here. For zero framing and n>1, the displayed framing prefactor is zero identically. For nonzero framing, tau^w-tau^-w is not automatically a unit: its exponent after squaring may be of order m², outside the supplied16H order window. Its vanishing could therefore introduce a zero unrelated to a native prefix hit. A unit test can sometimes return a factor, but global saturation cannot be treated as a successful prefix certificate. Removing the known polynomial factor formally is legitimate; after removal, the remaining companion factor is still only the single aggregate evaluation.

The underlying tensor space has dimension2^m (and the doubled crossing acts on dimension4^m). The published factorization avoids that expansion for this specific invariant, so it would be inaccurate to charge an inevitable exponential cost. Conversely, the factorization's final formula must be used as written; one cannot replace its aggregate color by an unproved product of evaluations. Intermediate projectors require actual nondegeneracy/unit conditions. A fixed fourth root in the quantum construction is not the native q and need not have native q's order; one may use the already integral classical link identity instead of specializing the representation theory.

## 4. What Torres and ordinary satellites actually supply

From Cimasoni's Corollary3.4, a pattern of winding ell gives the familiar one-variable identity

    Delta_satellite(T)=Delta_pattern(T)*Delta_K(T^ell),

up to the explicitly normalizable Laurent unit. Binary ell can make one endpoint evaluation cheap: q^ell is acquired by powering and Delta is already a degreeJ polynomial. A fixed finite number of satellite companions gives the same fixed number of such evaluations. No product over all intermediate winding numbers appears in that identity.

Iterating with winding1 connected sums multiplies the same Delta(T); iterating a fixed windingw produces Delta(T),Delta(T^w),Delta(T^(w²)),..., which is a multiplicative exponent chain rather than the full additive interval1,...,m. Choosing each winding separately can manufacture all desired factors, but then the list of operations has lengthm. These are explicit construction costs, not a general prohibition on a better satellite macro.

Likewise Fox calculus differentiates a binary word a^m to a geometric sum1+a+...+a^(m-1). Equation(3) is a concrete topological instance where that sum is genuinely fast. A geometric sum can describe an interval as a linear operator, but its determinant or torsion after coupling to K must still be proved to preserve P_m. The coupled determinant is the missing identity, not the availability of binary exponentiation or the formal Fox derivative.

## 5. Next constructive interface

The knotted keychain in Section1 fixes a precise target for a potentially useful satellite reduction. A sufficient new theorem would replace the m-leaf keychain macro by an acquired diagram/algebraic presentation with soft-O(J) entries and O(log N)-bit weights, and produce an exact determinant coefficient A_m such that

    A_m=U_m*prod_(i=1)^m Delta(q^i),

or at least A_m=0 iff the right-hand product is0 on every native allowed input, with every spurious boundary zero excluded. U_m must be an explicitly acquired unit. The theorem must also evaluate this coefficient in soft-k bits from V,q,m, without expanding m leaves, m colors, a rank-m character representation, or m copies of K. Prefix choices of m must be supported.

Morton's four-component identity proves that binary twist counts can sometimes be evaluated exactly at small cost; Cimasoni proves that the desired whole-prefix invariant has a concrete satellite realization. The missing bridge is a surgery/Fox determinant identity that couples the *many differently colored knotted keys* into a small evaluable presentation, rather than fusing them into one product color. The three audited papers do not provide that bridge. No native fast zero-only bound is claimed.
