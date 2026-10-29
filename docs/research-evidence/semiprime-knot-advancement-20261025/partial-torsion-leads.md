# Partial Alexander products: focused gluing audit

25 October 2026. Three primary papers inspected. None supplies an acquired soft-J computation of the native partial orbit product. The concrete constructions below explain exactly what would have to be added; this is not a claim that such an extension is impossible.

Target: for the acquired bandwidth3 Seifert matrix V of order2J, with Delta(T)=T^-J det(V-TV^T) normalized by Delta(1)=1 modulo N, compute or decide zero/nonunit of

    P_m=prod_(i=1)^m Delta(q^i),

for m below both large unknown local q-orders. The complete native catalogue and inherited scalar-prefix consumer remain unchanged. No expanded large knot diagram is supplied as free input.

## 1. Florens–Massuyeau: exact boundary functor, with the character part of the object

Primary: V. Florens and G. Massuyeau, *A functorial extension of the abelian Reidemeister torsions of three-manifolds*, https://arxiv.org/abs/1403.4050 ; full text https://arxiv.org/html/1403.4050 ; PDF https://arxiv.org/pdf/1403.4050 .

TheoremII defines a projective Reidemeister functor for a field F and G⊂F*. An object includes a surface and its character; composition requires matching boundary characters. Section4.2 assigns the exterior algebra of a dimension2g twisted relative homology space. Proposition7.2 states, for homology cobordisms,

    R(M,psi)=tau^psi(M,partial_+M) * exterior(Magnus^psi(M)).

TheoremI gives an integral Alexander functor over Z[G] for finitely generated free abelian G. The knot-exterior formulas are in Sections3 and6. These are exact composition results, not arithmetic-complexity estimates.

**Our dimension/cost deduction.** The full exterior state has dimension2^(2g)=4^g. Storing an arbitrary full map has quadratic cost in that dimension. Storing a factored scalar torsion and a 2g-dimensional Magnus map avoids exterior expansion, but still requires acquisition of the scalar torsion. Proposition7.2 does not compute that scalar from the Magnus map. For g=J the unexpanded matrix representation is essential; for fixed g the state is bounded, but obtaining a fixed colored block for the native clock is still necessary.

### Concrete Dehn-shear clock candidate

On a once-punctured torus take generators a,b and the Dehn shear f:a->ab, b->b. Let

    psi_i(a)=q^i, psi_i(b)=q.

Then psi_i∘f=psi_(i+1). This successfully encodes the geometric index by one fixed underlying mapping class, with genus1 and exterior state dimension4. It is a genuine candidate for organizing a colored gluing construction.

But it is **not a repeated endomorphism of one colored object**. Repeating the same colored mapping cylinder at a fixed psi requires psi∘f=psi; evaluated on a this forces psi(b)=1, whereas the native psi(b)=q has both local orders>16H. Each stage therefore has a different character psi_i. Functoriality composes these maps, but does not identify their scalar coefficients or torsion with one constant 4-by-4 matrix. This is an exact boundary-character mismatch, rather than an appeal to the old finite-quotient q-Weyl obstruction.

One can instead keep independent formal variables U=psi(a),Q=psi(b) and retain the semilinear substitution U->UQ. A scalar insertion Delta(U) then gives the formal operator

    (A h)(U)=Delta(U)h(UQ),
    A^m 1=prod_(i=0)^(m-1) Delta(UQ^i).

After U=Q=q this is the desired product. This algebraic construction is explicit and order-free, but its coefficient product is precisely P_m. A new fast scalar-evaluation theorem for this semilinear functor would be required. The cited functor does not provide it. Realizing a knot insertion as a particular cobordism with exactly this scalar factor would also require a supplied construction; it is not asserted here without proof.

## 2. Bigelow–Cattabriga–Florens: integral tangle composition

Primary: S. Bigelow, A. Cattabriga and V. Florens, *Alexander representation of tangles*, https://arxiv.org/abs/1203.4590 ; full text https://arxiv.org/html/1203.4590 .

Theorem2.1 identifies the invariant of a (1,1)-tangle with scalar multiplication by its closure's Alexander polynomial. Theorem5.2 proves functoriality from cup, braid and cap maps. Section2 constructs maps between exterior powers of twisted boundary homology over Z[t,t^-1]; Section3 gives explicit Burau-generator matrices. Theorem4.3 controls dependence on plat presentations up to a Laurent unit.

**Our candidate and cost.** A tangle representing the acquired knot gives the scalar Delta(t), so m copies at the **same** character t compose to Delta(t)^m, cheaply powered once Delta(t) is known. To get P_m one needs characters t=q,q²,...,q^m. Ordinary uncolored tangle composition uses one compatible character, not m changing substitutions. Declaring the copies differently colored records the clock but does not remove its acquisition.

The explicit cup/braid/cap framework could process a supplied word of length L with bounded strand count using bounded-size matrices. A repeated identical word block permits binary powering. Our sparse Seifert matrix does not itself supply a bounded-strand, logarithmic-length colored word encoding all m shifted evaluations. Expanding its integer twists into crossings can already exceed the soft-J budget. Thus neither the supplied diagram size nor a repeated-block hypothesis is available. The integral theorem is nevertheless preferable to rational torsion formulas when attempting a future composite-ring construction, because polynomial determinant identities can be specialized without assuming a field.

## 3. Borghini: gluing correction is actual input, not an ignorable boundary constant

Primary: S. Borghini, *A gluing formula for Reidemeister–Turaev torsion*, https://arxiv.org/abs/1401.0431 ; full text https://arxiv.org/html/1401.0431 .

TheoremIII.2 gives

    tau(M)=T(h,h1,h2)*tau(M1)*tau(M2),
    T=tau_a^-1*tau_b*tau_c^-1*tau_d*tau_e*tau_f*tau_g.

The seven factors are torsions of specified homology exact sequences from SectionIII.2, with chosen bases. SectionII uses a field and a representation Z[H1(M)]->F; Euler structures track the topological ambiguity. TheoremII.1 is the based-complex multiplicativity formula including the torsion of the long exact homology sequence.

**Our application boundary.** This theorem permits nontrivial boundary patterns and hence is relevant to an interval cut out of a cover. It does not state that the correction has constant size, is a known unit, or can be acquired from only the two interval endpoints. The bases and maps in all seven sequences must be supplied and computed. Cutting a chain into two halves reduces the number of geometric pieces only if their interior data and correction have already been compressed. Counting T as one arithmetic operation would omit the central acquisition problem.

At native collisions twisted homology may change rank locally at one unknown prime. Field calculations can divide by a determinant that vanishes at that prime. Over R=Z/NZ, each chosen pivot or normalization therefore needs a paid unit test or a division-free determinant formulation. A proper failed pivot can factor N; a globally zero pivot requires continued exact handling, not an unsupported field specialization.

## 4. Two explicit “finite cover with boundary” matrix tests

These are elementary tests of concrete constructions, not literature impossibility claims.

**Open weighted path.** Model interval translation by an m-by-m weighted unilateral shift W, strictly upper triangular. W is nilpotent, so for the ordinary polynomial S(T)=T^J G(T+T^-1), with S(0)=1,

    det S(W)=1.

The reciprocal Laurent Delta(W) is undefined because W is not invertible. Thus replacing a cyclic deck transformation by an open shift does not automatically turn full-cover torsion into the desired partial product; it loses the q^i spectral points.

**Close the path with one boundary weight.** A weighted cyclic shift W_c has characteristic polynomial T^m-c, where c is the product of its edge weights. Its eigenvalues are a multiplicative coset of a full m-th-root-of-unity cycle. Therefore det S(W_c) is a genuine cyclic-type resultant, but its spectral points are not the partial orbit q,...,q^m unless q has the corresponding supplied short order. The native order bound deliberately excludes q^m=1 in the relevant window.

In contrast, Z_m=diag(q,...,q^m) gives

    det Delta(Z_m)=P_m

exactly, with no order assumption. Its dimension is m and its determinant is the original product. Writing it as a named diagonal operator does not acquire its m entries or its norm in soft-J. These tests isolate what a useful boundary condition must accomplish: preserve the truncated geometric spectrum without paying dimension m.

## 5. Precise future constructive interface

A substantive extension of one of these gluing theorems would suffice if it supplied the following **acquired boundary-compressed torsion construction**:

- Input: the explicit sparse2J Seifert matrix V, unit q, O(log N)-bit m, and the native order/normalization guarantees.
- Output: a finite based chain complex or colored cobordism descriptor, including every boundary homology map/basis needed for gluing, of soft-O(J) total encoded size. Its torsion or specified integral determinant coefficient must equal U_m*P_m with U_m a cheaply acquired certified unit.
- Computation: the descriptor's scalar coefficient must be obtainable in soft-O(J) bit operations, not merely represented by a dimension-m induced representation, a length-m colored word, or a degree-m clock polynomial.
- Composite-ring behavior: a division-free computation, or explicit unit-tested pivots with every saturated branch handled. It must remain valid exactly at the local collisions used by the native factor consumer.
- Boundary/prefix behavior: the same construction for chosen m must preserve the root's prefix zero-decision contract; there is no need to output all interval factors or the full H_m polynomial.

The genus1 shear is a concrete place to seek such an identity because it records the q-clock with constant topological boundary width. What remains missing is an efficient exact scalar torsion evaluation across the changing boundary characters. The three inspected primary results provide legal composition and its corrections; none supplies that evaluation or a continued-fraction reduction of the native partial geometric spectrum.
