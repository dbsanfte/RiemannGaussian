# Independent character-resultant and exceptional-support review

2026-10-24. PASS for corrected `character-resultant.md`, SHA256
`87c7b82b0bcc516f63d8ff4f1f81f2214f1e8c4e3e23083072470d7c2a672fb1`.
The earlier draft omitted the exchange sign in its exact resultant
identity. The author corrected that sign and the proof before this PASS;
the squared-character support identity was unaffected.

For C=A-B with A,B monic of degree n, and
D=c^2*B-(c*X+h)*C with generic degrees n-1,n-2, successive resultant
exchanges give

    Res(A,B)=(-1)^n Res(B,C),
    Res(B,C)=c^2 Res(C,D/c^2),
    Res(C,D)=(-1)^n c^(2n-4) Res(A,B).

The corrected formula uses fixed-degree Sylvester polynomials at degree
drops, as required for specialization of its universal identity. It is
not an instruction to divide by c after specialization. For n>=3,
squaring the Jacobi symbols removes the unit sign but leaves the zero
mask of c. Boolean division at mask zero would lose information, so
the reported square cancellation is correctly guarded.

The first linear and second quartic polynomials agree with the reviewed
tensor Schur calculation. Their leading coefficients are units by the
short q-difference certificates. They therefore have at most one and
four roots, respectively, on either local outer grid. No hypothesis
about generic native coefficients is needed for these bounds.

The new support procedure is fully initialized. Evaluating either
constant-degree polynomial at all t acquired nodes and computing the
individual gcds costs soft t. If no proper gcd is found, each value is
either unit or zero modulo N; hence every retained bad node is PUBLIC
and globally bad. A saturated PRODUCT alone would not justify this
conclusion; the report explicitly uses the individual gcds.

At each bad node, the original inner slice consists of n evaluations
of the supplied degree-n F. Monic MPE and multiplication cost soft n.
Any nonunit slice is localized through its acquired values and the
original row product tree. The resulting index a+s*b is in the actual
original rectangle, so a saturated original leaf has the retained
bounded-beta decoder. There is no decoder for an auxiliary pivot zero
in this argument, and none is invoked.

If the original slice is unit, its acquired scalar is retained and
the node can be removed from the outer modulus by exact monic division.
The remaining known nodes retain unit differences. The processed pivot
is now a unit in their CRT algebra; interpolation of inverse values,
when needed, also costs soft t. Across the two stages there are at most
five removed nodes, even without deduplicating the bad sets in advance.
Thus scans, actual slice checks, removals, inversions and scalar factors
cost soft(n+t) in total. Small or empty remaining grids are handled by
their acquired slice products, including the empty-product convention.

Removing a unit slice cannot remove the promised original nonunit
witness. More precisely the original product equals the product of
the retained unit slice factors times the product on the remaining
nodes. This is the support-preserving invariant behind the procedure.
The two stage cleanup is consequently stronger than the former immediate
fallback on saturated auxiliary norms, while remaining conditional only
on the already acquired native setup.

No later pivot is supplied by this proof. Its public degree bound k^2
does not acquire its mixed coefficients or endpoint values, and repeating
full scans and slice evaluations over growing stages retains the stated
nt cost. The report explicitly charges these costs and retains the
existing soft(J+sqrt(JL)) complete-query fallback. Known-zero full
character output, formal q-hook units and reciprocity identities are
not promoted to a restriction evaluator. This audit checks the algebra
and algorithm; primary-source applicability is additionally documented
by the author's cached source inspections, not an exhaustive literature
claim. No whole-family exponent gain is established.
