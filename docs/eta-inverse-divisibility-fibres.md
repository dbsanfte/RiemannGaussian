# Sparse signed fibres from an outer-divisibility cut

This slice tests the repository-root
`RiemannGaussian_local_gap_signed_fibre_steer.md` on a concrete inverse
region. It begins from verified commit
`6daef5024abfb5261a58c9f0bc031a122ac5d5bd` (CI 34242858968).
The preceding [normalization and product-cut audit](eta-signed-inverse-energy.md)
already gives `W(K)=4*S(K)+O_rho(1)` and proves that a complete positive
product cutoff equals the full physical inverse.

The new result is an exact, cutoff-independent weighted coefficient
estimate for a region that cuts through product fibres. It does not give
the missing independent relative upper bound for `S` or a new zero exclusion.

## Actual selected region and coefficient energy

Let

\[
 H_T=\{(d,e):d,e\ge1,\ de\le T\},\qquad
 D_{T,q}=\{(d,e)\in H_T:q\mid d\},\qquad
 R_{T,q}=H_T\setminus D_{T,q}.
\]

These are `pairedEtaInverseOuterDivisible` and
`pairedEtaInverseOuterNondivisible`. Their coefficients remain the original
signed inner-divisor sums
`c_S(n)=sum_(de=n,(d,e) in S) mu(e)`.

For an arbitrary selected region, the compiled
`pairedEtaInverseRegionCoefficient_complement_add` retains the exact
identity `c_(H\S)(n)+c_S(n)=c_H(n)`.
`pairedEtaInverseRegionCoefficient_complement_eq_neg` specializes this
to exact anti-correlation on every included product `n!=1`.

For `1<=q<=T`, the map `(d,e) -> (q*d,e)` is a bijection from the divided
hyperbola `H_(T/q)` to `D_(T,q)`. It preserves the inner Möbius sign.
Complete fibre cancellation therefore gives

\[
 c_{D_{T,q}}(n)=\mathbf1_{n=q},\qquad
 c_{R_{T,q}}(n)=\mathbf1_{n=1}-\mathbf1_{n=q}.
\]

These identities are formalized as
`pairedEtaInverseRegionCoefficient_outerDivisible` and
`pairedEtaInverseRegionCoefficient_outerNondivisible`. The selected
coefficient identity holds even outside the original product range; the
complement identity is stated on `1<=n<=T`.

The terminal coefficient estimate is the exact equality

\[
 \sum_{n=1}^T(n+1)c_{R_{T,q}}(n)^2=q+3,
 \qquad 2\le q\le T.
\]

It is proved by
`pairedEtaInverseOuterNondivisible_weighted_coefficient_energy`.
For example, `q=2` gives the value `5` for every `T>=2`. The generic
weighted area cost is unnecessary for this actual family. This uses
classical Möbius inversion, not a new general Möbius cancellation theorem.

## Full moment and reflected quadratic identities

Write `A_z(n)=pairedEtaMomentDivisorAtom z k a M n`. Its physical cutoff
remains `M`, with divided cutoff `floor(M/n)` and translated center
`a-log n` inside the original completed atom. The compiled identities give

\[
 V_z(D_{T,q})=A_z(q),\qquad V_z(R_{T,q})=A_z(1)-A_z(q).
\]

They hold for every moment order and center. The exact complex carriers
precede all norm estimates.

At the original current's physical cutoff `M=2*(N+2)`, center `log(M+1)`,
and order zero, put `A_z=A_z(1)` and `B_z=A_z(q)`. The theorem
`pairedEtaCurrentFullInverseEnergy_eq_divisibility_split` retains, in each
reflected channel, the entire expression

\[
 |A_z-B_z|^2+|B_z|^2+
 2\Re\big((A_z-B_z)\overline{B_z}\big).
\]

The actual signed difference of the two channel expressions is weighted
by the original positive zeroth-energy coefficients and by `2*Delta_(N+1)`.
All complex phases and both mixed interactions survive. The expression
equals `|A_z|^2`, so reducing coefficient energy does not remove the full
physical source contribution.

## Consequence for the local-gap proposal

This slice does remove the generic area factor for a concrete family,
as requested by the steer. It does not establish a vanishing factor after
the complete reflected quadratic is restored. The product-one atom still
contains the entire physical prefix, so it cannot be treated as a fixed
cutoff-independent error.

Montgomery--Vaughan and the existing odd-heat transform control an
off-diagonal Hilbert form. The odd heat kernel is exactly zero on the
diagonal. A further exact relation to the normalized current must therefore
retain and control the source-bearing diagonal and all boundary terms.
The weighted coefficient equality alone supplies no such relation.

Any future local-gap estimate should use the actually occupied frequencies
after coefficient cancellation. It must also be compared against the full
signed expression above, before claiming a relative saving against `K^e`.
The main arithmetic inequality remains open.

## Verification

`EtaInverseDivisibilityFibres.lean` is imported by the root library.
Direct warning-as-error elaboration, the focused build (4327 jobs), full
build (9736 jobs), whole-project lint, and all 14 verbose root linters pass.
The nine selected terminal axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`. The compiled inventory reports
889 modules, 18919 declarations, 16272 theorems, no project axioms,
and no placeholder dependencies. The staged hook repeats the build,
lint, integrity, freshness, and whitespace gates; the exact commit must
also pass CI. The displayed normalized-current milestone is unchanged:
the new coefficient bound is auxiliary and does not advance the open
direction of the RH criterion.
