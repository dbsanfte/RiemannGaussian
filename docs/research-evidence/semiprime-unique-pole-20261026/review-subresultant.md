# Independent review: selected companion cofactors

26 October 2026. Paper-only audit of `selected-subresultant.md`; no tests or frozen-file edits. Sections 1–5 PASS. Final scalar-closure addendum, if appended, is reviewed in the final disposition below.

The chosen COLUMN companion is multiplication by X in the polynomial basis. At the good field, unique whole-bin intersection makes theta a simple factor and W_h invertible on the remaining algebra. This gives rank exactly J−1 even when D repeats elsewhere. Evaluation of e0=1 at theta is one, so adj(W_h(C))*e0 is nonzero and is lambda*D/(X−theta), lambda!=0. No random projection or semisimplicity of the other factor is required.

The two top coefficients have the stated signs: D/(X−theta) has top coefficient one and next coefficient d_(J−1)+theta. Thus A=lambda and B=d_(J−1)A−Vnext=−lambda*theta. These are projectively equivalent to the first subresultant in the good field, not numerical equality with a canonical normalization over the whole composite ring. The J=1 exception is handled separately.

For Q_a=(D(X)−D(a))/(X−a), (C−aI)Q_a(C)=−D(a)I and det(C−aI)=(-1)^J D(a). Hence adj(C−aI)=(-1)^(J+1)Q_a(C), with the report's sign. Adjugate multiplicativity holds as a universal polynomial identity, so the division-free recurrence remains valid at singular steps. It actually emits/acquires the full evolving vector at soft J per step, giving soft Jh, not an implicitly free adjugate.

Equation (6)'s top coefficient is v(a); its next coefficient is (a+d_(J−1))*v(a)−D(a)*[X^(J−1)]v. The formula is correct. Its proof must be understood as a UNIVERSAL polynomial identity before specialization: one may establish it over indeterminate a and then specialize. It is not legal numerically to infer the first equality merely by cancelling a potentially zero D(a). The universal proof in the report avoids that division; no algorithmic correction is needed.

With coefficient rows corresponding to powers of X, B0 for (D(X)−D(Y))/(X−Y) is anti-triangular with anti-diagonal one. Thus Bez(D,R)=R(C)B0=B0 R(C^t) has the correct column orientation. Its displacement input still needs R=W_h mod D, or W_h(C)e0. A small structured matrix is not an acquired generator list. The source-specific finite identities are proved directly and do not import arbitrary field pivots.

At the final good field A and D′(theta) are nonzero, so norm tests produce a proper factor or a genuine global unit. The weighted cofactor ratio then returns the actual tag. Wrong-bin saturated pivots are declined, and candidate factors/tags are checked before later bins continue. No empty gate is needed on the promised correct WHOLE bin. Arbitrary earlier top-coordinate zeros are not licensed annihilators, as the report correctly says.

All actual Q_a coefficients, monic reductions and unit base powers are charged. The old guarded half-GCD fallback only applies after its actual clock remainder is supplied at soft(J+sqrt(Jh)); no source theorem is used as an implicit-clock oracle. No substantive correction found in §§1–5.

## Final stable §6 scalar-closure review

Read the stable scalar-closure addendum after author notification. **Final PASS.** The Newton product rule for D*(1/D)=1 gives D(a_n)F_n+sum_(k>=1)D[a_(n-k),...,a_n]F_(n-k)=0. Multiplying by tau_n produces exactly the product range n−k+1 through n−1 in (10), including the empty k=1 range. E0=1 and eta_n=(-1)^(Jn)E_n have the stated signs. The consecutive-geometric divided difference of X^r is a_n^(r-k)q^(−k(r-k))*[r choose k]_q, so the formula for B_k and B_J=1 are correct.

The top-two-coordinate identity yields theta=a_(h−1)+D(a_(h−1))*E_(h−2)/E_(h−1), with a PLUS sign: the companion-adjugate sign cancels the consecutive E sign to minus in the intermediate ratio. The final denominator is nonzero at the promised good field because it is a fixed nonzero sign times the final top adjugate coefficient. No earlier E_n is inverted.

The actual first-J unit prefix, geometric Newton conversion and tau products initialize E0,...,E_(J−1) in soft J. Geometric node differences with gaps<=J are certified units. An acquired nonunit clock value is processed by the stated bounded native factor/tag branches, not inverted. Each later full B vector can be acquired by fast geometric Newton conversion in soft J; its rolling products and recurrence dot product cost O(J), not J², and all state has O(J) entries. Thus the scalar algorithm really is initialized with soft-J setup and soft-J work per clock step. It does not assume a full W_h remainder as input.

The nonzero highest-lag COEFFICIENT before the hit is correctly distinguished from a theorem of minimal recurrence order: the corresponding state value may vanish, and a different nonlinear identity is not excluded. The report's tail test therefore has the claimed narrow scope. The retained completion bounds Jh and J+sqrt(Jh), and the absence of a soft-K selected elimination algorithm, are reported honestly. No substantive correction is required.
