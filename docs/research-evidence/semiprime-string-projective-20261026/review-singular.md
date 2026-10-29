# Independent review: singular recurrence and full hit masks

26 October2026. Bounded paper audit of the actual formulas and algorithms; no tests or repository edits. **Scoped PASS.** The linear-precision gradient method and the stronger output-sensitive restriction method are genuinely initialized, and neither is overclaimed as a factoring-rate gain.

## Indicator and degree promises

For a hit row j, its unique hit factor has derivative constant -1/y_j and all other hit factors contribute delta. Thus [delta^(d-1)]partial P/partial y_j=-A/y_j at the corresponding local field; for a nonhit row, every differentiated summand retains all d hit factors and the coefficient is0. This proves e_j=-y_j A^-1 partial a_(d-1)/partial y_j, with the sign, index and scaling exactly as printed. Treating y_j as independent inputs, q fixed, is essential and correctly stated. The numerical zero a_(d-1)=0 is not differentiated as a constant function.

The first nonzero constant-Y coefficient has a proper gcd when local hit orders differ, and is a unit when they agree. The case d=0 is valid for restrictions. Mixed e_j gives a proper gcd; otherwise e_j is0 or1 globally and the selected row factors give the reciprocal monic gcd in both fields. Different clock indices at the two primes do not change that row-factor identity. The hit-count bound uses s_p<=h<p, not an unsupported soft-O bound J<p or a factorial normalization.

## Explicit monic circuit and ring reverse pass

The block B_b(T)=product_(t<b)(1-q^(-L-t)T) evaluated at(1-delta)y_j q^(-vb) gives exactly the native factors for clock positions vb,...,vb+b-1. The analogous tail covers all remaining indices once. Building degree-b B_b, evaluating at Ja points and multiplying their values costs soft(J+b+Jh/b), with b=min(h,ceil sqrt(Jh)); clipping at h retains the bound soft(J+sqrt(Jh)). Repeated points and zeros are lawful under MONIC subproduct/remainder trees; no node-difference inverse is introduced.

Over R[delta]/delta^(d+1), multiplication costs soft(d+1) base operations. Reverse addition/multiplication and certified-unit inverse gates have the stated commutative-ring derivatives. Expanding the actual arithmetic subroutines into such gates is legitimate; no numerical branch, integer-factor extraction or bit-level multiplication implementation is differentiated. Fast convolution must use an actual arithmetic implementation with certified constant-unit divisions as stated (the odd base ring supplies the usual2-unit route); monic reversal series have constant1. The proof does not require inverses of arbitrary integers through J.

Seeding the R[delta]-valued scalar output adjoint at1 computes the derivative polynomial partial P/partial y_j itself; extracting its delta^(d-1) coefficient gives the requested derivative of a_(d-1). Truncation is independent of y and therefore commutes with differentiation. All J output derivatives cost O(Jd) coefficients, already within the displayed d*C(J,h) bound. Precision doubling and one final reverse pass give soft((d+1)(J+sqrt(Jh))+T_ext). It improves the naive triangular delta,Y-jet completion, not the base scalar acquisition scale.

## Output-sensitive restriction alternative

At depth ell the number of tested children is O(min(2^ell,s)), since disjoint retained nodes must each contain an original hit. Summing their degree terms costs soft J, and summing their square-root terms costs soft sqrt(max(1,s)Jh). The max(1,s) correctly preserves the mandatory root test when no row hits. Source partitioning and polynomial acquisition are included; s need not be known in advance.

If no proper factor is returned, every final retained row hits both components and each discarded row hits neither. Their product gives the full reciprocal gcd; it does not assume equal clock indices. If memberships differ, some restriction exposes a proper gcd before completion. The worst dense-output bound is correctly soft J sqrt h, and a single nonunit path already factors at soft(J+sqrt(Jh)+T_ext). Listing all hits is unnecessary for that factoring objective.

The exact terminating extractor charge remains T_ext=soft O(N^(31/192)), once before termination. The cited q-holonomic and leading-factor desingularization statements are used only as scoped baseline/comparison: a monic forward recurrence has no removable leading singular factor, and no claimed theorem supplies its missing faster endpoint. No complete-query exponent improvement, general lower bound or new scalar acquisition is inferred.
