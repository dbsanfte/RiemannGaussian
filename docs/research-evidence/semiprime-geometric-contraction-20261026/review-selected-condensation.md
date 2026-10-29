# Independent review of selected-condensation.md §§1–6

26 October 2026. **PASS: finite weights, two-axis cancellation, source normalization and cost are valid under the stated actual-gap guards.** Read the stable §§1–6; any subsequent Gosper continuation is separate from this review.

## Exact identities and amplitudes

The shifted barycentric weights are units because their numerators are unit grid nodes and every derivative factor is a screened node gap. Lagrange coefficient extraction gives sum x_u^(b-1+k)/B'(x_u)=h_k(grid), hence both Gaussian moment factors and recurrence (2), with no missing q-power. One useful independent check is

    alpha_(u-1)/alpha_u=(q^u-1)/(q^u-q^b),

and the analogous beta ratio. Prefix sums A_u,C_v need not be units and are never inverted. Their terminal value is one, so the four terms in the summation-by-parts formula have the displayed signs and include the entire last row and column, corner counted once. If b or c is one, the residual disappears exactly as stated.

For Pearson (6), collect an interior coefficient at U=q^u,V=Q^v. Put r=(U-1)/(U-q^b), s=(V-1)/(V-Q^c). Its identity is precisely

    1-UV=r(q^b-UV)+s(Q^c-UV)+rs(UV-q^b Q^c).

Clearing denominators proves it directly. At the edges the same cleared identity cancels outside-grid terms. Thus its rational version is a finite weight identity, not an unjustified use of finitely many moments to determine every rational value. Specializing Q=q^b merges some locations but does not change the cleared identity.

The four-reciprocal mixed difference has numerator b0*c0*(a+d)-a*d*(b0+c0), with the displayed signs and delta-degree at most two. For a polynomial numerator p, its four terms are correctly assigned and its t-degree is at most4J-1. The source pair F'/(F+delta), H_w/(F+delta) has good residues alpha*beta*F'(theta) and w_hit times that quantity; the F' is essential. Unique row-clock incidence makes F'(theta) nonzero even if unrelated nonhit rows repeat. Pairing 1/(F+delta) with H_w/(F+delta) would indeed give the wrong extra derivative.

At an interior pole, the four adjacent mixed-difference weights telescope to (A_u-A_(u-1))(C_v-C_(v-1))=alpha_u beta_v. Multiplying by F'(theta) confirms the correction retains exactly the nonzero selected amplitude. There is no pole cancellation licensed merely by its unit boundaries.

## Guards, costs and scope

Moment denominators through the requested short precision are explicit actual q-gaps, including Q^(k+1)=q^(b(k+1)). The source correctly requires an actual integer-footprint check and fallback; this is important because bJ can exceed J substantially. If using the original-base doubling proof for the retuned parity base, check TWICE the displayed footprint against16H, or derive the equivalent actual-base unit certificate from its inherited odd order. The conservative retuning makes the doubled footprint safe for sufficiently large K; this must not be replaced by an unquantified all-precision claim.

Both GP polynomials, derivative MPE, batch inversion of true unit weights and boundary numerator evaluations cost soft(J+b+c). Boundary F values are actual clock evaluations; nonunits localize to actual row labels, with the once-only original soft-K extractor separately charged. The boundary-unit continuation is legitimate and does not assume the true hit was interior beforehand. No normalform evaluation, determinant, rank-J algebra operation or c*b value array is hidden in the stated short input acquisition. The remaining four-denominator rational functional is explicitly unpaid, so the report claims no selected norm algorithm or general lower bound.

## Executed coefficient-strip continuation test

The paid formal strips can precondition the numerator, but do not erase this correction's pole. This can be checked exactly without a degree/rank heuristic. For one source p(t)/(F(t)+delta), acquire its first M formal coefficients P_M(t) at zero using the unit F(0)+delta. Then polynomial division gives the ACTUAL finite identity

    p/(F+delta)=P_M+t^M E_M/(F+delta),
    E_M=[p-(F+delta)P_M]/t^M, deg E_M<J.

Both P_M and E_M are acquired in soft(J+M), using the same scalar formal arithmetic as qdifference-contraction. At any physical hit theta, with theta a unit,

    theta^M E_M(theta)|_(delta=0)=p(theta).

Thus the polynomial strip has zero delta residue, while the remaining rational term retains the entire source residue pointwise. Applying this identity separately at t,qt,Qt,qQt in the mixed correction preserves the same four-pole coefficient (5). It is not permissible to discard the remainder after summing its acquired strip against the short moments.

The reciprocal-end strip gives the same conclusion: its coefficients are regular in delta because the leading coefficient of F is a unit, and its negative powers of t are regular at every unit grid node. Subtracting ANY finite combination of those paid zero- and infinity-strips therefore leaves the full delta residue in the residual rational functional. This is a specific exact test of using the newly paid strips for this correction, not a proof that no fused use of their coefficients can help.

There is a limited lawful simplification: after a fixed strip subtraction, one may drop the compensating theta^M when taking a RATIO of the TWO transformed source residues, since the common theta^-M is a good-field unit. The transformed numerator pair is E_M(F') and E_M(H_w), and its hit ratio is still w_hit. This gives an initialized short preconditioned pair, not its acquisition. The denominator and its selected evaluation remain; no sparsity or clock cancellation of those transformed numerator coefficients is forced by the present native hypotheses.

Uniform doubled-gap refinement independently checked: for the retained retuned bound h<=sqrt(2)H/4+9 and K>=54, b=ceil(sqrt h)<=K. For every k<=4J, J<=K/3,

    b(c+k+1)<=h+4bJ+b
      <=(sqrt(2)/4+4/3)H+K+9<2H,
    b+k+1<=7K/3+1<2H.

Thus twice the FULL moment footprint, including the recurrence's k+1 factor, is <4H<16H. The original-base unit factorization certifies all moment inverses without a sufficiently-large qualifier. This is the requested precise guard for the amended source paragraph.

Final reread: the source §1 now contains this explicit K>=54 full-footprint bound and the doubled original-base certificate. The requested moment guard correction is resolved. **Final disposition for §§1–6 and their stated target: PASS, no outstanding correction.** Later §7 is separately authored and not included in this review's scope.
