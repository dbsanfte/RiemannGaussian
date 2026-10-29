# Independent review of projective-closure.md

26 October 2026. Scoped symbolic review, no tests or repository edits.

**PASS on the finite algebra and claimed scope, with two integration corrections requested below.**

The conjugation Psi diag(c,1) Psi^-1 gives exactly T_c=[[c,0],[kappa(1-c),1]], with determinant c a certified unit. Its commuting composition, automorphy cocycle, and homogeneous Theta(y) transformation check directly over the finite jet ring. J_c has constant 1; D_c has constant c. No comparison value is inverted. The comparison transformation (4) has the stated inverse argument x/D_c(x) and prefactor D_c/J_c, with no missing scalar. Ignoring acquired formal unit products for a zero predicate is legitimate; for the normalized hit polynomial their constant scalar cancels through the actual first-slice normalization.

The canonical carry sign is correct: y(v+w)=q^(-cplus)y(v)y(w). Formula (3) inserts the actual tau, rather than treating canonical rows as an unwrapped character. The HNF generators and their scalar exponents agree with the authoritative colour construction. The small group action does not remove finite support/deletion restrictions or identify its endpoint readout with the product of comparison sections.

The ordinary-clock matrices S_d are correctly distinguished from conjugated T_d. Both lines of (5) have the correct orientation. **Clarity correction:** at c=d=q the lower-left entry of TS-ST is -kappa(q-1)^2, whereas that of T S T^-1 S^-1 is -kappa(q-1)^2/q^2. The phrase “first mixed defect” should explicitly name the former. Both are genuinely first order in delta Y because q-1 and q are native units.

The two-sided repair (6) is exact. At an actual local hit x=y its comparison vanishes identically as a formal delta series, so it preserves the zero predicate while destroying the nonzero Hasse slice. The one-sided weighting and its Pochhammer (7) are correct, including q^-L and base q^-1. The automorphy cocycle telescopes only formal unit ratios; it supplies none of this singular comparison amplitude. No extra hidden-order or roughness assumption enters.

**Cost correction:** section 6 should use triangular rank Theta((s+1)^2) and cost soft((s+1)^2 C), C=J+sqrt(Jh), including s=0. Moreover it should not leave that naive execution as the best current full-output bound. The independently derived [singular-recurrence.md](singular-recurrence.md) gives the all-hit identity

    e_j=-y_j A^-1 [delta^(s-1)] partial P(delta;y)/partial y_j,

and reverse differentiation of the actual monic scalar circuit over R[delta]/delta^(s+1). This acquires the normalized reciprocal gcd or a factor in soft((s+1)C+T_ext), without the triangular Y jet. The ring proof uses only addition, multiplication and certified unit inverses, not an unexamined field-only differentiation theorem. The alternative row-restriction algorithm acquires the full hit mask or a factor in soft(J+sqrt(max(1,t)Jh)+T_ext), t the union hit-row count. Both are full-output overhead refinements; one nonunit path already factors at the OLD C bound, so neither is complete-query exponent progress.

The original-root MPE/one-row consumer and once-only extractor charges are correctly scoped. Equal local hit counts permit global-unit normalization; unequal counts yield a proper gcd. A saturated row need not have a common local clock index. All new additive group-word zeros remain excluded from this decoder unless independently assigned a nonzero integer beta label.

After those small text/cost updates, the report accurately gives an exact projective closure with an unacquired scalar readout, not a faster native query or a general impossibility claim.

## Final disposition and section 7 review

The author corrected the precision-zero rank/cost, distinguished TS-ST from the normalized group commutator, and incorporated the improved univariate and output-sensitive companion algorithms with their no-factoring-gain scope. The earlier requested corrections are resolved.

Read the new section 7. Equations (9)–(11) are exact: substituting the scaled row/clock/mark parameters leaves both terms (1-delta)y/x and delta Y y unchanged as required. In particular the carry y=q^-tau ytilde sends the clock to q^tau x and the marker to q^-tau Y, preserving Yx. The multipliers commute as a parameter torus; this is stronger than fixed-Y projective-position transport, and does not invalidate the fixed-Y commutator calculation.

The endpoint orientation in (12) is correct. P_(y/q)(delta,qY) contains precisely the original leaf indices 1,...,h, while P_y contains 0,...,h-1. Multiplication by the excluded endpoint on the left and included endpoint on the right gives the same full list 0,...,h, with no inversion. An interior hit at (y,x_i) maps to (y/q,x_i/q), and its complete marked factor delta(1-Yx_i) equals delta(1-(qY)(x_i/q)). Hence the cancelled factor includes its entire marked divisor, not just its zeroth-order zero. Hasse extraction cannot restore this missing amplitude from endpoint data alone.

The updated text correctly separates cheap parameter covariance from acquisition of the leading slice, retains finite endpoints/carry/source obligations and does not assert a general obstruction. Final review PASS.
