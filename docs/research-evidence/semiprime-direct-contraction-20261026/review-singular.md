# Independent review of singular-solve.md

26 October 2026. Paper-only algebra/source/ring-guard review. No repository edits or tests. **PASS for the displayed identities and scoped fallback; one wording clarification is advisable in §3.**

## Laurent mask and fallback

The separated evaluation algebra is a product of copies of the native étale coefficient algebra. At each field component and row, put a=1-y_j q^{-i} and b_j=b(y_j). The certified unit b_j makes (a+delta b_j)^{-1} regular at zero when a!=0 and exactly delta^{-1}b_j^{-1} when a=0. The physical-clock difference guard gives at most one zero per row in each field component. Consequently b times the constant coefficient of delta*S is exactly the 0/1 clock-membership idempotent. This is legitimate in the componentwise Laurent algebra, even though a mixed-component summand need not have a globally unit leading coefficient. No ordinary unit-start Newton inversion has thereby been acquired.

Traces in (3) are therefore hit counts and weighted tag sums; at the good component they are precisely (1,w_hit). Multiple other-component hits cause no higher pole. The fact that these amplitudes are normalized is an output-specification statement, not an initialized extraction algorithm.

The stated old-cost fallback is valid. For each acquired R_j=G_h(y_j), a proper norm gcd factors. If its norm gcd is saturated, coordinate gcds either factor or certify that R_j is globally zero; if the norm gcd is one, R_j is a unit. At the good nonsplit component a nonhit row has nonzero norm, so a saturated norm cannot silently represent a good-component nonzero row. A norm that is saturated only because another split component vanishes is resolved by the coordinate step. Thus on the no-factor continuation each row is indeed globally unit or globally zero, giving interpolable flags. All row classifications cost soft J after the old shared-product evaluation. The saturated one-row tag route is a separate permitted fallback, not an arbitrary additive-zero decoder.

## Normalized system and rational tail

At the good unique-hit field, (1-y_j q^{-i})Z_{j,i}=1-s forces s=1, all nonhit entries zero and the sole hit entry one. The logarithmic-derivative identity (4) has the correct minus sign and factor z^{-1}. It remains a finite q-Cauchy tail whose singular residue is unpaid. The paired polynomial cancellation E_A/F_B=R_B and E_A/(F_A F_B)=R_B/F_A are correct symbolic identities; neither licenses numerical inversion at an untested clock node.

Suggested clarification: the sentence “This is exactly the singular mask (2) in another basis” should explicitly say **at the good unique-hit field**. Globally, the displayed normalized system does not select a unique distribution if another component has multiple hits, whereas (2) selects a per-row idempotent. The report's preceding good-field qualifier makes its intended use sound, but the two systems should not be identified as globally equal operators.

## Companion orientation and exact determinant

For the column companion of multiplication by X, A e_r=e_{r+1} for r<J-1 and its last column is -f. With D=diag(q^r), DA-qAD has only its last column nonzero, equal to u_r=(q^J-q^r)f_r. The orientation and sign in §4 are correct. Since f_0 is a unit and q^J-1 is a supplied unit, this is a genuine rank-one pair, not merely rank at most one.

The source numerator is (D-xI)(A-zI)-u e_last^t; the source denominator is (A-zI)(D-xI). Their determinants have the same unperturbed value. The rank-one formula thus gives

    BA=1-e_last^t(A-zI)^{-1}(D-xI)^{-1}u.

The companion identity e_last^t(A-zI)^{-1}w=-w(z)/F(z) gives

    BA=1+sum_r[(q^J-q^r)f_r/(q^r-x)]z^r/F(z),

which simplifies exactly to (5). In particular neither the sign nor the placement of A,D is reversed. The coefficientwise identity (6) follows immediately; its leading coefficient is also correct.

At x=q^h, all q^r-q^h, r<J, have exponent differences 1<=h-r<=h and are certified units. Computing T_x(F), and evaluating this monic degree-J polynomial at all row roots, costs soft J. The quotient by F(z) is only asserted on its unit-denominator locus. Its residue at every row root is not a clock-membership certificate, and no new scalar zero gets an automatic original-annihilator decoder.

## Primary-source scope and disposition

I checked Gekhtman–Kasman, [math-ph/0408038, equations (10)–(11) and Theorem 2.1](https://arxiv.org/html/math-ph/0408038). Equation (11) has exactly the displayed numerator/denominator for X_source=D, Z_source=A and rank(XZ-qZX)=1. Theorem 2.1 assumes complex full-rank rectangular data and a nondegenerate initial determinant; it supplies an integrable tau-function construction, not a composite-ring singular-solve complexity theorem. The report correctly uses only the directly proved finite determinant identity over the native ring, and does not transfer the analytic background factor or formal hierarchy into an arithmetic algorithm.

Accept the componentwise mask, factor-or-global-classification fallback, rank-one orientation and exact BA core. No soft-K residue/locator acquisition follows. Apart from the local/global wording clarification above, no correction to the formulas is needed.

## Applied disposition

The primary agent applied the advised good-unique-hit qualification to singular-solve.md before archiving. The multiple-hit global distinction is now explicit.
