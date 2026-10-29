# A covered parity mask for the long collision query

26 October 2026. **An amended native row family has a public parity mask that retains its unique good collision.** The mask is acquired in soft K and permits one common q² clock. Coverage enlarges the original horizon by about sqrt(2), while parity selection halves it. This improves the leading horizon bound by a constant; the completed acquisition bound remains soft K^(5/4), and the all-semiprime soft-N^(1/6) goal remains open.

The results below are reviewed paper derivations under the existing preparation contracts. The constructor checks public arithmetic and support metadata; it does not implement group preparation or certify a factoring rate.

## An arithmetic source for a collision bit

Keep K=2*3^e, H=K² and N=RS with odd factors. For each public unit colour r modulo K, replace the old coefficient lattice by

    a*r*(r+K) = c*N mod 2K.

This lattice has determinant 2K. Its condition is precisely the old stationary congruence modulo K together with a+cN=0 modulo 4. Weighted Gauss reduction therefore still supplies a witness for every factor colour, with a sqrt(2) increase in the coefficient norm bound. This is a covered construction, rather than deletion of rows from the previous cover.

The canonical phase ell is divisible by 4. Every actual good hit obeys

    ell+aR+cS = H*i.

Since an odd R has R^(-1)=R modulo 8, S=NR modulo 8. Thus

    i = (ell+a+cN)/4 mod 2.

This bit depends only on the acquired row data. It is the same for every colour in that row's support. It does not reveal which row hits, and is not an acquired global phase of the old family. Its useful consequence is that every row can discard its impossible clock parity before the numerical query.

For normalized indices I=i+M0, put r_j=M0+(ell+a+cN)/4 modulo 2. Replacing T_j by T_j*q^(-r_j) and q by q² retains exactly the original indices r_j+2s. All rows share that new base.

See [native-phase.md](native-phase.md) for the arithmetic proof and [parity-cover-audit.md](parity-cover-audit.md) for the complete bounds and support selection.

## Coverage and uniform-clock integration

Complete the enlarged weighted ellipse, retain its parity condition, and include only its eligible shortest axes ±(2K,0), ±(0,2K). The complete catalogue has fewer than 44K rows. The old ±K axes do not satisfy the new condition.

The pure conductor still forces g²<K for every nonaxis content g, despite the enlarged bound |ac|<=2K/sqrt(3). The high-direction determinant bound remains below 3K. These two facts preserve the native support partition and its unique good collision, with at most phi(K)=K/3 selected rows.

The two shortened row lengths differ by one. A paid endpoint gate either factors or certifies the extra endpoint of each shorter row as a global unit. Padding with those units gives a literal common clock of length L=M0+1 and the acquired short polynomial D*(X)=product_j(X-T_j*q^(-r_j)). The previous q-Newton, pole-pair and first-subresultant consumers then apply with their existing norm gates. The audit includes the explicit horizon and exponent bounds; no unclassified endpoint is cancelled or inverted.

The [constructor](check_parity_cover.py) acquires the public partition, per-row phases, shifted exponents and clipped lengths. Its numerical group values and optional padding gates remain obligations of the inherited query implementation. Three structural fixtures check the arithmetic independently of the sparse selection: 11,088 direct support tests, 3,204 selected-support tests and 608 parity-lift tests passed. These diagnostics are not the uniform coverage proof.

## Why this particular mechanism does not provide all the needed bits

The full-fibre criterion is exact. Fix a support r modulo K and require the signed clock phase to be constant modulo b=2^t for every integer lift R=r+Ks. This happens exactly when

    b divides 2a,
    cN = a*r*(r+K) mod Kb.

For b>=2, these conditions force (a,c)=(b/2)*(a',c'), where (a',c') belongs to the determinant-2K parity lattice above. The resulting coefficient and clock growth cancels the additional thinning. This confines the present construction to a constant gain. It does not rule out a selector using information specific to actual factors, or a collective query that processes many phases together.

## Smaller response targets and actual cancellations

The [alternating-residue calculation](phase-recurrence.md) asks for one scalar:

    Res_delta sum_(i<h) (-1)^i/(D(q^i)+delta) = (-1)^I

at a unique good hit. Actual coordinate and ±1 gcd checks validate that bit. A fully initialized paired transfer has off-diagonal entry D(qX)-D(X): its delta terms cancel. The polynomial H(X)=sum d_r X^r/(1+q^r) is also acquired in soft J and satisfies H(q²X)-H(X)=D(qX)-D(X). The remaining reciprocal expression retains a moving denominator offset, so the executed algorithm still costs soft(J+sqrt(Jh)). The [independent review](review-phase-recurrence.md) checks its signs, finite endpoints and actual unit guards.

The [knot character calculation](knot-phase.md) supplies another exact source. If Bq is the finite q-Euler series, applying the same inverse operator to H_zeta=Bq(z)/Bq(zeta*z) multiplies its unique pole by zeta^I. Constant-rank characters have paid short input, and a supplied final response can be decoded within the budget. Acquiring that long response is still open. The [review](review-knot-phase.md) checks the finite identity and coordinate-only decoder; the cyclic-dilogarithm source is used with its published phase correction.

The [finite symmetric-character probe](symmetric-character.md) gives the exact relation C^-(z)=H(z)C^+(-z), with H=Bq(z)/Bq(-z), and a legal reciprocal rebuild that folds the query onto trace-clock nodes q^i+q^(-i). Its [review](review-symmetric-character.md) verifies the finite tail, regularizer and source matching. A terminating q-Dixon identity contracts one reciprocal quadratic to a paired q-factorial, but that remaining product is still long. The tested Schur-Q cancellation removes the needed collision divisor along with the other factors. Neither contraction supplies a faster selected residue.

The next required gain is more phase restriction without proportional clock growth, or a faster collective evaluation of these specified responses. The public parity mask is now supplied; it does not supply those remaining operations.

The inherited contracts are the [unique weighted cover](../semiprime-unique-weighted-20261026/README.md), [unique-pole readout](../semiprime-unique-pole-20261026/README.md), and [coupled clock sections](../semiprime-scalar-acceleration-20261026/coupled-section.md). Their numerical group preparation and mixed-relation decoders remain prerequisites.
