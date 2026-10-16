# Independent exact main-report review B

2026-10-16. Reviewer moving_carrier_attack_615. Verdict: PASS. I independently reviewed the main theorem and its compressed rectangle acquisition, scalar and matrix arguments. I did not author the main report. I authored its source-survival companion, so comments about that companion are a declared self-audit, not a second independent review of it. No source or reviewed report was changed.

## Exact target and prerequisites

- native-two-clock-obstruction.md: 19460 bytes, SHA-256 e6c98aabf00cd77fcb319b75850914cf601474b721826b20f91e31806bae0ee9.
- source-pins.json: 2016 bytes, SHA-256 9b3d96d5986fe968313b66c17a90a3d22c49dadfb5899c7af482978a61609811.

All seven prerequisite byte lengths and hashes were recomputed and match. The G15 stored gzip was also decompressed and its declared plain length/hash verified. These include the final source-survival companion 14019/f541f4a18e49d8ffe804c081c3ce33cc851350f126486dc553b87df32c330b09. Its own five source records, including both gzip raw/plain records, were verified during authorship; that is provenance/self-audit rather than an independent endorsement.

## 1. Paid composite-safe rectangle

The certificate is valid for arbitrary composite local orders on the stated all-semiprime prepared branch. The b=0 axis follows from D_g<d<local g order. For positive b, db-a is positive because D_g<d; its upper bound is dT+D_g<256m⁴<global order. Thus a globally saturated linear leaf cannot occur. Negative b reduces by reversing both signs, and a=0 is explicitly included in H. No local order input or prime-order substitution is used.

The linear preliminary implementation is valid, but the stated final cost is supported by the subsequent compressed algorithm. For h=2D_g+1, length t and block s=floor(sqrt(t/h)) when t>=h, the scaled product has degree hs. Product-tree construction costs soft O(hs+h). Its n=floor(t/s) geometric evaluations cost soft O(hs+n): the displayed binomial-exponent convolution identity uses only powers of a known unit, including inverse powers, not roots of unity, division by node differences, or inverses of 1-q^k. Unequal polynomial degree and point count simply give the sum of their lengths. Repeated geometric nodes are harmless. Horner evaluation of fewer than s tail factors costs O(hs). For t<h, s=1 gives cost soft O(h+t)=soft O(h), not an accidental h*t charge.

Consequently each interval product costs soft O(h+sqrt(ht)). A saturated root product can be localized by at most two child products at each level, retaining one saturated child when no proper factor is already found. The square-root costs form a geometric series, and h per level contributes only h log T. At the final b singleton, evaluations down the H root-product tree cost O(h) in summed child degrees. Either a proper gcd appears or the impossible global leaf would be reached. This proves the compressed soft O(h+sqrt(hT)) factor-or-unit-certificate clock. There is no rectangular output array, and no original J-by-L query oracle is hidden in this application: it uses the inherited generic degree-h/length-T product algorithm at its explicit degree-sensitive cost.

The storage and residue-bit claims are consistent with discarding interval arrays between levels and charging polynomial arithmetic via integer multiplication, with logarithmic size factors suppressed. Input exponents and the stated size bounds make the powering bookkeeping polylogarithmic.

## 2. Sparse finite-frequency principle

The certificate makes all g^v q^u in the advertised nonnegative rectangle distinct in EACH hidden field. A confluent Vandermonde on these frequencies, with polynomial ordinary-index degree D_k, is invertible for the first (D_k+1)(D_g+1)(T+1) samples. Hermite/Hasse interpolation only needs factorials through D_k to convert falling factorials to ordinary powers, hence characteristic>D_k is sufficient even if the total sample count exceeds the characteristic. A formally nonzero polynomial in the three variables therefore cannot vanish throughout that certified sample budget. The actual equality q=g^d is retained globally; only its occurrence inside the finite rectangle is excluded. No numerical multiplicative independence is claimed.

## 3. Direct transition theorem

Cross multiplication produces E=A(Q)S-R_0 with multidegree at most (D_k,D_g,J+D_q), exactly the certified rectangle and sample count. The regular denominator evaluations imply that S is formally nonzero. In the polynomial domain K[Z,G][Q], A(Q)S has Q-degree at least J, while R_0 has degree at most D_q<J, so the formal identity is impossible. This argument uses no division by U_k and is therefore valid on the complete collision-bearing canonical query after a successful screen. Neither primitive coefficient support nor local prime order is needed for this retained-clock theorem.

## 4. Prefix and matrix arguments

For prefixes, division by U_k is explicitly conditional on all U_n being nonzero. The ratio is exactly B_t(q^k), with B_t(Q)=prod_(i<t)A(q^iQ) of exact degree Jt. The cleared polynomial has Q-degree at most Jr+D_q. The original nominal range k=0,...,L-r is preserved, even if the highest formal coefficient occurs at a smaller shift or all its initial evaluations vanish. No regular-start sample deletion or imaginary extension of the equation range occurs.

Once grouped finite-frequency vanishing gives the formal identity, the largest nonzero P_t has Q-degree at least Jt, whereas all earlier summands have degree below Jt because D_q<J. The t=0-only case is also nonzero. This proves the claimed contradiction. Formal nonzeroness is a sufficient coefficient premise here precisely because the screen and sample budget eliminate spurious vanishing coefficient functions in this range.

The matrix scalarization is valid with common multidegrees. Clearing s transition denominators gives s+1 rows of multidegree at most s times each common degree. A maximal-rank minor and Cramer dependency give coefficient bounds s² times each degree; multiplying out the minors yields polynomial identities on all row coordinates, so no division by a minor after specialization is needed. Rank zero permits a constant dependency. The denominators need only be nonzero on actual transition windows. Singular matrices and advised initial states do not affect this existence argument. The scalar recurrence has the original nominal order s and original k<=L-s range. Separate entry denominators and affine coordinates are explicitly charged before applying the common-degree bounds.

## 5. Actual source and quantitative claims

The all-input application is correctly factor-or-certificate for transition values. It does not assume every prepared base has a prime local period or that the complete canonical cumulative sequence is zero-free. Hidden characteristics exceed the supplied local order margins, hence fixed/polylogarithmic ordinary-index degrees eventually fit.

The cumulative application is restricted to the ORIGINAL prime-period majority source and a private unit-row witness subset. The pinned density theorem counts BOTH fields and all current candidates, leaving m-o(m) labelled unit complete rows. Deduplication loses at most two tags per literal offset. Every individual residual is then a unit and all restricted prefixes are units, but finding the subset is not granted and collision coverage is not claimed for it.

The source-survival and novelty companion is my authored contribution: its role here is a declared dependency, independently reviewed by other agents. I checked the main's use against it. Fixed power envelopes r<=M^rho,D_g<=M^gamma,D_q<J have total alias-catalog loss soft O(M^(5.969+rho+gamma)); rho+gamma<.031 preserves the SAME original supply. Ordinary-index exponent kappa adds to the sample exponent 1+rho+gamma+kappa, with strict inequality below 2. The matrix s and all common degrees <=m^.005 give scalar degrees <=m^.015, loss5.989 and sample1.035 as stated. The compressed screen, unlike its linear preliminary implementation, has square-root term exponent (.015+1.005)/2=.510, so this power example genuinely fits soft O(m). This does not pay witness-subset acquisition or the original norm.

## 6. Provenance and limits

The comparison with old G15 is accurate: using beta as the single clock replaces A by A(G^d) of degree dJ, so the old dense prefix threshold cannot be reached at L=Theta(m²) for J=Theta(m),r>=1. G15 nevertheless already proves original-query same-clock degree rigidity and receives explicit credit. Earlier chirped three-frequency arguments are not the same coefficient contract as retaining both native geometric powers in the direct query. The inherited generic geometric-product primitive is explicitly credited; its new use is a small rectangle certificate, not a new general resultant algorithm.

The main report does not acquire long products, locators, diagonal values or witness leaves. It leaves arbitrary extra clocks, high-degree sparse circuits, nonlinear or selected-output constructions and direct factor acquisition outside its format. No arithmetic-operation lower bound, improved query exponent, new Lean declaration or all-input zero-free density result is claimed. I found no correction requiring mutation of the final target.
