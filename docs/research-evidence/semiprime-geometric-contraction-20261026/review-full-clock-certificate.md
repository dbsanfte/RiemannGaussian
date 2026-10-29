# Root review: full-clock Pearson certificate and source guards

26 October 2026. Independent review of selected-condensation.md §7,
including the corrected endpoint. Final PASS for the specified finite
ansatz; no selected-query algorithm or general obstruction follows.

The full-clock weights x_i^(h-1)/W'(x_i) give the displayed complete
homogeneous moments. Their adjacent ratio verifies the finite Pearson
identity, including its vanishing endpoint coefficients. Short moment
acquisition uses actual q gaps; on the rooted parity bank the original
screen must cover twice each required exponent. The retained conservative
margin covers the stated O(J) precision after its explicit footprint check.
The full h-entry weight vector is not claimed acquired.

An initial draft used F(q^(h-1)) to invert q^h-qX modulo D(qX). That was
incorrect. The revised report gates F(q^h), since substituting
X=q^(h-1) into D(qX) gives D(q^h). The correction is essential to the
certificate argument, not a cosmetic endpoint change.

The revised extra leaf is legitimate. For padded h=M0+1 and actual
q=(pi^H')², its relation is

    (ell'+H'(M0-phase-2h), A+CN).

It has signed physical index M0+2+phase, at most M0+3. The second label
is nonzero: for nonaxis C!=0 the ellipse product bound gives
|A|<=2K'/sqrt(3)<N; for C=0 the retained horizontal axis is nonzero.
The actual labels have O(log N) bits, so the original mixed-label decoder
handles a saturated nonunit after localization in any bin. In a correct
bin the earlier strict index and order margin also exclude an accidental
alias at this endpoint. The explicitly enlarged bound

    8*ceil(sqrt(2K'N))+(13/2)H'
      <=12K^(7/2)+7H+8<16H²<256H²

uses original K and N<=K^6; it does not import N<=(K')^6. This check was
compared with the frozen parity-cover §3–4 and retuned content-cover §5.2.

The monic division U=(F-F(1))/(X-1) gives
(1-X)U=D(1) modulo D=F+delta. Hence the forced residue P0=ApU/D(1)
mod D has the correct sign and an actually unit denominator. Its fixed
precision computation costs soft J. A complete rational identity is not
inferred from merely calculating that residue.

For the full certificate, reduction modulo D(qX), using the shifted-root
unit resultant and the corrected endpoint, forces P(qX)=0 modulo D(qX).
Since q is a unit, this implies P=0 modulo D. Reduction modulo D then
forces Ap=0 modulo D. At the good hit, the actual sources p=F' and H_w
are nonzero and have the correct common marker amplitude; a weight A
preserving that amplitude cannot satisfy the forced divisibility. The
argument applies to this ansatz, including a regular polynomial remainder,
and does not exclude a different pole-transfer denominator or algorithm.

The final equality of selected residues is likewise valid: Ap-(1-X)P0
is divisible by D, with a quotient regular in delta. Its polynomial
functional has zero delta residue. This proves a cheap numerator change,
not acquisition of the remaining rational functional.

Root also checked the coefficient-strip continuation in the independent
§§1–6 review. Formal division produces p/D=P_<M+t^M E_M/D, and at a
unit hit theta the exact equality theta^M E_M(theta)=p(theta) retains the
entire pole. Reciprocal strips are regular at unit nodes too. The common
unit multiplier may be dropped only for the guarded weak ratio, not for
an equality of amplitudes. These conclusions are finite identities; no
numerical fixtures or general complexity lower bounds are involved.
