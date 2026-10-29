# Integration review: archived Adams packet

26 October 2026. Read-only repository review; no experiments or repository edits. Reviewed README.md, shared-label-roots.md and its new addendum, modified adams-contraction.md cost/scope, and extra-divisor-elimination.md decoder in the archived semiprime-knot-adams-20261026 packet.

**PASS for the archived preparation and normalization claims.** One useful exact rebase, proved below, should accompany the raw different-row-clock discussion; it restores the old common-base cost without yielding a new exponent.

## Packet claims and cost scope

The README explicitly leaves the all-semiprime sixth-exponent goal unproved, distinguishes the desired soft(L+sqrt m) from current soft(L+sqrt(Lm)), and preserves the separate conductor-dependent quadratic supplier. Preparation costs now correctly include soft k for possible licensed extractor branches, rather than silently treating an extractor as soft L when L may be smaller. The inverse-alphabet transport has continuing coefficient cost soft L and uniform factor-or-output cost soft(L+k). No optional numerical Frobenius unit is presented as necessary for the zero/nonunit query. Root-powering is not treated as additive or as an inverse on unlisted clocks.

The Morton–Manchon source locator is corrected to Section7, Theorem13 and Corollary14. Its role remains annular plethysm/cabling, not acquisition of an arithmetic norm. No source-to-query overclaim was found.

## Shared-root addendum

For all retained labels, cleaning makes gcd(E_j,r'_p)=1. A surviving original witness satisfies E_j=HI modulo r'_P; hence both H and I are coprime to r'_P. Its actual swapped witness has the same integer I at Q, so the conclusion holds at both cleaned orders. This uses actual complete-swap coverage and the original row-survival proof, not the assumption that every accidentally introduced cleaned collision is a physical witness. The report correctly retains the original metadata, permits a fresh survival proof using b,q_b if needed, and does not delete rows based on an unknown residue of I. The deduction is only a preparation consistency/streamlining fact: it supplies neither I nor its inverse exponent nor a thinner public clock. No new query rate follows.

## Exact common-base rebase of the transformed query

There is a particularly simple public rebase that avoids interpreting the raw common-target/different-base form as a worse query class. For EVERY row j and either hidden prime p, not only a witness, beta_j and b have the SAME exact local order r'_p. Therefore for every signed physical i,

    q_j^i=b
      iff beta_j^(Hi-E_j)=1
      iff r'_p divides Hi-E_j
      iff b^(Hi-E_j)=1
      iff (b^H)^i=b^E_j.                            (A)

The first equivalence uses beta_j^E_j=b; the middle uses exact matching orders. All exponents and bases on the right are publicly acquired. The prior label-cleaning proof also supplies gcd(E_j,r'_p)=1, although equality of exact orders is already enough for (A).

Consequently the products of b-q_j^i and b^E_j-(b^H)^i have the same local zero pattern, hence identical zero/nonunit status over squarefree N. They need not be numerically equal. The new common-base target list b^E_j costs soft L, q_b=b^H retains local orders>16H, and the original block evaluator gives the existing soft(L+sqrt(Lm)) bound with the corresponding signed interval. No inverse group exponent or numerical correction is required. At a globally saturated rebased leaf, b^(E_j-Hi)=1 uses the short nonzero ORIGINAL gap, so b is directly a licensed large-odd-order extractor base. Proper gcds factor. The old whole-row deletion and interval metadata must remain in force.

This does not make the transformed family a faster query or defeat the still-open contraction. It simply gives an explicit safe continuation at the original baseline. The archived raw-form discussion correctly says the old baby polynomial cannot be silently reused across q_j, but this explicit algebraic rebase justifies reuse on q_b after acquiring the new targets. The README's “common-target long query remains open” is accurate for the desired improved rate; clarifying this baseline avoids suggesting that its only known completion requires enumerating physical windings.

## Common-extra normalization and endpoint decoder

The extra-divisor identity H_native(B)=B^(2L)D^-1 P_native(B) has a unit correction acquired by two scalar q-factorials. Its coefficient acquisition and correction acquisition do not acquire the remaining long norm, and the README states that distinction. Both orientations and pair indices are retained, so its zero/nonunit recovery uses genuine original differences.

The added endpoint mapping is correct. With v=x/eta and t_i=eta^(2i+1), v=t_i implies x=q^(i+1) and its ACTUAL opposite row x'=q/x=q^-i; v=t_i^-1 implies x=q^-i directly. The pair's second argument corresponds to t_(i+1), so its apparent positive m+1 endpoint transports to the legal negative index -m. The stored opposite-row metadata, complete previous pruning and original integer-zero deletion are essential; no newly enlarged positive index is licensed. The odd final factor uses the same mapping. Thus no extra-zero or endpoint-annihilator loophole remains in this common-unit skein representation.

No other material algebra, cost or scope issue found. All complete-query improvements remain open.

## Final narrow audit: cyclic-resultant follow-up

Read the archived cyclic-resultant-followup.md. PASS scoped. The common-base comparison and separation assertions are exact: locally b is a generator of the same order-r subgroup as every beta_j, and beta_j=b^(E_j^-1 mod r). Thus beta_j=beta_l iff E_j=E_l mod r iff b^E_j=b^E_l. The inverses are used only in the proof, not acquired by the algorithm. Pairwise zero patterns, hence unit separation, transport exactly. The signed-index and original short-label decoder qualifications are retained.

For A=lcm |E_j|, A divides the projection R, and tau=beta^(RH/A) is a known integral power; q_j=tau^(A/E_j) holds with signed integer exponents. The Laurent polynomial A_0(Z)=product_j(Z^(A/E_j)-b) therefore gives r_i=A_0(tau^i). Its Laurent span is exactly sum_j A/|E_j| over the formal nonzero-b characteristic-zero lift: extreme coefficients of each factor are nonzero, so spans add. Monomial clearing of A_0(Z)-U and A_0(tau Z)-V produces the stated resultant relation at every nonzero Z=tau^i. This relation is exact but not a uniquely initialized step, and its potentially enormous support is honestly charged rather than treated as a soft-L coefficient list. The report does not transfer characteristic-zero branch selection or field divisions to the composite ring.

The fixed-index scalar acquisition and full common-base fallback remain correct. The follow-up supplies neither a fast unique-step recurrence nor a cheaper complete product, and says so. No further algebraic or scope issue found; primary source theorem checks were supplied by root and are not repeated as a new literature audit here.
