# Independent review of recurrence and adaptive precision reports

24 October 2026. Files read independently; repository read only. No numerical examples or repository changes. SHA-256 fixes the reviewed versions.

| Reviewed source | SHA-256 |
|---|---|
| /tmp/semiprime-recurrence-innovation-20261024/literature.md | 65bd049c6c47107741595bd180b10ab10d1d634301fc57f3d099dad6ba94b877 |
| /tmp/semiprime-covering-lift-20261023/adaptive-precision-followup.md | ead3be1eea13a6bb882a2ddd25ccf30f5116c47bf7e33937c8ebe062b280e609 |

## Literature report: accepted, with source-access qualification

I independently opened the Bostan–Yurkevich, Wang–Yang–Zhong, and Bostan–Cluzeau–Salvy primary texts. The supplied velusqrt PDF failed twice with timeout/502, so I do not claim fresh verification of its section 3. That inaccessible citation is not needed for the report's independently derived chain algorithm.

Bostan–Yurkevich Theorem 3 assumes a field and nonzero leading recurrence values. Theorem 5 explicitly includes coefficient degree d in the soft sqrt(Nd) scale, so r=1,d=J yields the old scalar scale, not degree-independent soft sqrt h. This is the cleanest citation for the growing-degree conclusion; the report's section-3.3 discussion should be read alongside Theorem 5 in section 3.4. [Primary text](https://arxiv.org/html/2012.08656).

Wang–Yang–Zhong works over characteristic zero with indeterminate q. Theorem 2.4 is a summability characterization under its all-shift coprimality condition; Theorem 3.5 requires nondegeneracy and the stated reflection property. Neither is the missing finite-prefix composite-ring endpoint evaluator. [Primary text](https://arxiv.org/html/2606.07061).

Bostan–Cluzeau–Salvy Theorem 2 indeed retains sqrt(dN) and its finite-field characteristic condition. No rank-only shortcut follows from that statement. [Primary PDF](https://mathexp.eu/bostan/publications/BoClSa05.pdf).

The acquired-chain support proof checks algebraically: q^i=a*q^t is equivalent to a=q^(i-t), and the differences of the two integer intervals fill exactly [-(ell-1),h-1]. Squarefreeness of N makes equal local zero support equivalent to equal gcd with N. The scalar residues themselves need not agree. Evaluating each single-root interval product by ordinary geometric blocking is division free except known q units and costs soft sqrt(h+ell). Exact modulo-N sorting acquires only genuine chains; it does not claim to detect unknown-prime-only edges. Unit-separated roots ensure distinct vertices, and order(q)>J excludes cycles among J vertices. Restriction interval complexity is correctly charged. No native bound on the resulting number K of chains is proved or implied. The adaptive branch is valid but does not improve the native worst case.

The literature search's absence conclusion is appropriately scoped to the identified sources. This review confirms no omitted hypothesis was silently turned into the desired theorem; it cannot certify exhaustive coverage of all literature.

## Adaptive precision report: accepted under its stated stabilized-factor premise

Let N=pq be squarefree. The premise is that each acquired factor d_i has exact local valuation 0 or 1. Fixed lifts modulo N^2 preserve those valuations at every higher precision: an alteration divisible by p^2 cannot change a factor with valuation at most one. Hence the integer product W has local valuations cP,cQ, independent of representative choices.

For a canonical acquired residue w_t modulo N^t, if t<=min(cP,cQ), then w_t=0. If t>min(cP,cQ), at least one prime valuation is below t and is preserved in w_t; thus w_t is nonzero and its largest N-power divisor has exponent e=min(cP,cQ). Dividing leaves u modulo N well defined because changing the lift changes the quotient by a multiple of N^(t-e), with t-e>=1. If the counts agree, u is a unit; if they differ, precisely the lower-count prime becomes a unit while the other remains a divisor, yielding a proper gcd. Maximality of e excludes gcd=N.

The initialized blocking formula is correct: D_s(X)=product_(r<s)F_t(q1^r X-N), evaluated at X=q1^(ks), covers exactly the ks,...,ks+s-1 factors. Degree Js and h/s evaluations give soft(J+sqrt(Jh)) ring work per precision, including short tails by a paid MPE. Bit precision t multiplies the cost by soft(t log N). Geometric precision growth capped at J+1 has total precision O(min(cP,cQ)+1), because the first successful precision exceeds that minimum by at most a constant factor. The J+1 cap ensures success.

The stabilized valuation premise is imported from the pinned parent, not reproved by this short follow-up. The stated sparse-instance improvement is conditional on that already paid preparation and includes no new fast unit-argument evaluator. Worst-case equal counts Theta(J) retain the full precision penalty; the report correctly declines a new exponent claim. The old direct-list alternative remains relevant and should be included when selecting the implementation branch.

## Constructive extension delivered

See endpoint-qdifference-extension.md in this scratch directory. It explicitly acquires

    B(t)E(qt)=B(q^h t)E(t), E(0)=1,

then tests fraction-free reduction at t=1. The specific missing boundary is E(qt) modulo (t-1)^r: q-shift does not descend to this local quotient. Repairing it by orbit jets requires an uninitialized e_k boundary, while short Padé residual divisibility by t^r says nothing at t=1. This is an endpoint acquisition failure for an actual proposed algorithm, not the generic degree-Jh argument and not a lower bound for all implicit methods. Existing blocking remains the acquired terminal fallback.
