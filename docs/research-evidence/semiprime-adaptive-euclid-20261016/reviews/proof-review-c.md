# Final independent review: primitive hyperbolic and complete Euclidean catalogs

2026-10-16. PASS for BOTH final reports. Full source, constructor, energy and scope review; no correction requested. The earlier review-c.md is preserved unchanged as the base detailed review and is superseded only in its report-byte pin by this final review.

## Exact final reviewed bytes

- hyperbolic/report.md: 14077 bytes; SHA256 `242dbe88a63b516da5b659983f4dccf9c7b13cb805b5053cf7fc6e580cb62ca7`.
- hyperbolic/source-pins.json: 1277 bytes; SHA256 `cf8528861d5d6537fa29dab869c8c82f67675820d5a62987b34aaf06e9a31f43`.
- hyperbolic/full-ray-trimming.md: 7771 bytes; SHA256 `52684f92a92b2b037d687d99708ff3a3473c5b22502990686d308a9fdc902b23`.
- hyperbolic/full-ray-source-pins.json: 636 bytes; SHA256 `afce9896d4405c1b80dc87f6213ca087c7bd6594354a709f02aaaee962462cc6`.
- Preserved hyperbolic/review-c.md: 8015 bytes; SHA256 `1b1ca7d5570854f5ae1b2551b8cfebf7f2e49dc7117515dbb3216899d6a7f384`.

Every listed source byte count and SHA256 in BOTH source-pin manifests matches. This includes the final hyperbolic report pinned by the full-ray manifest. Native EuclidRowFamily and EuclidRowBudget definitions and relevant contracts were read directly, not merely inferred from a prose summary.

## Final primitive-hyperbolic report

The previous full review's arithmetic and cost checks remain valid: per-tag dyadic determinant count81, exact harmonic/root-table enumeration, centered lifts and ordinary scalar powering, weighted color multiplicities, FOUR possible fourth-row completions, raw high-digit energy and selector accounting, global no-wrap and relative-origin bounds, and the constants162 and81 in the carrier consequences.

The final text now accurately distinguishes publicRow's FIXED square-root threshold from other admissible positive-threshold nonzero Euclidean outputs. It does not imply that a zero terminal output belongs to the nonzero catalog. All current nonzero convergents satisfy |a|t<m and are primitive by the native determinant frame; arbitrary intermediates can fail that product bound and remain outside THIS first report. The full-ray corollary separately handles them. The main report does not claim any advice-selected family is collision-complete, nor that its representation lower bound is an operation lower bound.

## Complete-source budget and deterministic trimming

Native EuclidRowFamily.euclidPairs retains every current and proper intermediate vector; publicPairs depends only on quotientSlope modulo m and thus on n,m,j. Deduplication is by COORDINATE triple (j,a,t), not by b or public center, so the catalog and its occupancies are fixed before h varies. Each coordinate row emits two public center packets. Therefore the compiled publicPackets_length_le bound8mL_m² safely upper-bounds the deduplicated triple count; it is not an invalid use of the universal coordinate-set bound as a tag-incidence count.

Occupancy greater than B_m=64L_m⁴ implies at most m/(8L_m²) heavy tags. The stated light count at least2m/3 for odd m>=5 follows from m-1 original tags and the conservative displayed inequality. This trimming is a public low-digit operation; it does not depend on future factor or higher-digit advice.

For a native current frame m=r0*y+r*x with r0>r>0, x>=0, y>0, a proper intermediate has a_abs=r0-kr>0 and t=x+ky>0. Expansion gives EXACTLY m=r*t+a_abs*y. Hence t<m because the second term is positive, and a_abs<m because k>=1 and r0<=m. Current r and y are also below m. The native compiled congruence/positivity theorem supplies the signed relation. These bounds cover ALL emitted nonzero intermediates even though their product may exceed m. Their primitivity also follows from this identity for prime m, but the full-ray energy proof does not require it.

## Uniform energy and the full-family witness

The light triples have at most B_m rows per tag, nonzero coordinates below m, and the same low quadratic relation. The cap-color and weighted-multiset argument therefore applies without the hyperbolic product condition. The fourth-completion bound remains four, and the raw average8B_m⁴m^(7/2), bad-residue count8m²/lambda and original-selector loss O(K_*M^6/lambda) follow. The proof quantifies over the entire light catalog before choosing any policy, so full-input/factor-advised row choices add no union factor.

Global phase separation uses the same actual routed gamma and S,D qualifications as the main report. For a policy retaining one row at every original tag, restriction to the light tags gives at least2m/3 selected tags, at most two per equal target and therefore at least m/3 distinct light targets. Their multiplicative energy has the stated bound. Any cover of the COMPLETE selected target family contains this light witness and must satisfy the displayed k²T tradeoff.

Crucially, the report does NOT claim that the UNTRIMMED full target union itself has low energy: heavy-tag quadruples are not bounded. It proves the cover obstruction through a contained light selected subset. The same witness logic applies to the unselected complete union because every tag has an emitted initial nonzero row. This distinction is correct and essential.

Origin advice is also correctly limited to one assigned origin per source entry and the explicit no-wrap inequalities. Polylogarithmic relative span on the light witness is allowed; a common huge origin cancels. The native publicShift/reflectedShift lists may have much larger relative spans and are not automatically licensed. Multiple shifted copies require an additional multiplicity budget.

## Costs, provenance and limits

The complete Euclidean list's softly linear emission/setup budget is ALREADY inherited from the compiled count and the historical full-source analysis. Sorting/deduplication, occupancy counts and light/heavy labels add softly linear public work. Exact lifts and known-unit powers have the stated given-N,m,gamma bit/storage envelope. The report does not rebrand this old full-source generation as a new acquisition theorem or silently price gamma/long row products inside that charge.

The new full-ray scope is deterministic low-digit trimming plus raw energy domination for every higher-digit/factor-advised selection of current OR intermediate rows, beyond the prior fixed-low-digit one-row result and the primitive hyperbolic product catalog. Previous native hyperbolic-wrap rows and universal Euclidean ray cardinality results do not already prove this energy/advice statement. The cap lemma, supplied original prime-pair mass, selector telescope and energy-to-cover inequality remain credited as inherited.

Trimming is solely a proof witness for carrier containment. A useful collision may lie at a heavy tag, so no factoring algorithm may discard heavy tags under a claimed coverage theorem from this report. Tiny privately chosen tag subsets, unrestricted relative centers, high-productset carriers, shared computations, implicit norms and other sufficient factor queries remain open. The majority count is against the SAME original qualified supply, with additional nonpolynomial o(M^6/log²M) losses separately charged when earlier properties need them.

Final verdict: both reports are mathematically sound within their qualified global actual-source and representation contracts. The new energy domination is substantive; source generation and coverage/recovery inputs remain inherited. No whole-query improvement, arithmetic-operation lower bound, new compiled native lemma, all-input controller theorem or Lean sixth-rate factorizer is claimed. No reviewed file was mutated and no build or example search was used.
