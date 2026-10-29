# Paid materialization: paper factoring-time result

27 October 2026. Goal **ACTIVE**; substantive positive result. The explicit algorithm has a reviewed **paper-level deterministic bit-time bound of \(N^{o(1)}\)**, allowing subexponential memory. This is stronger asymptotically than the requested sixth-power bound. A complete Lean theorem connecting this implementation to its whole machine bit count remains open. The parameter schedule has an enormous crossover threshold; no practical speedup is asserted.

The advance is to pay for materializing the local truth tables and the head measurement fibres. These objects have subexponential total size. Any fixed polynomial overhead for constructing, scanning, copying and operating on them preserves the target asymptotic rate. This avoids making polynomial space or the existing SAT machine's particular parser/controller a prerequisite for a time-only result.

## Exact algorithm and argument

[paid_integer_counter.py](paid_integer_counter.py) provides an original-integer-input `factor(N)` entry point, using the previously frozen graph compiler and actual source constructor. It acquires its source internally, keeps the original scopes throughout prefix recovery, and uses the actual scheduled guard with a finite-prefix trial-division fallback. No count, source row, representative, or interpolation answer is supplied as an oracle. There is no resource-cap/no-result branch.

The counter acquires each local Boolean truth table once. At each sample node it materializes head assignments indexed by their integer measurements, then visits combinations of attained measurement keys. It sums each head's assignments separately and multiplies those sums. It never enumerates all original Boolean assignments in the fast branch.

Integer Taylor arrays carry a declared denominator degree. All source coefficients share one acquired denominator \(\Delta\); a port uses degree one and a full factor product uses degree \(M=2n\). Equal-degree addition prevents denominator growth across the large sums. Exact rational arithmetic is retained for source elimination and the polynomial-size Hermite reconstruction, whose intermediate heights are bounded separately.

The [paper proof and loop ledger](paid-materialization-route.md) cover source acquisition, Gaussian-elimination scratch values, truth tables, head fibres, support enumeration, corrected local interpolation, Hermite reconstruction, prefix recovery, and sequential-tape simulation. With

\[
S=\operatorname{poly}(n)+C_q+Y+2^h+2^w,
\]

where \(C_q\) is the actual signed-support count, \(Y\) the full integer summary-box bound, \(h\) the largest head and \(w\) the largest local scope, the actual scheduled bounds give \(\log S=o(n)\). The implementation has fixed-polynomial bit cost in \(S\), and the public graph has \(n=\Theta(\log N)\). Thus its paper bit-time bound is \(N^{o(1)}\). No unverified numerical polynomial exponent is used.

Independent reviews cover the [whole resource argument](review-paid-materialization.md) and the [actual integer implementation](review-paid-integer-counter.md). The operation meter is diagnostic; its recorded counts alone are not the proof of the bit-time bound.

## Other verified work retained

Seven new Lean modules preserve useful finite-ring/controller work completed during this investigation:

- `SemiprimeTernaryFactor` and `SemiprimeTernaryPublicFactor`: exact reject-third-symbol encoding, original/prefix counts and original graph coverage.
- `SemiprimeTernaryLocal`: exact three-point interpolation and degree bounds.
- `SemiprimeTernaryLocalPaid`: actual finite neg/add/mul interpreter, cached complements, and Boolean traversal with \(2^w\) checker calls and \(2w+3(2^w-1)\) scalar calls. Its primitive backend remains an explicit contract.
- `SemiprimeBooleanRingFactor`: direct Boolean interpolation over the original upstream finite ring and exact natural-count decoding. Constructing the matching finite-ring rows remains separate.
- `SemiprimeParametricFactorLoop` and `SemiprimeParametricFactorFrame`: the actual upstream record/setup loop made parametric in its callback, with execution and register-preservation proofs. The macro callback is not implemented here.

The [controller audit](controller-reuse.md) and [frame review](parametric-frame-review.md) state the remaining machine-interface obligations. These modules are alternatives for later formal refinement; the rational materialization proof does not require them.

## Validation and limits

All seven modules pass strict Lean compilation, ordinary-root scoped linting (15 linters each), and an audit of every generated declaration: **409 declarations / 202 theorem constants**, only the three standard axioms. Independent isolated objects match their canonical objects byte-for-byte. The final dependency checkpoint verifies the original upstream sources/objects without rebuilding the frozen published closure. Original and renamed-vendor SAT imports are kept in separate environments.

[Seven focused tests](test_paid_integer_counter.py) pass, including every two-input Boolean truth table, rational source rows, higher Taylor precision, restricted predicates, non-Boolean port values, empty factors and negative controls. The entry-point smoke exercises only the labelled fallback. These checks are implementation diagnostics, not empirical scaling evidence.

The paper algorithm/resource proof is separate from an end-to-end Lean machine-clock proof. No polynomial-space result is claimed. The older native long query remains at its previous \(\widetilde O(K^{1.25})\) bound; this result uses the factor-count route.

Replay the finite implementation checks with `python3 test_paid_integer_counter.py`. Lean audits use `run_with_upstream.py` and `final_strict_recheck.py`, which explicitly select the previously verified original OAI object closure. See [verification.json](verification.json) and [manifest.json](manifest.json) for the sealed evidence. Prior research, concurrent files and append-only journal prefixes are preserved. No commit or push was performed.
