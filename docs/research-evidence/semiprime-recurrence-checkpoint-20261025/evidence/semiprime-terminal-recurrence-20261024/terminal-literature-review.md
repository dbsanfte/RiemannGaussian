# Independent scalar-circuit derivative and adaptive Hasse review

2026-10-24. **PASS** for the exact original report below. No required mathematical fixes. Scratch review only; no source/repository edits, examples or backend work.

Reviewed source: `/tmp/semiprime-terminal-recurrence-20261024/terminal-literature.md`

SHA256: `49c90f496dcfaf1f4cc2e69e746950c9e3b597257ca94d21056c76ad7547ed06`

The cached primary Baur-Strassen introduction/model was inspected, in addition to the report's self-contained ring implementation. The subsequent root-gradient simplification is a separate addendum and is not needed to make this original algorithm correct; it will be audited separately when frozen.

## Exact AD contract, fixed parameters and legal inverses

The report requires an ACTUAL arithmetic circuit for E in independent monic coefficients, valid as a rational identity, with q,u,L and all source labels fixed. This is essential. It does not differentiate a zero-mask oracle, a native one-parameter restriction, or an unpriced endpoint circuit. A branch returning zero merely from coverage does not satisfy the contract.

The primary Baur-Strassen statement uses a field/nonscalar model. The source correctly distinguishes that model from its own composite-ring proof. Local reverse addition, multiplication and inverse rules are identities in every commutative ring at certified-unit denominators. Inverse differentiation uses the already acquired inverse, not an inverse of E or of a collision. At F+z those same unit constants give lawful truncated-series inverses. The formal-identity/branch qualification is therefore sufficient even when the current scalar output is zero modulo one or both primes.

All coefficient gradients cost O(C+J); composing with/reversing the explicit monic root-product tree adds soft J. Jet output costs are also covered by C*h: for nonempty E the generic independent-coefficient circuit depends on all J inputs, so its scalar gate count is Omega(J) up to the explicitly charged input/output convention; J=1 and empty cases are separately handled. No separate J directional executions are used.

## First derivatives and original-row recovery

The division-free D_k=sum_i x_i^k product_(v!=i)F(x_v) identity is correct. At one local hit only the omitted-hit term survives, with unit coefficient; at two or more hits all first derivatives vanish. The report does not infer a native global single-hit bound.

E=(-1)^(JL)product_j P_L(Y_j) gives the displayed root derivative with the correct sign. Exactly one local hit yields exactly one nonzero g_j because same-side target and seed separation makes P_L' at that hit nonzero. On the globally zero E branch, unequal multiplicities with minimum one, or different single-hit row labels, give a proper scalar gcd of some g_j. If both single hits use the same row, that g_j is a unit and publicly selects an original row. Different seed indices at the two primes are correctly deferred to the inherited one-row locator. Derivative outputs themselves are never sent to the original leaf decoder.

## Gradient-to-root map and scaled logarithmic remainder

The reversal/convolution formula V_rev=-D*F_rev modT^J is correct. Its coefficient functional identity gives lambda_F(X^k V)=-D_k for k<J. With the supplied unit-separated roots, Lagrange's coefficient identity and the root chain rule yield V(Y_j)=g_j. The algorithm uses only convolution/reversal and monic MPE; F' inversions appear only in the proof-side Lagrange identity, never as an unguarded algorithmic step.

On a unit-E branch, g_j=E*P_L'(Y_j)/P_L(Y_j), so V is the stated scaled logarithmic-derivative remainder modulo F. At zeros only the polynomial cofactor statistic is used. It is not P_L modF, and the report does not claim a free integration or far-remainder reconstruction.

## Adaptive Hasse multiplicities and coefficients

For A(z)=product_i(F(x_i)+z), its valuation modulo each prime is EXACTLY the local hit count: the leading coefficient is the product of the nonzero factors. Therefore the first coefficient not zero modulo N is at h=min(hP,hQ). A proper gcd of that coefficient separates unequal counts; a unit coefficient proves their equality. The precise stopping algorithm includes the UNIT coefficient case. Zero coefficients are compared, not divided.

Precision doubling, capped at min(J,L)+1, reaches a precision O(h+1); its summed primal cost is soft(C(h+1)+J). The final reverse run at sufficient precision costs soft(C*h+J). Unit denominator constants remain invertible as series throughout. No hit value is inverted, and no hidden h is given to the algorithm.

For B_k=[z^(h-1)]D_k(z), deleting a hit factor leaves exactly h-1 zeros and deleting a nonhit leaves h. Thus B_k=a_h sum_(hit nodes)x_i^k locally, with coefficient/sign exactly as stated. This is a Hasse coefficient statement and introduces no factorial denominator.

## Newton hit polynomial and final recovery

When the counts agree, a_h is a certified unit and can be inverted. If h<J, gradients supply powers k=1,...,h because those coefficient directions exist; Newton identities divide only by 1,...,h, all below both primes. The resulting monic polynomial is the local hit-node polynomial in both fields, with CRT coefficients in R. If h=J, every target is a hit locally and H_hit=F is valid; this correctly avoids requesting the derivative of the fixed monic leading coefficient. Empty and h=0 cases are handled separately.

Evaluating at original Y_j detects exactly the local hit-row sets, since targets are unit-separated and each seed hits at most one row. Different sets produce a proper gcd. Absent that, a global zero selects a row with a local hit at both primes. The original one-row locator then supplies a genuine proper factor or bounded saturated original leaf. No auxiliary jet coefficient or arbitrary translated-base equality is assigned that decoder.

## Actual-h cost and limitations

The total bound soft(C(h+1)+J+sqrt L) includes adaptive primal lifts, one reverse run, interpolation/Newton work, every gcd and the original row locator. A constant h would preserve a hypothetical fast scalar endpoint clock, but no such total-hit bound is supplied. Per-row hit caps and per-node uniqueness do not imply it.

The sparse-jet caveat is correct: mixed additions can cancel equal-valuation terms, so output h does not by itself acquire the needed intermediate leading coefficients. Supplying all canonical factor constants would restore the length-L work rather than solve the endpoint. Unit phases and a Jacobi oracle cannot replace this differentiable circuit input.

The source faithfully distinguishes the transformation of a given circuit from construction of a faster endpoint. Instantiating the old blocked circuit gives the old clock; the restriction/bisection fallback remains available for larger h. No new whole-query exponent or scalar-algorithm lower bound is asserted. PASS for these exact bytes.
