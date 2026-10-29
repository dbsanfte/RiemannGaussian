# Constructed finite Hermite formula: proof extension

Authorized sole source extended: `RiemannGaussian/SemiprimeHermiteRecovery.lean`. Root's original packet-uniqueness and rational sample-node lemmas are retained. No other recovery module or frozen evidence was edited.

The extension proves the actual cardinal-factor reconstruction over any field K, not merely uniqueness conditional on supplied matching jets.

## Explicit constructions

`cardinalFactor points J t` is exactly

`L_t(X) = product_(s in points, s!=t) ((X-s)*(t-s)^(-1))^J`.

`cardinalFactor_eval` proves `L_t(t)=1`; all inverses occur at distinct field elements. `cardinalFactor_dvd` proves `(X-s)^J` divides it for every other sample node s. `cardinalFactor_degree` proves degree at most `(|points|-1)*J` when t is a sample node.

`inverseJet L J = sum_(i<J) (1-L)^i`. If the actual constant coefficient of L is one, `inverseJet_congruence` proves `X^J | L*inverseJet-1`. The proof uses the finite geometric identity and `X | 1-L`; no existence oracle, inverse-congruence premise, power-series convergence, or infinite series is used.

`localQuotient H L J = (H*inverseJet L J) mod_monic X^J`. Its congruence `X^J | L*localQuotient-H` and degree `<J` for J>0 are proved. `localQuotient_truncate` proves that replacing H by its retained packet `H mod X^J` leaves this result EXACTLY unchanged.

`hermiteTerm points J H t = L_t * taylor(-t)(localQuotient(taylor(t)H, taylor(t)L_t,J))`.

The own-node divisibility, other-node divisibility and automatic degree `<|points|*J` of each term are established from these constructions.

## Final theorems

`explicit_hermite_reconstruction` proves

`sum_t hermiteTerm(points,J,H,t) = H`

for J>0 and degree(H)<|points|*J. It establishes all Taylor congruences from the constructed local inverse, then applies the existing polynomial uniqueness theorem. It does NOT assume the reconstructed jets agree.

`explicit_hermite_at_zero` proves the scalar formula used by the Python implementation:

`H(0) = sum_t L_t(0) * localQuotient(H_t, taylor(t)L_t,J)(-t)`,

where `H_t=(taylor(t)H) mod X^J` is the actual retained local packet. Thus the final theorem consumes no coefficients of H beyond the Q retained packets. Root's `samplePoints_card` and precision theorem supply the actual rational nodes and sufficient J.

## Validation and scope

Strict absolute-lake compilation PASS (`autoImplicit=false`, `warningAsError=true`) with repository build artifact and identical isolated scratch `.olean`. Twelve printed axiom reports contain only `propext, Classical.choice, Quot.sound`; no sorry or added axioms. Module build log: `hermite-explicit-build.log`.

This establishes finite algebraic reconstruction and the literal scalar expression. The finite geometric polynomial is an algebraic specification; executing it efficiently by truncated multiplication or the implementation's inverse-coefficient recurrence still needs a refinement theorem and bit/space accounting. No complete machine or factoring time bound is claimed by this extension.

Root-import scoped audit also PASS: `hermite-root-audit.lean` imports existing root plus this module, runs silent namespace lint and audits the final two theorem axioms. Strict exit status zero; log `hermite-root-audit.log`. No broad build launched.
