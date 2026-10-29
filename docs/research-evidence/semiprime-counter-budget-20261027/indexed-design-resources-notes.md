# Actual indexed design resources

NEW `RiemannGaussian/SemiprimeIndexedDesignResources.lean` proves quantitative bounds for the literal `FiniteEnumerations.indexed` source used by the executable counter. It never equates that enumeration, its search ties, or its selected IDs to `defaultEnumerations`.

The semantic design `indexedDesign` is exactly the old proved build on `AcquiredSourceCounter.raw`; `physicalDesign` names the actual paid raw acquisition + integer reader + encoded physical builder. `physical_eq` is the existing FullSetupCounter physical-design theorem, under occurrence/interval/node guards. It transfers these resources to the actual runtime designs without a second selection or supplied rank answer.

## Exact generic bridges

- `head_card`: actual head dimension equals the indexed source head subtype cardinal.
- `measurement`: actual W is the literal measurementBound B Q R.
- `rank_sum`: sum of actual selected m_g equals sum of indexed-source constraint ranks, including the padded family.
- `indexed_head_bound` / `indexed_head_ceil`: enumeration-parametric source balance specialized to indexed lists.
- `indexed_rank_le`: enumeration-parametric total-rank bound specialized to indexed lists.
- `head_le`: every head has at most n original variables.
- `summary_le_rank`: the literal PacketArrayExecution nested product is at most (2*n*W+1)^(sum m_g).
- `summary_le_floor`: a denominator-weighted rank bound gives the exact integer floor exponent.

These are proofs about actual source/rank/cardinality quantities. Generic packing and width guards remain explicit; no rank-budget, balanced-layout, selection or summary-cardinality conclusion is assumed.

## Actual schedule

`scheduledPackingGuard` derives the numerical source packing guard from sourceLayoutGuard n w, actual occurrence<=2, scope<=w, and total incidence sum arity=2n. It reuses the old scheduled numeric argument only; no layout from that proof is transported.

At the literal r,Q,R,epsilon schedule:

- `scheduled_head_bound`: h_g <= Nat.ceil(3*n/(2*r):Q).
- `scheduled_rank_budget`: (sum m_g)*(r*clog2 n)<=4*n.
- `scheduled_den_pos`: the denominator is positive, derived from the actual guard's positive tolerance.
- `scheduled_measurement_le`: each m_g<=4*n.
- `scheduled_summary_bound`: literal native summaryCount <= (2*n*measurementBound 2 Q R+1)^(4*n/(r*clog2 n)).
- `scheduled_summary_log_bound`: log(actual summaryCount) <= 48*n*nu^2/sqrt(lambda)*log 2, for nu>=64.
- `summary_envelope_log`: the SAME logarithmic bound holds for the CLOSED parameter-only floor-power envelope itself. Its rank premise is discharged by Nat.div_mul_le_self, not assumed from an actual layout.

The schedule hypotheses and public graph occurrence/scope/incidence facts are intended to be discharged by the existing public wrappers. No root source, frozen source, enumeration order or packet was edited.

## Scope

This closes the indexed-layout quantitative resource bridge. It does not itself sum the complete actual counter setup/native ledger, construct the final public uniform B, or prove a primitive bit/address clock. Those are separate parent/other-agent joins. In particular source measurement magnitude appears as W inside the summary base; physical encoding cost uses the separate parameter-only bits envelope.

Only ordinary Mathlib/local imports and the existing audited source bridge are used. The semantic theorem is not a claim that old/default and indexed runtime execution or work agree. The physical equality transfers values of the actual indexed design, and all paid work remains attached to the actual new builder in FullSetupCounter.
