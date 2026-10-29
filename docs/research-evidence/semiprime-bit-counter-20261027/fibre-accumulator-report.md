# Actual partial separated-fibre accumulator connector

New module `RiemannGaussian/SemiprimeFibreAccumulatorHeight.lean`: strict compile PASS, root-import all15 lint PASS, all-generated audit **34 declarations, 25 theorem constants**, standard axioms only. Logs: `fibre-build.log`, `fibre-audit.log`; auditor `CheckFibreHeight.lean`.

This closes the finite-expression gap left explicitly in PacketHeight: a product of partial local fibre sums and a prefix of signed summary/support-label records is now instantiated to actual native group values, rather than only covered by a generic masked-term bound.

`nativeAccumulator` uses the actual `NodeCertificate` measurement, `localForced` condition and `Function.update (representative label) group localAssignment`. The prefix label set is explicit, as are each group's partial Boolean scan set and the selected group-product prefix. No representative is assumed forced or shared across different groups.

`partial_product_expansion` and `accumulator_expansion` prove the exact finite product-of-sums expansion. Records are `labels.sigma (piFinset localOptions)`. Selected groups retain their supplied partial local scan sets; inactive groups receive exactly one dummy false assignment. Thus an empty/inactive group introduces no spurious multiplicity. Measurement/forced gates become literal zero/one weights before any cancellation. Distinct loop records remain distinct even when they produce identical numerical values.

`native_product_eq` reindexes the actual selected group products into native local factor products with factor-dependent Boolean bases. Constant-one inactive tensors preserve original scopes/arities and therefore supply the missing-incidence denominator padding. `native_records_card` proves the record count is at most `labels.card * 2^n` using the actual `splitAssignment` equivalence; there is no assumed small attained-signature type or materialized assignment list.

`built_accumulator_representation` obtains the row premises from the actual source constructor and gives every retained coefficient the SAME denominator `delta^m`, where m is original total incidence. Its numerator bound is

`labels.card * 2^n * Hterm`,

with Hterm exactly the PacketHeight envelope. This is cancellation-independent. `built_varying_accumulator_representation` allows different group prefixes for each label, covering completed records plus the currently unfinished record. `built_recordwise_accumulator_representation` additionally allows bounded integer tensor tables to vary by record: constant-one factor masks therefore cover an unfinished local factor-product prefix without altering scopes or m.

One can take label records to include the actual support pair and summary tuple, with Möbius sign as the record weight, correction U and forced S as their actual record projections. The supplied finite label-prefix cardinal is then bounded by the separately proved menu/summary counts (or coarse polynomial-log alternatives for height). No Cq/signature cardinality is assumed hidden inside a callback. The theorem's finite prefix sets are specifications of actual loop prefixes; it does not claim the interpreter has constructed the expanded record family.

Scope remaining: the new theorem is an exact connector for actual mathematical partial sum/product expressions. It does not yet encode the whole Python or Lean counter as a tracked bytecode/machine loop. Internal local multilinear truth-subtotal and partial leaf-product execution need their own connector; those are the next isolated task. Primitive data acquisition/index/allocation and global runtime/space remain separate from these proved coefficient heights.
