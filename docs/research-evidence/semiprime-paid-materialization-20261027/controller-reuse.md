# Original finite-ring controller reuse audit

Read-only audit, 27 October 2026. No upstream compilation or source changes performed. The direct Boolean route is preferable to a ternary-input adapter: the machine's assignment domain is already `List Bool`; characteristic three is an arithmetic representation, not a restriction of the Boolean variable domain.

## Executable seam

`SqrtLog/MomentsAssemblyProgramRelModel.lean:92`, `Relational.AssignmentContract`, is genuinely parametric in `produce : Code`. For every matching context, actual assignment bytes, valid frame, and good seed/product dictionaries, it requires an actual `Eval produce k` (with `k <= A`) returning the contribution weight and raw jet, preserving the specified frame and consuming assignment tape 174. Supplying only a mathematical tensor extension does not discharge this contract.

`MomentsAssemblyProgramRelReadout.lean:104`, `denseProgram_run`, executes `denseCommand produce` under that contract. The already-compiled nonrelational counterpart `MomentsAssemblyProgramReadout.denseProgram_run` is likewise parametric; its `meaning` can be the deterministic output of the new callback algorithm. Neither requires clauses or fixed local arity.

The old lower seam is narrower: `LeafProgramFactorLoopModel.lean:25`, `FactorLoop.CallbackContract`, hardcodes `Eval Factor.callback`. Its model and proofs otherwise use only `Product.Good`, ID record parsing, `FoldRel`, and record iterator budgets. Therefore the parent's new command-parametric loop/assignment adapter is a real required change, rather than an instantiation of that old callback theorem. `LeafAssignmentSetupProgram` itself is CNF-free: it merges assignment/head masks, computes head weights, saves/restores product and sum, and moves the accumulator. The new callback must preserve the shared context and collector footprint; parser flags 13/14/15 are protocol flags, not clause roles.

## Exact algebra after the callback

For a factor truth predicate on w ports, use its Boolean multiaffine extension

    T(B) = sum_(a in Bool^w) [entry(a)] prod_i (if a_i then B_i else 1-B_i).

This has degree one per port. It rejects no extra input symbol and needs no ZMod-3 interpolation conversion. Corrected port jets are already modeled by `MomentsPerturbation.incidenceZ`: constant beta plus row(T+theta)-row(theta). `incidenceZ_eval_row` proves its value is the shifted row when the measured beta agrees with the actual Boolean assignment. `PerturbationAssemblyStored.outputWords_denote` identifies actual emitted words with its canonical jet. The new callback must connect its literal source/measurement records to those hypotheses; beta is not free advice.

The compiled nonrelational `MomentsAssemblySemanticsFinite` and `MomentsAssemblySemanticsBuckets` give the finite-support/head product identity. Their hypotheses require complete, duplicate-free finite head/assignment/support enumerations, idempotent assignment values, and the actual contribution meaning. With the new Boolean extension, this is the original Boolean tensor contraction over the finite ring. It does not require the older ternary `Counting` interface. The corresponding relational semantic chain is not in the verified compiled closure, so prefer the compiled nonrelational theorem or explicitly charge a later small incremental proof build.

`LeafProgramCountCorrect.command_correct` (line 97) and `program_correct` (line 215) are generic in a target polynomial: actual jets, degree < QJ, and target(0)=count with count <= m*2^n < 3^t imply actual recovery of integer count bytes. Set m=1 and choose sufficient t for a Boolean network. No CNF-specific count decoder is needed.

## Actual resource dependencies

`MomentsAssemblyProgramUniformBounds` defines dictionary capacity

    L = u*J*card(supportUniverse vars J)

and byte envelope `L*(2*(n+u+J)+2*d*B+2)`, where B=2t. The assignment envelope is

    9H + A + weightedEnvelope(B,d,n+u+J,2L)
       + 2*dictionaryByteEnvelope(B,d,n+u+J,L) + 10.

Head, support and bucket envelopes multiply this by the actual assignment, head and support counts X,Y,S. `denseBudget` adds the actual K-bucket scan and finite-ring readout. Thus growing-scope callback work enters explicitly through A; it is not hidden in a fixed-k constant.

A Boolean extension evaluator needs 2^w actual truth-predicate calls. With cached input complements, the recursive ring arithmetic uses at most `3*(2^w-1)+2w` add/multiply/negate primitive calls, before dictionary/canonicalization overhead. A single abstract subtraction must be compiled as negate plus add. For macro scopes w=O(L_input^(3/4)), this is lower-order than the intended subexponential exponent, but that observation alone is not a composed machine-time theorem.

Input bucket/head assignment lists, source rows, support lists, and initial canonical dictionaries must actually be generated and charged. Generic controller theorems do not acquire these data for free. Their tapes may contain many entries; do not inherit a polynomial-space claim solely from the existence of the generic time theorem. The new leaf also needs an actual original-OAI instruction program implementing the macro Boolean predicate, not just its pure Lean evaluator and a separately asserted cost.

## Packaging and remaining exact contracts

The recursive import closure of `SemiprimePublicFactorCount` and `SemiprimeSubdividedEntry` consists of 107 local modules, with Mathlib/Batteries external roots and no OAI/OpenAISemiprime imports (see `macro-pure-imports.json`). Avoid `MacroFiniteEnumerations`, `ScheduledCounter`, and the current source-counter modules: these pull the renamed vendor branch. Original compiled OAI objects can instead share an isolated explicit LEAN_PATH with the pure macro closure and the pinned Mathlib/toolchain objects. The parent's import probe, rather than this read-only audit, tests that arrangement.

The smallest remaining execution obligations are:

1. A new command-parametric factor record loop/assignment wrapper (parent now implementing), preserving the old parser/frame and measured budgets.
2. A real macro truth-predicate program plus Boolean extension program over the existing finite-ring jet/dictionary primitives, with actual source-port decoding, corrected beta, canonical output, and callback cost/frame theorem.
3. A generic source/packing/bucket producer and finite enumeration bridge for growing-scope factors, instantiated with the already-proved literal macro graph semantics and public size bounds.
4. Compose generic moments semantics, node collection, and generic count recovery; then derive the growing-scope parameter/time/space bound from the actual tapes and costs.

No new algebraic count-recovery principle is needed. The unresolved work is the actual producer/program and its end-to-end resource refinement. No complete new factoring runtime or goal completion is claimed here.
