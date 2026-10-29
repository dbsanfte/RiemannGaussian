# Literal height of the actually constructed source layout

New source `RiemannGaussian/SemiprimeSourceLayoutHeight.lean`, importing the root-owned actual `SemiprimeSourceLayout` and its licensed `OpenAISemiprime.*` construction. No prior completed module or frozen evidence was edited. The module enables autoImplicit=false.

## Final constructor-facing theorem

`builtLayout_height owner factor en epsilon R B hQ hA hB t g j v`

proves the exact integer bound

`abs ((builtLayout owner factor en epsilon R).constraints t g j v) <= B*2*(8*Q)^(2*R)`.

The assumptions are **only** Q>=1, the public source interval start A<=Q, and each actual owner fibre having cardinality<=B. In particular no constructed-row-height, packing success, rank count, row locality, or desired counter identity is supplied as an assumption. A range corollary derives A<=Q from the usual r>=2,R>=4,4R<=Q source conditions. The lower-level core name is `builtLayout_constraints_abs_le`, with howner preceding hQ,hA; root callers already used that interface.

## Actual chain, with all multiplicities charged

1. `LayoutNumerator.clearedDefect_natAbs_le` bounds every literal integer cleared-defect entry by W0=2*(8Q)^(2R), for A<=Q and Q>=1.
2. `LayoutUniversal.constraints` pulls one such row through the joint-to-head map. This map is proved injective. Its fibre sum is therefore one old coefficient or zero, so there is no joint-coordinate multiplicity.
3. The `Layout.ofIndexed` enumeration merely selects the same actual row through `Fintype.equivFin`; the universal layout's actual constraints retain W0.
4. A complete-block constraint copies one universal row through the block's injective head embedding, or is a leftover singleton row with coefficient1. Rows from different blocks are separate constraint indices, not summed into a single coefficient. W0>=1 covers the singleton case. Reindexing the assembled rows again preserves every coefficient bound.
5. `LayoutHeadPullback.constraints` is a literal integer sum on the restricted owner fibre. An explicit injection from that head fibre into the original owner fibre proves its cardinality<=B. The triangle inequality therefore gives B*W0, not a factor depending on the number of blocks, all universal coordinates, or all original incidences.
6. The final theorem unfolds the actual root `builtLayout` composition and instantiates each helper with its searched packing, universal layout and actual block data. Thus helper row-bound hypotheses are discharged from the cleared-defect theorem; none survives in the final signature.

The proof works for signed integer coefficients and does not choose a rational basis or introduce basis denominators. For actual occurrence B=2 the bound is exactly W=4*(8Q)^(2R), the literal height budget proved numerically affordable in `SemiprimeSourceLayoutRate`. A later selection of actual rows preserves this height, but this module does not itself construct that selected basis or NodeCertificates.

## Scope and checks

This closes the actual coefficient-height bridge identified in `layout-bridge-map.md`; it is not a running-time theorem for building matrices or enumerating summaries. Source packing/rank, integer-kernel-to-rational-span, selected-basis construction, finite summary boxes, representatives, and primitive resources have their own interfaces.

Strict compilation and ordinary-root namespace/all-declaration audits are recorded in source-height build/audit logs and `source-height-verification.json`. All unused instance arguments were pruned rather than suppressing linters. Explicit constructor-facing parameter order is unchanged; only unneeded implicit typeclasses were removed, strengthening the theorem.

Final verification: strict autoImplicit=false/warnings-as-errors compile PASS. Ordinary-root import and all15 namespace linters PASS on13 named declarations plus6 generated declarations. All19 declaration/theorem constants have only standard axioms. Final source/object and audit hashes are in `source-height-verification.json`; no further source edits are planned.
