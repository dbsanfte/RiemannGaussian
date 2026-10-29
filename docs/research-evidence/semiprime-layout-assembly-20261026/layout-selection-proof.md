# Selected source-layout rows to bounded counter certificates

Sole new module `RiemannGaussian/SemiprimeLayoutSelection.lean`, importing the rewritten-prefix pinned source generic modules and the previously verified local certificate adapter. Existing local/vendor sources are preserved.

`SelectedRows` stores a finite selected index type and an injective map to actual original integer rows, full rational row-span preservation, and selected cardinality equal to source `LayoutRank.rowRank`. `selectRows` obtains this from the proved source `exists_actual_row_basis`, not from a supplied basis or rank-equality promise.

`selected_height` proves literal integer entry bounds remain true. No rescaled rational-basis entries or denominator growth are introduced. `selected_locality` uses the source's exact integer-kernel preservation theorem to derive selected kernel locality from the original layout locality.

`nodeCertificate` takes arbitrary source `Layout.Data` over ℚ, physical tensor arities and an incidence map e,i→I with `factor(incidence(e,i))=e`, actual node t, and an entry bound W_g for the original integer constraint matrix. It constructs the complete local `NodeCertificate`:

* local coordinates are the actual head fibres;
* the grouping equivalence is the inverse sigma-fibre equivalence;
* factor group is the source color;
* constraints are selected actual integer rows;
* all row-span witnesses, explicit signed-box measurements/readout and unforced representative scan come from the previously proved adapter.

`nodeCertificate_index_card` proves the selected counts equal the actual source rational ranks. `nodeCertificate_summary_card` proves exact whole-summary cardinality

`product_g [2*(card(head_g)*W_g)+1]^(rowRank(originalConstraints_g))`.

The generic physical incidence interface specializes immediately to I=Sigma(e,Fin(arity e)), factor=Sigma.fst and incidence(e,i)=⟨e,i⟩; factor compatibility is reflexivity. The original owner map gives the physical coordinate; original restoration/degree are source layout properties and remain separate from this node certificate's fields.

## Scope

This is a real layout→selected-certificate construction, not an assumed desired certificate or row-span property. Its original-constraint height bound is an EXPLICIT INPUT for arbitrary Layout.Data: arbitrary source layouts need not have bounded entries without such a bound. For the actual `builtLayout`, root must derive W from the concrete universal entries, copy embeddings and owner-fibre pullback, and use the existing source rank/head bounds. No final actual constructor-height theorem is claimed here.

The row selection uses the semantic finite-basis theorem via Classical.choice. A represented finite elimination/selection algorithm and its cost remain an execution refinement. Explicit box cardinality avoids an attained-summary enumeration oracle. Likewise the previous adapter's semantic finite Boolean decoder still requires primitive implementation/refinement. No end-to-end machine time/space theorem is asserted.

Strict absolute-lake compilation PASS, repository `.olean` and identical isolated scratch copy saved. Logs: `layout-selection-build.log`; all three explicit theorem/definition axiom reports contain only standard axioms.

Final root-import scoped gate PASS: `CheckSelection.lean` runs all 15 linters with zero errors and audits all 38 emitted declarations (15 theorem declarations) against the standard-only axiom allowlist. Log `layout-selection-audit.log`. No broad build was launched.
