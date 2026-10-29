/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesResources
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesOriginalCaps
/-! # Actual two-tape source for exact original recovery entries
The canonical rows and nested child words specify the two actual input tapes.
Their upstream acquisition is not assumed to be performed by this program.
The own whole-source clock and semantic byte envelope never use subtree clocks.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesOriginal
open SemiprimeD1StackRecoveryEntries
open SemiprimeD1StackRecoveryEntriesEncoding (childTape records)
open SemiprimeD1StackRecoveryDenominatorEncoding (Row tape)
open SemiprimeD1StackRecoveryEntriesExecution SemiprimeD1StackRecoveryEntriesBounds
open SemiprimeD1StackRecoveryEntriesOriginalRows SemiprimeD1StackRecoveryEntriesOriginalCaps
/-- Exact old physical entry bytes, including arbitrary padding, signs and missing-cache defaults. -/
theorem output_original (a M u:Nat) (children:List (List (List Bool))):
    (done (D.originalRows a M u) children).data output=
      records ((Up.entries children (R.acquire a M u).rows).entries.map encodeEntry):=by
  rw [output_tape]
  exact output_rows children _
/-- Real finite source from ONLY actual canonical-row bytes and actual nested child bytes. -/
theorem source_original (a M u:Nat) (children:List (List (List Bool))):
    ∃q ≤runBound (D.originalRows a M u) children,
      SemiprimeD1StackCalls.run program q
        (initial (tape (D.originalRows a M u)) (childTape children))=some (done (D.originalRows a M u) children) ∧
      (done (D.originalRows a M u) children).data output=
        records ((Up.entries children (R.acquire a M u).rows).entries.map encodeEntry):=by
  obtain ⟨q,hq,hr⟩:=source_run_bounded (D.originalRows a M u) children
  exact ⟨q,hq,hr,output_original a M u children⟩
/-- Fixed coefficient/degree are chosen before every physical source input. -/
theorem uniform_source:∃coef degree:Nat,∀(rows:List Row) (children:List (List (List Bool))),
    ∃q ≤coef*(resource rows children+1)^degree,
      SemiprimeD1StackCalls.run program q (initial (tape rows) (childTape children))=some (done rows children):=by
  exact ⟨1000000000000,4,source_run_bounded⟩
/-- Original semantic count/rank/precision caps bound the SAME executed source, independently of subtree runtimes. -/
theorem source_original_bounded (a M u Q rank P:Nat) (hM:u ≤M) (children:List (List (List Bool)))
    (hq:children.length ≤Q) (hr:∀row∈children,row.length ≤rank)
    (hp:∀row∈children,∀word∈row,word.length ≤P):
    ∃q ≤1000000000000*(byteEnvelope a M Q rank P+1)^4,
      SemiprimeD1StackCalls.run program q
        (initial (tape (D.originalRows a M u)) (childTape children))=some (done (D.originalRows a M u) children) ∧
      (done (D.originalRows a M u) children).data output=
        records ((Up.entries children (R.acquire a M u).rows).entries.map encodeEntry):=by
  obtain ⟨q,hq0,hsource,hout⟩:=source_original a M u children
  have hb:=original_resource a M u Q rank P hM children hq hr hp
  have hpow:=Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) 4
  exact ⟨q,hq0.trans (Nat.mul_le_mul_left 1000000000000 hpow),hsource,hout⟩
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesOriginal
