/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEdgeCatalogueScan

/-! # Complete actual edge transduction and final tape reversal -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackEdgeCatalogueTransduction
open SemiprimeD1StackEdgeCatalogue SemiprimeD1StackEdgeCatalogueComponents
open SemiprimeD1StackEdgeCatalogueView SemiprimeD1StackEdgeCatalogueEmit SemiprimeD1StackEdgeCatalogueScan
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeD1EdgeCatalogueEncoding (Record record half selected tape output)
open SemiprimeSourceHistogramKeyBits (frame frame_length)

/-- Final physical data: consumed source descriptors, retained metadata, actual edge tape. -/
def finalData (base:Cat.Stack→List Bool) (edges:List Bool) : Stack→List Bool :=
  Function.update (clean base [] (fun _=>[]) [] []) (aux .output) edges
/-- Exact emitted pair byte count. -/
theorem pair_length (words:Record) :
    (half false words (half true words [])).length=2*(record words []).length+4 := by
  simp only [half,SemiprimeD1EdgeCatalogueEncoding.sideWord,Bool.false_eq_true,ite_false,
    ite_true,List.length_cons,List.length_nil,frame_length,record_length]
  omega
/-- Emitting both half edges never needs a supplied output-byte bound. -/
theorem output_length (records:List Record) : (output records []).length≤3*(tape records []).length := by
  induction records with
  | nil => simp [output,tape]
  | cons words rest ih =>
    change (if selected words then half false words (half true words (output rest [])) else output rest []).length≤
      3*(record words (tape rest [])).length
    rw [record_append,List.length_append,mul_add]
    by_cases hs:selected words
    · rw [ite_eq_left hs,pair_append,List.length_append,pair_length]
      have hm:5≤(record words []).length:=by rw [record_length,List.length_nil];omega
      omega
    · rw [ite_eq_right hs]
      omega
/-- Actual EOF peek on the physically consumed descriptor tape. -/
theorem eof_run (base:Cat.Stack→List Bool) (raw:List Bool) :
    Runs program 1 (.inl .parse) (clean base [] (fun _=>[]) raw [])
      (.inl .finalReverse) (clean base [] (fun _=>[]) raw []) := by
  apply one_base program _ _ (.peek reader (.inl .finalReverse) (.inl (.field 0)) (.inl (.field 0))) _ _ rfl
  · rfl
  · rfl
/-- The WHOLE real transducer, including final reversal, not merely its per-record loop. -/
theorem ready (base:Cat.Stack→List Bool) (records:List Record) :
    ∃time≤56*(tape records []).length+4,Runs program time (.inl .parse)
      (clean base (tape records []) (fun _=>[]) [] []) (.inl .halt) (finalData base (output records [])) := by
  obtain ⟨time,ht,h0⟩:=scan_run base records []
  rw [List.append_nil] at h0
  have h1:=eof_run base (output records []).reverse
  have h2:=reverse_call true (clean base [] (fun _=>[]) (output records []).reverse [])
    (.inl .finalReverse) (.inl .halt) rfl
  change Runs program (2*(output records []).reverse.length+3) _ _ _
    (Function.update (Function.update (clean base [] (fun _=>[]) (output records []).reverse [])
      (aux .reversed) []) (aux .output) ((output records []).reverse.reverse++[])) at h2
  rw [List.length_reverse,List.reverse_reverse,List.append_nil,clean_raw] at h2
  have h:=h0.trans (h1.trans h2)
  refine ⟨time+(1+(2*(output records []).length+3)),?_,h⟩
  have ho:=output_length records
  omega
end RiemannGaussian.SemiprimeD1StackEdgeCatalogueTransduction
