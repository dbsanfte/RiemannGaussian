/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsCalls
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsRowView
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsLogger
/-! # Real retained-factor copy, fresh53 descriptor acquisition and logger initialization -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsAcquisition
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsView
open SemiprimeD1StackMarkedRootRecordsRowView SemiprimeD1StackMarkedRootRecordsPrimitives
open SemiprimeD1StackProcedureTrace
namespace VE
export SemiprimeD1StackVertexCatalogueExecution (result budget)
end VE
/-- Frozen53 initializes only its sole original binary-N word. -/
theorem catalogue_input_only (bits : List Bool) (k : V.Stack) :
    SemiprimeD1StackVertexCatalogue.input bits k=if k=V.originalInput then bits else [] := by
  rcases k with k|k
  · change SemiprimeD1BinaryPublicAcquisition.input bits k=_
    rw [SemiprimeD1StackPublicInputTableTrace.public_input_only]
    simp only [V.originalInput,SemiprimeD1StackVertexCatalogue.rootStack,Sum.inl.injEq]
  · rfl
/-- An actual paid copy into the sole N role reproduces the complete real53 initial bank. -/
theorem catalogue_input_update (bits : List Bool) :
    Function.update (fun _ : V.Stack => []) V.originalInput bits=SemiprimeD1StackVertexCatalogue.input bits := by
  funext k
  rw [catalogue_input_only]
  by_cases h : k=V.originalInput <;> simp [Function.update,h]
/-- One physical fresh-catalogue write preserves the whole actual root bank and table work. -/
theorem set_catalogue (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (k : V.Stack) (word : List Bool) :
    Function.update (view r v bits p w) (catalogue k) word=
      view r (Function.update v k word) bits p w := by
  unfold view
  rw [update_catalogue]
/-- The actual raw descriptor output retained by the new53 source. -/
def descriptorBytes (bits : List Bool) : List Bool :=
  VE.result bits (V.kernelStack (SemiprimeD1StackCartesian4.aux 2))
/-- Same-program bound pays all three real copies, the whole actual53 call and initialization. -/
def setupBudget (r : R.Stack → List Bool) (bits : List Bool) : Nat :=
  5*(r (R.factorStack SemiprimeD1StackFullFactorCatalogue.output)).length+5*bits.length+
    VE.budget bits+5*(descriptorBytes bits).length+16
/-- Ready entry uses the ACTUAL acquired1804 cache once, with no second root/source execution. -/
theorem setup_run (r : R.Stack → List Bool) (bits : List Bool)
    (hn : r R.originalInput=bits) (hs : r (R.aux .scratch)=[]) (hb : bits≠[]) :
    ∃ t ≤ setupBudget r bits, Runs program t (ctl .ready) (view r (fun _ => []) bits {} {})
      (ctl .rowTag) (view r (VE.result bits) bits {} {records := r (R.factorStack SemiprimeD1StackFullFactorCatalogue.output),descriptors := descriptorBytes bits,output := [false]}) := by
  let factors := r (R.factorStack SemiprimeD1StackFullFactorCatalogue.output)
  have h0 := copy_call .factors .ready .copyNumber rfl (view r (fun _ => []) bits {} {}) factors [] rfl rfl hs
  change Runs program _ _ _ _ (Function.update (view r (fun _ => []) bits {} {}) (aux .recordReader) (factors++[])) at h0
  rw [List.append_nil,set_records] at h0
  have h1 := copy_call .number .copyNumber .catalogue rfl
    (view r (fun _ => []) bits {} {records := factors}) bits [] hn rfl hs
  change Runs program _ _ _ _ (Function.update (view r (fun _ => []) bits {} {records := factors})
    (catalogue V.originalInput) (bits++[])) at h1
  rw [List.append_nil,set_catalogue,catalogue_input_update] at h1
  obtain ⟨a,ha,h2⟩ := SemiprimeD1StackMarkedRootRecordsCalls.catalogue_call bits hb
    (view r (SemiprimeD1StackVertexCatalogue.input bits) bits {} {records := factors})
    (view r (VE.result bits) bits {} {records := factors})
    (by constructor;intro k;rfl;intro k _;rfl)
    (by
      constructor
      · intro k;rfl
      · intro k hk
        rcases k with k|k
        · rfl
        · rcases k with k|k
          · exact False.elim (hk k rfl)
          · rfl)
  have h3 := copy_call .descriptors .copyDescriptors .initialize rfl
    (view r (VE.result bits) bits {} {records := factors}) (descriptorBytes bits) [] rfl rfl hs
  change Runs program _ _ _ _ (Function.update (view r (VE.result bits) bits {} {records := factors})
    (aux .descriptorReader) ((descriptorBytes bits)++[])) at h3
  rw [List.append_nil,set_descriptors] at h3
  have h4 := SemiprimeD1StackMarkedRootRecordsLogger.initialize_call
    (view r (VE.result bits) bits {} {records := factors,descriptors := descriptorBytes bits})
  rw [set_output] at h4
  have h := join h0 (join h1 (join h2 (join h3 h4)))
  refine ⟨(5*factors.length+4)+((5*bits.length+4)+(a+((5*(descriptorBytes bits).length+4)+3))),?_,h⟩
  unfold setupBudget
  dsimp only [factors] at *
  omega
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsAcquisition
