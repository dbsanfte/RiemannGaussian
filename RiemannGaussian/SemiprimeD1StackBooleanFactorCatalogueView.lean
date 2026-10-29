/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogue
import RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordAll
/-! # Exact physical views of the retained-source Boolean factor sweep -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueView
open SemiprimeD1StackBooleanFactorCatalogue
namespace DD
export SemiprimeD1StackBooleanDescriptorRecord (clean data recordInput)
end DD
namespace DV
export SemiprimeD1StackBooleanDescriptorRecordView (update_cache)
end DV
/-- The literal original catalogue role shared with the descriptor's physical reader. -/
def catalogueOutput : V.Stack := V.kernelStack (SemiprimeD1StackCartesian4.aux 2)
/-- The complete physical state, with empty alias shadows and copy scratch.
Actual reader and bank bytes reside only in their included source inventories. -/
def data (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool)
    (words : Fin 5→List Bool) (hist out : List Bool) : Stack→List Bool :=
  Sum.elim fibre (Sum.elim catalogue
    (Sum.elim (DD.clean (DD.recordInput [] hist out) words []) (fun _=>[])))
/-- Every physically retained source role is read unchanged. -/
theorem data_source (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool)
    (words : Fin 5→List Bool) (hist out : List Bool) (k : F.Stack) :
    data fibre catalogue words hist out (sourceStack k)=fibre k := rfl
/-- Every physical catalogue role is read unchanged. -/
theorem data_catalogue (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool)
    (words : Fin 5→List Bool) (hist out : List Bool) (k : V.Stack) :
    data fibre catalogue words hist out (catalogueStack k)=catalogue k := rfl
/-- The actual descriptor inclusion reads the real source bank and reader;
both unused aliases remain real empty roles in the outer inventory. -/
theorem data_descriptor (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool)
    (words : Fin 5→List Bool) (hist out : List Bool) (k : D.Stack) :
    data fibre catalogue words hist out (descriptorStack k)=
      DD.clean (DD.recordInput (fibre F.output) hist out) words (catalogue catalogueOutput) k := by
  rcases k with k|k|k
  · rcases k with k|k|k
    · cases k;rfl
    · cases k <;> rfl
    · cases k <;> rfl
  · rfl
  · cases k <;> rfl
/-- The four real logger roles see empty consumed fields and actual accumulators. -/
theorem data_logger (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool)
    (words : Fin 5→List Bool) (hist out : List Bool) (k : Log.Stack) :
    data fibre catalogue words hist out (loggerStack k)=SemiprimeD1StackVertexRecordStream.data [] [] hist out k := by
  cases k <;> rfl
/-- The original-N preserving copy scratch is an actual empty role. -/
theorem data_scratch (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool)
    (words : Fin 5→List Bool) (hist out : List Bool) :
    data fibre catalogue words hist out scratch=[] := rfl
/-- A real source write updates exactly that included physical source role. -/
theorem update_source (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool)
    (words : Fin 5→List Bool) (hist out value : List Bool) (k : F.Stack) :
    Function.update (data fibre catalogue words hist out) (sourceStack k) value=
      data (Function.update fibre k value) catalogue words hist out := by
  unfold data sourceStack
  rw [Sum.update_elim_inl]
/-- A real catalogue write updates exactly that included physical catalogue role. -/
theorem update_catalogue (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool)
    (words : Fin 5→List Bool) (hist out value : List Bool) (k : V.Stack) :
    Function.update (data fibre catalogue words hist out) (catalogueStack k) value=
      data fibre (Function.update catalogue k value) words hist out := by
  unfold data catalogueStack
  rw [Sum.update_elim_inr,Sum.update_elim_inl]
/-- Each real cached-descriptor drain changes exactly that physical finite field. -/
theorem update_cache (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool)
    (words : Fin 5→List Bool) (hist out value : List Bool) (part : Fin 5) :
    Function.update (data fibre catalogue words hist out) (descriptorStack (D.cache part)) value=
      data fibre catalogue (Function.update words part value) hist out := by
  have hk:descriptorStack (D.cache part)=.inr (.inr (.inl (D.cache part))):=rfl
  rw [hk]
  unfold data
  rw [Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inl]
  simp only [DD.clean,DV.update_cache]
/-- Actual history updates preserve every source byte, descriptor field and output accumulator. -/
theorem update_history (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool)
    (words : Fin 5→List Bool) (hist out value : List Bool) :
    Function.update (data fibre catalogue words hist out) history value=
      data fibre catalogue words value out := by
  funext k
  rcases k with k|k|k|k
  · rfl
  · rfl
  · rcases k with k|k|k
    · rcases k with k|k|k
      · cases k;rfl
      · cases k <;> rfl
      · cases k <;> rfl
    · rfl
    · cases k <;> rfl
  · cases k;rfl
/-- The one physical false terminator and final reversal write only actual output. -/
theorem update_output (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool)
    (words : Fin 5→List Bool) (hist out value : List Bool) :
    Function.update (data fibre catalogue words hist out) output value=
      data fibre catalogue words hist value := by
  funext k
  rcases k with k|k|k|k
  · rfl
  · rfl
  · rcases k with k|k|k
    · rcases k with k|k|k
      · cases k;rfl
      · cases k <;> rfl
      · cases k <;> rfl
    · rfl
    · cases k <;> rfl
  · cases k;rfl
/-- Outer original-N input has no preloaded descriptor, bank, table or terminator. -/
theorem input_data (bits : List Bool) :
    input bits=data (F.initial bits []).data (fun _=>[]) (fun _=>[]) [] [] := by
  funext k
  rcases k with k|k|k|k
  · rfl
  · rfl
  · rcases k with k|k|k
    · rcases k with k|k|k
      · cases k;rfl
      · cases k <;> rfl
      · cases k <;> rfl
    · rfl
    · cases k <;> rfl
  · cases k;rfl
end RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueView
