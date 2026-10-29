/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFreshBankRestore

/-! # Actual heap call, physical field parsing and consumed validation flags -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackFreshBankRestorePrimitives
open SemiprimeD1StackFreshBankRestore SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => (Sum.inl : Control→Label)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Exact trace composition for this one fixed cache consumer. -/
theorem join {m n:Nat} {pc mid finish:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between finish after) :
    Runs program (m+n) pc before finish after :=runs_trans program m n pc mid finish before between after h g
/-- Updating one restored Fresh word retains the entire physical heap reader. -/
theorem update_fresh (p:F.Stack→List Bool) (h:H.Stack→List Bool) (k:F.Stack) (word:List Bool) :
    Function.update (data p h) (freshStack k) word=data (Function.update p k word) h :=by
  unfold data freshStack
  rw [Sum.update_elim_inl]
/-- Updating one actual heap-reader word retains every Fresh word. -/
theorem update_heap (p:F.Stack→List Bool) (h:H.Stack→List Bool) (k:H.Stack) (word:List Bool) :
    Function.update (data p h) (heapStack k) word=data p (Function.update h k word) :=by
  unfold data heapStack
  rw [Sum.update_elim_inr]
/-- Parsed-field boundary; all heap-read work except its physical output and flag is clear. -/
def view (p:F.Stack→List Bool) (heap counter reference reader valid:List Bool) :Stack→List Bool :=
  data p (SemiprimeD1StackHeapReadExecution.payload heap counter reference [] [] [] reader valid)
/-- Actual reader update changes only the unconsumed suffix of the dereferenced record. -/
theorem view_reader (p:F.Stack→List Bool) (heap counter reference reader valid word:List Bool) :
    Function.update (view p heap counter reference reader valid) (heapStack .output) word=
      view p heap counter reference word valid :=by
  unfold view
  rw [update_heap]
  congr 1
  funext k;cases k <;> simp [SemiprimeD1StackHeapReadExecution.payload,Function.update]
/-- Actual validation writes and pops preserve both heap and restored coefficient parameters. -/
theorem view_valid (p:F.Stack→List Bool) (heap counter reference reader valid word:List Bool) :
    Function.update (view p heap counter reference reader valid) (heapStack .valid) word=
      view p heap counter reference reader word :=by
  unfold view
  rw [update_heap]
  congr 1
  funext k;cases k <;> simp [SemiprimeD1StackHeapReadExecution.payload,Function.update]
/-- A field writes directly into its actual bank role, with no reconstruction callback. -/
theorem view_fresh (p:F.Stack→List Bool) (heap counter reference reader valid word:List Bool) (k:F.Stack) :
    Function.update (view p heap counter reference reader valid) (freshStack k) word=
      view (Function.update p k word) heap counter reference reader valid :=by
  exact update_fresh p _ k word
/-- The real included heap program reads the issued ordinal and returns its actual stored bytes. -/
theorem heap_call (records:List (List Bool)) (i:Fin records.length) :
    Runs program (SemiprimeD1StackHeapReadBounds.readTimeAt records i+1) (ctl .start)
      (initial (SemiprimeD1StackHeapAllocate.heapBytes records) (List.replicate records.length true)
        (List.replicate i.val true)).data (ctl .heapCheck)
      (view (fun _=>[]) (SemiprimeD1StackHeapAllocate.heapBytes records)
        (List.replicate records.length true) (List.replicate i.val true) records[i.val] [true]) :=by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program heapStack heapLabel Sum.inr_injective
    H.program (.inl .start) (fun _=>rfl) (ctl .start) (ctl .heapCheck) rfl
    (SemiprimeD1StackHeapReadBounds.readTimeAt records i)
    (H.initial (SemiprimeD1StackHeapAllocate.heapBytes records) (List.replicate records.length true)
      (List.replicate i.val true))
    (H.done (SemiprimeD1StackHeapAllocate.heapBytes records) (List.replicate records.length true)
      (List.replicate i.val true) records[i.val]) _ _ rfl rfl rfl rfl
    (SemiprimeD1StackHeapReadBounds.read_run records i)
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · exact (hk k rfl).elim
/-- One real included field parser consumes one frame and copies its literal word. -/
theorem parse_call (part:Fin 85) (bank:Stack→List Bool) (word tail:List Bool)
    (hi:bank (heapStack .output)=frame word tail) (ho:bank (freshStack (I.role part))=[])
    (hs:bank (heapStack .fieldScratch)=[]) (hv:bank (heapStack .valid)=[]) :
    Runs program (8*word.length+7) (ctl (.field part)) bank (ctl (.check part))
      (Function.update (Function.update (Function.update bank (heapStack .output) tail)
        (freshStack (I.role part)) word) (heapStack .valid) [true]) :=by
  let before:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let after:SemiprimeD1StackBytecode.State Field.Stack Field.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Link.DataRel (fieldStack part) bank before.store bank :=by
    constructor
    · intro k;rcases k with k|k
      · cases k <;> simp [fieldStack,before,SemiprimeD1TensorTapeFieldBytecode.initial,
          SemiprimeD1TensorTapeFieldMachine.contents,hi,ho,hs]
      · cases k;exact hv
    · intro k _;rfl
  apply included_call program (fieldStack part) (fieldLabel part) (field_injective part) Field.code
    (Field.active .tagPop (none,false)) (fun _=>rfl) (ctl (.field part)) (ctl (.check part)) rfl
    (8*word.length+6) before after _ _ rfl rfl
    (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin
  have h0:=Link.data_update (fieldStack part) (field_injective part) bank before.store bank hin (.inl .input) tail
  have h1:=Link.data_update (fieldStack part) (field_injective part) bank _ _ h0 (.inl .output) word
  have h2:=Link.data_update (fieldStack part) (field_injective part) bank _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update before.store (.inl .input) tail)
      (.inl .output) word) (.inr ()) [true]=after.store :=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  simpa only [he,fieldStack] using h2
/-- Physically consume a true validity flag before entering the actual next label. -/
theorem valid_run (pc:Control) (finish:Label) (bank:Stack→List Bool)
    (hcode:program (ctl pc)=.base (.pop (heapStack .valid) (ctl .abort) (ctl .abort) finish))
    (hv:bank (heapStack .valid)=[true]) :
    Runs program 1 (ctl pc) bank finish (Function.update bank (heapStack .valid) []) :=by
  apply one_base program (ctl pc) finish
    (.pop (heapStack .valid) (ctl .abort) (ctl .abort) finish) bank _ hcode
  · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,hv]
  · simp [SemiprimeD1StackBytecode.execute,hv]
/-- One full actual field step includes the real parser call and consumed validity flag. -/
theorem field_run (part:Fin 85) (p:F.Stack→List Bool) (heap counter reference word tail:List Bool)
    (ho:p (I.role part)=[]) :
    Runs program (8*word.length+8) (ctl (.field part))
      (view p heap counter reference (frame word tail) []) (next part)
      (view (Function.update p (I.role part) word) heap counter reference tail []) :=by
  have h0:=parse_call part (view p heap counter reference (frame word tail) []) word tail rfl ho rfl rfl
  rw [view_reader,view_fresh,view_valid] at h0
  have h1:=valid_run (.check part) (next part)
    (view (Function.update p (I.role part) word) heap counter reference tail [true]) rfl rfl
  rw [view_valid] at h1
  simpa only [Nat.add_assoc] using join h0 h1
/-- The complete record is physically checked for EOF before successful return. -/
theorem eof_run (p:F.Stack→List Bool) (heap counter reference:List Bool) :
    Runs program 1 (ctl .eof) (view p heap counter reference [] []) (ctl .done)
      (view p heap counter reference [] []) :=by
  apply one_base program (ctl .eof) (ctl .done)
    (.peek (heapStack .output) (ctl .done) (ctl .abort) (ctl .abort)) _ _ rfl
  · rfl
  · rfl
end RiemannGaussian.SemiprimeD1StackFreshBankRestorePrimitives
