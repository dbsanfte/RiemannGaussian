/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackHeapRead

/-! # Actual included heap-read copy/parser effects
The certificates below unfold actual call push, included literal component
instructions and real return pop. Mapped payload and every auxiliary stack are
proved from the actual source components, not supplied read/count answers.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackHeapReadComponents
open SemiprimeD1StackHeapRead

/-- An actual call plus a proved included component trace, with exact auxiliary preservation. -/
theorem included_call {A L:Type} [DecidableEq A]
    (stack:A→Stack) (label:L→Label) (hinj:Function.Injective stack)
    (component:L→B.Instruction A L) (entry:L)
    (hcode:∀l,program (label l)=Link.instruction stack label (component l))
    (pc next:Label) (hcall:program pc=.call (label entry) next)
    (time:ℕ) (source out:B.State A L) (data result:Stack→List Bool)
    (hentry:source.pc=some entry) (hstop:out.pc=none)
    (hr:B.run component time source=some out)
    (hin:Link.DataRel stack data source.store data)
    (hout:Link.DataRel stack data out.store result) : Runs (time+1) pc data next result := by
  intro frames target h
  rcases h with ⟨hpc,hdata,hframes⟩
  let mid:=C.execute (.call (label entry) next) target
  have hm:C.run program 1 target=some mid:=by
    change C.step program target=some mid
    simp [C.step,SemiprimeD1StackCalls.step,hpc,hcall,mid]
  have hrel:Link.Rel stack label data next frames source mid:=by
    constructor
    · change Link.DataRel stack data source.store target.data
      rw [hdata]
      exact hin
    · simp [SemiprimeD1StackMultiplierLink.PcRel,hentry,mid,C.execute,hframes]
  obtain ⟨finish,hfinish,hrel⟩:=Link.run_rel stack label hinj program component hcode
    data next frames time source out mid hrel hr
  have he:finish.data=result:=Link.data_unique stack data out.store finish.data result hrel.1 hout
  have hp:finish.pc=some next ∧ finish.frames=frames:=by
    simpa only [SemiprimeD1StackMultiplierLink.PcRel,hstop] using hrel.2
  refine ⟨finish,?_,hp.1,he,hp.2⟩
  rw [show time+1=1+time by omega,SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,hfinish]

/-- Input projection for one actual copy instance, with its real empty scratch. -/
theorem copy_input (mode:Fin 3) (data:Stack→List Bool) (ht:data .temporary=[]) :
    Link.DataRel (copyStack mode) data
      (SemiprimeD1StackCopy.payload (data (copyInput mode)) (data (copyOutput mode)) []) data := by
  constructor
  · intro k
    fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.payload,ht]
  · intro k _
    rfl

/-- The actual component result determines its included destination and preserves every other stack. -/
theorem copy_output (mode:Fin 3) (data:Stack→List Bool) (ht:data .temporary=[]) :
    Link.DataRel (copyStack mode) data
      (SemiprimeD1StackCopy.payload (data (copyInput mode))
        (data (copyInput mode)++data (copyOutput mode)) [])
      (Function.update data (copyOutput mode) (data (copyInput mode)++data (copyOutput mode))) := by
  constructor
  · intro k
    fin_cases mode <;> fin_cases k <;>
      simp [copyStack,copyInput,copyOutput,SemiprimeD1StackCopy.payload,Function.update,ht]
  · intro k hk
    have hne:k≠copyOutput mode:=by
      intro he
      apply hk 1
      simpa only [copyStack,show ¬((1:Fin 3)=0) by decide,ite_false,ite_true] using he.symm
    exact Function.update_of_ne hne _ _

/-- Actual copy call effect, including its physical continuation push/pop. -/
theorem copy_call (mode:Fin 3) (data:Stack→List Bool) (ht:data .temporary=[])
    (pc next:Label) (hcall:program pc=.call (copyLabel mode 0) next) :
    Runs (5*(data (copyInput mode)).length+4) pc data next
      (Function.update data (copyOutput mode) (data (copyInput mode)++data (copyOutput mode))) := by
  apply included_call (copyStack mode) (copyLabel mode) (copyStack_injective mode)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hcall
    (5*(data (copyInput mode)).length+3)
    (SemiprimeD1StackCopy.state 0 none (data (copyInput mode)) (data (copyOutput mode)) [])
    (SemiprimeD1StackCopy.done (data (copyInput mode)) (data (copyInput mode)++data (copyOutput mode)))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words _ _ none
  · exact copy_input mode data ht
  · exact copy_output mode data ht
/-- Actual parser result store: exact suffix/field and physically acquired validity. -/
def parsed (data:Stack→List Bool) : Stack→List Bool :=
  let result:=SemiprimeSourceHistogramKeyBits.split (data .reader)
  Function.update (Function.update (Function.update data .reader result.rest) .output result.first)
    .valid (result.valid::data .valid)

/-- Projection onto the actual included parser inputs. -/
theorem field_input (data:Stack→List Bool) (hs:data .fieldScratch=[]) (ho:data .output=[]) :
    Link.DataRel fieldStack data (Field.initial (data .reader) (data .valid)).store data := by
  constructor
  · intro k
    cases k with
    | inl k => cases k <;> simp [fieldStack,Field.initial,SemiprimeD1TensorTapeFieldMachine.contents,hs,ho]
    | inr k => cases k; rfl
  · intro k _
    rfl

/-- Parser output is derived from its executed split, preserving every unmapped cell. -/
theorem field_output (data:Stack→List Bool) (hs:data .fieldScratch=[]) :
    Link.DataRel fieldStack data (Field.final (data .reader) (data .valid)).store (parsed data) := by
  constructor
  · intro k
    cases k with
    | inl k => cases k <;> simp [fieldStack,Field.final,SemiprimeD1TensorTapeFieldMachine.contents,parsed,hs]
    | inr k => cases k; simp [fieldStack,Field.final,parsed]
  · intro k hk
    have hr:k≠Stack.reader:=fun he=>hk (.inl .input) he.symm
    have ho:k≠Stack.output:=fun he=>hk (.inl .output) he.symm
    have hv:k≠Stack.valid:=fun he=>hk (.inr ()) he.symm
    simp [parsed,Function.update,hr,ho,hv]

/-- Actual parser call, including literal instructions and continuation push/pop. -/
theorem field_call (data:Stack→List Bool) (hs:data .fieldScratch=[]) (ho:data .output=[])
    (pc next:Label) (hcall:program pc=.call (fieldLabel (Field.active .tagPop (none,false))) next) :
    Runs (SemiprimeD1TensorTapeFieldExecution.fieldSteps (data .reader)+3) pc data next (parsed data) := by
  apply included_call fieldStack fieldLabel fieldStack_injective Field.code (Field.active .tagPop (none,false))
    (fun _=>rfl) pc next hcall (SemiprimeD1TensorTapeFieldExecution.fieldSteps (data .reader)+2)
    (Field.initial (data .reader) (data .valid)) (Field.final (data .reader) (data .valid))
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.parse_run _ _
  · exact field_input data hs ho
  · exact field_output data hs

/-- One actual literal local instruction, with data derived from its executed bytecode effect. -/
theorem one_base (pc next:Label) (op:B.Instruction Stack Label) (data out:Stack→List Bool)
    (hcode:program pc=.base op)
    (hp:(B.execute op ⟨some pc,none,data⟩).pc=some next)
    (hd:(B.execute op ⟨some pc,none,data⟩).store=out) : Runs 1 pc data next out := by
  intro frames state h
  rcases h with ⟨hpc,hdata,hframes⟩
  refine ⟨C.execute (.base op) state,?_,?_,?_,?_⟩
  · change C.step program state=some (C.execute (.base op) state)
    simp [C.step,SemiprimeD1StackCalls.step,hpc,hcode]
  · cases op <;> simpa only [C.execute,B.execute,hdata] using hp
  · cases op <;> simpa only [C.execute,B.execute,hdata] using hd
  · cases op <;> exact hframes
end RiemannGaussian.SemiprimeD1StackHeapReadComponents
