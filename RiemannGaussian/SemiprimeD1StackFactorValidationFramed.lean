/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFactorValidationExecution
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode

/-! # Single-input finite-stack factor-validation caller
Both binary operands are physically parsed from two framed fields before the
actual nested-call validator executes. No second prepared operand is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackFactorValidationFramed
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace V
export SemiprimeD1StackFactorValidation (Stack Label code payload)
end V
namespace X
export SemiprimeD1StackFactorValidationExecution (P atState executionTime timeBound source_run)
end X
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code initial active framed_run)
end Field
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)

/-- Three fixed parser data stacks outside the actual validator's data bank. -/
inductive Aux where
  | input | work | valid
  deriving DecidableEq,Repr

/-- Literal parser-stack enumeration. -/
instance : Fintype Aux := Fintype.ofList [.input,.work,.valid] (by intro k; cases k <;> simp)

/-- Twenty-one fixed Boolean data stacks. -/
abbrev Stack := V.Stack ⊕ Aux

/-- Fixed caller, field-parser and nested-validator program labels. -/
inductive Label where
  | start | inputValid | candidateCall | candidateValid | validationCall | done
  | field (second : Bool) (pc : Field.Label)
  | validation (pc : V.Label)
  deriving DecidableEq,Fintype,Repr

/-- Actual field outputs target the original validator's binary input stacks. -/
def fieldStack (second : Bool) : Field.Stack → Stack
  | .inl .input => .inr .input
  | .inl .scratch => .inr .work
  | .inl .output => .inl (.inr (if second then .candidate else .input))
  | .inr _ => .inr .valid

/-- The parser's input/work/output/valid cells are distinct physical stacks. -/
theorem fieldStack_injective (second : Bool) : Function.Injective (fieldStack second) := by
  intro i j h
  cases second <;> rcases i with i|i <;> rcases j with j|j <;>
    cases i <;> cases j <;> simp_all [fieldStack]

/-- Complete fixed caller; nested validator halts become real returns. -/
def program : Label → C.Instruction Stack Label
  | .start => .call (.field false (Field.active .tagPop (none,false))) .inputValid
  | .inputValid => .base (.pop (.inr .valid) .done .done .candidateCall)
  | .candidateCall => .call (.field true (Field.active .tagPop (none,false))) .candidateValid
  | .candidateValid => .base (.pop (.inr .valid) .done .done .validationCall)
  | .validationCall => .call (.validation (.control .start)) .done
  | .done => .base .halt
  | .field second pc => SemiprimeD1StackMultiplierLink.instruction (fieldStack second) (Label.field second) (Field.code pc)
  | .validation pc => SemiprimeD1StackValidationLink.instruction Sum.inl Label.validation (V.code pc)

/-- Literal boundary data; both declared validation results remain physical stacks. -/
def store (encoded input candidate cofactor valid parsed : List Bool) : Stack → List Bool
  | .inl k => X.P input candidate [] cofactor [] [] valid k
  | .inr .input => encoded
  | .inr .work => []
  | .inr .valid => parsed

/-- The actual single loaded binary input consists of two framed binary fields. -/
def input (original candidate : List Bool) : List Bool := frame original (frame candidate [])

/-- Actual fixed single-input machine, with valid/cofactor declared result stacks. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine
  (.inr .input) (.inl (.inr .valid)) .start program

/-- Exact actual instruction count, retaining both parsers and nested validation. -/
def totalTime (original candidate : List Bool) : ℕ :=
  (8*original.length+7)+1+(8*candidate.length+7)+1+(X.executionTime original candidate+1)+1

/-- Full single-input source run, with every parser and procedure call executed. -/
theorem source_run (original candidate : List Bool) :
    C.run program (totalTime original candidate)
      (⟨some .start,none,none,store (input original candidate) [] [] [] [] [],[]⟩:C.State Stack Label)=
    some (⟨none,none,none,store [] [] []
      (SemiprimeD1FactorValidationBits.run original candidate).cofactor
      [(SemiprimeD1FactorValidationBits.run original candidate).valid] [],[]⟩:C.State Stack Label) := by
  let d0:=store (input original candidate) [] [] [] [] []
  let d1:=store (frame candidate []) original [] [] [] [true]
  let d2:=store (frame candidate []) original [] [] [] []
  let d3:=store [] original candidate [] [] [true]
  let d4:=store [] original candidate [] [] []
  let d5:=store [] [] [] (SemiprimeD1FactorValidationBits.run original candidate).cofactor
    [(SemiprimeD1FactorValidationBits.run original candidate).valid] []
  have h0 : Runs program (8*original.length+7) .start d0 .inputValid d1 := by
    apply included_call program (fieldStack false) (Label.field false) (fieldStack_injective false)
      Field.code (Field.active .tagPop (none,false)) (fun _=>rfl) .start .inputValid rfl
      (8*original.length+6) (Field.initial (input original candidate) [])
      (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents (frame candidate []) [] original)
        (fun _=>[true])⟩:B.State Field.Stack Field.Label) d0 d1
    · rfl
    · rfl
    · exact Field.framed_run original (frame candidate []) []
    · constructor
      · intro k; rcases k with k|k <;> cases k <;> rfl
      · intro k hk; rfl
    · constructor
      · intro k; rcases k with k|k <;> cases k <;> rfl
      · intro k hk
        rcases k with k|k
        · rcases k with k|k
          · rfl
          · cases k <;> first | rfl | exact False.elim (hk (.inl .output) rfl)
        · cases k <;> exact False.elim (by
            first | exact hk (.inl .input) rfl | exact hk (.inl .scratch) rfl | exact hk (.inr ()) rfl)
  have h1 : Runs program 1 .inputValid d1 .candidateCall d2 := by
    apply one_base program .inputValid .candidateCall (.pop (.inr .valid) .done .done .candidateCall) d1 d2 rfl
    · rfl
    · funext k; rcases k with k|k
      · rfl
      · cases k <;> rfl
  have h2 : Runs program (8*candidate.length+7) .candidateCall d2 .candidateValid d3 := by
    apply included_call program (fieldStack true) (Label.field true) (fieldStack_injective true)
      Field.code (Field.active .tagPop (none,false)) (fun _=>rfl) .candidateCall .candidateValid rfl
      (8*candidate.length+6) (Field.initial (frame candidate []) [])
      (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents [] [] candidate)
        (fun _=>[true])⟩:B.State Field.Stack Field.Label) d2 d3
    · rfl
    · rfl
    · exact Field.framed_run candidate [] []
    · constructor
      · intro k; rcases k with k|k <;> cases k <;> rfl
      · intro k hk; rfl
    · constructor
      · intro k; rcases k with k|k <;> cases k <;> rfl
      · intro k hk
        rcases k with k|k
        · rcases k with k|k
          · rfl
          · cases k <;> first | rfl | exact False.elim (hk (.inl .output) rfl)
        · cases k <;> exact False.elim (by
            first | exact hk (.inl .input) rfl | exact hk (.inl .scratch) rfl | exact hk (.inr ()) rfl)
  have h3 : Runs program 1 .candidateValid d3 .validationCall d4 := by
    apply one_base program .candidateValid .validationCall (.pop (.inr .valid) .done .done .validationCall) d3 d4 rfl
    · rfl
    · funext k; rcases k with k|k
      · rfl
      · cases k <;> rfl
  have h4 : Runs program (X.executionTime original candidate+1) .validationCall d4 .done d5 := by
    intro outer start hs
    let entered : C.State Stack Label :=
      ⟨some (.validation (.control .start)),none,none,d4,.done::outer⟩
    have hstart : C.run program 1 start=some entered := by
      rcases hs with ⟨hp,hd,hf⟩
      simp [C.run,C.step,C.execute,hp,hd,hf,program,entered]
    have hrel : SemiprimeD1StackValidationLink.Rel Sum.inl Label.validation d4 .done outer
        (X.atState (some (.control .start)) none none (X.P original candidate [] [] [] [] [])) entered := by
      constructor
      · constructor
        · intro k; rfl
        · intro k hk
          rcases k with k|k
          · exact False.elim (hk k rfl)
          · rfl
      · exact ⟨rfl,rfl⟩
    obtain ⟨finish,hfinish,hr⟩:=SemiprimeD1StackValidationLink.run_rel Sum.inl Label.validation Sum.inl_injective
      program V.code (fun _=>rfl) d4 .done outer _ _ _ entered hrel (X.source_run original candidate) rfl
    have desired : SemiprimeD1StackMultiplierLink.DataRel Sum.inl d4
        (X.atState none none none (X.P [] [] [] (SemiprimeD1FactorValidationBits.run original candidate).cofactor [] []
          [(SemiprimeD1FactorValidationBits.run original candidate).valid])).data d5 := by
      constructor
      · intro k; rfl
      · intro k hk
        rcases k with k|k
        · exact False.elim (hk k rfl)
        · cases k <;> rfl
    have hd:=SemiprimeD1StackMultiplierLink.data_unique Sum.inl d4 _ _ _ hr.1 desired
    have hp : finish.pc=some .done ∧ finish.frames=outer := hr.2
    refine ⟨finish,?_,hp.1,hd,hp.2⟩
    simpa only [Nat.add_comm] using
      (show C.run program (1+X.executionTime original candidate) start=some finish from
        by rw [SemiprimeD1StackReturnLink.run_add,hstart,Option.bind_some,hfinish])
  have h01:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
  have h012:=runs_trans program _ _ _ _ _ _ _ _ h01 h2
  have h0123:=runs_trans program _ _ _ _ _ _ _ _ h012 h3
  have h01234:=runs_trans program _ _ _ _ _ _ _ _ h0123 h4
  obtain ⟨finish,hfinish,hout⟩:=h01234 []
    (⟨some .start,none,none,d0,[]⟩:C.State Stack Label) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl d5 [] finish hout
  rw [totalTime,SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]

/-- Complete bit-length budget includes both physical field parses. -/
def timeBound (n m : ℕ) : ℕ := X.timeBound n m+8*n+8*m+18

/-- Derived actual time, with no assumed parser or validation costs. -/
theorem totalTime_le (original candidate : List Bool) : totalTime original candidate ≤ timeBound original.length candidate.length := by
  have h:=SemiprimeD1StackFactorValidationExecution.source_time original candidate
  unfold totalTime timeBound
  omega

/-- Actual source certificate from the single physically framed input. -/
def sourceValidate (original candidate : List Bool) :
    StateTransition.EvalsToInTime (C.step program)
      (⟨some .start,none,none,store (input original candidate) [] [] [] [] [],[]⟩:C.State Stack Label)
      (some (⟨none,none,none,store [] [] [] (SemiprimeD1FactorValidationBits.run original candidate).cofactor
        [(SemiprimeD1FactorValidationBits.run original candidate).valid] [],[]⟩:C.State Stack Label))
      (timeBound original.length candidate.length) :=
  ⟨⟨_,source_run original candidate⟩,totalTime_le original candidate⟩

/-- Only the single framed input stack is initially populated. -/
theorem start_configuration (bits : List Bool) :
    SemiprimeD1StackCalls.configuration
      (⟨some .start,none,none,store bits [] [] [] [] [],[]⟩:C.State Stack Label)=
    Turing.initList machine bits := by
  have hs : (⟨some .start,none,none,store bits [] [] [] [] [],[]⟩:C.State Stack Label)=
      SemiprimeD1StackCalls.initial (Sum.inr Aux.input) Label.start bits := by
    congr 1
    funext k
    rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · cases k <;> rfl
        · cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  rw [hs]
  exact SemiprimeD1StackCalls.initial_correct (Sum.inr Aux.input) (Sum.inl (Sum.inr SemiprimeD1StackFactorValidation.Aux.valid))
    Label.start program bits

/-- Actual single-input FinTM2 certificate for the exact original validation results. -/
def machineValidate (original candidate : List Bool) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine (input original candidate))
      (some (SemiprimeD1StackCalls.configuration
        (⟨none,none,none,store [] [] [] (SemiprimeD1FactorValidationBits.run original candidate).cofactor
          [(SemiprimeD1FactorValidationBits.run original candidate).valid] [],[]⟩:C.State Stack Label)))
      (timeBound original.length candidate.length) := by
  have h:=SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label)
    (Sum.inr Aux.input) (Sum.inl (Sum.inr SemiprimeD1StackFactorValidation.Aux.valid)) Label.start program _ _ _
    (sourceValidate original candidate)
  rw [start_configuration] at h
  exact h

/-- Single-input framing itself has a literal linear physical length. -/
theorem input_length (original candidate : List Bool) :
    (input original candidate).length=2*original.length+2*candidate.length+2 := by
  simp [input,SemiprimeSourceHistogramKeyBits.frame_length]
  omega

/-- Every actual source prefix counts all twenty-one Boolean stacks plus return cells. -/
theorem prefix_cells (original candidate : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (⟨some .start,none,none,store (input original candidate) [] [] [] [] [],[]⟩:C.State Stack Label)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 22*((input original candidate).length+fuel) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (input original candidate).length
    _ out (by
      intro k
      rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k
          · cases k <;> simp [store,X.P,V.payload,SemiprimeD1StackDivider.payload]
          · cases k <;> simp [store,X.P,V.payload,SemiprimeD1StackDivider.payload]
        · cases k <;> simp [store,X.P,V.payload]
      · cases k <;> simp [store]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k:Stack,(out.data k).length) ≤ 21*((input original candidate).length+fuel) := by
    calc
      _ ≤ ∑_k:Stack,((input original candidate).length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = 21*((input original candidate).length+fuel) := by
        have h₀ : Fintype.card SemiprimeD1StackAdder.Stack=4 := by decide
        have h₁ : Fintype.card SemiprimeD1StackDivider.Aux=7 := by decide
        have h₂ : Fintype.card SemiprimeD1StackFactorValidation.Aux=7 := by decide
        have h₃ : Fintype.card Aux=3 := by decide
        simp [Stack,V.Stack,SemiprimeD1StackDivider.Stack,h₀,h₁,h₂,h₃]
  omega

/-- A successful source prefix cannot exceed the actual proved halt time. -/
theorem prefix_fuel_le (original candidate : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (⟨some .start,none,none,store (input original candidate) [] [] [] [] [],[]⟩:C.State Stack Label)=some out) :
    fuel ≤ totalTime original candidate := by
  by_contra hn
  have he : fuel=totalTime original candidate+(1+(fuel-(totalTime original candidate+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hh : C.run program 1
      (⟨none,none,none,store [] [] [] (SemiprimeD1FactorValidationBits.run original candidate).cofactor
        [(SemiprimeD1FactorValidationBits.run original candidate).valid] [],[]⟩:C.State Stack Label)=none := rfl
  rw [hh,Option.bind_none] at hr
  cases hr

/-- Every actual source prefix has an input-polynomial space bound, without a fuel promise. -/
theorem prefix_polynomial_cells (original candidate : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (⟨some .start,none,none,store (input original candidate) [] [] [] [] [],[]⟩:C.State Stack Label)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      22*(2*original.length+2*candidate.length+2+timeBound original.length candidate.length) := by
  have hf:=(prefix_fuel_le original candidate fuel out hr).trans (totalTime_le original candidate)
  have h:=prefix_cells original candidate fuel out hr
  rw [input_length] at h
  omega

/-- The actual single-input compiled machine satisfies that same all-prefix space bound. -/
theorem machine_prefix_polynomial_cells (original candidate : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine (input original candidate)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      22*(2*original.length+2*candidate.length+2+timeBound original.length candidate.length) := by
  let start : C.State Stack Label:=⟨some .start,none,none,store (input original candidate) [] [] [] [] [],[]⟩
  have he:=SemiprimeD1StackCalls.run_correct (Sum.inr Aux.input)
    (Sum.inl (Sum.inr SemiprimeD1StackFactorValidation.Aux.valid)) Label.start program fuel start
  change (C.run program fuel start).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  have hs : SemiprimeD1StackCalls.configuration start=Turing.initList machine (input original candidate) :=
    start_configuration _
  rw [hs] at he
  have full : (C.run program fuel start).map
      (fun out : C.State Stack Label => (SemiprimeD1StackCalls.configuration out : machine.Cfg))=some cfg :=
    @Eq.trans (Option machine.Cfg) _ _ _ he hr
  cases hc:C.run program fuel start with
  | none => rw [hc] at full; cases full
  | some out =>
    rw [hc] at full
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj full
    rw [←hcfg]
    exact prefix_polynomial_cells original candidate fuel out hc

/-- A single fixed quadratic monomial bounds the entire parsed validation procedure. -/
theorem timeBound_le_square (n m : ℕ) : timeBound n m ≤ 3000*(n+m+3)^2 := by
  have hv:=SemiprimeD1StackFactorValidationExecution.timeBound_le_square n m
  unfold timeBound
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (m*m),Nat.zero_le (n*m)]

end RiemannGaussian.SemiprimeD1StackFactorValidationFramed
