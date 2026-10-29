/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRadixDigit
import RiemannGaussian.SemiprimeMacroParameters

/-! # Actual digit acquisition without constructing a large power
The offset product and power occur only in the mathematical specification.
All input cells, width copies, EOF scans and cleanup execute literally.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRadixDigitExecution
open SemiprimeD1StackRadixDigit SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic

/-- An actual copy call obtains a disposable width word and restores the source. -/
theorem copy_call (word width index : List Bool) (pc next : Label)
    (hcall : program pc=.call (.copy 0) next) :
    Runs program (5*width.length+4) pc (store word width index [] [] [])
      next (store word width index [] width []) := by
  apply included_call program copyStack Label.copy copyStack_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) pc next hcall (5*width.length+3)
    (SemiprimeD1StackCopy.state 0 none width [] []) (SemiprimeD1StackCopy.done width width)
    (store word width index [] [] []) (store word width index [] width [])
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words width [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      have hc:=hk 1
      cases k <;> simp_all [store,copyStack]

/-- Every copied width marker causes one literal input pop, even at EOF. -/
theorem skip_run (copied word width index : List Bool) :
    Runs program (2*copied.length+1) .skip (store word width index [] copied [])
      .start (store (word.drop copied.length) width index [] [] []) := by
  induction copied generalizing word with
  | nil =>
    apply one_base program .skip .start (.pop .copied .start .dropBit .dropBit)
      (store word width index [] [] []) (store word width index [] [] []) rfl
    · rfl
    · funext k;cases k <;> rfl
  | cons b copied ih =>
    have h0 : Runs program 1 .skip (store word width index [] (b::copied) [])
        .dropBit (store word width index [] copied []) := by
      apply one_base program .skip .dropBit (.pop .copied .start .dropBit .dropBit)
        (store word width index [] (b::copied) []) (store word width index [] copied []) rfl
      · cases b <;> rfl
      · funext k;cases k <;> rfl
    have h1 : Runs program 1 .dropBit (store word width index [] copied [])
        .skip (store word.tail width index [] copied []) := by
      apply one_base program .dropBit .skip (.pop .input .skip .skip .skip)
        (store word width index [] copied []) (store word.tail width index [] copied []) rfl
      · cases word with
        | nil => rfl
        | cons b word => cases b <;> rfl
      · funext k;cases k <;> rfl
    have h2:=ih word.tail
    have hd : word.tail.drop copied.length=word.drop (b::copied).length := by
      cases word <;> simp only [List.tail_nil,List.drop_nil,List.length_cons,List.tail_cons,List.drop_succ_cons]
    rw [hd] at h2
    have hh:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
    convert hh using 1
    simp only [List.length_cons]
    omega

/-- One digit-index marker executes the copy and EVERY width-many bit pop. -/
theorem block_run (b : Bool) (word width index : List Bool) :
    Runs program (7*width.length+6) .start (store word width (b::index) [] [] [])
      .start (store (word.drop width.length) width index [] [] []) := by
  have h0 : Runs program 1 .start (store word width (b::index) [] [] [])
      .blockCopy (store word width index [] [] []) := by
    apply one_base program .start .blockCopy (.pop .index .finalCopy .blockCopy .blockCopy)
      (store word width (b::index) [] [] []) (store word width index [] [] []) rfl
    · cases b <;> rfl
    · funext k;cases k <;> rfl
  have h1:=copy_call word width index .blockCopy .skip rfl
  have h2:=skip_run width word width index
  have hh:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
  convert hh using 1
  omega

/-- The product offset is DERIVED from repeated physical blocks; its numeric
value is never an input or a hidden register of the machine. -/
theorem blocks_run (index word width : List Bool) :
    Runs program ((7*width.length+6)*index.length+1) .start
      (store word width index [] [] []) .finalCopy
        (store (word.drop (width.length*index.length)) width [] [] [] []) := by
  induction index generalizing word with
  | nil =>
    apply one_base program .start .finalCopy (.pop .index .finalCopy .blockCopy .blockCopy)
      (store word width [] [] [] []) (store word width [] [] [] []) rfl
    · rfl
    · funext k;cases k <;> rfl
  | cons b index ih =>
    have h0:=block_run b word width index
    have h1:=ih (word.drop width.length)
    have hd : (word.drop width.length).drop (width.length*index.length)=
        word.drop (width.length*(b::index).length) := by
      rw [List.drop_drop]
      congr 1
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
      omega
    rw [hd] at h1
    have hh:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
    convert hh using 1
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

/-- The retained width counter is physically cleared before the final halt. -/
theorem clear_width_run (width output : List Bool) :
    Runs program (width.length+1) .clearWidth (store [] width [] [] [] output)
      .done (store [] [] [] [] [] output) := by
  induction width with
  | nil =>
    apply one_base program .clearWidth .done (.pop .width .done .clearWidth .clearWidth)
      (store [] [] [] [] [] output) (store [] [] [] [] [] output) rfl
    · rfl
    · funext k;cases k <;> rfl
  | cons b width ih =>
    have h0 : Runs program 1 .clearWidth (store [] (b::width) [] [] [] output)
        .clearWidth (store [] width [] [] [] output) := by
      apply one_base program .clearWidth .clearWidth (.pop .width .done .clearWidth .clearWidth)
        (store [] (b::width) [] [] [] output) (store [] width [] [] [] output) rfl
      · cases b <;> rfl
      · funext k;cases k <;> rfl
    have hh:=runs_trans program _ _ _ _ _ _ _ _ h0 ih
    convert hh using 1
    simp only [List.length_cons]
    omega

/-- Proof-side output bytes, obtained by real nested block skips and reduction. -/
def result (word width index : List Bool) : List Bool :=
  (SemiprimeD1JetScalarBits.reduce width.length (word.drop (width.length*index.length))).bits

/-- Exact actual reducer subtrace on the physically remaining binary input. -/
def reduceTime (word width index : List Bool) : ℕ :=
  SemiprimeD1StackReduceExecution.trimTime
    ((word.drop (width.length*index.length)).take width.length).reverse+
      SemiprimeD1StackReduceExecution.prefixTime (word.drop (width.length*index.length)) width

/-- Exact trace includes nested skips, final counter copy, reduction and all cleanup. -/
def totalTime (word width index : List Bool) : ℕ :=
  ((7*width.length+6)*index.length+1)+(5*width.length+4)+
    (reduceTime word width index+1)+(width.length+1)+1

/-- Full actual source run with every input, copy, counter and return frame cleared. -/
theorem source_run (word width index : List Bool) :
    C.run program (totalTime word width index)
      (⟨some .start,none,none,store word width index [] [] [],[]⟩:C.State Stack Label)=
      some (⟨none,none,none,store [] [] [] [] [] (result word width index),[]⟩:C.State Stack Label) := by
  let remaining:=word.drop (width.length*index.length)
  have h0:=blocks_run index word width
  have h1:=copy_call remaining width [] .finalCopy .reduceCall rfl
  have h2 : Runs program (reduceTime word width index+1) .reduceCall
      (store remaining width [] [] width []) .clearWidth
        (store [] width [] [] [] (result word width index)) := by
    apply included_call program reduceStack Label.reduce reduceStack_injective SemiprimeD1StackReduce.code .take
      (fun _=>rfl) .reduceCall .clearWidth rfl (reduceTime word width index)
      (SemiprimeD1StackReduce.state (some .take) none remaining width [] [])
      (SemiprimeD1StackReduce.state none none [] [] [] (result word width index))
      (store remaining width [] [] width []) (store [] width [] [] [] (result word width index))
    · rfl
    · rfl
    · exact SemiprimeD1StackReduceExecution.source_run remaining width
    · constructor
      · intro k;cases k <;> rfl
      · intro k _;rfl
    · constructor
      · intro k;cases k <;> rfl
      · intro k hk
        have hi:=hk .left
        have hc:=hk .right
        have ho:=hk .output
        cases k <;> simp_all [store,reduceStack]
  have h3:=clear_width_run width (result word width index)
  have hh:=runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3
  obtain ⟨finish,hfinish,hout⟩:=hh []
    (⟨some .start,none,none,store word width index [] [] [],[]⟩:C.State Stack Label) ⟨rfl,rfl,rfl⟩
  have hf:=halt_run program .done rfl (store [] [] [] [] [] (result word width index)) [] finish hout
  rw [totalTime,SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hf]

/-- Full bit-operation budget pays all nested block scans, even past input EOF. -/
def timeBound (word width index : List Bool) : ℕ :=
  (7*width.length+6)*index.length+11*width.length+5*word.length+18

/-- Exact actual trace is bounded without a quotient/power/cost supplier. -/
theorem totalTime_le (word width index : List Bool) : totalTime word width index ≤ timeBound word width index := by
  have hr:=(SemiprimeD1StackReduceExecution.sourceReduce (word.drop (width.length*index.length)) width).steps_le_m
  change reduceTime word width index ≤ 5*((word.drop (width.length*index.length)).length+width.length)+10 at hr
  have hl : (word.drop (width.length*index.length)).length ≤ word.length := by
    simp only [List.length_drop]
    exact Nat.sub_le _ _
  unfold totalTime timeBound
  omega

/-- Source time certificate concerns the actual fixed program and its returned bytes. -/
def sourceDigit (word width index : List Bool) :
    StateTransition.EvalsToInTime (C.step program)
      (⟨some .start,none,none,store word width index [] [] [],[]⟩:C.State Stack Label)
      (some (⟨none,none,none,store [] [] [] [] [] (result word width index),[]⟩:C.State Stack Label))
      (timeBound word width index) := ⟨⟨_,source_run word width index⟩,totalTime_le word width index⟩

/-- Dropping physical low bits is exactly ordinary division by the dyadic power. -/
theorem bitValue_drop (word : List Bool) (p : ℕ) : bitValue (word.drop p)=bitValue word/2^p := by
  rw [SemiprimeD1JetScalarBits.bitValue_split p word,Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (SemiprimeD1JetScalarBits.bitValue_take_lt p word),Nat.zero_add]

/-- The actual resulting digits have exactly the original public native formula's value. -/
theorem result_value (word width index : List Bool) :
    bitValue (result word width index)=(bitValue word/2^(width.length*index.length))%2^width.length := by
  rw [result,SemiprimeD1JetScalarBits.reduce_value,bitValue_drop]

/-- Direct physical extraction refines the original public targetDigit. The
power remains exclusively proof-side; original N stays on the binary input. -/
theorem original_targetDigit (ell : ℕ) (word width index : List Bool)
    (hw : width.length=SemiprimeMacroParameters.radixBits ell) :
    bitValue (result word width index)=
      SemiprimeMacroParameters.targetDigit ell (bitValue word) index.length := by
  rw [result_value,hw]
  simp only [SemiprimeMacroParameters.targetDigit,←pow_mul]

end RiemannGaussian.SemiprimeD1StackRadixDigitExecution
