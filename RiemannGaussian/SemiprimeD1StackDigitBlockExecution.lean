/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDigitBlock

/-! # Exact streaming block execution
No high input tail is discarded. Every marker copy, source pop, unused marker
cleanup, canonicalization and real call/return is in the executed trace.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackDigitBlockExecution
open SemiprimeD1StackDigitBlock SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic

/-- A real included copy acquires the disposable width while restoring the cache. -/
theorem copy_call (word width : List Bool) :
    Runs program (5*width.length+4) .start (store word width [] [] [] [] [] [])
      .take (store word width width [] [] [] [] []) := by
  apply included_call program copyStack Label.copy copyStack_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) .start .take rfl (5*width.length+3)
    (SemiprimeD1StackCopy.state 0 none width [] []) (SemiprimeD1StackCopy.done width width)
    (store word width [] [] [] [] [] []) (store word width width [] [] [] [] [])
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

/-- Input EOF still physically consumes all unused width markers. -/
theorem clear_counter_run (counter width acc : List Bool) :
    Runs program (counter.length+1) .clearCounter (store [] width counter acc [] [] [] [])
      .trimCall (store [] width [] acc [] [] [] []) := by
  induction counter with
  | nil =>
    apply one_base program .clearCounter .trimCall (.pop .counter .trimCall .clearCounter .clearCounter)
      (store [] width [] acc [] [] [] []) (store [] width [] acc [] [] [] []) rfl
    · rfl
    · funext k;cases k <;> rfl
  | cons b counter ih =>
    have h0 : Runs program 1 .clearCounter (store [] width (b::counter) acc [] [] [] [])
        .clearCounter (store [] width counter acc [] [] [] []) := by
      apply one_base program .clearCounter .clearCounter (.pop .counter .trimCall .clearCounter .clearCounter)
        (store [] width (b::counter) acc [] [] [] []) (store [] width counter acc [] [] [] []) rfl
      · cases b <;> rfl
      · funext k;cases k <;> rfl
    have hh:=runs_trans program _ _ _ _ _ _ _ _ h0 ih
    convert hh using 1
    simp only [List.length_cons]
    omega

/-- Proof-side count of the exact literal prefix/EOF-cleanup instructions. -/
def prefixTime : List Bool→List Bool→ℕ
  | _,[] => 1
  | [],_::counter => counter.length+3
  | _::word,_::counter => 3+prefixTime word counter

/-- Physical bounded prefix acquisition preserves the high input tail. -/
theorem prefix_run (word counter width acc : List Bool) :
    Runs program (prefixTime word counter) .take (store word width counter acc [] [] [] [])
      .trimCall (store (word.drop counter.length) width []
        ((word.take counter.length).reverse++acc) [] [] [] []) := by
  induction word generalizing counter acc with
  | nil =>
    cases counter with
    | nil =>
      apply one_base program .take .trimCall (.pop .counter .trimCall .read .read)
        (store [] width [] acc [] [] [] []) (store [] width [] acc [] [] [] []) rfl
      · rfl
      · funext k;cases k <;> rfl
    | cons c counter =>
      have h0 : Runs program 1 .take (store [] width (c::counter) acc [] [] [] [])
          .read (store [] width counter acc [] [] [] []) := by
        apply one_base program .take .read (.pop .counter .trimCall .read .read)
          (store [] width (c::counter) acc [] [] [] []) (store [] width counter acc [] [] [] []) rfl
        · cases c <;> rfl
        · funext k;cases k <;> rfl
      have h1 : Runs program 1 .read (store [] width counter acc [] [] [] [])
          .clearCounter (store [] width counter acc [] [] [] []) := by
        apply one_base program .read .clearCounter (.pop .input .clearCounter (.save false) (.save true))
          (store [] width counter acc [] [] [] []) (store [] width counter acc [] [] [] []) rfl
        · rfl
        · funext k;cases k <;> rfl
      have h2:=clear_counter_run counter width acc
      have hh:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
      simpa only [prefixTime,List.drop_nil,List.take_nil,List.reverse_nil,List.nil_append,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
  | cons b word ih =>
    cases counter with
    | nil =>
      apply one_base program .take .trimCall (.pop .counter .trimCall .read .read)
        (store (b::word) width [] acc [] [] [] []) (store (b::word) width [] acc [] [] [] []) rfl
      · rfl
      · funext k;cases k <;> rfl
    | cons c counter =>
      have h0 : Runs program 1 .take (store (b::word) width (c::counter) acc [] [] [] [])
          .read (store (b::word) width counter acc [] [] [] []) := by
        apply one_base program .take .read (.pop .counter .trimCall .read .read)
          (store (b::word) width (c::counter) acc [] [] [] [])
          (store (b::word) width counter acc [] [] [] []) rfl
        · cases c <;> rfl
        · funext k;cases k <;> rfl
      have h1 : Runs program 1 .read (store (b::word) width counter acc [] [] [] [])
          (.save b) (store word width counter acc [] [] [] []) := by
        apply one_base program .read (.save b) (.pop .input .clearCounter (.save false) (.save true))
          (store (b::word) width counter acc [] [] [] []) (store word width counter acc [] [] [] []) rfl
        · cases b <;> rfl
        · funext k;cases k <;> rfl
      have h2 : Runs program 1 (.save b) (store word width counter acc [] [] [] [])
          .take (store word width counter (b::acc) [] [] [] []) := by
        apply one_base program (.save b) .take (.push .scratch b .take)
          (store word width counter acc [] [] [] []) (store word width counter (b::acc) [] [] [] []) rfl
        · rfl
        · funext k;cases k <;> rfl
      have h3:=ih counter (b::acc)
      have hh:=runs_trans program _ _ _ _ _ _ _ _
        (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3
      simpa only [prefixTime,List.length_cons,List.drop_succ_cons,List.take_succ_cons,List.reverse_cons,
        List.append_assoc,List.singleton_append] using hh

/-- Every prefix/EOF operation is paid without a requested prefix supplier. -/
theorem prefixTime_le (word counter : List Bool) :
    prefixTime word counter ≤ 3*(word.length+counter.length)+3 := by
  induction word generalizing counter with
  | nil => cases counter <;> simp only [prefixTime,List.length_nil,List.length_cons] <;> omega
  | cons b word ih =>
    cases counter with
    | nil => simp only [prefixTime,List.length_nil,List.length_cons];omega
    | cons c counter =>
      have hh:=ih counter
      simp only [prefixTime,List.length_cons]
      omega

/-- Exact output bytes after the actual trim-only procedure. -/
def result (word width : List Bool) : List Bool := (SemiprimeD1JetScalarBits.reduce width.length word).bits

/-- Exact time includes real Copy/trim calls and the real final halt. -/
def totalTime (word width : List Bool) : ℕ :=
  (5*width.length+4)+prefixTime word width+
    (SemiprimeD1StackReduceExecution.trimTime (word.take width.length).reverse+1)+1

/-- Complete actual block trace retains high input and width, clearing every work/frame cell. -/
theorem source_run (word width : List Bool) :
    C.run program (totalTime word width)
      (⟨some .start,none,none,store word width [] [] [] [] [] [],[]⟩:C.State Stack Label)=
      some (⟨none,none,none,store (word.drop width.length) width [] [] [] [] [] (result word width),[]⟩:
        C.State Stack Label) := by
  have h0:=copy_call word width
  have h1:=prefix_run word width width []
  simp only [List.append_nil] at h1
  have h2 : Runs program (SemiprimeD1StackReduceExecution.trimTime (word.take width.length).reverse+1)
      .trimCall (store (word.drop width.length) width [] (word.take width.length).reverse [] [] [] [])
        .done (store (word.drop width.length) width [] [] [] [] [] (result word width)) := by
    apply included_call program trimStack Label.trim trimStack_injective SemiprimeD1StackReduce.code .trim
      (fun _=>rfl) .trimCall .done rfl
      (SemiprimeD1StackReduceExecution.trimTime (word.take width.length).reverse)
      (SemiprimeD1StackReduce.state (some .trim) none [] [] (word.take width.length).reverse [])
      (SemiprimeD1StackReduce.state none none [] [] [] (result word width))
      (store (word.drop width.length) width [] (word.take width.length).reverse [] [] [] [])
      (store (word.drop width.length) width [] [] [] [] [] (result word width))
    · rfl
    · rfl
    · have hh:=SemiprimeD1StackReduceExecution.trim_run (word.take width.length).reverse [] none
      simpa only [result,List.append_nil,SemiprimeD1StackReduceExecution.trimReverse_reduce] using hh
    · constructor
      · intro k;cases k <;> rfl
      · intro k _;rfl
    · constructor
      · intro k;cases k <;> rfl
      · intro k hk
        have hs:=hk .scratch
        have ho:=hk .output
        cases k <;> simp_all [store,trimStack]
  have hh:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
  obtain ⟨finish,hfinish,hout⟩:=hh []
    (⟨some .start,none,none,store word width [] [] [] [] [] [],[]⟩:C.State Stack Label) ⟨rfl,rfl,rfl⟩
  have hf:=halt_run program .done rfl
    (store (word.drop width.length) width [] [] [] [] [] (result word width)) [] finish hout
  rw [totalTime,SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hf]

/-- The whole block acquisition is linear in supplied binary input and counter width. -/
theorem totalTime_le (word width : List Bool) : totalTime word width ≤ 8*width.length+5*word.length+11 := by
  have hp:=prefixTime_le word width
  have ht:=SemiprimeD1StackReduceExecution.trimTime_le (word.take width.length).reverse
  have hl:=(List.length_take_le' width.length word)
  simp only [List.length_reverse] at ht
  unfold totalTime
  omega

/-- Actual source certificate, retaining live high input and cached width. -/
def sourceBlock (word width : List Bool) :
    StateTransition.EvalsToInTime (C.step program)
      (⟨some .start,none,none,store word width [] [] [] [] [] [],[]⟩:C.State Stack Label)
      (some (⟨none,none,none,store (word.drop width.length) width [] [] [] [] [] (result word width),[]⟩:
        C.State Stack Label)) (8*width.length+5*word.length+11) :=
  ⟨⟨_,source_run word width⟩,totalTime_le word width⟩

/-- Actual finite machine certificate, with the same retained input/cache and
real step bound. This does not pretend those live stacks are empty at halt. -/
def machineBlock (word width : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (⟨some .start,none,none,store word width [] [] [] [] [] [],[]⟩:C.State Stack Label))
      (some (SemiprimeD1StackCalls.configuration
        (⟨none,none,none,store (word.drop width.length) width [] [] [] [] [] (result word width),[]⟩:
          C.State Stack Label))) (8*width.length+5*word.length+11) :=
  SemiprimeD1StackCalls.evalsCorrect Stack.input Stack.output Label.start program _ _ _ (sourceBlock word width)

end RiemannGaussian.SemiprimeD1StackDigitBlockExecution
