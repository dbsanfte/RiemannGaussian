/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordFit

/-! # Exact physically padded public-word trace
All cells beyond the template width are erased by literal pops. Missing low
cells are literal false pushes, with no decoded width or fitted answer operand.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWordFitExecution
open SemiprimeD1StackWordFit SemiprimeD1StackProcedureTrace

/-- The original public checker fitting bytes. -/
def result (word cached : List Bool) : List Bool := (SemiprimeBitDivision.fitBits word cached).bits
/-- Exact physical output width, for ALL words and templates. -/
theorem result_length (word cached : List Bool) : (result word cached).length=cached.length :=
  (SemiprimeBitDivision.fitBits_counts word cached).1
/-- Fitting reads one actual word bit or pads false at EOF. -/
theorem fit_cons (word count : List Bool) (c : Bool) :
    result word (c::count)=((word.head?).getD false)::result word.tail count := by
  cases word <;> rfl

/-- A real preserving copy acquires the disposable physical width word. -/
theorem copy_call (word cached : List Bool) :
    Runs program (5*cached.length+4) .start (store word cached [] [] [])
      .take (store word cached cached [] []) := by
  apply included_call program copyStack Label.copy copyStack_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) .start .take rfl (5*cached.length+3)
    (SemiprimeD1StackCopy.state 0 none cached [] []) (SemiprimeD1StackCopy.done cached cached)
    (store word cached [] [] []) (store word cached cached [] [])
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words cached [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      fin_cases k <;> first | rfl | exact False.elim (hk 1 rfl)

/-- Exactly three real steps consume one template cell and copy/pad one input bit. -/
theorem read_cell (c : Bool) (word cached count acc out : List Bool) :
    Runs program 3 .take (store word cached (c::count) acc out)
      .take (store word.tail cached count (((word.head?).getD false)::acc) out) := by
  have h0 : Runs program 1 .take (store word cached (c::count) acc out)
      .read (store word cached count acc out) := by
    apply one_base program .take .read (.pop counter .clear .read .read) _ _ rfl
    · cases c <;> rfl
    · funext k;fin_cases k <;> rfl
  have h1 : Runs program 1 .read (store word cached count acc out)
      (.save ((word.head?).getD false)) (store word.tail cached count acc out) := by
    apply one_base program .read (.save ((word.head?).getD false))
      (.pop operand (.save false) (.save false) (.save true)) _ _ rfl
    · cases word with
      | nil => rfl
      | cons b bs => cases b <;> rfl
    · funext k;fin_cases k <;> rfl
  have h2 : Runs program 1 (.save ((word.head?).getD false)) (store word.tail cached count acc out)
      .take (store word.tail cached count (((word.head?).getD false)::acc) out) := by
    apply one_base program (.save ((word.head?).getD false)) .take
      (.push scratch ((word.head?).getD false) .take) _ _ rfl
    · rfl
    · funext k;fin_cases k <;> rfl
  exact runs_trans program 2 1 _ _ _ _ _ _ (runs_trans program 1 1 _ _ _ _ _ _ h0 h1) h2

/-- Exact fitting prefix, preserving ALL template-width padding and exposing
the actual unconsumed high input for the subsequent physical drain. -/
theorem prefix_run (count word cached acc out : List Bool) :
    Runs program (3*count.length+1) .take (store word cached count acc out)
      .clear (store (word.drop count.length) cached [] ((result word count).reverse++acc) out) := by
  induction count generalizing word acc with
  | nil =>
    apply one_base program .take .clear (.pop counter .clear .read .read) _ _ rfl
    · rfl
    · funext k;fin_cases k <;> rfl
  | cons c count ih =>
    have h0:=read_cell c word cached count acc out
    have h1:=ih word.tail (((word.head?).getD false)::acc)
    have hd : word.tail.drop count.length=word.drop (c::count).length := by
      cases word <;> simp only [List.tail_nil,List.drop_nil,List.length_cons,List.tail_cons,List.drop_succ_cons]
    rw [hd] at h1
    have hh:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
    simpa only [List.length_cons,fit_cons,List.reverse_cons,List.append_assoc,List.singleton_append,
      show 3+(3*count.length+1)=3*(count.length+1)+1 by omega] using hh

/-- ALL excess input cells are actually consumed before reversal. -/
theorem clear_run (word cached acc out : List Bool) :
    Runs program (word.length+1) .clear (store word cached [] acc out)
      .restore (store [] cached [] acc out) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program .clear .restore operand rfl
    (store [] cached [] acc out) word
  have hi : Function.update (store [] cached [] acc out) operand word=store word cached [] acc out := by
    funext k;fin_cases k <;> simp [Function.update,operand,store]
  have ho : Function.update (store [] cached [] acc out) operand []=store [] cached [] acc out :=
    Function.update_eq_self _ _
  rw [hi,ho] at h
  exact h

/-- The fitted low cells are physically reversed into their exact original order. -/
theorem restore_run (acc cached out : List Bool) :
    Runs program (2*acc.length+1) .restore (store [] cached [] acc out)
      .done (store [] cached [] [] (acc.reverse++out)) := by
  induction acc generalizing out with
  | nil =>
    apply one_base program .restore .done (.pop scratch .done (.write false) (.write true)) _ _ rfl
    · rfl
    · funext k;fin_cases k <;> rfl
  | cons b acc ih =>
    have h0 : Runs program 1 .restore (store [] cached [] (b::acc) out)
        (.write b) (store [] cached [] acc out) := by
      apply one_base program .restore (.write b) (.pop scratch .done (.write false) (.write true)) _ _ rfl
      · cases b <;> rfl
      · funext k;fin_cases k <;> rfl
    have h1 : Runs program 1 (.write b) (store [] cached [] acc out)
        .restore (store [] cached [] acc (b::out)) := by
      apply one_base program (.write b) .restore (.push output b .restore) _ _ rfl
      · rfl
      · funext k;fin_cases k <;> rfl
    have hh:=runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _ h0 h1) (ih (b::out))
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,
      show (1+1)+(2*acc.length+1)=2*(acc.length+1)+1 by omega] using hh

/-- Complete actual elapsed count, with copy, padding, drain, reversal and halt. -/
def totalTime (word cached : List Bool) : ℕ :=
  (5*cached.length+4)+(3*cached.length+1)+((word.drop cached.length).length+1)+
    (2*cached.length+1)+1
/-- Actual final state retains only the template and padded result. -/
def done (word cached : List Bool) : C.State Stack Label :=
  ⟨none,none,none,store [] cached [] [] (result word cached),[]⟩

/-- Exact original fitBits bytes from the actual fixed program, for every raw
operand/template including empty, zero and overlong encodings. -/
theorem source_run (word cached : List Bool) :
    C.run program (totalTime word cached) (initial word cached)=some (done word cached) := by
  have h0:=copy_call word cached
  have h1:=prefix_run cached word cached [] []
  simp only [List.append_nil] at h1
  have h2:=clear_run (word.drop cached.length) cached (result word cached).reverse []
  have h3:=restore_run (result word cached).reverse cached []
  simp only [List.length_reverse,result_length,List.reverse_reverse,List.append_nil] at h3
  have hh:=runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3
  obtain ⟨finish,hfinish,hout⟩:=hh [] (initial word cached) ⟨rfl,rfl,rfl⟩
  have hf:=halt_run program .done rfl (store [] cached [] [] (result word cached)) [] finish hout
  rw [totalTime,SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hf]
  rfl

end RiemannGaussian.SemiprimeD1StackWordFitExecution
