/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSources
/-! # Literal pushes, preserving copies, saturating marker cancellation and powers
All helpers describe actual subtraces of the fixed source program. No helper is
an instruction/evaluator in finite control, and the closed caller supplies no advice.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackRootSourceStages
open SemiprimeD1StackRootSources SemiprimeD1StackProcedureTrace
/-- A proof-only finite path of actual pushes. The list and Nat-indexed location
map occur ONLY in this theorem; the executed program is already a fixed table. -/
theorem push_sequence {K L : Type} [DecidableEq K] (prog : L→C.Instruction K L)
    (word : List Bool) (pc : ℕ→L) (dest : K) (bank : K→List Bool) (tail : List Bool)
    (hcode : ∀i (_hi : i<word.length),prog (pc i)=.base (.push dest (word[i]?.getD false) (pc (i+1)))) :
    Runs prog word.length (pc 0) (Function.update bank dest tail)
      (pc word.length) (Function.update bank dest (word.reverse++tail)) := by
  induction word generalizing pc tail with
  | nil=>simpa only [List.length_nil,List.reverse_nil,List.nil_append] using runs_refl prog (pc 0) (Function.update bank dest tail)
  | cons b bs ih=>
    have h0 : Runs prog 1 (pc 0) (Function.update bank dest tail) (pc 1) (Function.update bank dest (b::tail)) := by
      apply one_base prog (pc 0) (pc 1) (.push dest b (pc 1)) _ _ (by simpa only [List.getElem?_cons_zero,Option.getD_some] using hcode 0 (by simp))
      · rfl
      · simp only [SemiprimeD1StackBytecode.execute,Function.update_self,Function.update_idem]
    have h1:=ih (fun i=>pc (i+1)) (b::tail) (fun i hi=>by
      simpa only [List.getElem?_cons_succ] using hcode (i+1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hi))
    have h:=runs_trans prog _ _ _ _ _ _ _ _ h0 h1
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,
      Nat.add_comm 1 bs.length] using h
/-- Every source literal has at most nine bits, fixed before original input. -/
theorem literal_length (kind : Fin 5) : (literalCode kind).length ≤ 9 := by fin_cases kind <;> decide
/-- All fixed source constants are really pushed, not inserted by a value opcode. -/
theorem seed_run (kind : Fin 5) (bank : Stack→List Bool) (tail : List Bool) :
    Runs program ((literalCode kind).length+1) (.seed kind 0)
      (Function.update bank (literalStack kind) tail) (afterSeed kind)
      (Function.update bank (literalStack kind) (literalCode kind++tail)) := by
  let pc : ℕ→Label:=fun i=>.seed kind ⟨min i 9,by omega⟩
  have h:=push_sequence program (literalCode kind).reverse pc (literalStack kind) bank tail (by
    intro i hi
    have hi' : i<(literalCode kind).length := by simpa only [List.length_reverse] using hi
    have him : min i 9=i := Nat.min_eq_left (by have hh:=literal_length kind;omega)
    simp only [pc,program,him,ite_eq_left hi'] )
  simp only [List.length_reverse,List.reverse_reverse] at h
  have hmin : min (literalCode kind).length 9=(literalCode kind).length := Nat.min_eq_left (literal_length kind)
  have h0 : pc 0=.seed kind 0 := rfl
  have h1 : Runs program 1 (pc (literalCode kind).length)
      (Function.update bank (literalStack kind) (literalCode kind++tail)) (afterSeed kind)
      (Function.update bank (literalStack kind) (literalCode kind++tail)) := by
    apply one_base program _ _ (.jump (afterSeed kind)) _ _
      (by simp only [pc,program,hmin,lt_self_iff_false,ite_false])
    · rfl
    · rfl
  rw [h0] at h
  exact runs_trans program _ _ _ _ _ _ _ _ h h1
/-- Exact real preserving-copy site, described on the literal physical store. -/
theorem copy_call (site : Fin 3) (pc next : Label) (hc : program pc=.call (.copy site 0) next)
    (cache : P.Stack→List Bool) (base root normal forwardRoot forwardNormal : List Bool) :
    Runs program (5*(cache (if site=2 then exponentKey else modulusKey)).length+4) pc
      (store cache base [] [] [] root normal forwardRoot forwardNormal) next
      (store cache base (if site=2 then [] else cache modulusKey)
        (if site=2 then cache exponentKey else []) [] root normal forwardRoot forwardNormal) := by
  apply included_call program (copyStack site) (Label.copy site) (copy_injective site) SemiprimeD1StackCopy.code 0
    (fun _=>rfl) pc next hc (5*(cache (if site=2 then exponentKey else modulusKey)).length+3)
    (SemiprimeD1StackCopy.state 0 none (cache (if site=2 then exponentKey else modulusKey)) [] [])
    (SemiprimeD1StackCopy.done (cache (if site=2 then exponentKey else modulusKey)) (cache (if site=2 then exponentKey else modulusKey)))
    _ _ rfl rfl (by simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words (cache (if site=2 then exponentKey else modulusKey)) [] none)
  · constructor
    · intro k;fin_cases site <;> fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases site <;> fin_cases k <;> rfl
    · intro k hk;rcases k with k|k
      · rfl
      · fin_cases site <;> cases k <;> first | rfl | exact (hk 1 rfl).elim
/-- Copying exponent markers when the modulus-derived marker word is already
present preserves that actual word and every source/output cache. -/
theorem copy_exponent (cache : P.Stack→List Bool) (markers root : List Bool) :
    Runs program (5*(cache exponentKey).length+4) .copyExponent
      (store cache [] markers [] [] root [] [] []) .cancel
      (store cache [] markers (cache exponentKey) [] root [] [] []) := by
  apply included_call program (copyStack 2) (Label.copy 2) (copy_injective 2) SemiprimeD1StackCopy.code 0
    (fun _=>rfl) .copyExponent .cancel rfl (5*(cache exponentKey).length+3)
    (SemiprimeD1StackCopy.state 0 none (cache exponentKey) [] [])
    (SemiprimeD1StackCopy.done (cache exponentKey) (cache exponentKey)) _ _ rfl rfl
    (by simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words (cache exponentKey) [] none)
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk;rcases k with k|k
      · rfl
      · cases k <;> first | rfl | exact (hk 1 rfl).elim
/-- One literal pop shortens an actual marker word, saturating at EOF. -/
theorem drop_marker (pc next : Label) (hc : program pc=.base (.pop (.inr .markers) next next next))
    (cache : P.Stack→List Bool) (markers root normal : List Bool) :
    Runs program 1 pc (store cache [] markers [] [] root normal [] []) next
      (store cache [] markers.tail [] [] root normal [] []) := by
  apply one_base program pc next (.pop (.inr .markers) next next next) _ _ hc
  · cases markers with
    | nil=>rfl
    | cons b bs=>cases b <;> rfl
  · funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Every acquired exponent-cache cell cancels one actual modulus-derived marker;
EOF on the latter is handled physically, never by native subtraction. -/
theorem cancel_run (count markers : List Bool) (cache : P.Stack→List Bool) (root : List Bool) :
    Runs program (2*count.length+1) .cancel (store cache [] markers count [] root [] [] [])
      (.seed 1 0) (store cache [] (markers.drop count.length) [] [] root [] [] []) := by
  induction count generalizing markers with
  | nil=>
    apply one_base program .cancel (.seed 1 0) (.pop (.inr .count) (.seed 1 0) .cancelMarker .cancelMarker) _ _ rfl
    · rfl
    · funext k;rcases k with k|k <;> first | rfl | (cases k <;> rfl)
  | cons b bs ih=>
    have h0 : Runs program 1 .cancel (store cache [] markers (b::bs) [] root [] [] []) .cancelMarker
        (store cache [] markers bs [] root [] [] []) := by
      apply one_base program .cancel .cancelMarker (.pop (.inr .count) (.seed 1 0) .cancelMarker .cancelMarker) _ _ rfl
      · cases b <;> rfl
      · funext k;rcases k with k|k <;> first | rfl | (cases k <;> rfl)
    have h1 : Runs program 1 .cancelMarker (store cache [] markers bs [] root [] [] []) .cancel
        (store cache [] markers.tail bs [] root [] [] []) := by
      apply one_base program .cancelMarker .cancel (.pop (.inr .markers) .cancel .cancel .cancel) _ _ rfl
      · cases markers with
        | nil=>rfl
        | cons c cs=>cases c <;> rfl
      · funext k;rcases k with k|k <;> first | rfl | (cases k <;> rfl)
    have h:=runs_trans program 2 (2*bs.length+1) _ _ _ _ _ _ (runs_trans program 1 1 _ _ _ _ _ _ h0 h1) (ih markers.tail)
    have hd : markers.tail.drop bs.length=markers.drop (b::bs).length := by
      cases markers <;> simp only [List.tail_nil,List.tail_cons,List.length_cons,List.drop_nil,List.drop_succ_cons]
    simpa only [hd,List.length_cons,show 2+(2*bs.length+1)=2*(bs.length+1)+1 by omega] using h
/-- Complete actual power constructor with physically acquired exponent markers. -/
theorem power_call (normal : Bool) (base markers root norm : List Bool) (cache : P.Stack→List Bool) :
    Runs program (SemiprimeD1StackExprPowerExecution.totalTime base markers+1)
      (if normal then .powerNormal else .powerRoot) (store cache base markers [] [] root norm [] [])
      (if normal then .clearNormalMarkers else .clearRootMarkers)
      (store cache base markers [] []
        (if normal then root else SemiprimeD1StackExprPowerSpec.result markers.length base root)
        (if normal then SemiprimeD1StackExprPowerSpec.result markers.length base norm else norm) [] []) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program (powerStack normal) (Label.power normal) (power_injective normal)
    Pow.program .start (fun _=>rfl) _ _ (by cases normal <;> rfl) _
    (Pow.initial base markers (if normal then norm else root))
    (SemiprimeD1StackExprPowerExecution.done base markers (if normal then norm else root))
    _ _ rfl rfl rfl rfl (SemiprimeD1StackExprPowerExecution.source_run base markers (if normal then norm else root))
  · constructor
    · intro k;cases normal <;> fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases normal <;> fin_cases k <;> rfl
    · intro k hk;rcases k with k|k
      · rfl
      · cases normal <;> cases k <;> first | rfl | exact (hk 4 rfl).elim
end RiemannGaussian.SemiprimeD1StackRootSourceStages
