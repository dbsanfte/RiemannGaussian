/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackInputWidthComponents

/-! # Actual offset subtraction and bounded minimum loops
Every source cell and zero bound bit comes from literal pop/push instructions.
Both zero and one counter cells are counted, including exhausted operands.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackInputWidthLoops
open SemiprimeD1StackInputWidth SemiprimeD1StackProcedureTrace

/-- Actual offset cleanup when the original width is already exhausted. -/
theorem clear_skip (c : Cache) (remaining skip : List Bool) :
    Runs program (skip.length+1) .clearSkip (store c remaining [] skip [] [])
      .copyLimit (store c remaining [] [] [] []) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program .clearSkip .copyLimit .skip rfl
    (store c remaining [] [] [] []) skip
  have hi : Function.update (store c remaining [] [] [] []) .skip skip=store c remaining [] skip [] [] := by
    funext k;cases k <;> rfl
  have ho : Function.update (store c remaining [] [] [] []) .skip []=store c remaining [] [] [] [] :=
    Function.update_eq_self Stack.skip _
  rw [hi,ho] at h
  exact h
/-- Actual complete width cleanup at the radix-limited exit. -/
theorem clear_remaining (c : Cache) (remaining out : List Bool) :
    Runs program (remaining.length+1) .clearRemaining (store c remaining [] [] [] out)
      .done (store c [] [] [] [] out) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program .clearRemaining .done .remaining rfl
    (store c [] [] [] [] out) remaining
  have hi : Function.update (store c [] [] [] [] out) .remaining remaining=store c remaining [] [] [] out := by
    funext k;cases k <;> rfl
  have ho : Function.update (store c [] [] [] [] out) .remaining []=store c [] [] [] [] out :=
    Function.update_eq_self Stack.remaining _
  rw [hi,ho] at h
  exact h
/-- Actual complete limit cleanup at the width-limited exit. -/
theorem clear_limit (c : Cache) (limit out : List Bool) :
    Runs program (limit.length+1) .clearLimit (store c [] [] [] limit out)
      .done (store c [] [] [] [] out) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program .clearLimit .done .limit rfl
    (store c [] [] [] [] out) limit
  have hi : Function.update (store c [] [] [] [] out) .limit limit=store c [] [] [] limit out := by
    funext k;cases k <;> rfl
  have ho : Function.update (store c [] [] [] [] out) .limit []=store c [] [] [] [] out :=
    Function.update_eq_self Stack.limit _
  rw [hi,ho] at h
  exact h

/-- One real offset-marker read, irrespective of its Boolean payload. -/
theorem skip_cell (c : Cache) (remaining skip : List Bool) (b : Bool) :
    Runs program 1 .skipLoop (store c remaining [] (b::skip) [] [])
      .dropWidth (store c remaining [] skip [] []) := by
  apply one_base program .skipLoop .dropWidth (.pop .skip .copyLimit .dropWidth .dropWidth) _ _ rfl
  · cases b <;> rfl
  · funext k;cases k <;> rfl
/-- One real original-width read after one real offset marker was consumed. -/
theorem drop_cell (c : Cache) (remaining skip : List Bool) (b : Bool) :
    Runs program 1 .dropWidth (store c (b::remaining) [] skip [] [])
      .skipLoop (store c remaining [] skip [] []) := by
  apply one_base program .dropWidth .skipLoop (.pop .remaining .clearSkip .skipLoop .skipLoop) _ _ rfl
  · cases b <;> rfl
  · funext k;cases k <;> rfl

/-- Complete actual saturating offset subtraction. The returned source suffix
is derived by these pops; neither a product value nor a difference is an input. -/
theorem skip_loop (c : Cache) (remaining skip : List Bool) :
    ∃t≤2*skip.length+2,Runs program t .skipLoop (store c remaining [] skip [] [])
      .copyLimit (store c (remaining.drop skip.length) [] [] [] []) := by
  induction skip generalizing remaining with
  | nil =>
    refine ⟨1,by simp,?_⟩
    apply one_base program .skipLoop .copyLimit (.pop .skip .copyLimit .dropWidth .dropWidth) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  | cons b skip ih =>
    have h0:=skip_cell c remaining skip b
    cases remaining with
    | nil =>
      have h1 : Runs program 1 .dropWidth (store c [] [] skip [] []) .clearSkip (store c [] [] skip [] []) := by
        apply one_base program .dropWidth .clearSkip (.pop .remaining .clearSkip .skipLoop .skipLoop) _ _ rfl
        · rfl
        · funext k;cases k <;> rfl
      have h2:=clear_skip c [] skip
      refine ⟨(1+1)+(skip.length+1),by simp only [List.length_cons];omega,?_⟩
      exact runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
    | cons a remaining =>
      have h1:=drop_cell c remaining skip a
      obtain ⟨t,ht,h2⟩:=ih remaining
      refine ⟨(1+1)+t,by simp only [List.length_cons];omega,?_⟩
      simpa only [List.length_cons,List.drop_succ_cons] using
        runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2

/-- Pushing one further literal zero is the correct power-of-two word growth. -/
theorem zeros_succ (n : ℕ) (tail : List Bool) :
    List.replicate n false++false::tail=List.replicate (n+1) false++tail := by
  induction n with
  | zero=>rfl
  | succ n ih=>simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons false) ih

/-- One real radix-limit read, irrespective of its Boolean payload. -/
theorem limit_cell (c : Cache) (remaining limit out : List Bool) (b : Bool) :
    Runs program 1 .minLoop (store c remaining [] [] (b::limit) out)
      .minWidth (store c remaining [] [] limit out) := by
  apply one_base program .minLoop .minWidth (.pop .limit .clearRemaining .minWidth .minWidth) _ _ rfl
  · cases b <;> rfl
  · funext k;cases k <;> rfl
/-- One actual remaining-width cell authorizes one actual bound-bit push. -/
theorem width_cell (c : Cache) (remaining limit out : List Bool) (b : Bool) :
    Runs program 1 .minWidth (store c (b::remaining) [] [] limit out)
      .grow (store c remaining [] [] limit out) := by
  apply one_base program .minWidth .grow (.pop .remaining .clearLimit .grow .grow) _ _ rfl
  · cases b <;> rfl
  · funext k;cases k <;> rfl
/-- The actual new low bound bit is literally false, never a shift opcode. -/
theorem grow_cell (c : Cache) (remaining limit out : List Bool) :
    Runs program 1 .grow (store c remaining [] [] limit out)
      .minLoop (store c remaining [] [] limit (false::out)) := by
  apply one_base program .grow .minLoop (.push .output false .minLoop) _ _ rfl
  · rfl
  · funext k;cases k <;> rfl

/-- Whole actual paired-pop minimum and complete excess cleanup. The minimum
and the output word occur only in this postcondition, never in machine control. -/
theorem min_loop (c : Cache) (remaining limit out : List Bool) :
    ∃t≤3*limit.length+remaining.length+3,
      Runs program t .minLoop (store c remaining [] [] limit out)
        .done (store c [] [] [] [] (List.replicate (min remaining.length limit.length) false++out)) := by
  induction limit generalizing remaining out with
  | nil =>
    have h0 : Runs program 1 .minLoop (store c remaining [] [] [] out)
        .clearRemaining (store c remaining [] [] [] out) := by
      apply one_base program .minLoop .clearRemaining (.pop .limit .clearRemaining .minWidth .minWidth) _ _ rfl
      · rfl
      · funext k;cases k <;> rfl
    have h1:=clear_remaining c remaining out
    refine ⟨1+(remaining.length+1),by simp;omega,?_⟩
    simpa only [List.length_nil,Nat.min_zero,List.replicate_zero,List.nil_append] using
      runs_trans program _ _ _ _ _ _ _ _ h0 h1
  | cons b limit ih =>
    have h0:=limit_cell c remaining limit out b
    cases remaining with
    | nil =>
      have h1 : Runs program 1 .minWidth (store c [] [] [] limit out)
          .clearLimit (store c [] [] [] limit out) := by
        apply one_base program .minWidth .clearLimit (.pop .remaining .clearLimit .grow .grow) _ _ rfl
        · rfl
        · funext k;cases k <;> rfl
      have h2:=clear_limit c limit out
      refine ⟨(1+1)+(limit.length+1),by simp only [List.length_cons,List.length_nil];omega,?_⟩
      simpa only [List.length_nil,Nat.zero_min,List.replicate_zero,List.nil_append] using
        runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
    | cons a remaining =>
      have h1:=width_cell c remaining limit out a
      have h2:=grow_cell c remaining limit out
      obtain ⟨t,ht,h3⟩:=ih remaining (false::out)
      have hn : min (remaining.length+1) (limit.length+1)=min remaining.length limit.length+1 := by omega
      refine ⟨((1+1)+1)+t,by simp only [List.length_cons];omega,?_⟩
      simpa only [List.length_cons,hn,zeros_succ] using
        runs_trans program _ _ _ _ _ _ _ _
          (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3
end RiemannGaussian.SemiprimeD1StackInputWidthLoops
