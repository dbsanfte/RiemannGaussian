/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScaleLeafPrimitives
/-! # Exact destructive physical subtraction against the actual copied odd block -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
namespace RiemannGaussian.SemiprimeD1StackRootScaleLeafSubtract
open SemiprimeD1StackRootScaleLeaf SemiprimeD1StackRootScaleLeafPrimitives
open SemiprimeD1StackProcedureTrace
/-- Actual remaining/counter/copy fields; old cache and outputs are retained. -/
def data (base : Stack→List Bool) (n d c : Nat) : Stack→List Bool :=
  withDiv base (D.contents (D.unary n) (D.unary d) (D.unary c) [] [] [])
/-- A copied odd marker and a remaining marker are each physically popped. -/
theorem pair (base : Stack→List Bool) (n d c : Nat) :
    Runs program 2 .popOdd (data base (n+1) d (c+1)) .popOdd (data base n d c) :=by
  have h0:Runs program 1 .popOdd (data base (n+1) d (c+1)) .popRemaining (data base (n+1) d c):=by
    apply one_base program .popOdd .popRemaining (.pop (divStack .copied) (.advance 0) .popRemaining .popRemaining) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> rfl
        · rfl
  have h1:Runs program 1 .popRemaining (data base (n+1) d c) .popOdd (data base n d c):=by
    apply one_base program .popRemaining .popOdd (.pop (divStack .input) .clearWork .popOdd .popOdd) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> rfl
        · rfl
  exact join h0 h1
/-- A fitting odd block is physically removed from the remaining input. -/
theorem fits (base : Stack→List Bool) (c n d : Nat) (h : c≤ n) :
    Runs program (2*c+1) .popOdd (data base n d c) (.advance 0) (data base (n-c) d 0) :=by
  induction c generalizing n with
  | zero=>
    apply one_base program .popOdd (.advance 0) (.pop (divStack .copied) (.advance 0) .popRemaining .popRemaining) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> rfl
        · rfl
  | succ c ih=>
    cases n with
    | zero=>omega
    | succ n=>
      have h0:=pair base n d c
      have h1:=ih n (by omega)
      have h:=join h0 h1
      have ht:2+(2*c+1)=2*(c+1)+1:=by omega
      rw [ht] at h
      rw [show n+1-(c+1)=n-c by omega]
      exact h
/-- A short remaining word reaches the actual failure branch after consuming
all its markers and one additional copied-odd marker. -/
theorem short (base : Stack→List Bool) (n c d : Nat) (h : n<c) :
    Runs program (2*n+2) .popOdd (data base n d c) .clearWork (data base 0 d (c-n-1)) :=by
  induction n generalizing c with
  | zero=>
    cases c with
    | zero=>omega
    | succ c=>
      have h0:Runs program 1 .popOdd (data base 0 d (c+1)) .popRemaining (data base 0 d c):=by
        apply one_base program .popOdd .popRemaining (.pop (divStack .copied) (.advance 0) .popRemaining .popRemaining) _ _ rfl
        · rfl
        · funext k;rcases k with k|k
          · rfl
          · rcases k with k|k
            · cases k <;> rfl
            · rfl
      have h1:Runs program 1 .popRemaining (data base 0 d c) .clearWork (data base 0 d c):=by
        apply one_base program .popRemaining .clearWork (.pop (divStack .input) .clearWork .popOdd .popOdd) _ _ rfl
        · rfl
        · funext k;rcases k with k|k
          · rfl
          · rcases k with k|k
            · cases k <;> rfl
            · rfl
      have hh:=join h0 h1
      rw [show c+1-0-1=c by omega]
      exact hh
  | succ n ih=>
    cases c with
    | zero=>omega
    | succ c=>
      have h0:=pair base n d c
      have h1:=ih c (by omega)
      have h:=join h0 h1
      have ht:2+(2*n+2)=2*(n+1)+2:=by omega
      rw [ht] at h
      rw [show c+1-(n+1)-1=c-n-1 by omega]
      exact h
/-- Failure cleanup physically drains BOTH remaining copied and retained odd words. -/
theorem clear (base : Stack→List Bool) (d c : Nat) :
    Runs program ((c+1)+(d+1)) .clearWork (data base 0 d c) .copyRoot (data base 0 0 0) :=by
  have h0:=SemiprimeD1StackPhysicalLoops.drain program .clearWork .clearOdd (divStack .copied) rfl (data base 0 d c) (D.unary c)
  have hi:Function.update (data base 0 d c) (divStack .copied) (D.unary c)=data base 0 d c:=Function.update_eq_self _ _
  have ho:Function.update (data base 0 d c) (divStack .copied) []=data base 0 d 0:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> rfl
      · rfl
  rw [hi,ho] at h0
  have h1:=SemiprimeD1StackPhysicalLoops.drain program .clearOdd .copyRoot (divStack .divisor) rfl (data base 0 d 0) (D.unary d)
  have hi1:Function.update (data base 0 d 0) (divStack .divisor) (D.unary d)=data base 0 d 0:=Function.update_eq_self _ _
  have ho1:Function.update (data base 0 d 0) (divStack .divisor) []=data base 0 0 0:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> rfl
      · rfl
  rw [hi1,ho1] at h1
  simpa only [D.unary,List.length_replicate] using join h0 h1
end RiemannGaussian.SemiprimeD1StackRootScaleLeafSubtract
