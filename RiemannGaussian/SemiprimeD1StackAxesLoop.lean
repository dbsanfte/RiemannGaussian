/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAxesLocal

/-! # Executed paired exponent loop -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackAxesLoop
open SemiprimeD1StackAxes SemiprimeD1StackAxesComponents SemiprimeD1StackAxesLocal
open SemiprimeD1StackProcedureFragments (Runs one_base)

/-- Actual residue marker count, used only to state the executed loop. -/
def tailBit (odd:Bool) : ℕ := if odd then 1 else 0
/-- Exact instruction count of paired doubling, including its real terminal EOF. -/
def loopTime (k:ℕ) : ℕ→Bool→ℕ
  | 0,false => 1
  | 0,true => 7*2^k+7
  | h+1,odd => 14*2^k+12+loopTime (k+1) h odd

/-- Two actual markers trigger both actual axis-doubling calls. -/
theorem pair (n:ℕ) (base:Meta.Stack→List Bool) (ew D:List Bool) :
    Runs program (14*n+12) (.inl .first)
      (data base (true::true::ew) [] [] (List.replicate n true) (List.replicate n true) D)
      (.inl .first) (data base ew [] [] (List.replicate (2*n) true) (List.replicate (2*n) true) D) := by
  have h0:Runs program 1 (.inl .first) (data base (true::true::ew) [] [] (List.replicate n true) (List.replicate n true) D) (.inl .second) (data base (true::ew) [] [] (List.replicate n true) (List.replicate n true) D):=by
    apply one_base program _ _ (.pop (.inl .squareWork) (.inl .copyDepth) (.inl .second) (.inl .second)) _ _ rfl
    · rfl
    · funext j;cases j with
      | inl j => cases j <;> simp [B.execute,data,Function.update]
      | inr j => fin_cases j <;> simp [B.execute,data,Function.update]
  have h1:Runs program 1 (.inl .second) (data base (true::ew) [] [] (List.replicate n true) (List.replicate n true) D) (.inl (.copyAxis 0)) (data base ew [] [] (List.replicate n true) (List.replicate n true) D):=by
    apply one_base program _ _ (.pop (.inl .squareWork) (.inl (.copyAxis 2)) (.inl (.copyAxis 0)) (.inl (.copyAxis 0))) _ _ rfl
    · rfl
    · funext j;cases j with
      | inl j => cases j <;> simp [B.execute,data,Function.update]
      | inr j => fin_cases j <;> simp [B.execute,data,Function.update]
  have h2:=double_axis n 0 base ew (List.replicate n true) D
  have h3:=double_axis n 1 base ew (List.replicate (2*n) true) D
  simp only [axisData,afterAxis,ite_true,show ¬((1:Fin 3)=0) by decide,ite_false] at h2 h3
  have h:=h0.trans (h1.trans (h2.trans h3))
  simpa only [show 1+(1+((7*n+5)+(7*n+5)))=14*n+12 by omega] using h

/-- The final unmatched marker doubles Q alone, with every EOF/return charged. -/
theorem odd_end (n:ℕ) (base:Meta.Stack→List Bool) (D:List Bool) :
    Runs program (7*n+7) (.inl .first)
      (data base [true] [] [] (List.replicate n true) (List.replicate n true) D)
      (.inl .copyDepth) (data base [] [] [] (List.replicate n true) (List.replicate (2*n) true) D) := by
  have h0:Runs program 1 (.inl .first) (data base [true] [] [] (List.replicate n true) (List.replicate n true) D) (.inl .second) (data base [] [] [] (List.replicate n true) (List.replicate n true) D):=by
    apply one_base program _ _ (.pop (.inl .squareWork) (.inl .copyDepth) (.inl .second) (.inl .second)) _ _ rfl
    · rfl
    · funext j;cases j with
      | inl j => cases j <;> simp [B.execute,data,Function.update]
      | inr j => fin_cases j <;> simp [B.execute,data,Function.update]
  have h1:Runs program 1 (.inl .second) (data base [] [] [] (List.replicate n true) (List.replicate n true) D) (.inl (.copyAxis 2)) (data base [] [] [] (List.replicate n true) (List.replicate n true) D):=by
    apply one_base program _ _ (.pop (.inl .squareWork) (.inl (.copyAxis 2)) (.inl (.copyAxis 0)) (.inl (.copyAxis 0))) _ _ rfl
    · rfl
    · funext j;cases j with
      | inl j => cases j <;> simp [B.execute,data,Function.update]
      | inr j => fin_cases j <;> simp [B.execute,data,Function.update]
  have h2:=double_axis n 2 base [] (List.replicate n true) D
  simp only [axisData,afterAxis,show ¬((2:Fin 3)=0) by decide,
    show ¬((2:Fin 3)=1) by decide,ite_false] at h2
  have h:=h0.trans (h1.trans h2)
  simpa only [show 1+(1+(7*n+5))=7*n+7 by omega] using h

/-- All pairs and the possible odd marker are physically executed in order. -/
theorem loop_run (h:ℕ) (odd:Bool) (k:ℕ) (base:Meta.Stack→List Bool) (D:List Bool) :
    Runs program (loopTime k h odd) (.inl .first)
      (data base (List.replicate (2*h+tailBit odd) true) [] []
        (List.replicate (2^k) true) (List.replicate (2^k) true) D)
      (.inl .copyDepth) (data base [] [] [] (List.replicate (2^(k+h)) true)
        (List.replicate (2^(k+h+tailBit odd)) true) D) := by
  induction h generalizing k with
  | zero =>
    cases odd with
    | false =>
      change Runs program 1 (.inl .first) (data base [] [] [] _ _ D) (.inl .copyDepth) (data base [] [] [] (List.replicate (2^k) true) (List.replicate (2^k) true) D)
      apply one_base program _ _ (.pop (.inl .squareWork) (.inl .copyDepth) (.inl .second) (.inl .second)) _ _ rfl
      · rfl
      · funext j;cases j with
        | inl j => cases j <;> simp [B.execute,data,Function.update]
        | inr j => fin_cases j <;> simp [B.execute,data,Function.update]
    | true =>
      simpa only [loopTime,tailBit,ite_true,Nat.zero_mul,Nat.mul_zero,Nat.zero_add,Nat.add_zero,pow_succ',List.replicate_succ,List.replicate_zero] using odd_end (2^k) base D
  | succ h ih =>
    have h0:=pair (2^k) base (List.replicate (2*h+tailBit odd) true) D
    have h1:=ih (k+1)
    rw [←pow_succ'] at h0
    have ht:2*(h+1)+tailBit odd=(2*h+tailBit odd)+2:=by omega
    have hk:(k+1)+h=k+(h+1):=by omega
    simpa only [loopTime,ht,List.replicate_succ,hk] using h0.trans h1
end RiemannGaussian.SemiprimeD1StackAxesLoop
