/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFermatComponents

/-! # Actual constant-word bit loops
All emitted bits are literal pushes. The retained metadata are untouched; work
counters are consumed one physical cell at a time, including every EOF test.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackFermatLocal
open SemiprimeD1StackFermatConstants SemiprimeD1StackFermatComponents
open SemiprimeD1StackProcedureFragments (At Runs one_base)

/-- Two real instructions consume one radius marker and write one modulus zero. -/
theorem mod_zero_bit (base:Meta.Stack→List Bool) (rw ew tmp modulus normalizer:List Bool) :
    Runs program 2 (.inl .modLoop) (data base (true::rw) ew tmp modulus normalizer)
      (.inl .modLoop) (data base rw ew tmp (false::modulus) normalizer) := by
  have h0:Runs program 1 (.inl .modLoop) (data base (true::rw) ew tmp modulus normalizer)
      (.inl .modZero) (data base rw ew tmp modulus normalizer):=by
    apply one_base program _ _ (.pop (.inl .squareWork) (.inl .modLow) (.inl .modZero) (.inl .modZero)) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr bit => cases bit <;> simp [B.execute,data,Function.update]
  have h1:Runs program 1 (.inl .modZero) (data base rw ew tmp modulus normalizer)
      (.inl .modLoop) (data base rw ew tmp (false::modulus) normalizer):=by
    apply one_base program _ _ (.push (.inr false) false (.inl .modLoop)) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr bit => cases bit <;> simp [B.execute,data,Function.update]
  exact h0.trans (h1)

/-- Two real instructions consume one residual radius marker and write one inverse zero. -/
theorem norm_zero_bit (base:Meta.Stack→List Bool) (rw ew tmp modulus normalizer:List Bool) :
    Runs program 2 (.inl .normZeros) (data base (true::rw) ew tmp modulus normalizer)
      (.inl .normZeros) (data base rw ew tmp modulus (false::normalizer)) := by
  have h0:Runs program 1 (.inl .normZeros) (data base (true::rw) ew tmp modulus normalizer)
      (.inl .normZero) (data base rw ew tmp modulus normalizer):=by
    apply one_base program _ _ (.pop (.inl .squareWork) (.inl .normLow) (.inl .normZero) (.inl .normZero)) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr bit => cases bit <;> simp [B.execute,data,Function.update]
  have h1:Runs program 1 (.inl .normZero) (data base rw ew tmp modulus normalizer)
      (.inl .normZeros) (data base rw ew tmp modulus (false::normalizer)):=by
    apply one_base program _ _ (.push (.inr true) false (.inl .normZeros)) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr bit => cases bit <;> simp [B.execute,data,Function.update]
  exact h0.trans (h1)

/-- Three real instructions consume E/R markers and write one high inverse bit. -/
theorem norm_pair (base:Meta.Stack→List Bool) (rw ew tmp modulus normalizer:List Bool) :
    Runs program 3 (.inl .normLoop) (data base (true::rw) (true::ew) tmp modulus normalizer)
      (.inl .normLoop) (data base rw ew tmp modulus (true::normalizer)) := by
  have h0:Runs program 1 (.inl .normLoop) (data base (true::rw) (true::ew) tmp modulus normalizer)
      (.inl .normOne) (data base (true::rw) ew tmp modulus normalizer):=by
    apply one_base program _ _ (.pop (.inl .thresholdWork) (.inl .normZeros) (.inl .normOne) (.inl .normOne)) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr bit => cases bit <;> simp [B.execute,data,Function.update]
  have h1:Runs program 1 (.inl .normOne) (data base (true::rw) ew tmp modulus normalizer)
      (.inl .normSubR) (data base (true::rw) ew tmp modulus (true::normalizer)):=by
    apply one_base program _ _ (.push (.inr true) true (.inl .normSubR)) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr bit => cases bit <;> simp [B.execute,data,Function.update]
  have h2:Runs program 1 (.inl .normSubR) (data base (true::rw) ew tmp modulus (true::normalizer))
      (.inl .normLoop) (data base rw ew tmp modulus (true::normalizer)):=by
    apply one_base program _ _ (.pop (.inl .squareWork) (.inl .bad) (.inl .normLoop) (.inl .normLoop)) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr bit => cases bit <;> simp [B.execute,data,Function.update]
  exact h0.trans (h1.trans (h2))

/-- All modulus gap zeros are physically emitted, including the terminal EOF test. -/
theorem mod_zeros (n:ℕ) (base:Meta.Stack→List Bool) (ew tmp modulus normalizer:List Bool) :
    Runs program (2*n+1) (.inl .modLoop) (data base (List.replicate n true) ew tmp modulus normalizer)
      (.inl .modLow) (data base [] ew tmp (List.replicate n false++modulus) normalizer) := by
  induction n generalizing modulus with
  | zero =>
    apply one_base program _ _ (.pop (.inl .squareWork) (.inl .modLow) (.inl .modZero) (.inl .modZero)) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr bit => cases bit <;> simp [B.execute,data,Function.update]
  | succ n ih =>
    have h:=(mod_zero_bit base (List.replicate n true) ew tmp modulus normalizer).trans (ih (false::modulus))
    have hd:List.replicate n false++false::modulus=List.replicate (n+1) false++modulus:=by
      rw [List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [hd] at h
    simpa only [List.replicate_succ,show 2+(2*n+1)=2*(n+1)+1 by omega] using h

/-- All normalizer low gap zeros are physically emitted after the actual high-one loop. -/
theorem norm_zeros (n:ℕ) (base:Meta.Stack→List Bool) (ew tmp modulus normalizer:List Bool) :
    Runs program (2*n+1) (.inl .normZeros) (data base (List.replicate n true) ew tmp modulus normalizer)
      (.inl .normLow) (data base [] ew tmp modulus (List.replicate n false++normalizer)) := by
  induction n generalizing normalizer with
  | zero =>
    apply one_base program _ _ (.pop (.inl .squareWork) (.inl .normLow) (.inl .normZero) (.inl .normZero)) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr bit => cases bit <;> simp [B.execute,data,Function.update]
  | succ n ih =>
    have h:=(norm_zero_bit base (List.replicate n true) ew tmp modulus normalizer).trans (ih (false::normalizer))
    have hd:List.replicate n false++false::normalizer=List.replicate (n+1) false++normalizer:=by
      rw [List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [hd] at h
    simpa only [List.replicate_succ,show 2+(2*n+1)=2*(n+1)+1 by omega] using h

/-- E high bits and the residual gap are acquired by the actual two-counter cancellation loop. -/
theorem norm_pairs (E gap:ℕ) (base:Meta.Stack→List Bool) (tmp modulus normalizer:List Bool) :
    Runs program (3*E+1) (.inl .normLoop)
      (data base (List.replicate (E+gap) true) (List.replicate E true) tmp modulus normalizer)
      (.inl .normZeros) (data base (List.replicate gap true) [] tmp modulus (List.replicate E true++normalizer)) := by
  induction E generalizing normalizer with
  | zero =>
    apply one_base program _ _ (.pop (.inl .thresholdWork) (.inl .normZeros) (.inl .normOne) (.inl .normOne)) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr bit => cases bit <;> simp [B.execute,data,Function.update]
  | succ E ih =>
    have h:=(norm_pair base (List.replicate (E+gap) true) (List.replicate E true) tmp modulus normalizer).trans
      (ih (true::normalizer))
    have hd:List.replicate E true++true::normalizer=List.replicate (E+1) true++normalizer:=by
      rw [List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [hd] at h
    simpa only [Nat.succ_add,List.replicate_succ,show 3+(3*E+1)=3*(E+1)+1 by omega] using h
end RiemannGaussian.SemiprimeD1StackFermatLocal
