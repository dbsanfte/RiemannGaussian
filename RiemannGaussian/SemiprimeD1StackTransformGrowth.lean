/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransformComponents

/-! # Actual marker doubling and quadrupling for transform acquisition
Every output marker is a literal push. Original input and threshold are retained;
work is consumed/restored physically rather than expanded by a native power.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackTransformGrowth
open SemiprimeD1StackTransform SemiprimeD1StackTransformComponents
open SemiprimeD1StackProcedureFragments (At Runs one_base)

/-- Three actual instructions replace one radius marker by two work markers. -/
theorem radius_bit (bits threshold radius square exponent tmp radix:List Bool) :
    Runs program 3 (.inl .radiusPop) (data bits threshold (true::radius) square exponent [] [] tmp radix)
      (.inl .radiusPop) (data bits threshold radius square exponent [] [] (true::true::tmp) radix) := by
  have h0:Runs program 1 (.inl .radiusPop) (data bits threshold (true::radius) square exponent [] [] tmp radix)
      (.inl .radiusPush1) (data bits threshold radius square exponent [] [] tmp radix):=by
    apply one_base program _ _ (.pop .radius (.inl .radiusRestore) (.inl .radiusPush1) (.inl .radiusPush1)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  have h1:Runs program 1 (.inl .radiusPush1) (data bits threshold radius square exponent [] [] tmp radix)
      (.inl .radiusPush2) (data bits threshold radius square exponent [] [] (true::tmp) radix):=by
    apply one_base program _ _ (.push .temporary true (.inl .radiusPush2)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  have h2:Runs program 1 (.inl .radiusPush2) (data bits threshold radius square exponent [] [] (true::tmp) radix)
      (.inl .radiusPop) (data bits threshold radius square exponent [] [] (true::true::tmp) radix):=by
    apply one_base program _ _ (.push .temporary true (.inl .radiusPop)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  exact h0.trans (h1.trans (h2))

/-- Two actual instructions restore one radius marker from work. -/
theorem radius_restore_bit (bits threshold radius square exponent tmp radix:List Bool) :
    Runs program 2 (.inl .radiusRestore) (data bits threshold radius square exponent [] [] (true::tmp) radix)
      (.inl .radiusRestore) (data bits threshold (true::radius) square exponent [] [] tmp radix) := by
  have h0:Runs program 1 (.inl .radiusRestore) (data bits threshold radius square exponent [] [] (true::tmp) radix)
      (.inl .radiusRestorePush) (data bits threshold radius square exponent [] [] tmp radix):=by
    apply one_base program _ _ (.pop .temporary (.inl .squarePop) (.inl .radiusRestorePush) (.inl .radiusRestorePush)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  have h1:Runs program 1 (.inl .radiusRestorePush) (data bits threshold radius square exponent [] [] tmp radix)
      (.inl .radiusRestore) (data bits threshold (true::radius) square exponent [] [] tmp radix):=by
    apply one_base program _ _ (.push .radius true (.inl .radiusRestore)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  exact h0.trans (h1)

/-- Five actual instructions replace one square marker by four work markers. -/
theorem square_bit (bits threshold radius square exponent tmp radix:List Bool) :
    Runs program 5 (.inl .squarePop) (data bits threshold radius (true::square) exponent [] [] tmp radix)
      (.inl .squarePop) (data bits threshold radius square exponent [] [] (true::true::true::true::tmp) radix) := by
  have h0:Runs program 1 (.inl .squarePop) (data bits threshold radius (true::square) exponent [] [] tmp radix)
      (.inl .squarePush1) (data bits threshold radius square exponent [] [] tmp radix):=by
    apply one_base program _ _ (.pop .square (.inl .squareRestore) (.inl .squarePush1) (.inl .squarePush1)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  have h1:Runs program 1 (.inl .squarePush1) (data bits threshold radius square exponent [] [] tmp radix)
      (.inl .squarePush2) (data bits threshold radius square exponent [] [] (true::tmp) radix):=by
    apply one_base program _ _ (.push .temporary true (.inl .squarePush2)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  have h2:Runs program 1 (.inl .squarePush2) (data bits threshold radius square exponent [] [] (true::tmp) radix)
      (.inl .squarePush3) (data bits threshold radius square exponent [] [] (true::true::tmp) radix):=by
    apply one_base program _ _ (.push .temporary true (.inl .squarePush3)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  have h3:Runs program 1 (.inl .squarePush3) (data bits threshold radius square exponent [] [] (true::true::tmp) radix)
      (.inl .squarePush4) (data bits threshold radius square exponent [] [] (true::true::true::tmp) radix):=by
    apply one_base program _ _ (.push .temporary true (.inl .squarePush4)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  have h4:Runs program 1 (.inl .squarePush4) (data bits threshold radius square exponent [] [] (true::true::true::tmp) radix)
      (.inl .squarePop) (data bits threshold radius square exponent [] [] (true::true::true::true::tmp) radix):=by
    apply one_base program _ _ (.push .temporary true (.inl .squarePop)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4))))

/-- Two actual instructions restore one square marker from work. -/
theorem square_restore_bit (bits threshold radius square exponent tmp radix:List Bool) :
    Runs program 2 (.inl .squareRestore) (data bits threshold radius square exponent [] [] (true::tmp) radix)
      (.inl .squareRestore) (data bits threshold radius (true::square) exponent [] [] tmp radix) := by
  have h0:Runs program 1 (.inl .squareRestore) (data bits threshold radius square exponent [] [] (true::tmp) radix)
      (.inl .squareRestorePush) (data bits threshold radius square exponent [] [] tmp radix):=by
    apply one_base program _ _ (.pop .temporary (.inl .incExponent) (.inl .squareRestorePush) (.inl .squareRestorePush)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  have h1:Runs program 1 (.inl .squareRestorePush) (data bits threshold radius square exponent [] [] tmp radix)
      (.inl .squareRestore) (data bits threshold radius (true::square) exponent [] [] tmp radix):=by
    apply one_base program _ _ (.push .square true (.inl .squareRestore)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  exact h0.trans (h1)

/-- The actual radius-consumption loop writes exactly two markers per input marker. -/
theorem radius_consume (n m:ℕ) (bits threshold square exponent radix:List Bool) :
    Runs program (3*n+1) (.inl .radiusPop)
      (data bits threshold (List.replicate n true) square exponent [] [] (List.replicate m true) radix)
      (.inl .radiusRestore)
      (data bits threshold [] square exponent [] [] (List.replicate (2*n+m) true) radix) := by
  induction n generalizing m with
  | zero =>
    apply one_base program _ _ (.pop .radius (.inl .radiusRestore) (.inl .radiusPush1) (.inl .radiusPush1)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  | succ n ih =>
    have hi:=ih (m+2)
    have hn:2*n+(m+2)=2*(n+1)+m:=by omega
    rw [hn] at hi
    simp only [List.replicate_succ] at hi
    have h:=(radius_bit bits threshold (List.replicate n true) square exponent (List.replicate m true) radix).trans hi
    simpa only [List.replicate_succ,show 3+(3*n+1)=3*(n+1)+1 by omega] using h

/-- Actual radius restoration consumes every work marker and retains the doubled radius. -/
theorem radius_restore (n r:ℕ) (bits threshold square exponent radix:List Bool) :
    Runs program (2*n+1) (.inl .radiusRestore)
      (data bits threshold (List.replicate r true) square exponent [] [] (List.replicate n true) radix)
      (.inl .squarePop) (data bits threshold (List.replicate (n+r) true) square exponent [] [] [] radix) := by
  induction n generalizing r with
  | zero =>
    apply one_base program _ _ (.pop .temporary (.inl .squarePop) (.inl .radiusRestorePush) (.inl .radiusRestorePush)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  | succ n ih =>
    have hi:=ih (r+1)
    have hn:n+(r+1)=(n+1)+r:=by omega
    rw [hn] at hi
    simp only [List.replicate_succ] at hi
    have h:=(radius_restore_bit bits threshold (List.replicate r true) square exponent (List.replicate n true) radix).trans hi
    simpa only [List.replicate_succ,show 2+(2*n+1)=2*(n+1)+1 by omega] using h

/-- The actual square-consumption loop writes four physical markers per square marker. -/
theorem square_consume (n m:ℕ) (bits threshold radius exponent radix:List Bool) :
    Runs program (5*n+1) (.inl .squarePop)
      (data bits threshold radius (List.replicate n true) exponent [] [] (List.replicate m true) radix)
      (.inl .squareRestore)
      (data bits threshold radius [] exponent [] [] (List.replicate (4*n+m) true) radix) := by
  induction n generalizing m with
  | zero =>
    apply one_base program _ _ (.pop .square (.inl .squareRestore) (.inl .squarePush1) (.inl .squarePush1)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  | succ n ih =>
    have hi:=ih (m+4)
    have hn:4*n+(m+4)=4*(n+1)+m:=by omega
    rw [hn] at hi
    simp only [List.replicate_succ] at hi
    have h:=(square_bit bits threshold radius (List.replicate n true) exponent (List.replicate m true) radix).trans hi
    simpa only [List.replicate_succ,show 5+(5*n+1)=5*(n+1)+1 by omega] using h

/-- Actual square restoration consumes every newly acquired work marker. -/
theorem square_restore (n s:ℕ) (bits threshold radius exponent radix:List Bool) :
    Runs program (2*n+1) (.inl .squareRestore)
      (data bits threshold radius (List.replicate s true) exponent [] [] (List.replicate n true) radix)
      (.inl .incExponent) (data bits threshold radius (List.replicate (n+s) true) exponent [] [] [] radix) := by
  induction n generalizing s with
  | zero =>
    apply one_base program _ _ (.pop .temporary (.inl .incExponent) (.inl .squareRestorePush) (.inl .squareRestorePush)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  | succ n ih =>
    have hi:=ih (s+1)
    have hn:n+(s+1)=(n+1)+s:=by omega
    rw [hn] at hi
    simp only [List.replicate_succ] at hi
    have h:=(square_restore_bit bits threshold radius (List.replicate s true) exponent (List.replicate n true) radix).trans hi
    simpa only [List.replicate_succ,show 2+(2*n+1)=2*(n+1)+1 by omega] using h

/-- One actual failure iteration doubles R, quadruples square and increments the exponent marker stack. -/
theorem grow (r s:ℕ) (bits threshold exponent radix:List Bool) :
    Runs program (7*r+13*s+5) (.inl .radiusPop)
      (data bits threshold (List.replicate r true) (List.replicate s true) exponent [] [] [] radix)
      (.inl .copySquare)
      (data bits threshold (List.replicate (2*r) true) (List.replicate (4*s) true) (true::exponent) [] [] [] radix) := by
  have h0:=radius_consume r 0 bits threshold (List.replicate s true) exponent radix
  have h1:=radius_restore (2*r) 0 bits threshold (List.replicate s true) exponent radix
  have h2:=square_consume s 0 bits threshold (List.replicate (2*r) true) exponent radix
  have h3:=square_restore (4*s) 0 bits threshold (List.replicate (2*r) true) exponent radix
  simp only [Nat.add_zero,List.replicate_zero] at h0 h1 h2 h3
  have h4:Runs program 1 (.inl .incExponent)
      (data bits threshold (List.replicate (2*r) true) (List.replicate (4*s) true) exponent [] [] [] radix)
      (.inl .copySquare)
      (data bits threshold (List.replicate (2*r) true) (List.replicate (4*s) true) (true::exponent) [] [] [] radix):=by
    apply one_base program _ _ (.push .exponent true (.inl .copySquare)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  have h:=h0.trans (h1.trans (h2.trans (h3.trans h4)))
  convert h using 1
  omega
end RiemannGaussian.SemiprimeD1StackTransformGrowth
