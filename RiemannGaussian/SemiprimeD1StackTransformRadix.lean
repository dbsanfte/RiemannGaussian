/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransformComponents

/-! # Actual four-marker radix extraction
R is retained by a real included Copy call. Every complete block of four copied
markers produces one radix marker, and EOF is tested physically. No division
or quotient/width answer is executed or supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackTransformRadix
open SemiprimeD1StackTransform SemiprimeD1StackTransformComponents
open SemiprimeD1StackProcedureFragments (At Runs one_base)

/-- Five actual instructions consume four radius-work markers and emit one radix marker. -/
theorem radix_group (bits threshold radius square exponent work radix:List Bool) :
    Runs program 5 (.inl .radixPop0)
      (data bits threshold radius square exponent (true::true::true::true::work) [] [] radix)
      (.inl .radixPop0) (data bits threshold radius square exponent work [] [] (true::radix)) := by
  have h0:Runs program 1 (.inl .radixPop0)
      (data bits threshold radius square exponent (true::true::true::true::work) [] [] radix)
      (.inl .radixPop1) (data bits threshold radius square exponent (true::true::true::work) [] [] radix):=by
    apply one_base program _ _ (.pop .squareWork (.inl .halt) (.inl .radixPop1) (.inl .radixPop1)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  have h1:Runs program 1 (.inl .radixPop1)
      (data bits threshold radius square exponent (true::true::true::work) [] [] radix)
      (.inl .radixPop2) (data bits threshold radius square exponent (true::true::work) [] [] radix):=by
    apply one_base program _ _ (.pop .squareWork (.inl .halt) (.inl .radixPop2) (.inl .radixPop2)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  have h2:Runs program 1 (.inl .radixPop2)
      (data bits threshold radius square exponent (true::true::work) [] [] radix)
      (.inl .radixPop3) (data bits threshold radius square exponent (true::work) [] [] radix):=by
    apply one_base program _ _ (.pop .squareWork (.inl .halt) (.inl .radixPop3) (.inl .radixPop3)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  have h3:Runs program 1 (.inl .radixPop3)
      (data bits threshold radius square exponent (true::work) [] [] radix)
      (.inl .radixPush) (data bits threshold radius square exponent work [] [] radix):=by
    apply one_base program _ _ (.pop .squareWork (.inl .halt) (.inl .radixPush) (.inl .radixPush)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  have h4:Runs program 1 (.inl .radixPush)
      (data bits threshold radius square exponent work [] [] radix)
      (.inl .radixPop0) (data bits threshold radius square exponent work [] [] (true::radix)):=by
    apply one_base program _ _ (.push .radix true (.inl .radixPop0)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  exact h0.trans (h1.trans (h2.trans (h3.trans h4)))

/-- Actual quarter loop, with every group and terminal EOF pop paid. -/
theorem quarter_run (b:ℕ) (bits threshold radius square exponent radix:List Bool) :
    Runs program (5*b+1) (.inl .radixPop0)
      (data bits threshold radius square exponent (List.replicate (4*b) true) [] [] radix)
      (.inl .halt) (data bits threshold radius square exponent [] [] [] (List.replicate b true++radix)) := by
  induction b generalizing radix with
  | zero =>
    apply one_base program _ _ (.pop .squareWork (.inl .halt) (.inl .radixPop1) (.inl .radixPop1)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  | succ b ih =>
    have h0:=radix_group bits threshold radius square exponent (List.replicate (4*b) true) radix
    have h1:=ih (true::radix)
    have h:=h0.trans h1
    have hd:List.replicate b true++true::radix=List.replicate (b+1) true++radix:=by
      rw [List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [hd] at h
    have hn:4*(b+1)=4*b+4:=by omega
    simpa only [hn,List.replicate_succ,List.replicate_succ',List.append_assoc,List.singleton_append,
      show 5+(5*b+1)=5*(b+1)+1 by omega] using h

/-- The zero-width radius has one marker; its incomplete four-block emits no radix marker. -/
theorem quarter_one (bits threshold radius square exponent radix:List Bool) :
    Runs program 2 (.inl .radixPop0) (data bits threshold radius square exponent [true] [] [] radix)
      (.inl .halt) (data bits threshold radius square exponent [] [] [] radix) := by
  have h0:Runs program 1 (.inl .radixPop0) (data bits threshold radius square exponent [true] [] [] radix)
      (.inl .radixPop1) (data bits threshold radius square exponent [] [] [] radix):=by
    apply one_base program _ _ (.pop .squareWork (.inl .halt) (.inl .radixPop1) (.inl .radixPop1)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  have h1:Runs program 1 (.inl .radixPop1) (data bits threshold radius square exponent [] [] [] radix)
      (.inl .halt) (data bits threshold radius square exponent [] [] [] radix):=by
    apply one_base program _ _ (.pop .squareWork (.inl .halt) (.inl .radixPop2) (.inl .radixPop2)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  exact h0.trans h1

/-- Acquired physical R is copied before quarter extraction; original R is preserved. -/
theorem copy_radius (bits threshold radius square exponent radix:List Bool) :
    Runs program (5*radius.length+4) (.inl .radixStart)
      (data bits threshold radius square exponent [] [] [] radix) (.inl .radixPop0)
      (data bits threshold radius square exponent radius [] [] radix) := by
  have h:=copy_call 3 (data bits threshold radius square exponent [] [] [] radix) rfl
    (.inl .radixStart) (.inl .radixPop0) rfl
  have hd:Function.update (data bits threshold radius square exponent [] [] [] radix) Stack.squareWork radius=
      data bits threshold radius square exponent radius [] [] radix:=by
    funext k;cases k <;> simp [data,Function.update]
  simp only [copyInput,copyOutput,data,show ¬((3:Fin 4)=0) by decide,
    show ¬((3:Fin 4)=1) by decide,show ¬((3:Fin 4)=2) by decide,ite_false,List.append_nil] at h
  rw [hd] at h
  exact h

/-- Real positive-width radix acquisition, with no native division or quotient advice. -/
theorem radix_run (b:ℕ) (bits threshold square exponent:List Bool) :
    Runs program (25*b+5) (.inl .radixStart)
      (data bits threshold (List.replicate (4*b) true) square exponent [] [] [] [])
      (.inl .halt) (data bits threshold (List.replicate (4*b) true) square exponent [] [] [] (List.replicate b true)) := by
  have h0:=copy_radius bits threshold (List.replicate (4*b) true) square exponent []
  have h1:=quarter_run b bits threshold (List.replicate (4*b) true) square exponent []
  have h:=h0.trans h1
  simp only [List.length_replicate,List.append_nil] at h
  convert h using 1
  omega

/-- Actual zero-width radix acquisition, including its incomplete-group EOF branch. -/
theorem radix_zero (bits threshold square exponent:List Bool) :
    Runs program 11 (.inl .radixStart) (data bits threshold [true] square exponent [] [] [] [])
      (.inl .halt) (data bits threshold [true] square exponent [] [] [] []) := by
  exact (copy_radius bits threshold [true] square exponent []).trans
    (quarter_one bits threshold [true] square exponent [])
end RiemannGaussian.SemiprimeD1StackTransformRadix
