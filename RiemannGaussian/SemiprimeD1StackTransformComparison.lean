/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransformSetup

/-! # Actual physical transform stopping comparison
Both operands are copied by the real included Copy loop. Paired marker pops
decide the order and all residual work is physically cleared; no scalar order
predicate is passed to the runtime program.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackTransformComparison
open SemiprimeD1StackTransform SemiprimeD1StackTransformComponents
open SemiprimeD1StackProcedureFragments (At Runs one_base)

/-- Any literal clear loop physically consumes every current stack symbol. -/
theorem clear_loop (pc next:Label) (stack:Stack) (store:Stack→List Bool)
    (hcode:program pc=.base (.pop stack next pc pc)) :
    Runs program ((store stack).length+1) pc store next (Function.update store stack []) := by
  generalize hw:store stack=word
  induction word generalizing store with
  | nil =>
    apply one_base program _ _ (.pop stack next pc pc) _ _ hcode
    · simp [B.execute,SemiprimeD1StackBytecode.choose,hw]
    · simp [B.execute,hw]
  | cons bit word ih =>
    have h0:Runs program 1 pc store pc (Function.update store stack word):=by
      apply one_base program _ _ (.pop stack next pc pc) _ _ hcode
      · cases bit <;> simp [B.execute,SemiprimeD1StackBytecode.choose,hw]
      · simp [B.execute,hw]
    have h1:=ih (Function.update store stack word) (by simp)
    have hd:Function.update (Function.update store stack word) stack []=Function.update store stack []:=by
      funext k
      by_cases hk:k=stack
      · subst k; simp
      · simp [Function.update,hk]
    rw [hd] at h1
    have h:=h0.trans h1
    convert h using 1
    simp only [List.length_cons]
    omega

/-- Actual comparison consumes one threshold and one square marker. -/
theorem compare_pair (bits threshold radius square exponent sw tw radix:List Bool) :
    Runs program 2 (.inl .compareThreshold) (data bits threshold radius square exponent (true::sw) (true::tw) [] radix)
      (.inl .compareThreshold) (data bits threshold radius square exponent sw tw [] radix) := by
  have h0:Runs program 1 (.inl .compareThreshold) (data bits threshold radius square exponent (true::sw) (true::tw) [] radix)
      (.inl .compareSquare) (data bits threshold radius square exponent (true::sw) tw [] radix):=by
    apply one_base program _ _ (.pop .thresholdWork (.inl .clearSuccess) (.inl .compareSquare) (.inl .compareSquare)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  have h1:Runs program 1 (.inl .compareSquare) (data bits threshold radius square exponent (true::sw) tw [] radix)
      (.inl .compareThreshold) (data bits threshold radius square exponent sw tw [] radix):=by
    apply one_base program _ _ (.pop .squareWork (.inl .clearFailure) (.inl .compareThreshold) (.inl .compareThreshold)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  exact h0.trans h1

/-- Threshold exhaustion is the actual successful stopping branch. -/
theorem pairs_success (t extra:ℕ) (bits threshold radius square exponent radix:List Bool) :
    Runs program (2*t+1) (.inl .compareThreshold)
      (data bits threshold radius square exponent (List.replicate (t+extra) true) (List.replicate t true) [] radix)
      (.inl .clearSuccess) (data bits threshold radius square exponent (List.replicate extra true) [] [] radix) := by
  induction t with
  | zero =>
    apply one_base program _ _ (.pop .thresholdWork (.inl .clearSuccess) (.inl .compareSquare) (.inl .compareSquare)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  | succ t ih =>
    have h:=compare_pair bits threshold radius square exponent (List.replicate (t+extra) true) (List.replicate t true) radix
    have hh:=h.trans ih
    simpa only [Nat.succ_add,List.replicate_succ,show 2+(2*t+1)=2*(t+1)+1 by omega] using hh

/-- Square exhaustion is the actual failed stopping branch, including its physical underflow test. -/
theorem pairs_failure (s extra:ℕ) (bits threshold radius square exponent radix:List Bool) :
    Runs program (2*s+2) (.inl .compareThreshold)
      (data bits threshold radius square exponent (List.replicate s true) (List.replicate (s+extra+1) true) [] radix)
      (.inl .clearFailure) (data bits threshold radius square exponent [] (List.replicate extra true) [] radix) := by
  induction s with
  | zero =>
    have h0:Runs program 1 (.inl .compareThreshold)
        (data bits threshold radius square exponent [] (true::List.replicate extra true) [] radix)
        (.inl .compareSquare) (data bits threshold radius square exponent [] (List.replicate extra true) [] radix):=by
      apply one_base program _ _ (.pop .thresholdWork (.inl .clearSuccess) (.inl .compareSquare) (.inl .compareSquare)) _ _ rfl
      · rfl
      · funext k;cases k <;> simp [B.execute,data,Function.update]
    have h1:Runs program 1 (.inl .compareSquare)
        (data bits threshold radius square exponent [] (List.replicate extra true) [] radix)
        (.inl .clearFailure) (data bits threshold radius square exponent [] (List.replicate extra true) [] radix):=by
      apply one_base program _ _ (.pop .squareWork (.inl .clearFailure) (.inl .compareThreshold) (.inl .compareThreshold)) _ _ rfl
      · rfl
      · funext k;cases k <;> simp [B.execute,data,Function.update]
    simpa only [Nat.mul_zero,Nat.zero_add,List.replicate_zero,List.replicate_succ] using h0.trans h1
  | succ s ih =>
    have h:=compare_pair bits threshold radius square exponent (List.replicate s true) (List.replicate (s+extra+1) true) radix
    have hh:=h.trans ih
    simpa only [Nat.succ_add,List.replicate_succ,show 2+(2*s+2)=2*(s+1)+2 by omega] using hh

/-- Both comparison operands are acquired from actual retained counters by real Copy calls. -/
theorem prepare_compare (bits threshold radius square exponent radix:List Bool) :
    Runs program (5*square.length+5*threshold.length+8) (.inl .copySquare)
      (data bits threshold radius square exponent [] [] [] radix) (.inl .compareThreshold)
      (data bits threshold radius square exponent square threshold [] radix) := by
  have h0:=copy_call 1 (data bits threshold radius square exponent [] [] [] radix) rfl
    (.inl .copySquare) (.inl .copyThreshold) rfl
  have hd0:Function.update (data bits threshold radius square exponent [] [] [] radix) Stack.squareWork square=
      data bits threshold radius square exponent square [] [] radix:=by funext k;cases k <;> simp [data,Function.update]
  simp only [copyInput,copyOutput,data,show ¬((1:Fin 4)=0) by decide,
    show ¬((1:Fin 4)=2) by decide,ite_false,ite_true,List.append_nil] at h0
  rw [hd0] at h0
  have h1:=copy_call 2 (data bits threshold radius square exponent square [] [] radix) rfl
    (.inl .copyThreshold) (.inl .compareThreshold) rfl
  have hd1:Function.update (data bits threshold radius square exponent square [] [] radix) Stack.thresholdWork threshold=
      data bits threshold radius square exponent square threshold [] radix:=by funext k;cases k <;> simp [data,Function.update]
  simp only [copyInput,copyOutput,data,show ¬((2:Fin 4)=0) by decide,
    show ¬((2:Fin 4)=1) by decide,ite_false,ite_true,List.append_nil] at h1
  rw [hd1] at h1
  have h:=h0.trans h1
  convert h using 1
  omega

/-- Actual success path, including all copied operands and leftover square clearing. -/
theorem compare_success (s t:ℕ) (hs:t≤s) (bits radius exponent radix:List Bool) :
    Runs program (6*(s+t)+10) (.inl .copySquare)
      (data bits (List.replicate t true) radius (List.replicate s true) exponent [] [] [] radix)
      (.inl .radixStart) (data bits (List.replicate t true) radius (List.replicate s true) exponent [] [] [] radix) := by
  have h0:=prepare_compare bits (List.replicate t true) radius (List.replicate s true) exponent radix
  have h1:=pairs_success t (s-t) bits (List.replicate t true) radius (List.replicate s true) exponent radix
  rw [Nat.add_sub_of_le hs] at h1
  have h2:=clear_loop (.inl .clearSuccess) (.inl .radixStart) .squareWork
    (data bits (List.replicate t true) radius (List.replicate s true) exponent (List.replicate (s-t) true) [] [] radix) rfl
  have hd:Function.update (data bits (List.replicate t true) radius (List.replicate s true) exponent
        (List.replicate (s-t) true) [] [] radix) Stack.squareWork []=
      data bits (List.replicate t true) radius (List.replicate s true) exponent [] [] [] radix:=by
    funext k;cases k <;> simp [data,Function.update]
  rw [hd] at h2
  have h:=h0.trans (h1.trans h2)
  simp only [data,List.length_replicate] at h
  convert h using 1
  omega

/-- Actual failure path, including all copied operands and residual threshold clearing. -/
theorem compare_failure (s t:ℕ) (hs:s<t) (bits radius exponent radix:List Bool) :
    Runs program (6*(s+t)+10) (.inl .copySquare)
      (data bits (List.replicate t true) radius (List.replicate s true) exponent [] [] [] radix)
      (.inl .radiusPop) (data bits (List.replicate t true) radius (List.replicate s true) exponent [] [] [] radix) := by
  let extra:=t-s-1
  have ht:s+extra+1=t:=by omega
  have h0:=prepare_compare bits (List.replicate t true) radius (List.replicate s true) exponent radix
  have h1:=pairs_failure s extra bits (List.replicate t true) radius (List.replicate s true) exponent radix
  rw [ht] at h1
  have h2:=clear_loop (.inl .clearFailure) (.inl .radiusPop) .thresholdWork
    (data bits (List.replicate t true) radius (List.replicate s true) exponent [] (List.replicate extra true) [] radix) rfl
  have hd:Function.update (data bits (List.replicate t true) radius (List.replicate s true) exponent
        [] (List.replicate extra true) [] radix) Stack.thresholdWork []=
      data bits (List.replicate t true) radius (List.replicate s true) exponent [] [] [] radix:=by
    funext k;cases k <;> simp [data,Function.update]
  rw [hd] at h2
  have h:=h0.trans (h1.trans h2)
  simp only [data,List.length_replicate] at h
  convert h using 1
  omega
end RiemannGaussian.SemiprimeD1StackTransformComparison
