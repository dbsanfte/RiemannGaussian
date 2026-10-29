/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBinarySquareRootPrimitives
/-! # Exact real copy/adapt stages of one greedy binary square-root test -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackBinarySquareRootCalls
open SemiprimeD1StackBinarySquareRoot SemiprimeD1StackBinarySquareRootEncoding
open SemiprimeD1StackBinarySquareRootPrimitives SemiprimeD1StackProcedureTrace
/-- Actual clean adder-source preparation copies the old root and actual power. -/
theorem operands_call (bits p r : List Bool) :
    Runs program ((5*r.length+4)+(5*p.length+4)) (ctl .rootCopy) (idle bits p r) (ctl .add)
      (bank (retained bits p) (A.store r p [] []) (fun _ => []) (fun _ => []) (words r [])) := by
  have h0:=copy_call .root (ctl .rootCopy) (ctl .powerCopy) rfl (idle bits p r) r [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (idle bits p r) (adder .left) (r++[])) at h0
  have e0 : Function.update (fun _ : A.Stack => []) .left r=A.store r [] [] [] := by
    funext k;cases k <;> rfl
  dsimp only [idle] at h0
  rw [List.append_nil,bank_adder,e0] at h0
  have h1:=copy_call .power (ctl .powerCopy) (ctl .add) rfl
    (bank (retained bits p) (A.store r [] [] []) (fun _ => []) (fun _ => []) (words r [])) p [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update _ (adder .right) (p++[])) at h1
  rw [List.append_nil,bank_adder,SemiprimeD1StackAdder.store_right] at h1
  exact join h0 h1
/-- Real trial copies prepare BOTH multiplier operands; the adder result is retained. -/
theorem square_operands_call (bits p r : List Bool) :
    Runs program ((5*(E.trial r p).length+4)+(5*(E.trial r p).length+4))
      (ctl .trialInputCopy)
      (bank (retained bits p) (A.store [] [] [] (E.trial r p)) (fun _ => []) (fun _ => []) (words r []))
      (ctl .square)
      (bank (retained bits p) (A.store [] [] [] (E.trial r p))
        (X.payload (E.trial r p) (E.trial r p) [] [] [] [] [] [] []) (fun _ => []) (words r [])) := by
  let t:=E.trial r p
  let m:=retained bits p
  let a:=A.store [] [] [] t
  have h0:=copy_call .trialInput (ctl .trialInputCopy) (ctl .trialFactorCopy) rfl
    (bank m a (fun _ => []) (fun _ => []) (words r [])) t [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update _ (multiply X.input) (t++[])) at h0
  have e0 : Function.update (fun _ : X.Stack => []) X.input t=X.payload t [] [] [] [] [] [] [] [] := by
    funext k
    rcases k with k|k|k
    · cases k <;> rfl
    · fin_cases k <;> rfl
    · cases k <;> rfl
  rw [List.append_nil,bank_multiply,e0] at h0
  have h1:=copy_call .trialFactor (ctl .trialFactorCopy) (ctl .square) rfl
    (bank m a (X.payload t [] [] [] [] [] [] [] []) (fun _ => []) (words r [])) t [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update _ (multiply X.factor) (t++[])) at h1
  rw [List.append_nil,bank_multiply,SemiprimeD1StackMultiplierExecution.payload_ys] at h1
  exact join h0 h1
/-- Real original-D and actual-square copies prepare the numeric comparison. -/
theorem compare_operands_call (bits p r : List Bool) :
    Runs program ((5*bits.length+4)+(5*(E.square r p).length+4))
      (ctl .discriminantCopy)
      (bank (retained bits p) (A.store [] [] [] (E.trial r p))
        (X.payload [] [] [] [] (E.square r p) [] [] [] []) (fun _ => []) (words r []))
      (ctl .compare)
      (bank (retained bits p) (A.store [] [] [] (E.trial r p))
        (X.payload [] [] [] [] (E.square r p) [] [] [] [])
        (W.store bits (E.square r p) [] [] []) (words r [])) := by
  let m:=retained bits p
  let a:=A.store [] [] [] (E.trial r p)
  let x:=X.payload [] [] [] [] (E.square r p) [] [] [] []
  have h0:=copy_call .discriminant (ctl .discriminantCopy) (ctl .squareCopy) rfl
    (bank m a x (fun _ => []) (words r [])) bits [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update _ (SemiprimeD1StackBinarySquareRoot.compare (.inl .left)) (bits++[])) at h0
  have e0 : Function.update (fun _ : W.Stack => []) (.inl .left) bits=W.store bits [] [] [] [] := by
    funext k
    rcases k with k|k
    · cases k <;> rfl
    · cases k;rfl
  rw [List.append_nil,bank_compare,e0] at h0
  have h1:=copy_call .square (ctl .squareCopy) (ctl .compare) rfl
    (bank m a x (W.store bits [] [] [] []) (words r [])) (E.square r p) [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update _ (SemiprimeD1StackBinarySquareRoot.compare (.inl .right)) (_++[])) at h1
  have e1 : Function.update (W.store bits [] [] [] []) (.inl .right) (E.square r p)=W.store bits (E.square r p) [] [] [] := by
    funext k
    rcases k with k|k
    · cases k <;> rfl
    · cases k;rfl
  rw [List.append_nil,bank_compare,e1] at h1
  exact join h0 h1
/-- Exact own clock for all arithmetic and copy calls before the decision. -/
def testTime (bits p r : List Bool) : ℕ :=
  ((5*r.length+4)+(5*p.length+4))+addTime r p+
  ((5*(E.trial r p).length+4)+(5*(E.trial r p).length+4))+
  multiplyTime (E.trial r p) (E.trial r p)+
  ((5*bits.length+4)+(5*(E.square r p).length+4))+compareTime bits (E.square r p)
/-- Complete real trial preparation, square and comparison from a clean boundary. -/
theorem test_call (bits p r : List Bool) :
    Runs program (testTime bits p r) (ctl .rootCopy) (idle bits p r) (ctl .decide) (tested bits p r) := by
  have h0:=operands_call bits p r
  have h1:=add_call (retained bits p) (fun _ => []) (fun _ => []) (words r []) r p
  have h2:=square_operands_call bits p r
  have h3:=multiply_call (retained bits p) (A.store [] [] [] (E.trial r p)) (fun _ => []) (words r []) r p
  have h4:=compare_operands_call bits p r
  have h5:=compare_call (retained bits p) (A.store [] [] [] (E.trial r p))
    (X.payload [] [] [] [] (E.square r p) [] [] [] []) (words r []) bits (E.square r p)
  exact join (join (join (join (join h0 h1) h2) h3) h4) h5
end RiemannGaussian.SemiprimeD1StackBinarySquareRootCalls
