/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBinarySquareRoot
/-! # Exact whole33-word square-root boundaries and physical updates -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackBinarySquareRootEncoding
open SemiprimeD1StackBinarySquareRoot
namespace E
export SemiprimeD1StackBinarySquareRootArithmetic (trial square rejects nextWord wordLoop output)
end E
/-- Both actual additional words, with no implicit discarded workspace. -/
def words (root out : List Bool) : Aux→List Bool
  | .root => root | .output => out
/-- Whole retained13-word metadata bank; only its descending base is mutable. -/
def retained (bits p : List Bool) : M.Stack→List Bool :=
  Function.update (SemiprimeD1StackPackedRootMetadataEncoding.result bits) (M.aux .base) p
/-- Every clean iteration boundary has all18 private arithmetic words empty. -/
def idle (bits p r : List Bool) : Stack→List Bool :=
  bank (retained bits p) (fun _ => []) (fun _ => []) (fun _ => []) (words r [])
/-- Actual post-metadata ready entry, before the first greedy-bit trial. -/
def ready (bits : List Bool) : C.State Stack Label :=
  ⟨some (ctl .rootCopy),none,none,idle bits (SemiprimeD1StackPackedRootMetadataEncoding.baseWord bits.length) [],[]⟩
/-- Exact full compared bank, before its actual borrow flag is consumed. -/
def tested (bits p r : List Bool) : Stack→List Bool :=
  bank (retained bits p) (A.store [] [] [] (E.trial r p))
    (X.payload [] [] [] [] (E.square r p) [] [] [] [])
    (W.store [] [] [] [] [E.rejects bits r p]) (words r [])
/-- After real flag consumption the only nonempty private words are trial and square. -/
def selected (bits p r newRoot : List Bool) : Stack→List Bool :=
  bank (retained bits p) (A.store [] [] [] (E.trial r p))
    (X.payload [] [] [] [] (E.square r p) [] [] [] [])
    (fun _ => []) (words newRoot [])
/-- Every metadata word except the consumed descending base is retained at halt. -/
def result (bits : List Bool) : Stack→List Bool :=
  bank (retained bits []) (fun _ => []) (fun _ => []) (fun _ => []) (words [] (E.output bits))
/-- Genuine clean halt, with all33 roles and empty real return stack specified. -/
def done (bits : List Bool) : C.State Stack Label := ⟨none,none,none,result bits,[]⟩
/-- Exact actual update to one retained metadata role. -/
theorem bank_metadata (m : M.Stack→List Bool) (a : A.Stack→List Bool) (x : X.Stack→List Bool)
    (w : W.Stack→List Bool) (u : Aux→List Bool) (k : M.Stack) (xs : List Bool) :
    Function.update (bank m a x w u) (metadata k) xs=bank (Function.update m k xs) a x w u := by
  exact Sum.update_elim_inl
/-- Exact actual update to one candidate-adder role. -/
theorem bank_adder (m : M.Stack→List Bool) (a : A.Stack→List Bool) (x : X.Stack→List Bool)
    (w : W.Stack→List Bool) (u : Aux→List Bool) (k : A.Stack) (xs : List Bool) :
    Function.update (bank m a x w u) (adder k) xs=bank m (Function.update a k xs) x w u := by
  dsimp only [bank,adder]
  rw [Sum.update_elim_inr,Sum.update_elim_inl]
/-- Exact actual update to one square-multiplier role. -/
theorem bank_multiply (m : M.Stack→List Bool) (a : A.Stack→List Bool) (x : X.Stack→List Bool)
    (w : W.Stack→List Bool) (u : Aux→List Bool) (k : X.Stack) (xs : List Bool) :
    Function.update (bank m a x w u) (multiply k) xs=bank m a (Function.update x k xs) w u := by
  dsimp only [bank,multiply]
  rw [Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inl]
/-- Exact actual update to one comparison role. -/
theorem bank_compare (m : M.Stack→List Bool) (a : A.Stack→List Bool) (x : X.Stack→List Bool)
    (w : W.Stack→List Bool) (u : Aux→List Bool) (k : W.Stack) (xs : List Bool) :
    Function.update (bank m a x w u) (compare k) xs=bank m a x (Function.update w k xs) u := by
  dsimp only [bank,SemiprimeD1StackBinarySquareRoot.compare]
  rw [Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inl]
/-- Exact actual update to either additional word. -/
theorem bank_aux (m : M.Stack→List Bool) (a : A.Stack→List Bool) (x : X.Stack→List Bool)
    (w : W.Stack→List Bool) (u : Aux→List Bool) (k : Aux) (xs : List Bool) :
    Function.update (bank m a x w u) (aux k) xs=bank m a x w (Function.update u k xs) := by
  dsimp only [bank,aux]
  rw [Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inr]
/-- Both extra-word updates are literal raw-word updates. -/
theorem words_update (r out xs : List Bool) (k : Aux) :
    Function.update (words r out) k xs=words (if k=.root then xs else r) (if k=.output then xs else out) := by
  funext q
  cases k <;> cases q <;> rfl
/-- Shifting the binary power changes only the actual metadata base word. -/
theorem retained_update (bits p q : List Bool) :
    Function.update (retained bits p) (M.aux .base) q=retained bits q :=
  by funext k;by_cases h:k=M.aux .base <;> simp [retained,Function.update,h]
/-- The whole real metadata result is exactly the original ready bank's source. -/
theorem retained_original (bits : List Bool) :
    retained bits (SemiprimeD1StackPackedRootMetadataEncoding.baseWord bits.length)=
      SemiprimeD1StackPackedRootMetadataEncoding.result bits :=
  Function.update_eq_self _ _
/-- Every actual trial retains the original binary operand verbatim. -/
theorem retained_input (bits p : List Bool) : retained bits p (M.boot .input)=bits := rfl
/-- The borrowed copy scratch is actually empty at every iteration boundary. -/
theorem retained_scratch (bits p : List Bool) : retained bits p (M.aux .copyScratch)=[] := rfl
end RiemannGaussian.SemiprimeD1StackBinarySquareRootEncoding
