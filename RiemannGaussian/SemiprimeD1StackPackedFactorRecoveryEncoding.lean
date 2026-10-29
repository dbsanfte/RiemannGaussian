/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecovery
/-! # Complete physical recovery views and exact binary stage words -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryEncoding
open SemiprimeD1StackPackedFactorRecovery SemiprimeBitArithmetic SemiprimeBitDivision
/-- All four additional words, with no discarded scratch. -/
def words (small large status scratch : List Bool) : Aux→List Bool
  | .small=>small | .large=>large | .status=>status | .scratch=>scratch
/-- Full readout, metadata, arithmetic and factor bank at every stage. -/
def view (r : R.Stack→List Bool) (m : SemiprimeD1StackBinarySquareRoot.M.Stack→List Bool)
    (a : A.Stack→List Bool) (x : X.Stack→List Bool) (w : W.Stack→List Bool)
    (v : SemiprimeD1StackBinarySquareRoot.Aux→List Bool) (u : Aux→List Bool) : Stack→List Bool :=
  bank r (SemiprimeD1StackBinarySquareRoot.bank m a x w v) u
/-- Literal raw square word emitted by the actual multiplier. -/
def squareWord (s : List Bool) : List Bool := (mulBits s s).bits
/-- Two physically pushed low FALSE bits implement multiplication by four. -/
def fourWord (n : List Bool) : List Bool := false::false::n
/-- Exact actual subtraction report, including the physical underflow bit. -/
def discriminantReport (n s : List Bool) : SubReport := subBits (squareWord s) (fourWord n) false
/-- Binary discriminant bytes, never expanded into unary. -/
def discriminant (n s : List Bool) : List Bool := (discriminantReport n s).result.bits
/-- Actual frozen whole square-root output on the acquired discriminant. -/
def rootWord (n s : List Bool) : List Bool :=
  SemiprimeD1StackBinarySquareRootArithmetic.output (discriminant n s)
/-- Exact actual lower-numerator report, including the physical borrow. -/
def minusReport (s root : List Bool) : SubReport := subBits s root false
/-- Exact actual upper numerator, emitted by the real binary adder. -/
def plusWord (s root : List Bool) : List Bool := (addBits s root false).bits
/-- Real reversal and trim compact precisely the physically popped low-bit tail. -/
def halfWord (numerator : List Bool) : List Bool :=
  SemiprimeD1StackReduceExecution.trimReverse numerator.tail.reverse
/-- Exact update of one actual retained readout role. -/
theorem bank_readout (r : R.Stack→List Bool) (s : S.Stack→List Bool) (u : Aux→List Bool)
    (k : R.Stack) (xs : List Bool) :
    Function.update (bank r s u) (readout k) xs=bank (Function.update r k xs) s u :=
  Sum.update_elim_inl
/-- Exact update of one actual square-root-bank role. -/
theorem bank_squareRoot (r : R.Stack→List Bool) (s : S.Stack→List Bool) (u : Aux→List Bool)
    (k : S.Stack) (xs : List Bool) :
    Function.update (bank r s u) (squareRoot k) xs=bank r (Function.update s k xs) u := by
  dsimp only [bank,squareRoot]
  rw [Sum.update_elim_inr,Sum.update_elim_inl]
/-- Exact update of one dedicated factor/status/scratch role. -/
theorem bank_aux (r : R.Stack→List Bool) (s : S.Stack→List Bool) (u : Aux→List Bool)
    (k : Aux) (xs : List Bool) :
    Function.update (bank r s u) (aux k) xs=bank r s (Function.update u k xs) := by
  dsimp only [bank,aux]
  rw [Sum.update_elim_inr,Sum.update_elim_inr]
/-- Each dedicated-word update retains the other three physical words. -/
theorem words_update (small large status scratch xs : List Bool) (k : Aux) :
    Function.update (words small large status scratch) k xs=
      words (if k=.small then xs else small) (if k=.large then xs else large)
        (if k=.status then xs else status) (if k=.scratch then xs else scratch) := by
  funext q;cases k <;> cases q <;> rfl
/-- A real shared-adder update preserves every foreign bank. -/
theorem view_adder (r m a x w v u) (k : A.Stack) (xs : List Bool) :
    Function.update (view r m a x w v u) (adder k) xs=view r m (Function.update a k xs) x w v u := by
  change Function.update (bank r _ u) (squareRoot (S.adder k)) xs=_
  rw [bank_squareRoot,SemiprimeD1StackBinarySquareRootEncoding.bank_adder]
  rfl
/-- A real shared-multiplier update preserves every foreign bank. -/
theorem view_multiply (r m a x w v u) (k : X.Stack) (xs : List Bool) :
    Function.update (view r m a x w v u) (multiply k) xs=view r m a (Function.update x k xs) w v u := by
  change Function.update (bank r _ u) (squareRoot (S.multiply k)) xs=_
  rw [bank_squareRoot,SemiprimeD1StackBinarySquareRootEncoding.bank_multiply]
  rfl
/-- A real shared-comparison update preserves every foreign bank. -/
theorem view_compare (r m a x w v u) (k : W.Stack) (xs : List Bool) :
    Function.update (view r m a x w v u) (compare k) xs=view r m a x (Function.update w k xs) v u := by
  change Function.update (bank r _ u) (squareRoot (S.compare k)) xs=_
  rw [bank_squareRoot,SemiprimeD1StackBinarySquareRootEncoding.bank_compare]
  rfl
/-- A real retained-metadata update preserves all arithmetic and output words. -/
theorem view_metadata (r m a x w v u) (k : SemiprimeD1StackBinarySquareRoot.M.Stack) (xs : List Bool) :
    Function.update (view r m a x w v u) (squareRoot (SemiprimeD1StackBinarySquareRoot.metadata k)) xs=
      view r (Function.update m k xs) a x w v u := by
  change Function.update (bank r _ u) (squareRoot _) xs=_
  rw [bank_squareRoot,SemiprimeD1StackBinarySquareRootEncoding.bank_metadata]
  rfl
/-- A dedicated output update preserves all55 included physical words. -/
theorem view_aux (r m a x w v u) (k : Aux) (xs : List Bool) :
    Function.update (view r m a x w v u) (aux k) xs=view r m a x w v (Function.update u k xs) :=
  bank_aux r _ u k xs
/-- Both final factor encodings are compact after the actual reversal/trim. -/
theorem halfWord_compact (numerator : List Bool) : SemiprimeSourceCompactBits.Compact (halfWord numerator) :=
  SemiprimeD1StackReduceExecution.trimReverse_compact _
/-- Physical compaction preserves the actual low-bit-pop quotient. -/
theorem halfWord_value (numerator : List Bool) : bitValue (halfWord numerator)=bitValue numerator.tail := by
  rw [halfWord,SemiprimeD1StackReduceExecution.trimReverse_value,List.reverse_reverse]
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryEncoding
