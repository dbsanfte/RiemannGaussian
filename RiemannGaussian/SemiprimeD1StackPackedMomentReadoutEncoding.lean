/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedMomentReadout
/-! # Exact22-word count/sum readout views and compact output bytes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedMomentReadoutEncoding
open SemiprimeD1StackPackedMomentReadout
/-- The TRUE digit width is actually acquired by metadata from the N input. -/
def width (bits : List Bool) : List Bool := List.replicate bits.length true
/-- Only two literal indices, never an externally supplied offset. -/
def index (high : Bool) : List Bool := if high then [true] else []
/-- Exact proof-side byte result of the actually included radix source. -/
def moment (bits scalar : List Bool) (high : Bool) : List Bool :=
  SemiprimeD1StackRadixDigitExecution.result scalar (width bits) (index high)
/-- Actual destination for the low/high block. -/
def target (high : Bool) : Aux := if high then .sum else .count
/-- Entire acquired metadata bank is retained during both digit calls. -/
def metadataResult (bits : List Bool) : M.Stack→List Bool := SemiprimeD1StackPackedRootMetadataEncoding.result bits
/-- Actual real-metadata-ready continuation, with no supplied width/moments. -/
def ready (bits scalar : List Bool) : C.State Stack Label :=
  ⟨some (ctl (.copyWidth false)),none,none,bank (metadataResult bits) (fun _ => []) (words scalar [] []),[]⟩
/-- Full source result retains N, every metadata word and the original scalar. -/
def result (bits scalar : List Bool) : Stack→List Bool :=
  bank (metadataResult bits) (fun _ => []) (words scalar (moment bits scalar false) (moment bits scalar true))
/-- True final halt, with all six radix/private roles and the real frame stack empty. -/
def done (bits scalar : List Bool) : C.State Stack Label := ⟨none,none,none,result bits scalar,[]⟩
/-- Exact physical update to one of the six actual radix-source words. -/
theorem bank_digit (m : M.Stack→List Bool) (d : D.Stack→List Bool) (u : Aux→List Bool)
    (k : D.Stack) (xs : List Bool) :
    Function.update (bank m d u) (digit k) xs=bank m (Function.update d k xs) u := by
  dsimp only [bank,digit]
  rw [Sum.update_elim_inr,Sum.update_elim_inl]
/-- Exact physical update to one actual retained moment output. -/
theorem bank_aux (m : M.Stack→List Bool) (d : D.Stack→List Bool) (u : Aux→List Bool)
    (k : Aux) (xs : List Bool) :
    Function.update (bank m d u) (aux k) xs=bank m d (Function.update u k xs) := by
  dsimp only [bank,aux]
  rw [Sum.update_elim_inr,Sum.update_elim_inr]
/-- Full zeroed six-word bank has the literal actual radix-store encoding. -/
theorem empty_digit : (fun _ : D.Stack => [])=D.store [] [] [] [] [] [] := by
  funext k;cases k <;> rfl
/-- Literal raw-word update to radix input. -/
theorem digit_input (a b c d e f xs : List Bool) :
    Function.update (D.store a b c d e f) .input xs=D.store xs b c d e f := by
  funext k;cases k <;> rfl
/-- Literal raw-word update to actual width. -/
theorem digit_width (a b c d e f xs : List Bool) :
    Function.update (D.store a b c d e f) .width xs=D.store a xs c d e f := by
  funext k;cases k <;> rfl
/-- Literal raw-word update to actual finite-index tape. -/
theorem digit_index (a b c d e f xs : List Bool) :
    Function.update (D.store a b c d e f) .index xs=D.store a b xs d e f := by
  funext k;cases k <;> rfl
/-- Literal physical radix-output update and cleanup. -/
theorem digit_output (a b c d e f xs : List Bool) :
    Function.update (D.store a b c d e f) .output xs=D.store a b c d e xs := by
  funext k;cases k <;> rfl
/-- Each additional output update preserves both other actual words. -/
theorem words_update (scalar count sum xs : List Bool) (k : Aux) :
    Function.update (words scalar count sum) k xs=
      words (if k=.scalar then xs else scalar) (if k=.count then xs else count) (if k=.sum then xs else sum) := by
  funext q;cases k <;> cases q <;> rfl
/-- Both real digit outputs are compact, including zero and short input scalars. -/
theorem moment_compact (bits scalar : List Bool) (high : Bool) :
    SemiprimeSourceCompactBits.Compact (moment bits scalar high) :=
  SemiprimeD1JetScalarBits.reduce_compact _ _
/-- Each actually produced moment has at most the physically acquired width. -/
theorem moment_length (bits scalar : List Bool) (high : Bool) :
    (moment bits scalar high).length ≤ bits.length := by
  have h:=SemiprimeD1JetScalarBits.reduce_length (width bits).length (scalar.drop ((width bits).length*(index high).length))
  simpa only [moment,SemiprimeD1StackRadixDigitExecution.result,width,List.length_replicate] using h
/-- The full low block is actual reduction modulo the N-derived dyadic base. -/
theorem count_value (bits scalar : List Bool) :
    SemiprimeBitArithmetic.bitValue (moment bits scalar false)=SemiprimeBitArithmetic.bitValue scalar%2^bits.length := by
  rw [moment,SemiprimeD1StackRadixDigitExecution.result_value]
  simp only [width,index,Bool.false_eq_true,ite_false,List.length_nil,List.length_replicate,Nat.mul_zero,pow_zero,Nat.div_one]
/-- The high block is obtained by the physically executed one-block skip and reduction. -/
theorem sum_value (bits scalar : List Bool) :
    SemiprimeBitArithmetic.bitValue (moment bits scalar true)=(SemiprimeBitArithmetic.bitValue scalar/2^bits.length)%2^bits.length := by
  rw [moment,SemiprimeD1StackRadixDigitExecution.result_value]
  simp only [width,index,ite_true,List.length_singleton,List.length_replicate,Nat.mul_one]
end RiemannGaussian.SemiprimeD1StackPackedMomentReadoutEncoding
