/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootMetadata
/-! # Exact physical metadata words and original binary value identities -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPackedRootMetadataEncoding
open SemiprimeD1StackPackedRootMetadata SemiprimeBitArithmetic
/-- Actual repeated add-two result word; this is a proof-side trace description. -/
def precisionWord : ℕ→List Bool
  | 0 => []
  | n+1 => (addBits (precisionWord n) [false,true] false).bits
/-- Actual shifted public base starts at the literal one and shifts once per marker. -/
def baseWord (n : ℕ) : List Bool := List.replicate n false++[true]
/-- Exact five-role source/loop view. -/
def words (reader scratch precision base template : List Bool) : Aux→List Bool
  | .reader => reader | .copyScratch => scratch | .precision => precision
  | .base => base | .template => template
/-- Each real helper update changes exactly one actual role. -/
theorem words_update (reader scratch precision base template xs : List Bool) (k : Aux) :
    Function.update (words reader scratch precision base template) k xs=
      words (if k=.reader then xs else reader) (if k=.copyScratch then xs else scratch)
        (if k=.precision then xs else precision) (if k=.base then xs else base) (if k=.template then xs else template) := by
  funext p
  cases k <;> cases p <;> rfl
/-- Actual whole physical loop boundary, retaining the complete actual bootstrap bank. -/
def loop (b : B.Stack→List Bool) (done todo : ℕ) : Stack→List Bool :=
  bank b (fun _ => []) (words (List.replicate todo true) [] (precisionWord done) (baseWord done) (List.replicate (2*done) false))
/-- Exact final bank contains only retained originals, actual precision/base/template and empty private/shadow roles. -/
def result (bits : List Bool) : Stack→List Bool := loop (B.done bits).store bits.length 0
/-- Genuine clean halt, with every work word physically drained. -/
def done (bits : List Bool) : C.State Stack Label := ⟨none,none,none,result bits,[]⟩
/-- A real whole-bootstrap boundary is the SAME finite program's ready entry. -/
def ready (bits : List Bool) : C.State Stack Label :=
  ⟨some (.local .seedBase),none,none,bank (B.done bits).store (fun _ => []) (fun _ => []),[]⟩
/-- Exact binary precision VALUE; its counter word is never runtime Nat advice. -/
theorem precision_value (n : ℕ) : bitValue (precisionWord n)=2*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [precisionWord,addBits_correct,ih]
    change 2*n+2+0=2*(n+1)
    omega
/-- Every actual ripple counter word has a linear PHYSICAL width bound. -/
theorem precision_length (n : ℕ) : (precisionWord n).length ≤ 3*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := (addBits_counts (precisionWord n) [false,true] false).2.2.2.2
    have hm : max (precisionWord n).length [false,true].length ≤ 3*n+2 := max_le (by omega) (by simp)
    change (addBits (precisionWord n) [false,true] false).bits.length ≤ 3*(n+1)
    omega
/-- Each actual base shift exactly doubles the original one. -/
theorem base_value (n : ℕ) : bitValue (baseWord n)=2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change bitValue (false::baseWord n)=2^(n+1)
    change 0+2*bitValue (baseWord n)=2^(n+1)
    rw [ih,pow_succ]
    omega
/-- Actual output lengths, including every FALSE width cell. -/
theorem base_length (n : ℕ) : (baseWord n).length=n+1 := by simp only [baseWord,List.length_append,List.length_replicate,List.length_singleton]
end RiemannGaussian.SemiprimeD1StackPackedRootMetadataEncoding
