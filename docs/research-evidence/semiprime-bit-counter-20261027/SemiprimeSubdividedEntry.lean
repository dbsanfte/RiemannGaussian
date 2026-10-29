/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMacroEntryBitCheck

/-! # Actual primitive entry checker for the complete subdivided public graph -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSubdividedEntry
open SemiprimeMacroGraph SemiprimeMacroGraphSemantics SemiprimeMacroParameters
open SemiprimeMacroEntryExecution SemiprimeMacroEntryBitCheck SemiprimeMacroEntryBitPrimitives

/-- Two input reads and the literal XOR/NOT equality circuit, with its five charges. -/
def equalityRun (input : Fin 2 → Bool) : CheckRun :=
  ⟨!(Bool.xor (input 0) (input 1)),5⟩

/-- The equality vertex compares its actual ordered two Boolean ports. -/
theorem equalityRun_correct (input : Fin 2 → Bool) :
    (equalityRun input).accepted=decide (input 0=input 1) := by
  simp only [equalityRun]
  cases h0 : input 0 <;> cases h1 : input 1 <;> rfl

/-- Complete public checker, covering both original arithmetic and equality vertices. -/
def publicSubdividedEntry (N : ℕ) (hN : 0<N) :
    (v : SubdividedVertex (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N))) →
    (Fin (subdividedArity v) → Bool) → CheckRun
  | .inl vertex,input => publicBitEntry N hN vertex input
  | .inr _,input => equalityRun input

/-- Every entry of the actual occurrence-two counter graph has the proved bit checker. -/
theorem publicSubdividedEntry_correct (N : ℕ) (hN : 0<N)
    (v : SubdividedVertex (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N)))
    (input : Fin (subdividedArity v) → Bool) :
    (publicSubdividedEntry N hN v input).accepted=
      subdividedTable (SemiprimePublicFactorCount.publicConfig N hN) v input := by
  cases v with
  | inl vertex => exact publicBitEntry_correct N hN vertex input
  | inr signal => exact equalityRun_correct input

/-- The same public polynomial backend bound holds on the full subdivided graph. -/
theorem publicSubdividedEntry_polynomial (N : ℕ) (hN : 0<N)
    (v : SubdividedVertex (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N)))
    (input : Fin (subdividedArity v) → Bool) :
    (publicSubdividedEntry N hN v input).clock≤1048576*(64*bitLength N+2)^10 := by
  cases v with
  | inl vertex => exact publicBitEntry_polynomial N hN vertex input
  | inr signal =>
    change 5≤1048576*(64*bitLength N+2)^10
    have h := Nat.pow_le_pow_left (show 1≤64*bitLength N+2 by omega) 10
    norm_num at h
    omega

end RiemannGaussian.SemiprimeSubdividedEntry
