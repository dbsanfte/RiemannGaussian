/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicCarryBounds
/-! # Exact original word-before-bit assignment order for carry queries -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicCarryFinite
open SemiprimeD1StackPublicCarry SemiprimeD1StackPublicCarryState
open SemiprimeD1StackPublicCarryExecution SemiprimeD1StackPublicCarryOriginal
open SemiprimeMacroGraph SemiprimeMacroEntryBitCheck SemiprimeMacroParameters SemiprimeBitArithmetic
/-- The original three consecutive word coordinates, used only in specifications. -/
def indexedWord (context : T.Stack→List Bool) (input : Fin (3*(width context).length)→Bool)
    (j : Fin 3) : List Bool := List.ofFn (fun b : Fin (width context).length=>input (finProdFinEquiv (j,b)))
/-- Actual grouping agrees with all three original indexed words. -/
theorem words_original (context : T.Stack→List Bool) (input : Fin (3*(width context).length)→Bool) :
    coefficient context (List.ofFn input)=indexedWord context input 0 ∧
    previous context (List.ofFn input)=indexedWord context input 1 ∧
    next context (List.ofFn input)=indexedWord context input 2 := by
  have h:=SemiprimeD1StackWordVectorFinite.blocks_ofFn (width context) (show 3≤3 from le_rfl) input
  rw [blocks_three] at h
  change [coefficient context (List.ofFn input),previous context (List.ofFn input),next context (List.ofFn input)]=
    [indexedWord context input 0,indexedWord context input 1,indexedWord context input 2] at h
  simpa only [List.cons.injEq,and_true] using h
/-- Original three-word local-slot coordinate order. This function is proof-side;
all executing words are acquired by the real WordVector program. -/
def localInput (context : T.Stack→List Bool) (input : Fin (3*(width context).length)→Bool) :
    (Fin 2×Fin (width context).length)⊕Fin (width context).length→Bool
  | .inl (j,b)=>input (finProdFinEquiv (⟨j.val,by omega⟩,b))
  | .inr b=>input (finProdFinEquiv (2,b))
/-- Every complete original finite three-word assignment has exactly the same
computed carry verdict as the original local integer checker, in its bit order. -/
theorem original_three_words (bits index : List Bool) (input : Fin (3*(width (actualContext bits index)).length)→Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (hi : index.length=k.val) :
    answer (actualContext bits index) (List.ofFn input)=
      (carryRun (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN)
        ((configTargets (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN)).words k)
        (localWord (fun b=>localInput (actualContext bits index) input (.inl (0,b))))
        (localWord (fun b=>localInput (actualContext bits index) input (.inl (1,b))))
        (localWord (fun b=>localInput (actualContext bits index) input (.inr b)))).accepted := by
  rw [acquired_target_carry bits (List.ofFn input) index hc hN k hi]
  obtain ⟨h0,h1,h2⟩:=words_original (actualContext bits index) input
  rw [h0,h1,h2]
  rfl
/-- Actual acquired width equals the original public graph's word width. -/
theorem public_width (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    (width (actualContext bits index)).length=
      firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1 := by
  rw [acquired_width_length,SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc,axes_product]
/-- The original vertex's finite raw assignment, viewed in three-word order.
Only finite proof casts occur here; the executed input remains literal raw bytes. -/
def originalInput (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.carry (digits:=digitCount (bitLength (bitValue bits))) k))→Bool) :
    Fin (3*(width (actualContext bits index)).length)→Bool := fun j=>input ⟨j.val,by
      rw [carry_arity,←public_width bits index hc];exact j.isLt⟩
/-- Every acquired block is the original carry vertex's literal local word,
with its exact slot flattening; all assignments and parallel bit coordinates remain. -/
theorem public_words (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.carry (digits:=digitCount (bitLength (bitValue bits))) k))→Bool) :
    indexedWord (actualContext bits index) (originalInput bits index hc k input) 0=
      localWord (fun b=>input (localSlotFinEquiv (.carry k) (.inl (0,b)))) ∧
    indexedWord (actualContext bits index) (originalInput bits index hc k input) 1=
      localWord (fun b=>input (localSlotFinEquiv (.carry k) (.inl (1,b)))) ∧
    indexedWord (actualContext bits index) (originalInput bits index hc k input) 2=
      localWord (fun b=>input (localSlotFinEquiv (.carry k) (.inr b))) := by
  have hw:=public_width bits index hc
  constructor
  · apply List.ext_getElem
    · simpa only [indexedWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.length_ofFn] using hw
    · intro i hi hi'
      simp only [indexedWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.getElem_ofFn,originalInput]
      congr 1
  constructor
  · apply List.ext_getElem
    · simpa only [indexedWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.length_ofFn] using hw
    · intro i hi hi'
      simp only [indexedWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.getElem_ofFn,originalInput]
      congr 1
      apply Fin.ext
      simp only [localSlotFinEquiv,finProdFinEquiv]
      change i+(width (actualContext bits index)).length*1=i+(_+1)*1
      rw [hw]
  · apply List.ext_getElem
    · simpa only [indexedWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.length_ofFn] using hw
    · intro i hi hi'
      simp only [indexedWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.getElem_ofFn,originalInput]
      congr 1
      apply Fin.ext
      simp only [localSlotFinEquiv]
      change i+(width (actualContext bits index)).length*2=2*(_+1)+i
      rw [hw]
      omega
/-- The proof cast changes no raw assignment byte or its order. -/
theorem original_raw (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.carry (digits:=digitCount (bitLength (bitValue bits))) k))→Bool) :
    List.ofFn (originalInput bits index hc k input)=List.ofFn input := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,carry_arity,public_width bits index hc]
  · intro i hi hi'
    simp only [List.getElem_ofFn,originalInput]
/-- ENTIRE original public carry vertex on EVERY finite raw assignment. The
only index format hypothesis identifies actual caller-supplied physical index
markers with the original descriptor; metadata/target/guards are all acquired. -/
theorem public_original (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.carry (digits:=digitCount (bitLength (bitValue bits))) k))→Bool)
    (hi : index.length=k.val) :
    answer (actualContext bits index) (List.ofFn input)=
      (publicBitEntry (bitValue bits) hN (.carry k) input).accepted := by
  rw [←original_raw bits index hc k input]
  rw [acquired_target_carry bits _ index hc hN k hi]
  obtain ⟨h0,h1,h2⟩:=words_original (actualContext bits index) (originalInput bits index hc k input)
  rw [h0,h1,h2]
  obtain ⟨h0,h1,h2⟩:=public_words bits index hc k input
  rw [h0,h1,h2]
  rw [publicBitEntry_correct]
  exact entryRun_correct (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN)
    (configTargets _) (.carry k) input
/-- The actually completed physical output cell is the OLD original carry
checker on every finite assignment; this is literal output-byte equality. -/
theorem output_original (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.carry (digits:=digitCount (bitLength (bitValue bits))) k))→Bool)
    (hi : index.length=k.val) :
    (done bits (List.ofFn input) index).data output=
      [(publicBitEntry (bitValue bits) hN (.carry k) input).accepted] := by
  change [answer (actualContext bits index) (List.ofFn input)]=_
  rw [public_original bits index hc hN k input hi]
/-- Original all-assignment physical input inventory is linear in bitlength. -/
theorem original_inventory (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.carry (digits:=digitCount (bitLength (bitValue bits))) k))→Bool)
    (hi : index.length=k.val) :
    bits.length+(List.ofFn input).length+index.length+2≤260*(bitLength (bitValue bits)+1) := by
  rw [List.length_ofFn,carry_arity,hi,SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc]
  have hk:=k.isLt
  have he:=axes_product (bitLength (bitValue bits))
  have hR : transformLength (bitLength (bitValue bits))≤64*bitLength (bitValue bits)+1 :=
    (SemiprimeD1StackTransformArithmetic.prefix_powers _ _ le_rfl).1
  omega
/-- Uniform genuine machine-time allowance in ORIGINAL binary bitlength,
before the entire family of vertices and assignments; no expected-time advice. -/
theorem original_time (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.carry (digits:=digitCount (bitLength (bitValue bits))) k))→Bool)
    (hi : index.length=k.val) :
    SemiprimeD1StackPublicCarryBounds.runBound bits (List.ofFn input) index≤
      1000000000000000000*(bitLength (bitValue bits)+1)^2 := by
  have h:=Nat.pow_le_pow_left (original_inventory bits index hc k input hi) 2
  rw [mul_pow] at h
  norm_num at h
  unfold SemiprimeD1StackPublicCarryBounds.runBound
  simp only [List.length_ofFn]
  omega
/-- Uniform all-prefix storage in original bitlength, INCLUDING real return
symbols. Source/assignment/index acquisition stays the explicit caller boundary. -/
theorem original_prefix_cells (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.carry (digits:=digitCount (bitLength (bitValue bits))) k))→Bool)
    (hi : index.length=k.val) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits (List.ofFn input) index)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      100000000000000000000*(bitLength (bitValue bits)+1)^2 := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact (Nat.lt_irrefl 0 hN)
  have h:=SemiprimeD1StackPublicCarryBounds.machine_prefix_cells bits (List.ofFn input) index hb fuel cfg hr
  have hp:=Nat.pow_le_pow_left (original_inventory bits index hc k input hi) 2
  rw [mul_pow] at hp
  norm_num at hp
  simp only [List.length_ofFn] at h
  omega
end RiemannGaussian.SemiprimeD1StackPublicCarryFinite
