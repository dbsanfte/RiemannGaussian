/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScaleBounds
import RiemannGaussian.SemiprimeD1StackWordVectorFinite
/-! # Exact original finite public scale assignments and descriptor order -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicScaleFinite
open SemiprimeD1StackPublicScale SemiprimeD1StackPublicScaleState SemiprimeD1StackPublicScaleDot
open SemiprimeD1StackPublicScaleInputs SemiprimeD1StackPublicScaleExecution SemiprimeD1StackPublicScaleOriginal
open SemiprimeBitArithmetic SemiprimeMacroParameters SemiprimeMacroGraph SemiprimeMacroEntryBitCheck
/-- Physical descriptor selector; original forward side does not change root4. -/
def selector : Transform→Bool | .inl _=>false | .inr _=>true
/-- Exact actual acquired public word width, without a size oracle. -/
theorem public_width (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    (cached bits).length=firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1 := by
  rw [original_modulus bits hc hN,modulus_length]
  rfl
/-- Original two consecutive word coordinates, used only in specifications. -/
def indexedWord (bits : List Bool) (input : Fin (2*(cached bits).length)→Bool) (j : Fin 2) : List Bool :=
  List.ofFn (fun b : Fin (cached bits).length=>input (finProdFinEquiv (j,b)))
/-- Both actually parsed words equal the original consecutive indexed words. -/
theorem words_original (bits : List Bool) (input : Fin (2*(cached bits).length)→Bool) :
    inputWord bits (List.ofFn input)=indexedWord bits input 0 ∧
    outputWord bits (List.ofFn input)=indexedWord bits input 1 := by
  have h:=SemiprimeD1StackWordVectorFinite.blocks_ofFn (cached bits) (show 2≤2 from le_rfl) input
  change [inputWord bits (List.ofFn input),outputWord bits (List.ofFn input)]=
    [indexedWord bits input 0,indexedWord bits input 1] at h
  simpa only [List.cons.injEq,and_true] using h
/-- Finite proof cast into actual acquired two-word coordinates; executing input
is still the literal original raw assignment, not this function. -/
def originalInput (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (firstAxis (bitLength (bitValue bits)))) (k : Fin (secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.scale (digits:=digitCount (bitLength (bitValue bits))) tr j k))→Bool) :
    Fin (2*(cached bits).length)→Bool := fun b=>input ⟨b.val,by
      have hw:=public_width bits hc hN
      change b.val<(_+_)
      have hb:=b.isLt
      omega⟩
/-- The finite cast changes neither a byte nor raw word-before-bit order. -/
theorem original_raw (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (firstAxis (bitLength (bitValue bits)))) (k : Fin (secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.scale (digits:=digitCount (bitLength (bitValue bits))) tr j k))→Bool) :
    List.ofFn (originalInput bits hc hN tr j k input)=List.ofFn input := by
  apply List.ext_getElem
  · rw [List.length_ofFn,List.length_ofFn]
    change 2*(cached bits).length=(firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)+
      (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)
    rw [public_width bits hc hN]
    omega
  · intro b hb hb'
    simp only [List.getElem_ofFn,originalInput]
/-- Both original local-slot words match the actual input/output parsing. -/
theorem public_words (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (firstAxis (bitLength (bitValue bits)))) (k : Fin (secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.scale (digits:=digitCount (bitLength (bitValue bits))) tr j k))→Bool) :
    indexedWord bits (originalInput bits hc hN tr j k input) 0=
      localWord (fun b=>input (localSlotFinEquiv (.scale tr j k) (.inl b))) ∧
    indexedWord bits (originalInput bits hc hN tr j k input) 1=
      localWord (fun b=>input (localSlotFinEquiv (.scale tr j k) (.inr b))) := by
  have hw:=public_width bits hc hN
  constructor
  · apply List.ext_getElem
    · simpa only [indexedWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.length_ofFn] using hw
    · intro b hb hb'
      simp only [indexedWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.getElem_ofFn,originalInput]
      congr 1
  · apply List.ext_getElem
    · simpa only [indexedWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.length_ofFn] using hw
    · intro b hb hb'
      simp only [indexedWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.getElem_ofFn,originalInput]
      congr 1
      apply Fin.ext
      change b+(cached bits).length*1=(_+1)+b
      rw [hw]
      omega
/-- ENTIRE original public scale checker for EVERY original finite assignment,
transform direction and typed j/k. Only their physical descriptor formats enter
the actual caller, no word/vector/canonicality/source/verdict advice. -/
theorem public_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (firstAxis (bitLength (bitValue bits)))) (k : Fin (secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.scale (digits:=digitCount (bitLength (bitValue bits))) tr j k))→Bool) :
    (done bits (List.ofFn input) (SemiprimeD1StackUnaryDivmod.unary j.val)
      (SemiprimeD1StackUnaryDivmod.unary k.val) (selector tr) j.val k.val).data (auxRole .output)=
      [(publicBitEntry (bitValue bits) hN (.scale tr j k) input).accepted] := by
  rw [←original_raw bits hc hN tr j k input]
  rw [original_equation bits _ _ _ (selector tr) j.val k.val hc hN]
  obtain ⟨h0,h1⟩:=words_original bits (originalInput bits hc hN tr j k input)
  rw [h0,h1]
  obtain ⟨h0,h1⟩:=public_words bits hc hN tr j k input
  rw [h0,h1]
  have hr : rootExpr (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN) (transform (selector tr))=
      rootExpr (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN) tr := by cases tr <;> rfl
  rw [hr,publicBitEntry_correct]
  exact congrArg (fun b : Bool=>[b]) (entryRun_correct (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN)
    (configTargets _) (.scale tr j k) input)
/-- Every original physical query inventory is linear in original bitlength. -/
theorem original_inventory (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (firstAxis (bitLength (bitValue bits)))) (k : Fin (secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.scale (digits:=digitCount (bitLength (bitValue bits))) tr j k))→Bool) :
    SemiprimeD1StackPublicScaleBounds.inputSize bits (List.ofFn input)
      (SemiprimeD1StackUnaryDivmod.unary j.val) (SemiprimeD1StackUnaryDivmod.unary k.val)≤
      300*(bitLength (bitValue bits)+1) := by
  have hj:=j.isLt
  have hk:=k.isLt
  have ha:=axes_ge_two (bitLength_pos hN)
  have hr:=Nat.mul_le_mul_left (firstAxis (bitLength (bitValue bits))) (show 1≤ secondAxis (bitLength (bitValue bits)) by omega)
  have ht:=Nat.mul_le_mul_right (secondAxis (bitLength (bitValue bits))) (show 1≤ firstAxis (bitLength (bitValue bits)) by omega)
  simp only [Nat.mul_one,Nat.one_mul] at hr ht
  have he:=axes_product (bitLength (bitValue bits))
  have hR : transformLength (bitLength (bitValue bits))≤64*bitLength (bitValue bits)+1 :=
    (SemiprimeD1StackTransformArithmetic.prefix_powers _ _ le_rfl).1
  unfold SemiprimeD1StackPublicScaleBounds.inputSize
  rw [List.length_ofFn]
  simp only [SemiprimeD1StackUnaryDivmod.unary,List.length_replicate]
  rw [SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc]
  change bitLength (bitValue bits)+
    ((firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)+
      (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1))+
        j.val+k.val+2≤_
  omega
/-- A fixed transition polynomial in ORIGINAL bitlength before every transform,
index pair and raw finite assignment; not an advised source/count clock. -/
theorem original_time (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (firstAxis (bitLength (bitValue bits)))) (k : Fin (secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.scale (digits:=digitCount (bitLength (bitValue bits))) tr j k))→Bool) :
    SemiprimeD1StackPublicScaleBounds.runBound bits (List.ofFn input)
      (SemiprimeD1StackUnaryDivmod.unary j.val) (SemiprimeD1StackUnaryDivmod.unary k.val)≤
      10^120*(bitLength (bitValue bits)+1)^16 := by
  have h:=Nat.pow_le_pow_left (original_inventory bits hc hN tr j k input) 16
  rw [mul_pow] at h
  norm_num at h
  unfold SemiprimeD1StackPublicScaleBounds.runBound
  norm_num only
  omega
/-- Whole original finite-assignment machine certificate, with literal physical
N/raw/j/k/selector inputs. Original descriptor acquisition remains caller work. -/
noncomputable def machineOriginal (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (firstAxis (bitLength (bitValue bits)))) (k : Fin (secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.scale (digits:=digitCount (bitLength (bitValue bits))) tr j k))→Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits (List.ofFn input)
        (SemiprimeD1StackUnaryDivmod.unary j.val) (SemiprimeD1StackUnaryDivmod.unary k.val) (selector tr)))
      (some (SemiprimeD1StackCalls.configuration (done bits (List.ofFn input)
        (SemiprimeD1StackUnaryDivmod.unary j.val) (SemiprimeD1StackUnaryDivmod.unary k.val) (selector tr) j.val k.val)))
      (10^120*(bitLength (bitValue bits)+1)^16) := by
  let h:=SemiprimeD1StackPublicScaleBounds.machineCheck bits (List.ofFn input)
    (SemiprimeD1StackUnaryDivmod.unary j.val) (SemiprimeD1StackUnaryDivmod.unary k.val) (selector tr) j.val k.val rfl rfl hc hN
  exact ⟨h.toEvalsTo,h.steps_le_m.trans (original_time bits hc hN tr j k input)⟩
/-- All-prefix data+real-return storage has a fixed original bitlength polynomial. -/
theorem original_prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (firstAxis (bitLength (bitValue bits)))) (k : Fin (secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.scale (digits:=digitCount (bitLength (bitValue bits))) tr j k))→Bool)
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration
      (initial bits (List.ofFn input) (SemiprimeD1StackUnaryDivmod.unary j.val)
        (SemiprimeD1StackUnaryDivmod.unary k.val) (selector tr))))=some cfg) :
    (∑q : Stack,(cfg.stk (some q)).length)+(cfg.stk none).length≤10^124*(bitLength (bitValue bits)+1)^16 := by
  have h:=SemiprimeD1StackPublicScaleBounds.machine_prefix_cells bits (List.ofFn input)
    (SemiprimeD1StackUnaryDivmod.unary j.val) (SemiprimeD1StackUnaryDivmod.unary k.val) (selector tr) j.val k.val rfl rfl hc hN fuel cfg hr
  have hp:=Nat.pow_le_pow_left (original_inventory bits hc hN tr j k input) 16
  rw [mul_pow] at hp
  norm_num at hp
  unfold SemiprimeD1StackPublicScaleBounds.spaceBound at h
  norm_num only at h ⊢
  omega
end RiemannGaussian.SemiprimeD1StackPublicScaleFinite
