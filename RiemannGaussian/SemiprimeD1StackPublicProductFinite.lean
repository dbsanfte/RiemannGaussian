/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicProductBounds
import RiemannGaussian.SemiprimeD1StackWordVectorFinite

/-! # All original product vertices, all assignments, original bit time
Only finite proof casts identify the original input-before-output,
word-before-bit coordinates. The executed program acquires the metadata,
modulus, vector and operands itself from original N and literal raw bytes.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPublicProductFinite
open SemiprimeD1StackPublicProduct SemiprimeD1StackPublicProductExecution
open SemiprimeD1StackProductCheckParse SemiprimeD1StackProductCheckMeaning
open SemiprimeMacroGraph SemiprimeMacroEntryBitCheck SemiprimeMacroParameters SemiprimeBitArithmetic

/-- Equal-width little-endian words are determined by their integer values. -/
theorem words_eq {xs ys : List Bool} (hl : xs.length=ys.length) (hv : bitValue xs=bitValue ys) : xs=ys := by
  induction xs generalizing ys with
  | nil=>cases ys <;> simp_all
  | cons b xs ih=>
    cases ys with
    | nil=>simp at hl
    | cons c ys=>
      have ht : xs.length=ys.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hl
      cases b <;> cases c <;> simp only [bitValue,bitNat,Bool.false_eq_true,ite_false,ite_true] at hv
      · exact congrArg (List.cons false) (ih ht (by omega))
      · omega
      · omega
      · exact congrArg (List.cons true) (ih ht (by omega))
/-- The ACTUALLY acquired modulus is exactly the old original word, not an
assumed interpretation or canonicality answer. -/
theorem original_modulus (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    cached bits=modulus (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN) := by
  let p:=SemiprimePublicFactorCount.publicConfig (bitValue bits) hN
  have hp:=(SemiprimeD1StackRootSourceOriginal.original_parameters bits hc hN).1
  apply words_eq
  · rw [SemiprimeD1StackPublicProductBounds.cached_length,modulus_length,hp]
  · change bitValue (SemiprimeD1StackFermatWords.modulusWord (transformLength bits.length))=_
    rw [SemiprimeD1StackFermatWords.modulus_value _ (by unfold transformLength;positivity),modulus_value,hp,p.shape]
/-- Exact original public graph width, derived from the actual acquisition. -/
theorem public_width (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    (cached bits).length=firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1 := by
  rw [SemiprimeD1StackPublicProductBounds.cached_length,
    SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc,axes_product]
/-- Exact three-word arity of every original product vertex. -/
theorem product_arity {r t digits : ℕ} (k : Fin (r*t)) :
    arity (Vertex.product (r:=r) (t:=t) (digits:=digits) k)=3*(r*t+1) := by simp only [arity];ring
/-- Proof-side original indexed word; the runtime has no indexed-word getter. -/
def indexedWord (width : List Bool) (input : Fin (3*width.length)→Bool) (j : Fin 3) : List Bool :=
  List.ofFn (fun b : Fin width.length=>input (finProdFinEquiv (j,b)))
/-- The real grouped raw blocks match the original finite-product bit order. -/
theorem words_original (width : List Bool) (input : Fin (3*width.length)→Bool) :
    first (List.ofFn input) width=indexedWord width input 0 ∧
    second (List.ofFn input) width=indexedWord width input 1 ∧
    third (List.ofFn input) width=indexedWord width input 2 := by
  have h:=SemiprimeD1StackWordVectorFinite.blocks_ofFn width (show 3≤3 from le_rfl) input
  change [first (List.ofFn input) width,second (List.ofFn input) width,third (List.ofFn input) width]=
    [indexedWord width input 0,indexedWord width input 1,indexedWord width input 2] at h
  simpa only [List.cons.injEq,and_true] using h
/-- Finite proof cast changes no original assignment byte or order. -/
def originalInput (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.product (digits:=digitCount (bitLength (bitValue bits))) k))→Bool) :
    Fin (3*(cached bits).length)→Bool := fun j=>input ⟨j.val,by
      rw [product_arity,←public_width bits hc];exact j.isLt⟩
/-- Every actually acquired word is the original product vertex's local word. -/
theorem public_words (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.product (digits:=digitCount (bitLength (bitValue bits))) k))→Bool) :
    indexedWord (cached bits) (originalInput bits hc k input) 0=
      localWord (fun b=>input (localSlotFinEquiv (.product k) (.inl (0,b)))) ∧
    indexedWord (cached bits) (originalInput bits hc k input) 1=
      localWord (fun b=>input (localSlotFinEquiv (.product k) (.inl (1,b)))) ∧
    indexedWord (cached bits) (originalInput bits hc k input) 2=
      localWord (fun b=>input (localSlotFinEquiv (.product k) (.inr b))) := by
  have hw:=public_width bits hc
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
      change i+(cached bits).length*1=i+(_+1)*1
      rw [hw]
  · apply List.ext_getElem
    · simpa only [indexedWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.length_ofFn] using hw
    · intro i hi hi'
      simp only [indexedWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.getElem_ofFn,originalInput]
      congr 1
      apply Fin.ext
      simp only [localSlotFinEquiv]
      change i+(cached bits).length*2=2*(_+1)+i
      rw [hw]
      omega
/-- The finite proof cast is byte-for-byte the same actual raw assignment. -/
theorem original_raw (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.product (digits:=digitCount (bitLength (bitValue bits))) k))→Bool) :
    List.ofFn (originalInput bits hc k input)=List.ofFn input := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,product_arity,public_width bits hc]
  · intro i hi hi';simp only [List.getElem_ofFn,originalInput]
/-- ENTIRE original public product checker, for ALL original indices and ALL
finite assignments; modulus, guards and every operand are actually acquired. -/
theorem public_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.product (digits:=digitCount (bitLength (bitValue bits))) k))→Bool) :
    SemiprimeD1StackProductCheckExecution.answer (List.ofFn input) (cached bits)=
      (publicBitEntry (bitValue bits) hN (.product k) input).accepted := by
  rw [←original_raw bits hc k input]
  let p:=SemiprimePublicFactorCount.publicConfig (bitValue bits) hN
  have he:=old_product p (List.ofFn (originalInput bits hc k input))
  rw [←original_modulus bits hc hN] at he
  rw [he]
  obtain ⟨a,b,c⟩:=words_original (cached bits) (originalInput bits hc k input)
  obtain ⟨x,y,z⟩:=public_words bits hc k input
  have ha:=a.trans x
  have hb:=b.trans y
  have hcWord:=c.trans z
  have hi : inputWords (List.ofFn (originalInput bits hc k input)) (cached bits)=
      fun j : Fin 2=>localWord (fun bit=>input (localSlotFinEquiv (.product k) (.inl (j,bit)))) := by
    funext j
    fin_cases j
    · exact ha
    · exact hb
  rw [hi,ha,hb,hcWord,publicBitEntry_correct]
  exact entryRun_correct p (configTargets p) (.product k) input
/-- Literal output singleton equals the ORIGINAL public checker on every input. -/
theorem output_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.product (digits:=digitCount (bitLength (bitValue bits))) k))→Bool) :
    (done bits (List.ofFn input)).data output=[(publicBitEntry (bitValue bits) hN (.product k) input).accepted] := by
  rw [output_answer,public_original bits hc hN k input]
/-- Original all-assignment input inventory is linear in original binary width. -/
theorem original_inventory (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.product (digits:=digitCount (bitLength (bitValue bits))) k))→Bool) :
    bits.length+(List.ofFn input).length+2≤210*(bitLength (bitValue bits)+1) := by
  rw [List.length_ofFn,product_arity,←public_width bits hc]
  have h:=SemiprimeD1StackPublicProductBounds.cached_length_le bits
  rw [SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc] at h ⊢
  omega
/-- Whole actual original product-query time, uniformly before every N/index/
assignment. No old checker report or callback clock has been substituted. -/
theorem original_time (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.product (digits:=digitCount (bitLength (bitValue bits))) k))→Bool) :
    SemiprimeD1StackPublicProductBounds.runBound bits (List.ofFn input)≤100000000000000000000*(bitLength (bitValue bits)+1)^3 := by
  have h:=Nat.pow_le_pow_left (original_inventory bits hc k input) 3
  rw [mul_pow] at h
  norm_num at h
  unfold SemiprimeD1StackPublicProductBounds.runBound
  simp only [List.length_ofFn]
  omega
/-- SAME genuine machine, complete source trace and fixed original bitlength
clock for every product index and finite assignment. -/
noncomputable def machineOriginal (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.product (digits:=digitCount (bitLength (bitValue bits))) k))→Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits (List.ofFn input)))
      (some (SemiprimeD1StackCalls.configuration (done bits (List.ofFn input))))
      (100000000000000000000*(bitLength (bitValue bits)+1)^3) := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact (Nat.lt_irrefl 0 hN)
  let h:=SemiprimeD1StackPublicProductBounds.machineCheck bits (List.ofFn input) hb
  exact ⟨h.toEvalsTo,h.steps_le_m.trans (original_time bits hc k input)⟩
/-- Full original all-prefix inventory, including every acquired public cache,
all76 data roles and every actual return-label cell, uniformly for all inputs. -/
theorem original_prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.product (digits:=digitCount (bitLength (bitValue bits))) k))→Bool)
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits (List.ofFn input))))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤10000000000000000000000*(bitLength (bitValue bits)+1)^3 := by
  have hbits : bits≠[] := by intro he;rw [he] at hN;exact (Nat.lt_irrefl 0 hN)
  have h:=SemiprimeD1StackPublicProductBounds.machine_prefix_cells bits (List.ofFn input) hbits fuel cfg hr
  have hp:=Nat.pow_le_pow_left (original_inventory bits hc k input) 3
  rw [mul_pow] at hp
  norm_num at hp
  simp only [List.length_ofFn] at h
  omega
end RiemannGaussian.SemiprimeD1StackPublicProductFinite
