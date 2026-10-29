/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePublicFactorCount
import Batteries.Data.BitVec.Lemmas

/-! # Explicit arithmetic behind the ordered macro entry tables -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace RiemannGaussian.SemiprimeMacroEntryExecution
open scoped BigOperators
open SemiprimeBooleanNetwork SemiprimeMacroFermatNetwork
open SemiprimeMacroGraphSemantics

/-- Executable little-endian decoder, with one multiply/add per input bit. -/
def binaryDecode {width : ℕ} (input : Fin width → Bool) : ℕ := Nat.ofBits input

/-- The decoder is the literal weighted binary sum on the ordered ports. -/
theorem binaryDecode_eq_sum {width : ℕ} (input : Fin width → Bool) :
    binaryDecode input = ∑ i : Fin width, (input i).toNat * 2^i.val := by
  induction width with
  | zero => simp [binaryDecode]
  | succ width ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Nat.mul_one, Fin.val_succ, pow_succ]
    rw [show binaryDecode input = 2 * binaryDecode (input ∘ Fin.succ) + (input 0).toNat
      from Nat.ofBits_succ input, ih]
    rw [Finset.mul_sum]
    simp only [Function.comp_apply]
    have hs : (∑ x : Fin width, 2 * ((input x.succ).toNat * 2^x.val)) =
        ∑ x : Fin width, (input x.succ).toNat * (2^x.val * 2) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hs]
    omega

/-- The old finite-equivalence inverse is exactly the executable decoder. -/
theorem readWord_eq_binaryDecode {width : ℕ} (input : Fin width → Bool) :
    readWord width input = binaryDecode input := by
  have he : (BitVec.ofFnLE input).getLsb = input := by
    funext i
    exact BitVec.getLsb_ofFnLE input i
  calc
    readWord width input = readWord width (BitVec.ofFnLE input).getLsb := congrArg _ he.symm
    _ = decode (BitVec.ofFnLE input) := readWord_bits (BitVec.ofFnLE input)
    _ = binaryDecode input := BitVec.toNat_ofFnLE input

/-- Closed-form inverse of the transform length in the actual Fermat ring. -/
def explicitNormalizer (depth : ℕ) : MacroRing depth :=
  -(2 : MacroRing depth)^(macroLength depth-(depth+1))

/-- No prime-modulus or modular-inverse oracle is needed for this inverse. -/
theorem explicitNormalizer_spec (depth : ℕ) :
    (macroLength depth : MacroRing depth) * explicitNormalizer depth = 1 := by
  have hle : depth+1 ≤ macroLength depth := by
    unfold macroLength
    exact Nat.le_of_lt (Nat.lt_two_pow_self)
  unfold explicitNormalizer
  rw [show (macroLength depth : MacroRing depth) = (2 : MacroRing depth)^(depth+1) by
    simp only [macroLength, Nat.cast_pow, Nat.cast_ofNat]]
  rw [mul_neg, ← pow_add, Nat.add_sub_of_le hle]
  have hf := SemiprimeBitFermatArithmetic.fermat_radix (macroLength depth)
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hf
  rw [hf]
  ring

/-- Every semantics configuration has exactly this computable normalizer. -/
theorem normalizer_eq_explicit (p : Config) : p.normalizer=explicitNormalizer p.depth := by
  have h := explicitNormalizer_spec p.depth
  calc
    p.normalizer = p.normalizer * ((macroLength p.depth : MacroRing p.depth) * explicitNormalizer p.depth) := by rw [h]; ring
    _ = (macroLength p.depth : MacroRing p.depth) * p.normalizer * explicitNormalizer p.depth := by ring
    _ = explicitNormalizer p.depth := by rw [p.normalizer_spec]; ring


/-- Explicit width argument matches each actual ordered word block. -/
def decodeWord (width : ℕ) (input : Fin width → Bool) : ℕ := binaryDecode input

/-- Executable second-stage normalization, including the inverse transform. -/
def explicitNormalization (p : Config) : SemiprimeMacroGraph.Transform → MacroRing p.depth
  | .inl _ => 1
  | .inr _ => explicitNormalizer p.depth

open SemiprimeMacroGraph

/-- Same literal tests with only binary decoding and the explicit normalizer. -/
def executableLocalPredicate (p : Config) : (v : Vertex p.r p.t p.digits)→(LocalSlot v→Bool)→Prop
  | .input _ i,x =>
      let word := decodeWord (p.r*p.t+1) (fun bit => x (.inl bit))
      if hi : i.val<p.digits then
        word<2^(p.width ⟨i.val,hi⟩) ∧
          ∀ j : {j : Fin p.digits // j.val=i.val},x (.inr j)=digitFlag i.val word
      else word=0
  | .first tr _,x =>
      let input := fun j : Fin p.t => decodeWord (p.r*p.t+1) (fun bit => x (.inl (j,bit)))
      let output := fun k : Fin p.t => decodeWord (p.r*p.t+1) (fun bit => x (.inr (k,bit)))
      (∀ j,input j<2^(p.r*p.t)+1) ∧ (∀ k,output k<2^(p.r*p.t)+1) ∧
        ∀ k,(output k : MacroRing p.depth)=
          ∑ j : Fin p.t,(input j : MacroRing p.depth)*(root p tr^p.r)^(j.val*k.val)
  | .scale tr j k,x =>
      let input := decodeWord (p.r*p.t+1) (fun bit => x (.inl bit))
      let output := decodeWord (p.r*p.t+1) (fun bit => x (.inr bit))
      input<2^(p.r*p.t)+1 ∧ output<2^(p.r*p.t)+1 ∧
        (output : MacroRing p.depth)=(input : MacroRing p.depth)*root p tr^(j.val*k.val)
  | .second tr _,x =>
      let input := fun j : Fin p.r => decodeWord (p.r*p.t+1) (fun bit => x (.inl (j,bit)))
      let output := fun k : Fin p.r => decodeWord (p.r*p.t+1) (fun bit => x (.inr (k,bit)))
      (∀ j,input j<2^(p.r*p.t)+1) ∧ (∀ k,output k<2^(p.r*p.t)+1) ∧
        ∀ k,(output k : MacroRing p.depth)=explicitNormalization p tr*
          ∑ j : Fin p.r,(input j : MacroRing p.depth)*(root p tr^p.t)^(j.val*k.val)
  | .product _,x =>
      let input := fun side : Fin 2 => decodeWord (p.r*p.t+1) (fun bit => x (.inl (side,bit)))
      let output := decodeWord (p.r*p.t+1) (fun bit => x (.inr bit))
      (∀ side,input side<2^(p.r*p.t)+1) ∧ output<2^(p.r*p.t)+1 ∧
        (output : MacroRing p.depth)=(input 0 : MacroRing p.depth)*(input 1 : MacroRing p.depth)
  | .carryInitial,x => decodeWord (p.r*p.t+1) x=0
  | .carry k,x =>
      let coefficient := decodeWord (p.r*p.t+1) (fun bit => x (.inl (0,bit)))
      let previous := decodeWord (p.r*p.t+1) (fun bit => x (.inl (1,bit)))
      let next := decodeWord (p.r*p.t+1) (fun bit => x (.inr bit))
      coefficient<2^(p.r*p.t)+1 ∧ previous<2^(p.r*p.t) ∧ next<2^(p.r*p.t) ∧
        coefficient+previous=p.target k.val+2^p.bits*next
  | .carryTerminal,x => decodeWord (p.r*p.t+1) x=0
  | .orGate _ _,x => x 2=(x 0 || x 1)
  | .inputCheck _,x => x 0=true


/-- Every literal arithmetic predicate is preserved, including integer carries. -/
theorem executableLocalPredicate_iff (p : Config) (v : Vertex p.r p.t p.digits)
    (input : LocalSlot v → Bool) :
    executableLocalPredicate p v input ↔ localTable p v input := by
  cases v <;> simp only [executableLocalPredicate, localTable, decodeWord,
    ← readWord_eq_binaryDecode]
  simp only [explicitNormalization, normalization]
  split <;> simp only [normalizer_eq_explicit]

/-- Actual executable zero/one entry on the compiler's ordered bit ports. -/
instance executableLocalPredicateDecidable (p : Config) (v : Vertex p.r p.t p.digits)
    (input : LocalSlot v → Bool) : Decidable (executableLocalPredicate p v input) := by
  cases v <;> unfold executableLocalPredicate <;> infer_instance

/-- Execute the decidable finite arithmetic checks without a truth table. -/
def executableEntry (p : Config) (v : Vertex p.r p.t p.digits)
    (input : Fin (arity v) → Bool) : Bool :=
  decide (executableLocalPredicate p v (fun slot => input (localSlotFinEquiv v slot)))

/-- The executable entry is exactly the previously counted literal tensor. -/
theorem executableEntry_eq_table (p : Config) (v : Vertex p.r p.t p.digits)
    (input : Fin (arity v) → Bool) : executableEntry p v input = table p v input := by
  apply Bool.eq_iff_iff.mpr
  simp only [executableEntry, table, decide_eq_true_eq]
  exact executableLocalPredicate_iff p v _


/-- Instrumented decoder: the returned value is computed by the very recursion
whose primitive bit-read/multiply/add work is accumulated in the second field. -/
def decodeRun : {width : ℕ} → (Fin width → Bool) → ℕ × ℕ
  | 0, _ => (0,0)
  | _+1, input =>
      let tail := decodeRun (input ∘ Fin.succ)
      (2*tail.1+(input 0).toNat,tail.2+3)

/-- The tracked data path computes the executable word decoder. -/
theorem decodeRun_value {width : ℕ} (input : Fin width → Bool) :
    (decodeRun input).1=binaryDecode input := by
  induction width with
  | zero => rfl
  | succ width ih =>
    simp only [decodeRun]
    rw [ih]
    exact (Nat.ofBits_succ input).symm

/-- Exact primitive word-decoding work, not an external clock annotation. -/
theorem decodeRun_work {width : ℕ} (input : Fin width → Bool) :
    (decodeRun input).2=3*width := by
  induction width with
  | zero => rfl
  | succ width ih => simp only [decodeRun,ih]; omega

/-- Explicit repeated-multiplication ring power, returning actual product work. -/
def powerRun {α : Type*} [Monoid α] (base : α) : ℕ → α × ℕ
  | 0 => (1,0)
  | e+1 => let previous := powerRun base e
           (previous.1*base,previous.2+1)

/-- Both tracked outputs of repeated multiplication are exact. -/
theorem powerRun_correct {α : Type*} [Monoid α] (base : α) (e : ℕ) :
    powerRun base e=(base^e,e) := by
  induction e with
  | zero => simp [powerRun]
  | succ e ih => simp only [powerRun,ih,pow_succ]

/-- A DFT output evaluated by explicit products and additions; no DFT oracle. -/
def dotRun {α : Type*} [CommRing α] (base : α) (stride frequency : ℕ)
    (input : ℕ → α) : ℕ → α × ℕ
  | 0 => (0,0)
  | count+1 =>
      let previous := dotRun base stride frequency input count
      let power := powerRun base (stride*(count*frequency))
      (previous.1+input count*power.1,previous.2+power.2+2)

/-- The computed value is precisely the polynomial DFT output used locally. -/
theorem dotRun_value {α : Type*} [CommRing α] (base : α) (stride frequency count : ℕ)
    (input : ℕ → α) :
    (dotRun base stride frequency input count).1=
      ∑ j ∈ Finset.range count,input j*(base^stride)^(j*frequency) := by
  induction count with
  | zero => simp [dotRun]
  | succ count ih =>
    simp only [dotRun,powerRun_correct,ih,Finset.sum_range_succ,pow_mul]

/-- Exact ring-operation count for that same output computation. -/
theorem dotRun_work {α : Type*} [CommRing α] (base : α) (stride frequency count : ℕ)
    (input : ℕ → α) :
    (dotRun base stride frequency input count).2=
      ∑ j ∈ Finset.range count,(stride*(j*frequency)+2) := by
  induction count with
  | zero => simp [dotRun]
  | succ count ih => simp only [dotRun,powerRun_correct,ih,Finset.sum_range_succ]; omega

/-- Uniform polynomial work for a local output with all indices at most n. -/
theorem dotRun_work_le {α : Type*} [CommRing α] (base : α)
    {stride frequency count n : ℕ} (hs : stride≤n) (hf : frequency≤n) (hc : count≤n)
    (input : ℕ → α) :
    (dotRun base stride frequency input count).2 ≤ n*(n^3+2) := by
  rw [dotRun_work]
  calc
    _ ≤ ∑ _j ∈ Finset.range count,(n^3+2) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j≤n := (Nat.le_of_lt (Finset.mem_range.mp hj)).trans hc
      have hm := Nat.mul_le_mul hs (Nat.mul_le_mul hjn hf)
      nlinarith
    _ = count*(n^3+2) := by simp
    _ ≤ n*(n^3+2) := Nat.mul_le_mul_right _ hc


open SemiprimeMacroBitNetwork SemiprimeMacroParameters

/-- Literal public configuration with executable normalization data. -/
def executablePublicConfig (N : ℕ) (hN : 0<N) : Config where
  depth := macroDepth (bitLength N)
  r := firstAxis (bitLength N)
  t := secondAxis (bitLength N)
  digits := digitCount (bitLength N)
  bits := radixBits (bitLength N)
  shape := (axes_product _).trans (transform_eq_macroLength (bitLength_pos hN))
  quarter := (axes_product _).trans (transform_eq_four_radixBits (bitLength_pos hN))
  bits_pos := radixBits_pos (bitLength_pos hN)
  digits_pos := (digitCount_bounds (bitLength_pos hN)).1
  digits_le := (digitCount_bounds (bitLength_pos hN)).2
  width i := activeDigitBits (bitLength N) i.val
  width_le i := (activeDigitBits_bounds (bitLength_pos hN) i.isLt).2
  target := targetDigit (bitLength N) N
  target_lt i hi := Nat.mod_lt _ (by positivity)
  normalizer := explicitNormalizer (macroDepth (bitLength N))
  normalizer_spec := explicitNormalizer_spec (macroDepth (bitLength N))


/-- Replacing choice by its explicit value preserves the entire public config. -/
theorem executablePublicConfig_eq (N : ℕ) (hN : 0<N) :
    executablePublicConfig N hN = SemiprimePublicFactorCount.publicConfig N hN := by
  have hn := normalizer_eq_explicit (SemiprimePublicFactorCount.publicConfig N hN)
  unfold executablePublicConfig SemiprimePublicFactorCount.publicConfig
  congr 1
  exact hn.symm

/-- Dependent table equality under equality of numerical configurations. -/
theorem congrArg_heq (f : (p : Config) → ((v : Vertex p.r p.t p.digits) →
    (Fin (arity v) → Bool) → Bool)) {p q : Config} (h : p=q) : HEq (f p) (f q) := by
  cases h
  rfl

/-- The fully public executable table retains the existing counted tensor. -/
def publicEntry (N : ℕ) (hN : 0<N)
    (v : Vertex (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N)))
    (input : Fin (arity v) → Bool) : Bool := executableEntry (executablePublicConfig N hN) v input

/-- Entrywise refinement at the actual public graph shape. -/
theorem publicEntry_eq (N : ℕ) (hN : 0<N)
    (v : Vertex (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N)))
    (input : Fin (arity v) → Bool) :
    publicEntry N hN v input = table (SemiprimePublicFactorCount.publicConfig N hN) v input := by
  unfold publicEntry
  erw [executableEntry_eq_table]
  have ht : HEq (table (executablePublicConfig N hN))
      (table (SemiprimePublicFactorCount.publicConfig N hN)) := by
    apply congrArg_heq table (executablePublicConfig_eq N hN)
  exact congrFun (congrFun (eq_of_heq ht) v) input

end RiemannGaussian.SemiprimeMacroEntryExecution
