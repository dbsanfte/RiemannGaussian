/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePaidPrefixController
import RiemannGaussian.SemiprimePublicAcquiredExecution
import RiemannGaussian.SemiprimeMaterializedSourceWords

/-!
# Reported input-bit reconstruction

Every selected-label lookup, original wire-index lookup, binary accumulation,
power multiplication and digit sum executes a finite loop. Public enumeration
construction and primitive word addressing retain their separate acquisition/
bit-refinement interfaces; the edge list is cached before its repeated scans.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimePaidFactorDecoder
open scoped BigOperators
open SemiprimePaidPrefixController SemiprimePublicAcquiredExecution SemiprimeMacroParameters
open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking

/-- Actual selected-bit list scan, correctly handling even repeated false labels. -/
def selectedBit {I : Type*} [DecidableEq I] (i : I) : List (I × Bool) → Run Bool
  | [] => ⟨false,1⟩
  | p::ps => if decide (p.1=i) && p.2 then ⟨true,4⟩ else
    let rest := selectedBit i ps
    ⟨rest.value,rest.work+4⟩

/-- Literal selected-bit decoder used by the original public algorithm. -/
theorem selectedBit_value {I : Type*} [DecidableEq I] (i : I) (values : List (I × Bool)) :
    (selectedBit i values).value=values.any (fun p => decide (p.1=i) && p.2) := by
  induction values with
  | nil => rfl
  | cons p ps ih => by_cases h : p.1=i ∧ p.2=true <;> simp [selectedBit,List.any_cons,h,ih]

/-- Every selected-label comparison and list step is paid. -/
theorem selectedBit_work {I : Type*} [DecidableEq I] (i : I) (values : List (I × Bool)) :
    (selectedBit i values).work≤4*values.length+1 := by
  induction values with
  | nil => simp [selectedBit]
  | cons p ps ih => by_cases h : p.1=i ∧ p.2=true <;>
      simp [selectedBit,h,List.length_cons] <;> omega

/-- Actual original physical wire carried by an input digit coordinate. -/
def inputWire (N : ℕ) (side : Fin 2) (i : ℕ)
    (hi : i< firstAxis (bitLength N)*secondAxis (bitLength N))
    (bit : Fin (firstAxis (bitLength N)*secondAxis (bitLength N)+1)) : PublicEdge N :=
  ((.inl (.input side ⟨i,hi⟩,bit)),false)

/-- Scan an already acquired public edge list to obtain the physical wire index. -/
def inputIndex (N : ℕ) (edges : FiniteEnumeration (PublicEdge N)) (side : Fin 2) (i : ℕ)
    (hi : i< firstAxis (bitLength N)*secondAxis (bitLength N))
    (bit : Fin (firstAxis (bitLength N)*secondAxis (bitLength N)+1)) : Run ℕ :=
  let found := SemiprimeMaterializedSourceWords.indexRun (inputWire N side i hi bit) edges.values
  ⟨found.value,found.work+1⟩

/-- The reported index scan is exactly the original finite-enumeration inverse. -/
theorem inputIndex_value (N : ℕ) (edges : FiniteEnumeration (PublicEdge N)) (side : Fin 2) (i : ℕ)
    (hi : i< firstAxis (bitLength N)*secondAxis (bitLength N))
    (bit : Fin (firstAxis (bitLength N)*secondAxis (bitLength N)+1)) :
    (inputIndex N edges side i hi bit).value=
      OAI.Algorithms.SubexponentialSAT.LocalExpectation.indexCode edges.values (inputWire N side i hi bit) :=
  SemiprimeMaterializedSourceWords.indexRun_value _ _

/-- Finite physical index lookup has its actual linear scan bound. -/
theorem inputIndex_work (N : ℕ) (edges : FiniteEnumeration (PublicEdge N)) (side : Fin 2) (i : ℕ)
    (hi : i< firstAxis (bitLength N)*secondAxis (bitLength N))
    (bit : Fin (firstAxis (bitLength N)*secondAxis (bitLength N)+1)) :
    (inputIndex N edges side i hi bit).work≤2*edges.values.length+3 := by
  have h := SemiprimeMaterializedSourceWords.indexRun_work (inputWire N side i hi bit) edges.values
  change (SemiprimeMaterializedSourceWords.indexRun (inputWire N side i hi bit) edges.values).work+1≤_
  omega

/-- Execute physical index lookup and a literal natural-index selected-label scan. -/
def inputBit (N : ℕ) (side : Fin 2) (values : List (Fin (wireCount N) × Bool)) (i : ℕ)
    (hi : i< firstAxis (bitLength N)*secondAxis (bitLength N))
    (bit : Fin (firstAxis (bitLength N)*secondAxis (bitLength N)+1))
    (edges : FiniteEnumeration (PublicEdge N)) : Run Bool :=
  let index := inputIndex N edges side i hi bit
  let labels := values.map (fun p => (p.1.val,p.2))
  let result := selectedBit index.value labels
  ⟨result.value,index.work+result.work+2*values.length+2⟩

/-- Actual selected input bit, with the original physical indexing convention. -/
theorem inputBit_value (N : ℕ) (side : Fin 2) (values : List (Fin (wireCount N) × Bool)) (i : ℕ)
    (hi : i< firstAxis (bitLength N)*secondAxis (bitLength N))
    (bit : Fin (firstAxis (bitLength N)*secondAxis (bitLength N)+1))
    (edges : FiniteEnumeration (PublicEdge N)) (he : edges=edgeEnumeration N) :
    (inputBit N side values i hi bit edges).value=
      SemiprimeAcquiredPrefixSearch.selectedBits values
        ((edgeEnumeration N).equivFin.symm (inputWire N side i hi bit)) := by
  subst edges
  simp only [inputBit,inputIndex_value,selectedBit_value,List.any_map,Function.comp_def,
    SemiprimeAcquiredPrefixSearch.selectedBits]
  apply congrArg (fun f : (Fin (wireCount N) × Bool) → Bool => values.any f)
  funext p
  let idx : Fin (wireCount N) := (edgeEnumeration N).equivFin.symm (inputWire N side i hi bit)
  change (decide (p.1.val=idx.val) && p.2)=(decide (p.1=idx) && p.2)
  apply congrArg (fun b : Bool => b && p.2)
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact Fin.ext_iff.symm

/-- Work of each actual physical input-bit request, including the copied index list. -/
theorem inputBit_work (N : ℕ) (side : Fin 2) (values : List (Fin (wireCount N) × Bool)) (i : ℕ)
    (hi : i< firstAxis (bitLength N)*secondAxis (bitLength N))
    (bit : Fin (firstAxis (bitLength N)*secondAxis (bitLength N)+1))
    (edges : FiniteEnumeration (PublicEdge N)) (he : edges=edgeEnumeration N) :
    (inputBit N side values i hi bit edges).work≤2*wireCount N+6*values.length+6 := by
  have hx := inputIndex_work N edges side i hi bit
  have hb := selectedBit_work (inputIndex N edges side i hi bit).value
    (values.map (fun p => (p.1.val,p.2)))
  simp only [List.length_map] at hb
  have hl : edges.values.length=wireCount N := congrArg (fun e => e.values.length) he
  change (inputIndex N edges side i hi bit).work+_+2*values.length+2≤_
  rw [hl] at hx
  omega

/-- Execute little-endian binary accumulation, retaining all actual bit reports. -/
def binary : (width : ℕ) → (Fin width → Run Bool) → Run ℕ
  | 0, _ => ⟨0,1⟩
  | width+1, get =>
    let bit := get 0
    let tail := binary width (fun i => get i.succ)
    ⟨2*tail.value+bit.value.toNat,bit.work+tail.work+3⟩

/-- Exact agreement with the original physical binary decoder. -/
theorem binary_value (width : ℕ) (get : Fin width → Run Bool) :
    (binary width get).value=SemiprimeMacroEntryExecution.binaryDecode (fun i => (get i).value) := by
  induction width with
  | zero => rfl
  | succ width ih =>
    rw [SemiprimeMacroEntryExecution.binaryDecode,Nat.ofBits_succ]
    simp only [binary,ih,SemiprimeMacroEntryExecution.binaryDecode]
    rfl

/-- Every actual bit callback, multiply/add and branch is retained. -/
theorem binary_work (width B : ℕ) (get : Fin width → Run Bool) (hb : ∀ i, (get i).work≤ B) :
    (binary width get).work≤ width*(B+3)+1 := by
  induction width with
  | zero => simp [binary]
  | succ width ih =>
    have ht := ih (fun i => get i.succ) (fun i => hb i.succ)
    have hh := hb 0
    simp only [binary]
    nlinarith

/-- Actual scalar power construction, with multiplication and loop reports. -/
def power (base : ℕ) : ℕ → Run ℕ
  | 0 => ⟨1,1⟩
  | k+1 => let old := power base k; ⟨old.value*base,old.work+2⟩

theorem power_value (base k : ℕ) : (power base k).value=base^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [power,ih,pow_succ]

theorem power_work (base k : ℕ) : (power base k).work=2*k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [power,ih]; omega

/-- Actual finite sum of already reported digit computations. -/
def sumRun {A : Type*} (f : A → Run ℕ) : List A → Run ℕ
  | [] => ⟨0,1⟩
  | a::as => let v := f a; let tail := sumRun f as
            ⟨v.value+tail.value,v.work+tail.work+3⟩

theorem sumRun_value {A : Type*} (f : A → Run ℕ) (xs : List A) :
    (sumRun f xs).value=(xs.map (fun a => (f a).value)).sum := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [sumRun,List.map_cons,List.sum_cons,ih]

theorem sumRun_work {A : Type*} (f : A → Run ℕ) (xs : List A) (B : ℕ)
    (hb : ∀ a ∈ xs, (f a).work≤ B) : (sumRun f xs).work≤ xs.length*(B+3)+1 := by
  induction xs with
  | nil => simp [sumRun]
  | cons a as ih =>
    have ha := hb a (by simp)
    have ht := ih (fun b hb' => hb b (by simp [hb']))
    simp only [sumRun,List.length_cons]
    nlinarith

/-- One real physical input digit, including its radix power and accumulation. -/
def digit (N base : ℕ) (side : Fin 2) (values : List (Fin (wireCount N) × Bool)) (i : ℕ)
    (edges : FiniteEnumeration (PublicEdge N)) : Run ℕ :=
  if hi : i< firstAxis (bitLength N)*secondAxis (bitLength N) then
    let bits := binary (firstAxis (bitLength N)*secondAxis (bitLength N)+1)
      (fun bit => inputBit N side values i hi bit edges)
    let place := power base i
    ⟨bits.value*place.value,bits.work+place.work+3⟩
  else ⟨0,2⟩

/-- One digit computes the same little-endian summand as the original decoder. -/
theorem digit_value (N base : ℕ) (side : Fin 2) (values : List (Fin (wireCount N) × Bool)) (i : ℕ)
    (edges : FiniteEnumeration (PublicEdge N)) (he : edges=edgeEnumeration N) :
    (digit N base side values i edges).value=
      (if hi : i< firstAxis (bitLength N)*secondAxis (bitLength N) then
        SemiprimeMacroEntryExecution.binaryDecode (fun bit =>
          SemiprimeAcquiredPrefixSearch.selectedBits values
            ((edgeEnumeration N).equivFin.symm (inputWire N side i hi bit))) else 0)*base^i := by
  unfold digit
  by_cases hi : i< firstAxis (bitLength N)*secondAxis (bitLength N)
  · have hb (bit : Fin (firstAxis (bitLength N)*secondAxis (bitLength N)+1)) :=
      inputBit_value N side values i hi bit edges he
    simp only [dite_eq_left hi,binary_value,power_value,hb]
  · simp only [dite_eq_right hi,Nat.zero_mul]

/-- Fully computed operand, caching the original public edge list and radix once. -/
def decode (N : ℕ) (values : List (Fin (wireCount N) × Bool)) (side : Fin 2) : Run ℕ :=
  let edges := edgeEnumeration N
  let base := power 2 (radixBits (bitLength N))
  let indices := finIndices (digitCount (bitLength N))
  let result := sumRun (fun i : Fin (digitCount (bitLength N)) =>
    digit N base.value side values i.val edges) indices.value
  ⟨result.value,base.work+result.work+indices.work+1⟩

/-- Exact original physical little-endian operand, not a semantic normalizer oracle. -/
theorem decode_value (N : ℕ) (values : List (Fin (wireCount N) × Bool)) (side : Fin 2) :
    (decode N values side).value=decodeOperand N values side := by
  let f : ℕ → ℕ := fun i =>
    (if hi : i< firstAxis (bitLength N)*secondAxis (bitLength N) then
      SemiprimeMacroEntryExecution.binaryDecode (fun bit =>
        SemiprimeAcquiredPrefixSearch.selectedBits values
          ((edgeEnumeration N).equivFin.symm (inputWire N side i hi bit))) else 0)*
      (2^radixBits (bitLength N))^i
  calc
    (decode N values side).value = ∑ i : Fin (digitCount (bitLength N)), f i.val := by
      simp only [decode,finIndices_value,sumRun_value,digit_value _ _ _ _ _ _ rfl,power_value,
        ← List.ofFn_eq_map,List.sum_ofFn]
      rfl
    _ = ∑ i ∈ Finset.range (digitCount (bitLength N)), f i := Fin.sum_univ_eq_sum_range f _
    _ = decodeOperand N values side := rfl

/-- Uniform selected-operation operand reconstruction budget. -/
def budget (N v : ℕ) : ℕ :=
  digitCount (bitLength N)*((firstAxis (bitLength N)*secondAxis (bitLength N)+1)*
    (2*wireCount N+6*v+9)+2*digitCount (bitLength N)+8)+2*radixBits (bitLength N)+3*(digitCount (bitLength N)+1)^2+3

/-- Every actual index/selected-bit read and integer digit operation is charged. -/
theorem decode_work (N : ℕ) (values : List (Fin (wireCount N) × Bool)) (side : Fin 2) :
    (decode N values side).work≤ budget N values.length := by
  have hd (i : Fin (digitCount (bitLength N))) :
      (digit N (power 2 (radixBits (bitLength N))).value side values i.val (edgeEnumeration N)).work≤
        (firstAxis (bitLength N)*secondAxis (bitLength N)+1)*(2*wireCount N+6*values.length+9)+
          2*digitCount (bitLength N)+5 := by
    unfold digit
    split
    · rename_i hi
      have hb := binary_work (firstAxis (bitLength N)*secondAxis (bitLength N)+1)
        (2*wireCount N+6*values.length+6) _ (fun bit => inputBit_work N side values i.val hi bit _ rfl)
      simp only [power_work]
      have he : 2*wireCount N+6*values.length+6+3=2*wireCount N+6*values.length+9 := by omega
      rw [he] at hb
      have hi' := i.isLt
      omega
    · change 2≤_
      omega
  have hs := sumRun_work (fun i : Fin (digitCount (bitLength N)) =>
    digit N (power 2 (radixBits (bitLength N))).value side values i.val (edgeEnumeration N))
    (List.finRange (digitCount (bitLength N))) _ (fun i _ => hd i)
  simp only [List.length_finRange] at hs
  have ha := finIndices_work (digitCount (bitLength N))
  simp only [decode,finIndices_value,power_work,budget]
  have he : (firstAxis (bitLength N)*secondAxis (bitLength N)+1)*(2*wireCount N+6*values.length+9)+
      2*digitCount (bitLength N)+5+3 =
      (firstAxis (bitLength N)*secondAxis (bitLength N)+1)*(2*wireCount N+6*values.length+9)+
      2*digitCount (bitLength N)+8 := by omega
  rw [he] at hs
  omega

end RiemannGaussian.SemiprimePaidFactorDecoder
