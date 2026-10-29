/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1HermiteWeightBits
import RiemannGaussian.SemiprimeBitArithmetic

/-! # One-denominator integer recovery from actual child words
The executable numerator stage multiplies canonical weight numerators by exact
integer denominator cofactors. It decodes supplied child words itself. Native
integer arithmetic and canonical rational extraction remain scalar boundaries;
this module does not claim a primitive-bit or tape clock.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1IntegerRecovery
open scoped BigOperators
open SemiprimeD1JetRecoveryWeights SemiprimeD1JetRecoveryGrid
  SemiprimeD1TaperedLoss SemiprimeD1HermiteNodes SemiprimeJetArray

/-- An acquired scalar weight paired with its actual retained child word. -/
structure Term where
  /-- Actual canonical scalar weight. -/
  weight : ℚ
  /-- Little-endian child representative digits. -/
  child : List Bool

/-- Original weights are acquired inside the constructor, once per active node. -/
def terms (a M u : ℕ) (children : ℕ → Array (List Bool)) : List Term :=
  ((List.range (SemiprimeD1WireKernelOriginal.size a)).filter (fun t =>
    t≠SemiprimeD1WireKernelOriginal.center a ∧ 0<nodeMultiplicity a (height M u) u t)).flatMap fun t =>
    let w := acquire a (height M u) u t
    (List.range w.retained).map fun j =>
      ⟨coefficient w.weights j,(children t)[j]?.getD []⟩

/-- Actual product of every acquired canonical denominator. -/
def denominator (ts : List Term) : ℕ := (ts.map fun t => t.weight.den).prod

/-- Scalar decoding explicitly traverses every child digit. -/
def decode : List Bool → ℕ
  | [] => 0
  | b::bs => (if b then 1 else 0)+2*decode bs

/-- Decoding agrees with the binary-word specification. -/
theorem decode_eq (bs : List Bool) : decode bs=SemiprimeBitArithmetic.bitValue bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [decode,SemiprimeBitArithmetic.bitValue,SemiprimeBitArithmetic.bitNat,ih]

/-- Scaled signed integer term, with exact natural denominator division. -/
def scaled (D : ℕ) (t : Term) : ℤ :=
  t.weight.num*(D/t.weight.den : ℕ)*(decode t.child : ℤ)

/-- Actual right-recursive integer accumulator. -/
def accumulate (D : ℕ) : List Term → ℤ
  | [] => 0
  | t::ts => scaled D t+accumulate D ts

/-- Mathematical scalar specification of the same finite input list. -/
def rationalSum : List Term → ℚ
  | [] => 0
  | t::ts => t.weight*(decode t.child : ℚ)+rationalSum ts

/-- Decoded child arrays are a semantic view; the runtime consumes the original words. -/
def decodedPackets (children : ℕ → Array (List Bool)) (t : ℕ) : Array ℚ :=
  (children t).map fun bs => (decode bs:ℚ)

/-- Default-zero array access commutes with actual word decoding. -/
theorem decodedPackets_coefficient (children : ℕ → Array (List Bool)) (t j : ℕ) :
    coefficient (decodedPackets children t) j=(decode ((children t)[j]?.getD []):ℚ) := by
  simp only [coefficient,decodedPackets,Array.getElem?_map]
  cases (children t)[j]? <;> simp [decode]

/-- The scalar specification is exactly its literal list sum. -/
theorem rationalSum_eq (ts : List Term) :
    rationalSum ts=(ts.map fun t => t.weight*(decode t.child:ℚ)).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [rationalSum,ih]

/-- Appending terms appends the same scalar functional. -/
theorem rationalSum_append (xs ys : List Term) :
    rationalSum (xs++ys)=rationalSum xs+rationalSum ys := by
  simp [rationalSum_eq]

/-- The actual acquired list has precisely the original D.5 scalar meaning. -/
theorem terms_value (a M u : ℕ) (children : ℕ → Array (List Bool)) :
    rationalSum (terms a M u children)=
      SemiprimeD1JetRecoveryPrecision.recover a M u (decodedPackets children) := by
  let nodes := (List.range (SemiprimeD1WireKernelOriginal.size a)).filter (fun t =>
    t≠SemiprimeD1WireKernelOriginal.center a ∧ 0<nodeMultiplicity a (height M u) u t)
  let f : ℕ → List Term := fun t =>
    let w := acquire a (height M u) u t
    (List.range w.retained).map fun j =>
      ⟨coefficient w.weights j,(children t)[j]?.getD []⟩
  have hflat : ∀xs : List ℕ, rationalSum (xs.flatMap f)=(xs.map fun t => rationalSum (f t)).sum := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [rationalSum_append,ih]
  have hn : nodes.Nodup := List.nodup_range.filter _
  have hnodes : nodes.toFinset=active a (height M u) u := by
    ext t
    simp [nodes,active]
  change rationalSum (nodes.flatMap f)=_
  rw [hflat,← List.sum_toFinset _ hn,hnodes]
  apply Finset.sum_congr rfl
  intro t ht
  rw [rationalSum_eq]
  simp only [f,List.map_map]
  change ((List.range (nodeMultiplicity a (height M u) u t)).map (fun j =>
    coefficient (acquire a (height M u) u t).weights j*
      (decode ((children t)[j]?.getD []):ℚ))).sum=_
  rw [← List.sum_toFinset _ List.nodup_range,List.toFinset_range]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [decodedPackets_coefficient]

/-- One common denominator is positive, including the empty packet. -/
theorem denominator_pos (ts : List Term) : 0<denominator ts := by
  induction ts with
  | nil => simp [denominator]
  | cons t ts ih => simpa [denominator] using Nat.mul_pos t.weight.den_pos ih

/-- Every actual weight denominator divides the acquired product. -/
theorem denominator_dvd (ts : List Term) (t : Term) (ht : t∈ts) :
    t.weight.den∣denominator ts := by
  unfold denominator
  exact List.dvd_prod (List.mem_map.mpr ⟨t,ht,rfl⟩)

/-- Exact cofactor multiplication recovers the actual rational scalar. -/
theorem scaled_value (D : ℕ) (hD : 0<D) (t : Term) (hd : t.weight.den∣D) :
    (scaled D t : ℚ)/(D:ℚ)=t.weight*(decode t.child : ℚ) := by
  have hc : (t.weight.den:ℚ)*(D/t.weight.den:ℕ)=(D:ℚ) := by
    exact_mod_cast Nat.mul_div_cancel' hd
  have hn := Rat.num_div_den t.weight
  have hden : (t.weight.den:ℚ)≠0 := by exact_mod_cast t.weight.den_nz
  have hDq : (D:ℚ)≠0 := by positivity
  unfold scaled
  simp only [Int.cast_mul,Int.cast_natCast]
  calc
    _ = ((t.weight.num:ℚ)/(t.weight.den:ℚ))*(decode t.child:ℚ) := by
      field_simp
      linear_combination (t.weight.num:ℚ)*(decode t.child:ℚ)*hc
    _ = _ := by rw [hn]

/-- Every actual suffix uses the SAME denominator; no cancellation is needed. -/
theorem accumulate_value (D : ℕ) (hD : 0<D) (ts : List Term)
    (hd : ∀t∈ts,t.weight.den∣D) :
    (accumulate D ts : ℚ)/(D:ℚ)=rationalSum ts := by
  induction ts with
  | nil => simp [accumulate,rationalSum]
  | cons t ts ih =>
    simp only [accumulate,rationalSum,Int.cast_add,add_div]
    rw [scaled_value D hD t (hd t (by simp)),ih (fun t ht => hd t (by simp [ht]))]

/-- Every scaled term has a cancellation-independent integer magnitude bound. -/
theorem scaled_abs (D A C : ℕ) (t : Term)
    (hA : t.weight.num.natAbs≤A) (hC : decode t.child≤C) :
    (scaled D t).natAbs≤A*D*C := by
  unfold scaled
  simp only [Int.natAbs_mul,Int.natAbs_natCast]
  exact Nat.mul_le_mul (Nat.mul_le_mul hA (Nat.div_le_self _ _)) hC

/-- All actual right-recursive accumulator frames have linear numerator growth. -/
theorem accumulate_abs (D A C : ℕ) (ts : List Term)
    (hA : ∀t∈ts,t.weight.num.natAbs≤A) (hC : ∀t∈ts,decode t.child≤C) :
    (accumulate D ts).natAbs≤ts.length*(A*D*C) := by
  induction ts with
  | nil => simp [accumulate]
  | cons t ts ih =>
    have hs := scaled_abs D A C t (hA t (by simp)) (hC t (by simp))
    have hi := ih (fun t ht => hA t (by simp [ht])) (fun t ht => hC t (by simp [ht]))
    exact (Int.natAbs_add_le _ _).trans (by simpa [List.length_cons,Nat.add_mul,Nat.add_comm] using Nat.add_le_add hs hi)

/-- In particular every cached suffix accumulator has the SAME denominator bound. -/
theorem accumulate_suffix_abs (D A C : ℕ) (ts : List Term) (k : ℕ)
    (hA : ∀t∈ts,t.weight.num.natAbs≤A) (hC : ∀t∈ts,decode t.child≤C) :
    (accumulate D (ts.drop k)).natAbs≤ts.length*(A*D*C) := by
  exact (accumulate_abs D A C (ts.drop k)
    (fun t ht => hA t (List.mem_of_mem_drop ht))
    (fun t ht => hC t (List.mem_of_mem_drop ht))).trans
    (Nat.mul_le_mul_right _ (by simp only [List.length_drop]; omega))

/-- Executed integer numerator and its one acquired common denominator. -/
structure Result where
  /-- Shared positive denominator. -/
  denominator : ℕ
  /-- Signed integer accumulator. -/
  numerator : ℤ
  /-- Native integer multiplications/additions/divisions in the numerator stage. -/
  arithmetic : ℕ
  /-- Actual child digit cells traversed by decoding. -/
  digitReads : ℕ

/-- Native scalar execution trace for the denominator product. -/
def denominatorRun : List Term → ℕ × ℕ
  | [] => (1,0)
  | t::ts => let tail := denominatorRun ts; (t.weight.den*tail.1,tail.2+1)

/-- Native scalar execution trace for all numerator and digit operations. -/
def accumulateRun (D : ℕ) : List Term → ℤ × ℕ × ℕ
  | [] => (0,0,0)
  | t::ts =>
    let tail := accumulateRun D ts
    let child := decode t.child
    let cofactor := D/t.weight.den
    let term := t.weight.num*(cofactor:ℤ)*(child:ℤ)
    (term+tail.1,tail.2.1+4+2*t.child.length,tail.2.2+t.child.length)

/-- The reported product is the actual acquired common denominator. -/
theorem denominatorRun_value (ts : List Term) : (denominatorRun ts).1=denominator ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [denominatorRun,denominator,ih]

/-- The counted numerator stage refines the literal integer accumulator. -/
theorem accumulateRun_value (D : ℕ) (ts : List Term) : (accumulateRun D ts).1=accumulate D ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [accumulateRun,accumulate,scaled,ih]

/-- Original-input recovery numerator; no weight or decoded-count answer input. -/
def run (a M u : ℕ) (children : ℕ → Array (List Bool)) : Result :=
  let ts := terms a M u children
  let dr := denominatorRun ts
  let ar := accumulateRun dr.1 ts
  ⟨dr.1,ar.1,dr.2+ar.2.1,ar.2.2⟩

/-- Exact scalar meaning of the executed common-denominator numerator. -/
theorem run_value (a M u : ℕ) (children : ℕ → Array (List Bool)) :
    ((run a M u children).numerator:ℚ)/(run a M u children).denominator=
      rationalSum (terms a M u children) := by
  simp only [run,denominatorRun_value,accumulateRun_value]
  exact accumulate_value _ (denominator_pos _) _ (fun t ht => denominator_dvd _ t ht)

/-- Every acquired term has an original active node and retained coefficient index. -/
theorem terms_mem (a M u : ℕ) (children : ℕ → Array (List Bool)) (v : Term)
    (hv : v∈terms a M u children) :
    ∃t, t<SemiprimeD1WireKernelOriginal.size a ∧
      0<nodeMultiplicity a (height M u) u t ∧ ∃j,
      j<nodeMultiplicity a (height M u) u t ∧
      v=⟨coefficient (acquire a (height M u) u t).weights j,(children t)[j]?.getD []⟩ := by
  rcases List.mem_flatMap.mp hv with ⟨t,ht,hv⟩
  have ht' := List.mem_filter.mp ht
  have htN := List.mem_range.mp ht'.1
  have hq := (of_decide_eq_true ht'.2).2
  rcases List.mem_map.mp hv with ⟨j,hj,rfl⟩
  exact ⟨t,htN,hq,j,List.mem_range.mp hj,rfl⟩

/-- Exact original recovery identity for the executed integer numerator and child words. -/
theorem run_recover (a M u : ℕ) (children : ℕ → Array (List Bool)) :
    ((run a M u children).numerator:ℚ)/(run a M u children).denominator=
      SemiprimeD1JetRecoveryPrecision.recover a M u (decodedPackets children) := by
  rw [run_value,terms_value]

end RiemannGaussian.SemiprimeD1IntegerRecovery
