/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryWeightRunBounds

/-! # Original-derived states of the executed scalar weight producer
Raw grid products and right-recursive scalar suffixes are controlled directly,
without identifying a suffix with an ascending-prefix theorem or assuming its
normalized output height. This is a state bound, not a machine simulation.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1RecoveryWeightRunState
open scoped BigOperators
open SemiprimeD1RecoveryWeightRun SemiprimeD1RecoveryScalarRun
open SemiprimeD1WireKernelOriginal SemiprimeD1JetRecoveryGrid SemiprimeD1TaperedLoss
open SemiprimeD1JetRecoveryScalarHeight SemiprimeD1JetRecoveryWeights
open SemiprimeD1HermiteDenominatorHeight SemiprimeD1HermiteWeightHeight
open SemiprimeJetArray SemiprimeJetArrayHeight SemiprimeHermiteArrayHeight
open SemiprimeD1WireKernelFactors

/-- Every integer-power recursion prefix has the original factor/power cap. -/
theorem intPower_bound (x : ℤ) (N m k : ℕ) (hN : 0 < N)
    (hx : x.natAbs ≤ N) (hk : k ≤ m) :
    (intPower x k).value.natAbs ≤ N^m := by
  rw [intPower_value,Int.natAbs_pow]
  exact (Nat.pow_le_pow_left hx k).trans (Nat.pow_le_pow_right hN hk)

/-- Literal signed finite product bound, also for every recursive sublist. -/
theorem product_bound (qs : List ℕ) (f : ℕ → ℤ) (N B : ℕ)
    (hf : ∀q∈qs,(f q).natAbs ≤ N^B) :
    (qs.map f).prod.natAbs ≤ N^(B*qs.length) := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    have ht:=ih (fun q hq => hf q (List.mem_cons_of_mem _ hq))
    have hh:=hf q List.mem_cons_self
    simp only [List.map_cons,List.prod_cons,Int.natAbs_mul,List.length_cons]
    calc
      _ ≤ N^B*N^(B*qs.length) := Nat.mul_le_mul hh ht
      _ = _ := by rw [← pow_add]; congr 1; ring

/-- Every original grid numerator/denominator suffix has its own literal
factor-count bound, including the actual right-recursive traversal frames. -/
theorem grid_bounds (a h u : ℕ) (t : Fin (size a)) (qs : List ℕ)
    (hq : ∀q∈qs,q < size a) :
    (gridRows (geometry a t.val) h u t.val qs).numerator.natAbs ≤ (size a)^((h*u)*qs.length) ∧
    (gridRows (geometry a t.val) h u t.val qs).denominator.natAbs ≤ (size a)^((h*u)*qs.length) := by
  have hN : 0 < size a := by unfold size; positivity
  have hm (q : ℕ) : nodeMultiplicity a h u q ≤ h*u := Nat.mul_le_mul_left h (Nat.sub_le _ _)
  constructor
  · rw [gridRows_numerator a h u t.val qs hq]
    apply product_bound
    intro q hmem
    split_ifs
    · simp only [Int.natAbs_one]; exact Nat.one_le_pow _ _ hN
    · simp only [Int.natAbs_pow,Int.natAbs_neg]
      exact (Nat.pow_le_pow_left (point_abs_lt a q (hq q hmem)).le _).trans
        (Nat.pow_le_pow_right hN (hm q))
  · rw [gridRows_denominator a h u t.val qs hq]
    apply product_bound
    intro q hmem
    split_ifs
    · simp only [Int.natAbs_one]; exact Nat.one_le_pow _ _ hN
    · simp only [Int.natAbs_pow]
      have he : point a t.val-point a q=difference t.val q := by unfold point difference; ring
      rw [he]
      exact (Nat.pow_le_pow_left (difference_abs_lt (size a) t.val q t.isLt (hq q hmem)).le _).trans
        (Nat.pow_le_pow_right hN (hm q))

/-- Actual original full-grid suffixes use the SAME polynomial bit exponent;
no rational cancellation or final-output height is used. -/
theorem grid_suffix_bits (a h u : ℕ) (t : Fin (size a)) (k : ℕ) :
    let qs:=((indices (geometry a t.val).size).value).drop k
    (gridRows (geometry a t.val) h u t.val qs).numerator.natAbs ≤ 2^bitExponent a h u ∧
    (gridRows (geometry a t.val) h u t.val qs).denominator.natAbs ≤ 2^bitExponent a h u := by
  dsimp only
  simp only [indices_value,geometry_size]
  have hq : ∀q∈(List.range (size a)).drop k,q < size a := by
    intro q hq
    exact List.mem_range.mp (List.mem_of_mem_drop hq)
  have hb:=grid_bounds a h u t ((List.range (size a)).drop k) hq
  have hl : ((List.range (size a)).drop k).length ≤ size a := by simp
  have he : (size a)^((h*u)*((List.range (size a)).drop k).length) ≤ 2^bitExponent a h u := by
    change (2^(a+1))^_ ≤ _
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by decide : 0 < (2:ℕ))
    unfold bitExponent
    nlinarith only [hl,Nat.mul_le_mul_left ((a+1)*(h*u)) hl]
  exact ⟨hb.1.trans he,hb.2.trans he⟩

/-- A common-denominator certificate for every executed right-recursive local
sum on actual retained indices. The numerator cap uses its literal length. -/
theorem sum_representation (a h u : ℕ) (t : Fin (size a))
    (hq : 0 < nodeMultiplicity a h u t.val) (j : ℕ) (keys : List ℕ)
    (hk : ∀k∈keys,k < nodeMultiplicity a h u t.val) :
    let q:=nodeMultiplicity a h u t.val
    let D:=sourceDenominator a h u t.val
    let V:=SemiprimeJetArrayHeight.inverseBase q D (sourceNumerator a h u t.val)
    Representation
      (sumWeights j (SemiprimeD1JetRecoveryWeights.acquire a h u t.val).inverse.coefficients
        (powersRun (SemiprimeD1WeightPrecision.argument a t.val) q).value keys).value
      ((D*size a)^q) (keys.length*(V*size a)^q) := by
  dsimp only
  let q:=nodeMultiplicity a h u t.val
  let D:=sourceDenominator a h u t.val
  let V:=SemiprimeJetArrayHeight.inverseBase q D (sourceNumerator a h u t.val)
  induction keys with
  | nil => simpa only [sumWeights,List.length_nil,Nat.zero_mul] using representation_zero ((D*size a)^q)
  | cons k ks ih =>
    have hkt:=hk k List.mem_cons_self
    have ht:=ih (fun k h => hk k (List.mem_cons_of_mem _ h))
    have term : Representation
        (if j ≤ k then coefficient (SemiprimeD1JetRecoveryWeights.acquire a h u t.val).inverse.coefficients (k-j)*
          coefficient (powersRun (SemiprimeD1WeightPrecision.argument a t.val) q).value k else 0)
        ((D*size a)^q) ((V*size a)^q) := by
      split_ifs with hj
      · rw [powersRun_coefficient _ q k hkt]
        have hm:=representation_mul (original_inverse_representation a h u t hq (k-j) (by omega))
          (argument_power_representation a h u t k hkt.le)
        simpa only [mul_pow] using hm
      · exact representation_mono (representation_zero _) (Nat.zero_le _)
    by_cases hj : j ≤ k
    · simp only [sumWeights,hj,ite_true]
      have hm:=representation_add (by simpa only [hj,ite_true] using term) ht
      convert hm using 1
      simp only [List.length_cons]
      ring
    · simp only [sumWeights,hj,ite_false]
      exact representation_mono ht (Nat.mul_le_mul_right _ (by simp))

/-- The actually executed scalar multiply after ANY retained right suffix has
the SAME original common denominator and numerator cap as the stored weight. -/
theorem weight_suffix_representation (a h u : ℕ) (t : Fin (size a))
    (hq : 0 < nodeMultiplicity a h u t.val) (j k : ℕ) :
    let q:=nodeMultiplicity a h u t.val
    Representation
      (weightRun (Ezero a h u t.val) j
        (SemiprimeD1JetRecoveryWeights.acquire a h u t.val).inverse.coefficients
        (powersRun (SemiprimeD1WeightPrecision.argument a t.val) q).value
        ((indices q).value.drop k)).value
      (weightDenominator a h u t.val) (weightNumerator a h u t.val) := by
  dsimp only
  let q:=nodeMultiplicity a h u t.val
  have hk : ∀x∈((indices q).value.drop k),x < q := by
    intro x hx
    rw [indices_value] at hx
    exact List.mem_range.mp (List.mem_of_mem_drop hx)
  have hs:=sum_representation a h u t hq j ((indices q).value.drop k) hk
  have hm:=representation_mul (scalar_representation a h u t.val) hs
  change Representation _ _ _ at hm
  apply representation_mono hm
  have hl : ((indices q).value.drop k).length ≤ q := by simp [indices_value]
  unfold weightNumerator
  dsimp only [q] at *
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (scalarNumerator a h u t.val)
    (Nat.mul_le_mul_right _ hl)

/-- Every actual repeated rational-power prefix has an original common
representation, including all recursive frames inside the power cache. -/
theorem rationalPower_representation (a h u : ℕ) (t : Fin (size a)) (k : ℕ)
    (hk : k ≤ nodeMultiplicity a h u t.val) :
    Representation (rationalPower (SemiprimeD1WeightPrecision.argument a t.val) k).value
      ((size a)^nodeMultiplicity a h u t.val) ((size a)^nodeMultiplicity a h u t.val) := by
  rw [rationalPower_value]
  exact argument_power_representation a h u t k hk

/-- Actual normalized rational powers cannot exceed the original integer
power denominator, at ANY executed recursion prefix. -/
theorem rationalPower_bounds (a h u : ℕ) (t : Fin (size a)) (k : ℕ)
    (hk : k ≤ nodeMultiplicity a h u t.val) :
    (rationalPower (SemiprimeD1WeightPrecision.argument a t.val) k).value.den ≤
      (size a)^nodeMultiplicity a h u t.val ∧
    (rationalPower (SemiprimeD1WeightPrecision.argument a t.val) k).value.num.natAbs ≤
      (size a)^nodeMultiplicity a h u t.val :=
  representation_reduced_bound (by unfold size; positivity) (rationalPower_representation a h u t k hk)

/-- Every ACTUAL weighted right-recursive suffix has the original dyadic
normalization cap, derived from its common representation and original factors. -/
theorem weight_suffix_bits (a h u : ℕ) (t : Fin (size a))
    (hq : 0 < nodeMultiplicity a h u t.val) (j k : ℕ) :
    let q:=nodeMultiplicity a h u t.val
    let value:=(weightRun (Ezero a h u t.val) j
      (SemiprimeD1JetRecoveryWeights.acquire a h u t.val).inverse.coefficients
      (powersRun (SemiprimeD1WeightPrecision.argument a t.val) q).value
      ((indices q).value.drop k)).value
    value.den ≤ 2^SemiprimeD1HermiteWeightBits.weightExponent a h u t.val ∧
    value.num.natAbs ≤ 2^SemiprimeD1HermiteWeightBits.weightExponent a h u t.val := by
  have hr:=representation_reduced_bound (weightDenominator_pos a h u t.val)
    (weight_suffix_representation a h u t hq j k)
  have hb:=SemiprimeD1HermiteWeightBits.weight_bounds a h u t
  exact ⟨hr.1.trans hb.1,hr.2.trans hb.2⟩

/-- Literal dyadic cap for the NEW unweighted right-recursive scalar sums. -/
def sumExponent (a h u t : ℕ) : ℕ :=
  nodeMultiplicity a h u t+SemiprimeD1HermiteDenominatorBits.inverseExponent a h u t+
    (a+1)*nodeMultiplicity a h u t+1

/-- Every actual normalized unweighted scalar-sum suffix has a dyadic cap,
derived from actual inverse and power representations, without cancellation. -/
theorem sum_suffix_bits (a h u : ℕ) (t : Fin (size a))
    (hq : 0 < nodeMultiplicity a h u t.val) (j k : ℕ) :
    let q:=nodeMultiplicity a h u t.val
    let value:=(sumWeights j (SemiprimeD1JetRecoveryWeights.acquire a h u t.val).inverse.coefficients
      (powersRun (SemiprimeD1WeightPrecision.argument a t.val) q).value
      ((indices q).value.drop k)).value
    value.den ≤ 2^sumExponent a h u t.val ∧ value.num.natAbs ≤ 2^sumExponent a h u t.val := by
  dsimp only
  let q:=nodeMultiplicity a h u t.val
  let D:=sourceDenominator a h u t.val
  let V:=inverseBase q D (sourceNumerator a h u t.val)
  let keys:=((indices q).value.drop k)
  have hk : ∀x∈keys,x < q := by
    intro x hx
    dsimp only [keys] at hx
    rw [indices_value] at hx
    exact List.mem_range.mp (List.mem_of_mem_drop hx)
  have hr:=representation_reduced_bound (by
      exact pow_pos (Nat.mul_pos (sourceDenominator_pos a h u t.val) (by unfold size; positivity)) q)
    (sum_representation a h u t hq j keys hk)
  have hi:=SemiprimeD1HermiteDenominatorBits.inverse_power_bounds a h u t
  have hN : (size a)^q=2^((a+1)*q) := by unfold size; rw [← pow_mul]
  have hlen : keys.length ≤ 2^q := by
    have hl : keys.length ≤ q := by simp [keys,indices_value]
    exact hl.trans (SemiprimeD1HermiteDenominatorBits.self_le_two_power q)
  have hd : (D*size a)^q ≤ 2^(SemiprimeD1HermiteDenominatorBits.inverseExponent a h u t.val+(a+1)*q) := by
    rw [mul_pow,hN,pow_add]
    exact Nat.mul_le_mul_right _ hi.1
  have hn : keys.length*(V*size a)^q ≤
      2^(q+SemiprimeD1HermiteDenominatorBits.inverseExponent a h u t.val+(a+1)*q) := by
    rw [mul_pow,hN,pow_add,pow_add]
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul hlen
      (Nat.mul_le_mul_right (2^((a+1)*q)) hi.2)
  constructor
  · apply hr.1.trans (hd.trans _)
    apply Nat.pow_le_pow_right (by decide : 0 < (2:ℕ))
    unfold sumExponent
    dsimp only [q]
    omega
  · apply hr.2.trans (hn.trans _)
    apply Nat.pow_le_pow_right (by decide : 0 < (2:ℕ))
    unfold sumExponent
    dsimp only [q]
    omega

/-- Original taper parameters make the new scalar-sum exponent polynomial
in original dimensions. No numerical sum value or target height is supplied. -/
theorem original_sumExponent_le (a M u t : ℕ) (hM : u ≤ M) :
    sumExponent a (height M u) u t ≤ 4*M+SemiprimeD1HermiteDenominatorBits.inverseEnvelope a M+(a+1)*(4*M)+1 := by
  have hq:=SemiprimeD1WeightPrecision.nodeMultiplicity_le a M u t hM
  have hi:=SemiprimeD1HermiteDenominatorBits.original_inverseExponent_le a M u t hM
  unfold sumExponent
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hq hi) (Nat.mul_le_mul_left _ hq)) 1

end RiemannGaussian.SemiprimeD1RecoveryWeightRunState
