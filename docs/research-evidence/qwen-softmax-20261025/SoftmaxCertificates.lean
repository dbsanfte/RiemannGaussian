import LeanCert.Core.IntervalRat.Taylor
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open scoped BigOperators
namespace SoftmaxCertificates

theorem normalized_interval (w l u L U : ℝ)
    (hl : 0 ≤ l) (hlw : l ≤ w) (hwu : w ≤ u)
    (hL : 0 < L) (hLs : L ≤ U)
    (S : ℝ) (hLS : L ≤ S) (hSU : S ≤ U) :
    l / U ≤ w / S ∧ w / S ≤ u / L := by
  have hS : 0 < S := hL.trans_le hLS
  have hU : 0 < U := hL.trans_le hLs
  have hw : 0 ≤ w := hl.trans hlw
  constructor
  · exact (div_le_div_of_nonneg_left hl hS hSU).trans
      (div_le_div_of_nonneg_right hlw hS.le)
  · exact (div_le_div_of_nonneg_left hw hL hLS).trans
      (div_le_div_of_nonneg_right hwu hL.le)

/-- Keep the numerator/denominator dependency: S is the mass of other entries. -/
theorem dependent_interval (w l u L U S : ℝ)
    (hl : 0 ≤ l) (hlw : l ≤ w) (hwu : w ≤ u)
    (hL : 0 ≤ L) (hLS : L ≤ S) (hSU : S ≤ U)
    (hlU : 0 < l + U) (hwS : 0 < w + S) (huL : 0 < u + L) :
    l / (l + U) ≤ w / (w + S) ∧ w / (w + S) ≤ u / (u + L) := by
  have hw := hl.trans hlw
  have hu := hw.trans hwu
  have hS := hL.trans hLS
  constructor
  · apply (div_le_div_iff₀ hlU hwS).2
    have hmul := mul_le_mul hlw hSU hS hw
    nlinarith
  · apply (div_le_div_iff₀ hwS huL).2
    have hmul := mul_le_mul hwu hLS hL hu
    nlinarith

/-- Certify a rounding-cell interior with cross-products; no divisions in the checker. -/
theorem cell_of_cross_products (w l u S L U a b : ℝ)
    (hl : 0 ≤ l) (hlw : l ≤ w) (hwu : w ≤ u)
    (hL : 0 < L) (hLS : L ≤ S) (hSU : S ≤ U)
    (ha : a * U < l) (hb : u < b * L) : a < w / S ∧ w / S < b := by
  have h := normalized_interval w l u L U hl hlw hwu hL (hLS.trans hSU) S hLS hSU
  have hU : 0 < U := hL.trans_le (hLS.trans hSU)
  exact ⟨((lt_div_iff₀ hU).2 ha).trans_le h.1,
    h.2.trans_lt ((div_lt_iff₀ hL).2 hb)⟩

def weightLo (x : ℚ) (depth : ℕ) : ℚ :=
  max 0 (LeanCert.Core.IntervalRat.expPointComputable x depth).lo

def weightHi (x : ℚ) (depth : ℕ) : ℚ :=
  (LeanCert.Core.IntervalRat.expPointComputable x depth).hi

theorem weight_enclosure (x : ℚ) (depth : ℕ) :
    (weightLo x depth : ℝ) ≤ Real.exp x ∧
      Real.exp x ≤ (weightHi x depth : ℝ) := by
  have h := LeanCert.Core.IntervalRat.mem_expPointComputable x depth
  constructor
  · simp only [weightLo, Rat.cast_max, Rat.cast_zero]
    exact max_le (Real.exp_pos _).le h.1
  · exact h.2

def partitionLo {n : ℕ} (x : Fin n → ℚ) (depth : ℕ) : ℚ :=
  ∑ i, weightLo (x i) depth

def partitionHi {n : ℕ} (x : Fin n → ℚ) (depth : ℕ) : ℚ :=
  ∑ i, weightHi (x i) depth

def probabilityLo {n : ℕ} (x : Fin n → ℚ) (depth : ℕ) (i : Fin n) : ℚ :=
  weightLo (x i) depth / partitionHi x depth

def probabilityHi {n : ℕ} (x : Fin n → ℚ) (depth : ℕ) (i : Fin n) : ℚ :=
  weightHi (x i) depth / partitionLo x depth

theorem probability_enclosure {n : ℕ} (x : Fin n → ℚ) (depth : ℕ)
    (hL : 0 < partitionLo x depth) (i : Fin n) :
    (probabilityLo x depth i : ℝ) ≤ Real.exp (x i) / (∑ j, Real.exp (x j)) ∧
      Real.exp (x i) / (∑ j, Real.exp (x j)) ≤ (probabilityHi x depth i : ℝ) := by
  have hsL : (partitionLo x depth : ℝ) ≤ ∑ j, Real.exp (x j) := by
    simp only [partitionLo, Rat.cast_sum]
    exact Finset.sum_le_sum fun j _ => (weight_enclosure (x j) depth).1
  have hsU : (∑ j, Real.exp (x j)) ≤ (partitionHi x depth : ℝ) := by
    simp only [partitionHi, Rat.cast_sum]
    exact Finset.sum_le_sum fun j _ => (weight_enclosure (x j) depth).2
  have hrealL : (0 : ℝ) < partitionLo x depth := by exact_mod_cast hL
  have hlo : (0 : ℝ) ≤ weightLo (x i) depth := by
    simp only [weightLo, Rat.cast_max, Rat.cast_zero]
    exact le_max_left _ _
  simpa only [probabilityLo, probabilityHi, Rat.cast_div] using
    normalized_interval _ _ _ _ _ hlo (weight_enclosure (x i) depth).1
      (weight_enclosure (x i) depth).2 hrealL (hsL.trans hsU) _ hsL hsU

/-- A strict enclosure inside one rounding cell certifies that rounding result.
The cell hypothesis must be proved for the intended concrete rounding map. -/
theorem rounding_cell {α : Type*} (round : ℝ → α) (r : α)
    (p l u a b : ℝ) (hp : l ≤ p ∧ p ≤ u)
    (ha : a < l) (hb : u < b)
    (cell : ∀ y, a < y → y < b → round y = r) : round p = r :=
  cell p (ha.trans_le hp.1) (hp.2.trans_lt hb)

/-- Exact cancellation of the common component of relative weight errors. -/
theorem relative_error_identity (w Z δ δbar : ℝ)
    (hZ : Z ≠ 0) (hδ : 1 + δbar ≠ 0) :
    w * (1 + δ) / (Z * (1 + δbar)) - w / Z =
      (w / Z) * ((δ - δbar) / (1 + δbar)) := by
  field_simp
  ring

theorem common_scale_cancels (w Z c : ℝ) (hZ : Z ≠ 0) (hc : c ≠ 0) :
    (c * w) / (c * Z) = w / Z := by
  field_simp

/-- The mean relative error is weighted by the exact normalized distribution. -/
theorem weighted_relative_error_identity {n : ℕ} (w δ : Fin n → ℝ) (i : Fin n)
    (hZ : (∑ j, w j) ≠ 0) (hQ : (∑ j, w j * (1 + δ j)) ≠ 0) :
    (w i * (1 + δ i)) / (∑ j, w j * (1 + δ j)) - w i / (∑ j, w j) =
      (w i / (∑ j, w j)) *
        ((δ i - (∑ j, w j * δ j) / (∑ j, w j)) /
          (1 + (∑ j, w j * δ j) / (∑ j, w j))) := by
  have hs : (∑ j, w j * (1 + δ j)) = (∑ j, w j) + ∑ j, w j * δ j := by
    simp [mul_add, Finset.sum_add_distrib]
  rw [hs] at hQ ⊢
  have hd : 1 + (∑ j, w j * δ j) / (∑ j, w j) ≠ 0 := by
    intro hz
    apply hQ
    field_simp at hz
    linarith
  field_simp
  ring

/-- A nonnegative omitted tail changes a retained probability by this exact amount. -/
theorem tail_error_identity (w S T : ℝ) (hS : S ≠ 0) (hST : S + T ≠ 0) :
    w / S - w / (S + T) = w * T / (S * (S + T)) := by
  field_simp
  ring

/-- Uncomputed entries can be paid by their count and a shared score-gap bound. -/
theorem omitted_tail_bound {ι : Type*} (tail : Finset ι) (score : ι → ℝ)
    (anchor gap : ℝ) (hgap : ∀ j ∈ tail, score j - anchor ≤ -gap) :
    (∑ j ∈ tail, Real.exp (score j - anchor)) ≤
      (tail.card : ℝ) * Real.exp (-gap) := by
  calc
    _ ≤ ∑ _j ∈ tail, Real.exp (-gap) := Finset.sum_le_sum fun j hj =>
      Real.exp_le_exp.mpr (hgap j hj)
    _ = _ := by simp

def exampleLogits : Fin 2 → ℚ := ![0, -1]

-- Exact rational endpoint checks, reduced by the Lean kernel.
theorem example_positive : 0 < partitionLo exampleLogits 5 := by
  simp only [partitionLo, Fin.sum_univ_two]
  decide +kernel

theorem example_high_checks :
    (373 : ℚ) / 512 < probabilityLo exampleLogits 5 0 ∧
      probabilityHi exampleLogits 5 0 < (375 : ℚ) / 512 := by
  simp only [probabilityLo, probabilityHi, partitionLo, partitionHi, Fin.sum_univ_two]
  decide +kernel

theorem example_low_checks :
    (275 : ℚ) / 1024 < probabilityLo exampleLogits 5 1 ∧
      probabilityHi exampleLogits 5 1 < (277 : ℚ) / 1024 := by
  simp only [probabilityLo, probabilityHi, partitionLo, partitionHi, Fin.sum_univ_two]
  decide +kernel

/-- The high probability lies strictly inside the nearest-BF16 cell for 187/256. -/
theorem example_high_bf16_cell :
    (373 : ℝ) / 512 < Real.exp (exampleLogits 0) / (∑ j, Real.exp (exampleLogits j)) ∧
      Real.exp (exampleLogits 0) / (∑ j, Real.exp (exampleLogits j)) < (375 : ℝ) / 512 := by
  have h := probability_enclosure exampleLogits 5 example_positive 0
  have ha : (373 : ℝ) / 512 < (probabilityLo exampleLogits 5 0 : ℝ) := by
    have hcast := (Rat.cast_lt (K := ℝ)).mpr example_high_checks.1
    norm_num at hcast ⊢
    exact hcast
  have hb : (probabilityHi exampleLogits 5 0 : ℝ) < (375 : ℝ) / 512 := by
    have hcast := (Rat.cast_lt (K := ℝ)).mpr example_high_checks.2
    norm_num at hcast ⊢
    exact hcast
  exact ⟨ha.trans_le h.1, h.2.trans_lt hb⟩

/-- The low probability lies strictly inside the nearest-BF16 cell for 69/256. -/
theorem example_low_bf16_cell :
    (275 : ℝ) / 1024 < Real.exp (exampleLogits 1) / (∑ j, Real.exp (exampleLogits j)) ∧
      Real.exp (exampleLogits 1) / (∑ j, Real.exp (exampleLogits j)) < (277 : ℝ) / 1024 := by
  have h := probability_enclosure exampleLogits 5 example_positive 1
  have ha : (275 : ℝ) / 1024 < (probabilityLo exampleLogits 5 1 : ℝ) := by
    have hcast := (Rat.cast_lt (K := ℝ)).mpr example_low_checks.1
    norm_num at hcast ⊢
    exact hcast
  have hb : (probabilityHi exampleLogits 5 1 : ℝ) < (277 : ℝ) / 1024 := by
    have hcast := (Rat.cast_lt (K := ℝ)).mpr example_low_checks.2
    norm_num at hcast ⊢
    exact hcast
  exact ⟨ha.trans_le h.1, h.2.trans_lt hb⟩

/-- The local nearest codes in the two relevant BF16 binades are 187 and 138.
BF16 decoding is 187/256 and 138/512 = 69/256, respectively. -/
theorem example_nearest_local_codes :
    Int.floor (256 * (Real.exp (exampleLogits 0) /
      (∑ j, Real.exp (exampleLogits j))) + 1/2) = 187 ∧
    Int.floor (512 * (Real.exp (exampleLogits 1) /
      (∑ j, Real.exp (exampleLogits j))) + 1/2) = 138 := by
  constructor
  · apply Int.floor_eq_iff.mpr
    have h := example_high_bf16_cell
    constructor <;> norm_num at * <;> linarith
  · apply Int.floor_eq_iff.mpr
    have h := example_low_bf16_cell
    constructor <;> norm_num at * <;> linarith

#print axioms probability_enclosure
#print axioms dependent_interval
#print axioms cell_of_cross_products
#print axioms rounding_cell
#print axioms relative_error_identity
#print axioms common_scale_cancels
#print axioms weighted_relative_error_identity
#print axioms tail_error_identity
#print axioms omitted_tail_bound
#print axioms example_high_bf16_cell
#print axioms example_low_bf16_cell
#print axioms example_nearest_local_codes
end SoftmaxCertificates
