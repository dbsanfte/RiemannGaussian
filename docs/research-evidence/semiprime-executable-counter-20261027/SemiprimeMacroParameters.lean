/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMacroGraph
import Mathlib

/-!
# Actual public macro-FFT compiler parameters

The dyadic transform is characterized by the literal loop's least admissible
power, then all radix/axis/graph bounds are derived from those public formulas.
No wanted wire or scope bound is an input.
-/
set_option autoImplicit false
noncomputable section
namespace RiemannGaussian.SemiprimeMacroParameters
open scoped BigOperators
open RiemannGaussian.SemiprimeMacroFermatNetwork
open RiemannGaussian.SemiprimeMacroGraph

/-- Python's `N.bit_length()`, with the usual zero convention. -/
def bitLength (N : ℕ) : ℕ := N.size

/-- Least exponent whose square dyadic reaches 16L. -/
def transformExponent (L : ℕ) : ℕ := (Nat.clog 2 (16 * L) + 1) / 2

/-- The actual least dyadic transform length, for positive L. -/
def transformLength (L : ℕ) : ℕ := 2 ^ transformExponent L

/-- The actual compiler radix bit width. -/
def radixBits (L : ℕ) : ℕ := transformLength L / 4

/-- The literal integer ceiling used for the number of active input digits. -/
def digitCount (L : ℕ) : ℕ := (L + radixBits L - 1) / radixBits L

/-- The literal public first-axis power. -/
def firstAxis (L : ℕ) : ℕ := 2 ^ (transformExponent L / 2)

/-- The literal public second-axis integer quotient. -/
def secondAxis (L : ℕ) : ℕ := transformLength L / firstAxis L

theorem bitLength_pos {N : ℕ} (hN : 0 < N) : 0 < bitLength N := Nat.size_pos.mpr hN

theorem input_lt_bitLength_power (N : ℕ) : N < 2 ^ bitLength N := Nat.lt_size_self N

/-- The loop's minimum length four is automatic from a positive input width. -/
theorem transformExponent_ge_two {L : ℕ} (hL : 0 < L) : 2 ≤ transformExponent L := by
  have hm : 8 < 16 * L := by omega
  have hc : 3 < Nat.clog 2 (16 * L) := (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by norm_num; omega)
  unfold transformExponent
  omega

/-- The exact transform square meets the stopping threshold. -/
theorem transform_square_lower (L : ℕ) :
    16 * L ≤ transformLength L ^ 2 := by
  have hc := Nat.le_pow_clog (by decide : 1 < 2) (16 * L)
  have he : Nat.clog 2 (16 * L) ≤ 2 * transformExponent L := by unfold transformExponent; omega
  calc
    16 * L ≤ 2 ^ Nat.clog 2 (16 * L) := hc
    _ ≤ 2 ^ (2 * transformExponent L) := Nat.pow_le_pow_right (by decide) he
    _ = _ := by rw [transformLength, ← pow_mul]; congr 1; omega

/-- The square overshoots by less than four, uniformly on every positive L. -/
theorem transform_square_upper {L : ℕ} (hL : 0 < L) :
    transformLength L ^ 2 < 64 * L := by
  have hc : 1 ≤ Nat.clog 2 (16 * L) := Nat.clog_pos (by decide) (by omega)
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (show 1 < 16 * L by omega)
  simp only [Nat.pred_eq_sub_one] at hp
  have he : 2 * transformExponent L ≤ Nat.clog 2 (16 * L) + 1 := by unfold transformExponent; omega
  have hex : (2 : ℕ) ^ (Nat.clog 2 (16 * L) + 1) =
      4 * 2 ^ (Nat.clog 2 (16 * L) - 1) := by
    rw [show Nat.clog 2 (16 * L) + 1 = (Nat.clog 2 (16 * L) - 1) + 2 by omega, pow_add]
    norm_num
    ring
  calc
    transformLength L ^ 2 = 2 ^ (2 * transformExponent L) := by
      rw [transformLength, ← pow_mul]; congr 1; omega
    _ ≤ 2 ^ (Nat.clog 2 (16 * L) + 1) := Nat.pow_le_pow_right (by decide) he
    _ = _ := hex
    _ < _ := by omega

/-- No smaller dyadic can pass the actual loop's stopping condition. -/
theorem transform_minimal {L k : ℕ} (hstop : 16 * L ≤ (2 ^ k) ^ 2) :
    transformExponent L ≤ k := by
  have hc : Nat.clog 2 (16 * L) ≤ 2 * k := by
    apply Nat.clog_le_of_le_pow
    simpa only [← pow_mul, Nat.mul_comm] using hstop
  unfold transformExponent
  omega

/-- Explicit dyadic factorization licensing the division by four. -/
theorem transform_quarter_factor {L : ℕ} (hL : 0 < L) :
    transformLength L = 4 * 2 ^ (transformExponent L - 2) := by
  have hk := transformExponent_ge_two hL
  unfold transformLength
  rw [show transformExponent L = 2 + (transformExponent L - 2) by omega, pow_add]
  norm_num

/-- Radix width is a positive power of two, not a floor approximation. -/
theorem radixBits_eq_power {L : ℕ} (hL : 0 < L) :
    radixBits L = 2 ^ (transformExponent L - 2) := by
  unfold radixBits
  rw [transform_quarter_factor hL, Nat.mul_div_cancel_left _ (by decide)]

theorem radixBits_pos {L : ℕ} (hL : 0 < L) : 0 < radixBits L := by rw [radixBits_eq_power hL]; positivity

theorem transform_eq_four_radixBits {L : ℕ} (hL : 0 < L) :
    transformLength L = 4 * radixBits L := by rw [radixBits_eq_power hL, transform_quarter_factor hL]

theorem input_width_le_radix_square {L : ℕ} (hL : 0 < L) : L ≤ radixBits L ^ 2 := by
  have hs := transform_square_lower L
  rw [transform_eq_four_radixBits hL] at hs
  nlinarith

/-- The actual digit ceiling is positive and lies within the quarter length. -/
theorem digitCount_bounds {L : ℕ} (hL : 0 < L) : 0 < digitCount L ∧ digitCount L ≤ radixBits L := by
  have hb := radixBits_pos hL
  have hsq := input_width_le_radix_square hL
  have hid : L + radixBits L - 1 + 1 = L + radixBits L := Nat.sub_add_cancel (by omega)
  have hnum : L + radixBits L - 1 < (radixBits L + 1) * radixBits L := by nlinarith
  have hnumlo : radixBits L ≤ L + radixBits L - 1 := by omega
  constructor
  · have hd : 1 ≤ digitCount L := (Nat.le_div_iff_mul_le hb).mpr (by simpa using hnumlo)
    exact Nat.lt_of_lt_of_le (by decide : 0 < 1) hd
  · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hb).mpr hnum)

/-- Active digits cover precisely enough radix width for every original bit. -/
theorem digitCount_covers {L : ℕ} (hL : 0 < L) : L ≤ digitCount L * radixBits L := by
  have hb := radixBits_pos hL
  have h := Nat.lt_mul_div_succ (L + radixBits L - 1) hb
  change L + radixBits L - 1 < radixBits L * (digitCount L + 1) at h
  have hid : L + radixBits L - 1 + 1 = L + radixBits L := Nat.sub_add_cancel (by omega)
  nlinarith

/-- The last active digit is nonempty; there is no extra active zero digit. -/
theorem digitCount_minimal {L : ℕ} (hL : 0 < L) :
    (digitCount L - 1) * radixBits L < L := by
  have hd := (digitCount_bounds hL).1
  have hb := radixBits_pos hL
  have h := Nat.div_mul_le_self (L + radixBits L - 1) (radixBits L)
  change digitCount L * radixBits L ≤ L + radixBits L - 1 at h
  have he : (digitCount L - 1) * radixBits L + radixBits L = digitCount L * radixBits L := by
    calc
      _ = (digitCount L - 1 + 1) * radixBits L := by ring
      _ = _ := by rw [Nat.sub_add_cancel hd]
  have hid : L + radixBits L - 1 + 1 = L + radixBits L := Nat.sub_add_cancel (by omega)
  nlinarith

/-- The formula is exactly the least allowed dyadic of the original while loop. -/
theorem transform_loop_characterization {L : ℕ} (hL : 0 < L) :
    4 ≤ transformLength L ∧ 16 * L ≤ transformLength L ^ 2 ∧
      ∀ k : ℕ, 2 ≤ k → 16 * L ≤ (2 ^ k) ^ 2 → transformLength L ≤ 2 ^ k := by
  refine ⟨?_, transform_square_lower L, ?_⟩
  · have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (transformExponent_ge_two hL)
    simpa only [transformLength] using h
  · intro k _ hk
    exact Nat.pow_le_pow_right (by decide) (transform_minimal hk)

/-- The source arithmetic bridge's actual dyadic-depth parameter. -/
def macroDepth (L : ℕ) : ℕ := transformExponent L - 1

theorem transform_eq_macroLength {L : ℕ} (hL : 0 < L) :
    transformLength L = macroLength (macroDepth L) := by
  unfold transformLength macroLength macroDepth
  rw [Nat.sub_add_cancel (by have := transformExponent_ge_two hL; omega)]

/-- The actual dyadic bit length licenses the Python axis formula verbatim. -/
theorem firstAxis_code_formula (L : ℕ) :
    firstAxis L = 2 ^ ((bitLength (transformLength L) - 1) / 2) := by
  simp [firstAxis, bitLength, transformLength, Nat.size_pow]

/-- The second-axis quotient is an exact power of two. -/
theorem secondAxis_eq_power (L : ℕ) :
    secondAxis L = 2 ^ (transformExponent L - transformExponent L / 2) := by
  have he : transformLength L = firstAxis L *
      2 ^ (transformExponent L - transformExponent L / 2) := by
    unfold transformLength firstAxis
    rw [← pow_add, Nat.add_sub_of_le (Nat.div_le_self _ _)]
  unfold secondAxis
  rw [he, Nat.mul_div_cancel_left _ (by unfold firstAxis; positivity)]

/-- The actual public axes factor the complete transform exactly. -/
theorem axes_product (L : ℕ) : firstAxis L * secondAxis L = transformLength L := by
  rw [secondAxis_eq_power, firstAxis, ← pow_add, Nat.add_sub_of_le (Nat.div_le_self _ _)]
  rfl

/-- The code's two powers are balanced with a factor at most two. -/
theorem axes_balanced (L : ℕ) :
    firstAxis L ≤ secondAxis L ∧ secondAxis L ≤ 2 * firstAxis L := by
  rw [secondAxis_eq_power, firstAxis]
  constructor
  · exact Nat.pow_le_pow_right (by decide) (by omega)
  · calc
      _ ≤ 2 ^ (transformExponent L / 2 + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = _ := by rw [pow_succ]; ring

/-- Quantitative balanced-axis square, used to obtain a fourth-power scope bound. -/
theorem secondAxis_square_le (L : ℕ) : secondAxis L ^ 2 ≤ 2 * transformLength L := by
  rw [secondAxis_eq_power, transformLength, ← pow_mul]
  calc
    2 ^ ((transformExponent L - transformExponent L / 2) * 2) ≤
        2 ^ (transformExponent L + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = _ := by rw [pow_succ]; ring

theorem axes_ge_two {L : ℕ} (hL : 0 < L) : 2 ≤ firstAxis L ∧ 2 ≤ secondAxis L := by
  have hk := transformExponent_ge_two hL
  have hr : 2 ≤ firstAxis L := by
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 1 ≤ transformExponent L / 2 by omega)
    simpa only [firstAxis] using h
  exact ⟨hr, hr.trans (axes_balanced L).1⟩

/-- Actual Boolean variables after equality subdivision. -/
def variableCount (L : ℕ) : ℕ :=
  Fintype.card (SemiprimeMacroGraph.Edge (firstAxis L) (secondAxis L) (digitCount L))

/-- Actual uniform scope bound for the compiled equality graph. -/
def scopeBound (L : ℕ) : ℕ :=
  (2 * (firstAxis L + secondAxis L) + 3) * (transformLength L + 1)

theorem variableCount_le {L : ℕ} (hL : 0 < L) : variableCount L ≤ 6400 * L := by
  have hn := (transform_loop_characterization hL).1
  have hd := digitCount_bounds hL
  have hb := transform_eq_four_radixBits hL
  have hu := transform_square_upper hL
  rw [variableCount, SemiprimeMacroGraph.edge_card _ _ _ hd.1, axes_product]
  have hsub := Nat.sub_le ((13 * transformLength L + 1) *
    (transformLength L + 1) + 4 * digitCount L) 2
  have hd' : digitCount L ≤ transformLength L := by omega
  nlinarith

theorem input_le_variableCount {L : ℕ} (hL : 0 < L) : L ≤ variableCount L := by
  have hd := digitCount_bounds hL
  have hl := transform_square_lower L
  rw [variableCount, SemiprimeMacroGraph.edge_card _ _ _ hd.1, axes_product]
  have hs : 2 ≤ (13 * transformLength L + 1) * (transformLength L + 1) +
      4 * digitCount L := by nlinarith
  have he := Nat.sub_add_cancel hs
  nlinarith

theorem actual_arity_le {L : ℕ}
    (v : SemiprimeMacroGraph.SubdividedVertex (firstAxis L) (secondAxis L) (digitCount L)) :
    SemiprimeMacroGraph.subdividedArity v ≤ scopeBound L := by
  simpa only [scopeBound, axes_product] using SemiprimeMacroGraph.subdivided_arity_bound v

/-- An integer-only fourth-power form of the actual `O(L^(3/4))` scope bound. -/
theorem scopeBound_fourth_le {L : ℕ} (hL : 0 < L) :
    scopeBound L ^ 4 ≤ 512 ^ 4 * L ^ 3 := by
  have hn := (transform_loop_characterization hL).1
  have ht := (axes_ge_two hL).2
  have hr := (axes_balanced L).1
  have hs := secondAxis_square_le L
  have hu := transform_square_upper hL
  have hsmall : scopeBound L ≤ 16 * secondAxis L * transformLength L := by
    unfold scopeBound
    nlinarith
  calc
    scopeBound L ^ 4 ≤ (16 * secondAxis L * transformLength L) ^ 4 :=
      Nat.pow_le_pow_left hsmall 4
    _ = 65536 * (secondAxis L ^ 2) ^ 2 * transformLength L ^ 4 := by ring
    _ ≤ 65536 * (2 * transformLength L) ^ 2 * transformLength L ^ 4 := by
      gcongr
    _ = 262144 * (transformLength L ^ 2) ^ 3 := by ring
    _ ≤ 262144 * (64 * L) ^ 3 := by gcongr
    _ = 512 ^ 4 * L ^ 3 := by ring

/-- The public input gives the actual real scope estimate, uniformly for all positive widths. -/
theorem scopeBound_le_rpow {L : ℕ} (hL : 0 < L) :
    (scopeBound L : ℝ) ≤ 512 * (L : ℝ) ^ ((3 : ℝ) / 4) := by
  have h := scopeBound_fourth_le hL
  have hr : (scopeBound L : ℝ) ^ 4 ≤ (512 : ℝ) ^ 4 * (L : ℝ) ^ 3 := by
    exact_mod_cast h
  apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (by positivity)
  convert hr using 1
  rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ L)]
  norm_num

/-- Literal quarter-radix capacity follows from the public schedule. -/
theorem physical_coefficient_capacity {L : ℕ} (hL : 0 < L) :
    digitCount L * (2 ^ radixBits L) ^ 2 < 2 ^ transformLength L :=
  SemiprimeMacroFermatNetwork.compiler_quarter_strict_bound _ _ _ (digitCount_bounds hL).2
    (radixBits_pos hL) (transform_eq_four_radixBits hL)

/-- Number of physically active bits in input digit `i`. -/
def activeDigitBits (L i : ℕ) : ℕ := min (radixBits L) (L - i * radixBits L)

theorem activeDigitBits_bounds {L i : ℕ} (hL : 0 < L) (hi : i < digitCount L) :
    0 < activeDigitBits L i ∧ activeDigitBits L i ≤ radixBits L := by
  have hb := radixBits_pos hL
  have hm := digitCount_minimal hL
  have hi' : i ≤ digitCount L - 1 := by omega
  have hm' := Nat.mul_le_mul_right (radixBits L) hi'
  simp only [activeDigitBits, lt_min_iff]
  omega

/-- Literal least-significant-first radix digit of an integer. -/
def targetDigit (L N i : ℕ) : ℕ := (N / (2 ^ radixBits L) ^ i) % (2 ^ radixBits L)

theorem radix_digit_sum (N base d : ℕ) :
    (∑ i ∈ Finset.range d, (N / base ^ i % base) * base ^ i) = N % base ^ d := by
  induction d generalizing N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, pow_zero, Nat.mod_one]
  | succ d ih =>
    rw [SemiprimeMacroFermatNetwork.radix_sum_succ]
    simp only [pow_zero, Nat.div_one]
    have hsum : (∑ k ∈ Finset.range d, N / base ^ (k + 1) % base * base ^ k) =
        ∑ k ∈ Finset.range d, (N / base) / base ^ k % base * base ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Nat.div_div_eq_div_mul, pow_succ']
    rw [hsum, ih, pow_succ', Nat.mod_mul]

theorem targetDigit_sum {L N : ℕ} (hL : 0 < L) (hN : N < 2 ^ L) :
    (∑ i ∈ Finset.range (digitCount L), targetDigit L N i *
      (2 ^ radixBits L) ^ i) = N := by
  have hp : N < (2 ^ radixBits L) ^ digitCount L := by
    rw [← pow_mul]
    exact hN.trans_le (Nat.pow_le_pow_right (by decide) (by
      simpa only [Nat.mul_comm] using digitCount_covers hL))
  exact (radix_digit_sum N (2 ^ radixBits L) (digitCount L)).trans (Nat.mod_eq_of_lt hp)

theorem targetDigit_active_bound {L N i : ℕ} (hL : 0 < L) (hN : N < 2 ^ L)
    (hi : i < digitCount L) : targetDigit L N i < 2 ^ activeDigitBits L i := by
  have hb := radixBits_pos hL
  have hm := digitCount_minimal hL
  have hi' : i ≤ digitCount L - 1 := by omega
  have him : i * radixBits L < L := lt_of_le_of_lt
    (Nat.mul_le_mul_right (radixBits L) hi') hm
  have hpow : 0 < (2 ^ radixBits L) ^ i := by positivity
  have hquot : N / (2 ^ radixBits L) ^ i < 2 ^ (L - i * radixBits L) := by
    apply (Nat.div_lt_iff_lt_mul hpow).mpr
    rw [← pow_mul, Nat.mul_comm (radixBits L) i,
      Nat.pow_sub_mul_pow 2 (Nat.le_of_lt him)]
    exact hN
  unfold targetDigit activeDigitBits
  rcases le_total (radixBits L) (L - i * radixBits L) with h | h
  · rw [min_eq_left h]
    exact Nat.mod_lt _ (by positivity)
  · rw [min_eq_right h]
    exact lt_of_le_of_lt (Nat.mod_le _ _) hquot

/-- The graph scope estimate in terms of its own actual Boolean variable count. -/
theorem scopeBound_le_variableCount_rpow {L : ℕ} (hL : 0 < L) :
    (scopeBound L : ℝ) ≤ 512 * (variableCount L : ℝ) ^ ((3 : ℝ) / 4) := by
  apply (scopeBound_le_rpow hL).trans
  gcongr
  exact_mod_cast input_le_variableCount hL

/-- Every active nonfinal input digit has exactly the full radix width. -/
theorem activeDigitBits_full {L i : ℕ} (hL : 0 < L) (hi : i + 1 < digitCount L) :
    activeDigitBits L i = radixBits L := by
  have hm := digitCount_minimal hL
  have hstep : (i + 1) * radixBits L ≤ (digitCount L - 1) * radixBits L :=
    Nat.mul_le_mul_right _ (by omega)
  have hsum : i * radixBits L + radixBits L < L := by nlinarith
  unfold activeDigitBits
  apply min_eq_left
  omega

/-- The final digit width is precisely the literal top-bit truncation. -/
theorem activeDigitBits_last {L : ℕ} (hL : 0 < L) :
    activeDigitBits L (digitCount L - 1) = L - (digitCount L - 1) * radixBits L := by
  have hc := digitCount_covers hL
  have hd := (digitCount_bounds hL).1
  have he : (digitCount L - 1) * radixBits L + radixBits L =
      digitCount L * radixBits L := by
    calc
      _ = (digitCount L - 1 + 1) * radixBits L := by ring
      _ = _ := by rw [Nat.sub_add_cancel hd]
  unfold activeDigitBits
  apply min_eq_right
  omega

/-- The actual public target digits reconstruct `N`. -/
theorem public_targetDigit_sum {N : ℕ} (hN : 0 < N) :
    (∑ i ∈ Finset.range (digitCount (bitLength N)), targetDigit (bitLength N) N i *
      (2 ^ radixBits (bitLength N)) ^ i) = N :=
  targetDigit_sum (bitLength_pos hN) (input_lt_bitLength_power N)

/-- All candidate factors up to the public target respect every forced padding bit. -/
theorem public_factor_digit_bound {N x i : ℕ} (hN : 0 < N) (hx : x ≤ N)
    (hi : i < digitCount (bitLength N)) :
    targetDigit (bitLength N) x i < 2 ^ activeDigitBits (bitLength N) i :=
  targetDigit_active_bound (bitLength_pos hN)
    (hx.trans_lt (input_lt_bitLength_power N)) hi

/-- All target digits beyond the active input digit count are literally zero. -/
theorem targetDigit_zero {L N i : ℕ} (hL : 0 < L) (hN : N < 2 ^ L)
    (hi : digitCount L ≤ i) : targetDigit L N i = 0 := by
  have hp : N < (2 ^ radixBits L) ^ digitCount L := by
    rw [← pow_mul]
    exact hN.trans_le (Nat.pow_le_pow_right (by decide) (by
      simpa only [Nat.mul_comm] using digitCount_covers hL))
  have hp' : N < (2 ^ radixBits L) ^ i :=
    hp.trans_le (Nat.pow_le_pow_right (by positivity) hi)
  simp only [targetDigit, Nat.div_eq_of_lt hp', Nat.zero_mod]

/-- Reconstruction holds at every padded horizon, including the transform length. -/
theorem targetDigit_sum_padded {L N m : ℕ} (hL : 0 < L) (hN : N < 2 ^ L)
    (hm : digitCount L ≤ m) :
    (∑ i ∈ Finset.range m, targetDigit L N i * (2 ^ radixBits L) ^ i) = N := by
  have hs : (∑ i ∈ Finset.range (digitCount L), targetDigit L N i * (2 ^ radixBits L) ^ i) =
      ∑ i ∈ Finset.range m, targetDigit L N i * (2 ^ radixBits L) ^ i := by
    apply Finset.sum_subset (Finset.range_mono hm)
    intro i hi hnot
    have hiz : digitCount L ≤ i := by
      simp only [Finset.mem_range, not_lt] at hnot
      exact hnot
    rw [targetDigit_zero hL hN hiz, zero_mul]
  exact hs.symm.trans (targetDigit_sum hL hN)

/-- Literal public target reconstruction at the full transform horizon. -/
theorem public_targetDigit_sum_transform {N : ℕ} (hN : 0 < N) :
    (∑ i ∈ Finset.range (transformLength (bitLength N)), targetDigit (bitLength N) N i *
      (2 ^ radixBits (bitLength N)) ^ i) = N := by
  apply targetDigit_sum_padded (bitLength_pos hN) (input_lt_bitLength_power N)
  have hd := (digitCount_bounds (bitLength_pos hN)).2
  have hn := transform_eq_four_radixBits (bitLength_pos hN)
  omega

end RiemannGaussian.SemiprimeMacroParameters
