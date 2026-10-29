import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.ParameterOrder

namespace OAI.Algorithms

/-!
# Explicit parameters and the binomial tail for the interpolation layout

The binomial law is represented by exact integer weights
`choose m w * 3^(m-w)`, of total mass `4^m`.  The central second moment is proved
by the binomial recursion, without any assumed concentration inequality.
-/

namespace SubexponentialSAT.LayoutParameters

open scoped BigOperators
open Finset

/-- Integer numerator of `Bin(m,1/4)` at `w`. -/
def binomialWeight (m w : ℕ) : ℕ := m.choose w * 3 ^ (m - w)

/-- An unnormalized finite expectation, kept rational for subtraction. -/
def weightedSum (m : ℕ) (f : ℕ → ℚ) : ℚ :=
  ∑ w ∈ range (m + 1), (binomialWeight m w : ℚ) * f w

lemma weightedSum_add (m : ℕ) (f g : ℕ → ℚ) :
    weightedSum m (fun w => f w + g w) = weightedSum m f + weightedSum m g := by
  simp [weightedSum, mul_add, sum_add_distrib]

lemma weightedSum_const_mul (m : ℕ) (c : ℚ) (f : ℕ → ℚ) :
    weightedSum m (fun w => c * f w) = c * weightedSum m f := by
  simp [weightedSum, mul_left_comm, ← mul_sum]

lemma weightedSum_succ (m : ℕ) (f : ℕ → ℚ) :
    weightedSum (m + 1) f = weightedSum m (fun w => 3 * f w + f (w + 1)) := by
  unfold weightedSum binomialWeight
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc]
  rw [Finset.sum_choose_succ_mul (fun i j => (3 : ℚ) ^ j * f i) m]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro w hw
  have hwle : w ≤ m := by have := mem_range.mp hw; omega
  have he : m + 1 - w = m - w + 1 := by omega
  rw [he, pow_succ]
  ring

lemma weightedSum_mass (m : ℕ) : weightedSum m (fun _ => 1) = (4 : ℚ) ^ m := by
  induction m with
  | zero => simp [weightedSum, binomialWeight]
  | succ m ih =>
      rw [weightedSum_succ]
      have hfun : (fun _ : ℕ => (3 : ℚ) * 1 + 1) = (fun _ : ℕ => (4 : ℚ) * 1) := by
        funext w
        norm_num
      rw [hfun, weightedSum_const_mul, ih, pow_succ]
      ring

/-- The exact central second moment, after multiplying the centered variable by four. -/
theorem weightedSum_centered_square (m : ℕ) :
    weightedSum m (fun w => (4 * (w : ℚ) - m) ^ 2) = 3 * m * (4 : ℚ) ^ m := by
  induction m with
  | zero => simp [weightedSum, binomialWeight]
  | succ m ih =>
      rw [weightedSum_succ]
      have hfun :
          (fun w : ℕ => (3 : ℚ) * (4 * (w : ℚ) - (m + 1 : ℕ)) ^ 2 +
            (4 * (w + 1 : ℕ) - (m + 1 : ℕ) : ℚ) ^ 2) =
          (fun w : ℕ => 4 * (4 * (w : ℚ) - m) ^ 2 + 12 * 1) := by
        funext w
        push_cast
        ring
      rw [hfun, weightedSum_add, weightedSum_const_mul, weightedSum_const_mul,
        ih, weightedSum_mass, pow_succ]
      push_cast
      ring

/-- The total mass of the exact integer binomial numerators. -/
theorem binomialWeight_sum (m : ℕ) :
    ∑ w ∈ range (m + 1), binomialWeight m w = 4 ^ m := by
  have h : ((∑ w ∈ range (m + 1), binomialWeight m w : ℕ) : ℚ) = (4 : ℚ) ^ m := by
    simpa only [weightedSum, mul_one, Nat.cast_sum] using weightedSum_mass m
  exact_mod_cast h


/-- A consecutive interval centered within a bounded rounding error of `m/4`. -/
def intervalStart (m R : ℕ) : ℕ := (m - 2 * R) / 4

lemma intervalStart_bounds {m R : ℕ} (h : 2 * R ≤ m) :
    4 * intervalStart m R + 2 * R ≤ m ∧
      m < 4 * intervalStart m R + 2 * R + 4 := by
  unfold intervalStart
  omega

lemma intervalStart_end_le {m R : ℕ} (h : 2 * R ≤ m) :
    intervalStart m R + R ≤ m + 1 := by
  have hb := intervalStart_bounds h
  omega

lemma intervalStart_deviation {m R w : ℕ} (hsize : 2 * R ≤ m) (hR : 3 ≤ R)
    (hw : w ∉ Ico (intervalStart m R) (intervalStart m R + R)) :
    (R : ℚ) ^ 2 ≤ (4 * (w : ℚ) - m) ^ 2 := by
  have hb := intervalStart_bounds hsize
  have hR0 : (0 : ℚ) ≤ R := Nat.cast_nonneg _
  by_cases hleft : w < intervalStart m R
  · have hdev : 4 * w + R ≤ m := by omega
    have hdevQ : 4 * (w : ℚ) + R ≤ m := by exact_mod_cast hdev
    have hs := mul_self_le_mul_self hR0
      (show (R : ℚ) ≤ - (4 * (w : ℚ) - m) by linarith)
    nlinarith
  · have hright : intervalStart m R + R ≤ w := by
      simp only [mem_Ico] at hw
      omega
    have hdev : m + R ≤ 4 * w := by omega
    have hdevQ : (m : ℚ) + R ≤ 4 * (w : ℚ) := by exact_mod_cast hdev
    have hs := mul_self_le_mul_self hR0
      (show (R : ℚ) ≤ 4 * (w : ℚ) - m by linarith)
    nlinarith

/-- Integer numerator of the mass outside `[A,A+R)`. -/
def intervalTail (m A R : ℕ) : ℕ :=
  ∑ w ∈ range (m + 1), if w ∈ Ico A (A + R) then 0 else binomialWeight m w

/-- Exact finite second-moment (Chebyshev) inequality, with no probabilistic assumptions. -/
theorem intervalTail_second_moment {m R : ℕ} (hsize : 2 * R ≤ m) (hR : 3 ≤ R) :
    R ^ 2 * intervalTail m (intervalStart m R) R ≤ 3 * m * 4 ^ m := by
  have hs : (R : ℚ) ^ 2 * (intervalTail m (intervalStart m R) R : ℚ) ≤
      weightedSum m (fun w => (4 * (w : ℚ) - m) ^ 2) := by
    simp only [intervalTail, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero,
      weightedSum, mul_sum]
    apply sum_le_sum
    intro w hw
    by_cases hin : w ∈ Ico (intervalStart m R) (intervalStart m R + R)
    · simp only [ite_eq_left hin, mul_zero]
      positivity
    · simp only [ite_eq_right hin]
      have hd := intervalStart_deviation hsize hR hin
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (binomialWeight m w) :
          (0 : ℚ) ≤ binomialWeight m w)
  rw [weightedSum_centered_square] at hs
  exact_mod_cast hs

/-- A sufficient arithmetic budget converts the second moment into the required tail. -/
theorem intervalTail_bound {m R Δ : ℕ} (hsize : 2 * R ≤ m) (hR : 3 ≤ R)
    (hbudget : 24 * Δ * m ≤ R ^ 2) :
    8 * Δ * intervalTail m (intervalStart m R) R ≤ 4 ^ m := by
  have hm := intervalTail_second_moment hsize hR
  have hs : R ^ 2 * (8 * Δ * intervalTail m (intervalStart m R) R) ≤ R ^ 2 * 4 ^ m := by
    calc
      R ^ 2 * (8 * Δ * intervalTail m (intervalStart m R) R) =
          8 * Δ * (R ^ 2 * intervalTail m (intervalStart m R) R) := by ring
      _ ≤ 8 * Δ * (3 * m * 4 ^ m) := Nat.mul_le_mul_left _ hm
      _ = (24 * Δ * m) * 4 ^ m := by ring
      _ ≤ R ^ 2 * 4 ^ m := Nat.mul_le_mul_right _ hbudget
  have hp : 0 < R ^ 2 := by positivity
  exact Nat.le_of_mul_le_mul_left hs hp


/-- The denominator in the layout's degree choice. -/
def layoutDenom (p k Δ : ℕ) : ℕ := 8 * Δ * k * p

/-- A deliberately generous explicit sufficient lower bound on `Q`. -/
def layoutThreshold (p k Δ : ℕ) : ℕ := 512 * Δ * (layoutDenom p k Δ) ^ 2

lemma layoutDenom_ge_eight {p k Δ : ℕ} (hp : 1 < p) (hk : 0 < k) (hΔ : 0 < Δ) :
    8 ≤ layoutDenom p k Δ := by
  have hp1 : 1 ≤ p := by omega
  have hk1 : 1 ≤ k := by omega
  have hΔ1 : 1 ≤ Δ := by omega
  calc
    8 = 8 * 1 * 1 * 1 := by norm_num
    _ ≤ 8 * Δ * k * p :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 8 hΔ1) hk1) hp1
    _ = layoutDenom p k Δ := rfl

/-- The explicit threshold handles the floor loss and the second-moment budget. -/
theorem arithmetic_of_large_Q {p k Δ Q : ℕ}
    (hp : 1 < p) (hk : 0 < k) (hΔ : 0 < Δ)
    (hQ : layoutThreshold p k Δ ≤ Q) :
    32 ≤ Q / layoutDenom p k Δ ∧
      2 * (Q / layoutDenom p k Δ) ≤ Q - 1 ∧
      24 * Δ * (Q - 1) ≤ (Q / layoutDenom p k Δ) ^ 2 ∧
      Δ * k * (p - 1) * (Q / layoutDenom p k Δ) < Q := by
  let a := layoutDenom p k Δ
  let R := Q / a
  have ha8 : 8 ≤ a := layoutDenom_ge_eight hp hk hΔ
  have ha0 : 0 < a := by omega
  have hbase : (64 * Δ * a) * a ≤ Q := by
    calc
      (64 * Δ * a) * a = 64 * (Δ * a ^ 2) := by ring
      _ ≤ 512 * (Δ * a ^ 2) := Nat.mul_le_mul_right _ (by norm_num)
      _ = layoutThreshold p k Δ := by unfold layoutThreshold; dsimp [a]; ring
      _ ≤ Q := hQ
  have hRlower : 64 * Δ * a ≤ R := (Nat.le_div_iff_mul_le ha0).2 hbase
  have hΔa : 1 ≤ Δ * a := Nat.succ_le_of_lt (Nat.mul_pos hΔ ha0)
  have hR32 : 32 ≤ R := by nlinarith
  have hRpos : 0 < R := by omega
  have hident : Q % a + a * R = Q := Nat.mod_add_div Q a
  have hrem : Q % a < a := Nat.mod_lt Q ha0
  have haR : a ≤ a * R := by simpa using Nat.mul_le_mul_left a (show 1 ≤ R by omega)
  have hQR : Q ≤ 2 * a * R := by nlinarith
  have hmul : a * R ≤ Q := by omega
  have hsize : 2 * R ≤ Q - 1 := by
    have hh := Nat.mul_le_mul_right R ha8
    omega
  have h48 : 48 * Δ * a ≤ R := by nlinarith
  have hbudget : 24 * Δ * (Q - 1) ≤ R ^ 2 := by
    calc
      24 * Δ * (Q - 1) ≤ 24 * Δ * Q := Nat.mul_le_mul_left _ (Nat.sub_le Q 1)
      _ ≤ 24 * Δ * (2 * a * R) := Nat.mul_le_mul_left _ hQR
      _ = (48 * Δ * a) * R := by ring
      _ ≤ R * R := Nat.mul_le_mul_right R h48
      _ = R ^ 2 := by ring
  have hsmall : Δ * k * (p - 1) < a := by
    have hprod : 0 < Δ * k * p := Nat.mul_pos (Nat.mul_pos hΔ hk) (by omega)
    calc
      Δ * k * (p - 1) ≤ Δ * k * p := Nat.mul_le_mul_left _ (Nat.sub_le p 1)
      _ < 8 * (Δ * k * p) := by omega
      _ = a := by dsimp [a, layoutDenom]; ring
  have hdegree : Δ * k * (p - 1) * R < Q :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hsmall hRpos) hmul
  exact ⟨hR32, hsize, hbudget, hdegree⟩

/-- The explicit large-`Q` hypothesis implies the actual binomial tail bound. -/
theorem tail_of_large_Q {p k Δ Q : ℕ}
    (hp : 1 < p) (hk : 0 < k) (hΔ : 0 < Δ)
    (hQ : layoutThreshold p k Δ ≤ Q) :
    let R := Q / layoutDenom p k Δ
    8 * Δ * intervalTail (Q - 1) (intervalStart (Q - 1) R) R ≤ 4 ^ (Q - 1) := by
  dsimp only
  obtain ⟨hR, hsize, hbudget, _⟩ := arithmetic_of_large_Q hp hk hΔ hQ
  exact intervalTail_bound hsize (by omega) hbudget

/-- Existence of all integer parameters in (5.1)--(5.2), with the actual tail
proved rather than included as a hypothesis. Field construction can use this
strictly positive exponent. -/
theorem exists_layout_parameters (p k Δ : ℕ)
    (hp : 1 < p) (hk : 0 < k) (hΔ : 0 < Δ) :
    ∃ h Q R A : ℕ,
      0 < h ∧ Q = p ^ h - 1 ∧ R = Q / (8 * Δ * k * p) ∧
      32 ≤ R ∧ A + R ≤ Q ∧
      8 * Δ * intervalTail (Q - 1) A R ≤ 4 ^ (Q - 1) ∧
      Δ * k * (p - 1) * R < Q := by
  let h := ParameterOrder.powerExponent p (layoutThreshold p k Δ) hp
  let Q := p ^ h - 1
  let R := Q / layoutDenom p k Δ
  let A := intervalStart (Q - 1) R
  have hQ : layoutThreshold p k Δ ≤ Q :=
    ParameterOrder.powerExponent_spec p (layoutThreshold p k Δ) hp
  obtain ⟨hR, hsize, hbudget, hdegree⟩ := arithmetic_of_large_Q hp hk hΔ hQ
  have hQpos : 0 < Q := by omega
  have hh : 0 < h := by
    by_contra hn
    have hz : h = 0 := by omega
    simp [Q, hz] at hQpos
  have hend : A + R ≤ Q := by
    have hh := intervalStart_end_le hsize
    dsimp [A, R]
    simpa only [Nat.sub_add_cancel (show 1 ≤ Q by omega)] using hh
  refine ⟨h, Q, R, A, hh, rfl, rfl, hR, hend, ?_, hdegree⟩
  exact intervalTail_bound hsize (by omega) hbudget


/-- The normalized rational probability mass of `Bin(m,1/4)`. -/
def binomialProbability (m w : ℕ) : ℚ :=
  (binomialWeight m w : ℚ) / (4 : ℚ) ^ m

lemma binomialProbability_nonneg (m w : ℕ) : 0 ≤ binomialProbability m w := by
  unfold binomialProbability
  exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (pow_pos (by norm_num) _))

lemma binomialProbability_sum (m : ℕ) :
    ∑ w ∈ range (m + 1), binomialProbability m w = 1 := by
  have hm : (∑ w ∈ range (m + 1), (binomialWeight m w : ℚ)) = (4 : ℚ) ^ m := by
    exact_mod_cast binomialWeight_sum m
  simp only [binomialProbability, ← sum_div, hm]
  exact div_self (by positivity)

lemma binomialProbability_formula {m w : ℕ} (hw : w ≤ m) :
    binomialProbability m w =
      (m.choose w : ℚ) * (1 / 4 : ℚ) ^ w * (3 / 4 : ℚ) ^ (m - w) := by
  have he : w + (m - w) = m := by omega
  unfold binomialProbability binomialWeight
  push_cast
  simp only [div_pow, one_pow]
  field_simp
  rw [mul_assoc, ← pow_add, he]

/-- The interval in the theorem really contains exactly `R` integers. -/
lemma interval_card (A R : ℕ) : (Ico A (A + R)).card = R := by simp

lemma interval_subset_range {A R Q : ℕ} (hend : A + R ≤ Q) :
    Ico A (A + R) ⊆ range Q := by
  intro w hw
  exact mem_range.mpr (lt_of_lt_of_le (mem_Ico.mp hw).2 hend)

/-- Exact equivalence between the finite tail sum and its integer numerator. -/
lemma tail_probability_eq (m A R : ℕ) :
    (∑ w ∈ range (m + 1),
      if w ∈ Ico A (A + R) then 0 else binomialProbability m w) =
        (intervalTail m A R : ℚ) / (4 : ℚ) ^ m := by
  simp only [intervalTail, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, sum_div]
  apply sum_congr rfl
  intro w hw
  split_ifs <;> simp [binomialProbability]

/-- The integer tail inequality is precisely the probability bound (5.2). -/
theorem tail_probability_le {m A R Δ : ℕ} (hΔ : 0 < Δ)
    (htail : 8 * Δ * intervalTail m A R ≤ 4 ^ m) :
    (∑ w ∈ range (m + 1),
      if w ∈ Ico A (A + R) then 0 else binomialProbability m w) ≤
        1 / (8 * (Δ : ℚ)) := by
  rw [tail_probability_eq]
  have hcast : (8 : ℚ) * Δ * (intervalTail m A R : ℚ) ≤ (4 : ℚ) ^ m := by
    exact_mod_cast htail
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

end SubexponentialSAT.LayoutParameters

end OAI.Algorithms
