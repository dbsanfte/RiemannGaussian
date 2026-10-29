import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Multiplicities of register-swap eigenvalue labels

The negative local labels are strictly below the diagonal and the positive
labels are on or above it. Counting these labels and their tensor words is
independent of the characteristic of the coefficient field.
-/

namespace SubexponentialSAT.SubexpSwapMultiplicity

open scoped BigOperators

section PredicateWords

variable {ι β υ : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
variable (Neg : β → Prop) [DecidablePred Neg]

def negativeSupport (word : ι → β) : Finset ι :=
  Finset.univ.filter fun l => Neg (word l)

def weight (word : ι → β) : ℕ := (negativeSupport Neg word).card

omit [DecidableEq ι] [Fintype β] in
@[simp] theorem mem_negativeSupport (word : ι → β) (l : ι) :
    l ∈ negativeSupport Neg word ↔ Neg (word l) := by
  simp [negativeSupport]

omit [DecidableEq ι] [Fintype β] in
theorem weight_le (word : ι → β) : weight Neg word ≤ Fintype.card ι := by
  exact Finset.card_filter_le _ _

/-- Prescribing the negative positions leaves independent negative and
positive label choices on the two parts. -/
noncomputable def supportFiberEquiv (s : Finset ι) :
    {word : ι → β // negativeSupport Neg word = s} ≃
      (s → {b : β // Neg b}) × ({l : ι // l ∉ s} → {b : β // ¬ Neg b}) := by
  classical
  refine
    { toFun := fun word =>
        (fun l => ⟨word.1 l.1, ?_⟩, fun l => ⟨word.1 l.1, ?_⟩)
      invFun := fun labels =>
        ⟨fun l => if h : l ∈ s then labels.1 ⟨l, h⟩ else labels.2 ⟨l, h⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply (mem_negativeSupport Neg word.1 l.1).mp
    simpa only [word.2] using l.2
  · intro h
    apply l.2
    simpa only [word.2] using (mem_negativeSupport Neg word.1 l.1).mpr h
  · apply Finset.ext
    intro l
    by_cases hl : l ∈ s
    · simp [negativeSupport, hl, (labels.1 ⟨l, hl⟩).2]
    · simp [negativeSupport, hl, (labels.2 ⟨l, hl⟩).2]
  · intro word
    apply Subtype.ext
    funext l
    by_cases hl : l ∈ s <;> simp [hl]
  · intro labels
    apply Prod.ext
    · funext l
      apply Subtype.ext
      simp [l.2]
    · funext l
      apply Subtype.ext
      simp [l.2]

theorem card_support_fiber (s : Finset ι) :
    Fintype.card {word : ι → β // negativeSupport Neg word = s} =
      Fintype.card {b : β // Neg b} ^ s.card *
        Fintype.card {b : β // ¬ Neg b} ^ (Fintype.card ι - s.card) := by
  classical
  rw [Fintype.card_congr (supportFiberEquiv Neg s), Fintype.card_prod]
  simp []

/-- Exact tensor multiplicities for any finite positive/negative alphabet. -/
theorem card_weight (w : ℕ) :
    Fintype.card {word : ι → β // weight Neg word = w} =
      (Fintype.card ι).choose w *
        Fintype.card {b : β // ¬ Neg b} ^ (Fintype.card ι - w) *
        Fintype.card {b : β // Neg b} ^ w := by
  classical
  let e := Equiv.sigmaSubtypeFiberEquivSubtype (negativeSupport (ι := ι) Neg)
    (p := fun word => weight Neg word = w)
    (q := fun s : Finset ι => s.card = w) (fun _ => Iff.rfl)
  rw [← Fintype.card_congr e, Fintype.card_sigma]
  calc
    (∑ s : {s : Finset ι // s.card = w},
      Fintype.card {word : ι → β // negativeSupport Neg word = s.1}) =
        ∑ _s : {s : Finset ι // s.card = w},
          Fintype.card {b : β // Neg b} ^ w *
            Fintype.card {b : β // ¬ Neg b} ^ (Fintype.card ι - w) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [card_support_fiber, s.2]
    _ = _ := by simp [Nat.mul_comm, Nat.mul_assoc]

noncomputable def weightedProductLeftEquiv (w : ℕ) :
    {x : υ × (ι → β) // weight Neg x.2 = w} ≃
      υ × {word : ι → β // weight Neg word = w} where
  toFun x := (x.1.1, ⟨x.1.2, x.2⟩)
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_weight_with_unused_left [Fintype υ] (w : ℕ) :
    Fintype.card {x : υ × (ι → β) // weight Neg x.2 = w} =
      Fintype.card υ * (Fintype.card ι).choose w *
        Fintype.card {b : β // ¬ Neg b} ^ (Fintype.card ι - w) *
        Fintype.card {b : β // Neg b} ^ w := by
  rw [Fintype.card_congr (weightedProductLeftEquiv (ι := ι) (υ := υ) Neg w),
    Fintype.card_prod, card_weight]
  simp only [Nat.mul_assoc]

end PredicateWords

abbrev PositiveLabels (r : ℕ) := {x : Fin r × Fin r // x.1 ≤ x.2}
abbrev NegativeLabels (r : ℕ) := {x : Fin r × Fin r // x.2 < x.1}

def positiveSigmaEquiv (r : ℕ) :
    PositiveLabels r ≃ Σ b : Fin r, {a : Fin r // a ≤ b} where
  toFun x := ⟨x.1.2, x.1.1, x.2⟩
  invFun x := ⟨(x.2.1, x.1), x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_negative_eq_sum (r : ℕ) :
    Fintype.card (NegativeLabels r) = ∑ i ∈ Finset.range r, i := by
  rw [Fintype.card_congr
    (Equiv.subtypeProdEquivSigmaSubtype (fun a b : Fin r => b < a)), Fintype.card_sigma]
  have h (a : Fin r) : Fintype.card {b : Fin r // b < a} = a.1 := by
    rw [Fintype.card_of_subtype (Finset.Iio a) (by intro b; simp), Fin.card_Iio]
  simp_rw [h]
  simpa using Fin.sum_univ_eq_sum_range (fun i : ℕ => i) r

theorem card_positive_eq_sum (r : ℕ) :
    Fintype.card (PositiveLabels r) = ∑ i ∈ Finset.range (r + 1), i := by
  rw [Fintype.card_congr (positiveSigmaEquiv r), Fintype.card_sigma]
  have h (b : Fin r) : Fintype.card {a : Fin r // a ≤ b} = b.1 + 1 := by
    rw [Fintype.card_of_subtype (Finset.Iic b) (by intro a; simp), Fin.card_Iic]
  simp_rw [h]
  rw [show (∑ b : Fin r, (b.1 + 1)) = ∑ i ∈ Finset.range r, (i + 1) by
    simpa using Fin.sum_univ_eq_sum_range (fun i : ℕ => i + 1) r]
  simpa using (Finset.sum_range_succ' (fun i : ℕ => i) r).symm

theorem card_negative (r : ℕ) :
    Fintype.card (NegativeLabels r) = r * (r - 1) / 2 := by
  rw [card_negative_eq_sum, Finset.sum_range_id]

theorem card_positive (r : ℕ) :
    Fintype.card (PositiveLabels r) = r * (r + 1) / 2 := by
  rw [card_positive_eq_sum, Finset.sum_range_id]
  simp [Nat.mul_comm]

theorem two_mul_card_negative (r : ℕ) :
    2 * Fintype.card (NegativeLabels r) = r * (r - 1) := by
  rw [card_negative_eq_sum, Nat.mul_comm]
  exact Finset.sum_range_id_mul_two r

theorem two_mul_card_positive (r : ℕ) :
    2 * Fintype.card (PositiveLabels r) = r * (r + 1) := by
  rw [card_positive_eq_sum, Nat.mul_comm]
  simpa [Nat.mul_comm] using Finset.sum_range_id_mul_two (r + 1)

def positiveMultiplicity (r : ℕ) : ℕ := r * (r + 1) / 2
def negativeMultiplicity (r : ℕ) : ℕ := r * (r - 1) / 2

def negativePair {r : ℕ} (x : Fin r × Fin r) : Prop := x.2 < x.1

instance {r : ℕ} : DecidablePred (@negativePair r) :=
  fun x => inferInstanceAs (Decidable (x.2 < x.1))

abbrev swapWeight {r : ℕ} {ι : Type*} [Fintype ι]
    (word : ι → Fin r × Fin r) := weight negativePair word

theorem card_not_negativePair (r : ℕ) :
    Fintype.card {x : Fin r × Fin r // ¬ negativePair x} = positiveMultiplicity r := by
  simpa [negativePair, not_lt, positiveMultiplicity] using card_positive r

theorem card_negativePair (r : ℕ) :
    Fintype.card {x : Fin r × Fin r // negativePair x} = negativeMultiplicity r := by
  change Fintype.card (NegativeLabels r) = negativeMultiplicity r
  exact card_negative r

def swapMultiplicity (r q w : ℕ) : ℕ :=
  q.choose w * positiveMultiplicity r ^ (q - w) * negativeMultiplicity r ^ w

theorem card_swap_weight {ι : Type*} [Fintype ι] [DecidableEq ι] (r w : ℕ) :
    Fintype.card {word : ι → Fin r × Fin r // swapWeight word = w} =
      swapMultiplicity r (Fintype.card ι) w := by
  rw [card_weight negativePair, card_not_negativePair, card_negativePair]
  rfl

theorem card_swap_weight_fin (r q w : ℕ) :
    Fintype.card {word : Fin q → Fin r × Fin r // swapWeight word = w} =
      swapMultiplicity r q w := by
  simpa using card_swap_weight (ι := Fin q) r w

theorem card_swap_weight_with_unused_left {ι υ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype υ] (r w : ℕ) :
    Fintype.card {x : υ × (ι → Fin r × Fin r) // swapWeight x.2 = w} =
      Fintype.card υ * swapMultiplicity r (Fintype.card ι) w := by
  rw [card_weight_with_unused_left negativePair, card_not_negativePair, card_negativePair]
  simp only [swapMultiplicity, Nat.mul_assoc]

/-- The positive and negative labels account for every ordered pair. -/
theorem multiplicities_add (r : ℕ) :
    positiveMultiplicity r + negativeMultiplicity r = r ^ 2 := by
  have h := Fintype.card_congr (Equiv.sumCompl (@negativePair r))
  rw [Fintype.card_sum, card_negativePair, card_not_negativePair,
    Fintype.card_prod, Fintype.card_fin] at h
  simpa [Nat.add_comm, pow_two] using h

/-- Total tensor multiplicity; neither the number of registers nor the
number of positions is hidden as a fixed parameter. -/
theorem sum_swap_multiplicities (r q : ℕ) :
    (∑ w ∈ Finset.range (q + 1), swapMultiplicity r q w) = (r ^ 2) ^ q := by
  calc
    _ = (positiveMultiplicity r + negativeMultiplicity r) ^ q := by
      simpa [swapMultiplicity, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
        Nat.add_comm] using
        (add_pow (negativeMultiplicity r) (positiveMultiplicity r) q).symm
    _ = _ := by rw [multiplicities_add]

theorem card_swap_words (r q : ℕ) :
    Fintype.card (Fin q → Fin r × Fin r) = (r ^ 2) ^ q := by
  simp [ Fintype.card_prod, pow_two]

theorem positiveMultiplicity_cast (r : ℕ) :
    (positiveMultiplicity r : ℚ) = (r : ℚ) * (r + 1) / 2 := by
  have h := congrArg (fun n : ℕ => (n : ℚ)) (two_mul_card_positive r)
  rw [card_positive] at h
  change ((2 * positiveMultiplicity r : ℕ) : ℚ) = ((r * (r + 1) : ℕ) : ℚ) at h
  push_cast at h
  linarith

theorem negativeMultiplicity_cast (r : ℕ) (hr : 0 < r) :
    (negativeMultiplicity r : ℚ) = (r : ℚ) * (r - 1) / 2 := by
  have h := congrArg (fun n : ℕ => (n : ℚ)) (two_mul_card_negative r)
  rw [card_negative] at h
  change ((2 * negativeMultiplicity r : ℕ) : ℚ) = ((r * (r - 1) : ℕ) : ℚ) at h
  have hr1 : 1 ≤ r := hr
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hr1, Nat.cast_one] at h
  linarith

/-- Probability of a negative local eigenvalue for a uniformly chosen
ordered pair label. -/
def negativeProbability (r : ℕ) : ℚ := ((r : ℚ) - 1) / (2 * r)

theorem negativeMultiplicity_ratio (r : ℕ) (hr : 0 < r) :
    (negativeMultiplicity r : ℚ) / (r : ℚ) ^ 2 = negativeProbability r := by
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
  rw [negativeMultiplicity_cast r hr, negativeProbability]
  field_simp

theorem positiveMultiplicity_ratio (r : ℕ) (hr : 0 < r) :
    (positiveMultiplicity r : ℚ) / (r : ℚ) ^ 2 = 1 - negativeProbability r := by
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
  rw [positiveMultiplicity_cast, negativeProbability]
  field_simp
  ring

/-- The uniform word measure, expressed with exact rational arithmetic. -/
def swapProbability (r q w : ℕ) : ℚ :=
  (swapMultiplicity r q w : ℚ) / ((r : ℚ) ^ 2) ^ q

theorem swapProbability_nonneg (r q w : ℕ) : 0 ≤ swapProbability r q w := by
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (sq_nonneg _) _)

theorem sum_swap_probabilities (r q : ℕ) (hr : 0 < r) :
    (∑ w ∈ Finset.range (q + 1), swapProbability r q w) = 1 := by
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
  simp_rw [swapProbability, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, sum_swap_multiplicities]
  simp only [Nat.cast_pow]
  exact mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hr0))

/-- Exact binomial probability mass function of the negative weight. -/
theorem swapProbability_eq_binomial (r q w : ℕ) (hr : 0 < r) :
    swapProbability r q w =
      (q.choose w : ℚ) * negativeProbability r ^ w *
        (1 - negativeProbability r) ^ (q - w) := by
  by_cases hw : w ≤ q
  · unfold swapProbability swapMultiplicity
    push_cast
    calc
      _ = (q.choose w : ℚ) *
          (((positiveMultiplicity r : ℚ) / (r : ℚ) ^ 2) ^ (q - w) *
            ((negativeMultiplicity r : ℚ) / (r : ℚ) ^ 2) ^ w) := by
        rw [div_pow, div_pow, ← mul_div_mul_comm, ← pow_add, Nat.sub_add_cancel hw]
        ring
      _ = _ := by
        rw [positiveMultiplicity_ratio r hr, negativeMultiplicity_ratio r hr]
        ring
  · have hz : q.choose w = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hw)
    simp [swapProbability, swapMultiplicity, hz]

/-- The source paper uses precisely `Q - 1` independent register pairs. -/
theorem swapProbability_Q_eq_binomial (r Q w : ℕ) (hr : 0 < r) :
    swapProbability r (Q - 1) w =
      ((Q - 1).choose w : ℚ) * (((r : ℚ) - 1) / (2 * r)) ^ w *
        (1 - ((r : ℚ) - 1) / (2 * r)) ^ (Q - 1 - w) :=
  swapProbability_eq_binomial r (Q - 1) w hr

/-- The local negative probability belongs to the range used in the paper. -/
theorem negativeProbability_bounds (r : ℕ) (hr : 2 ≤ r) :
    (1 / 4 : ℚ) ≤ negativeProbability r ∧ negativeProbability r < 1 / 2 := by
  have hrQ : (2 : ℚ) ≤ r := by exact_mod_cast hr
  have hden : (0 : ℚ) < 2 * r := by linarith
  constructor
  · unfold negativeProbability
    apply (le_div_iff₀ hden).mpr
    linarith
  · unfold negativeProbability
    apply (div_lt_iff₀ hden).mpr
    linarith

theorem regression_three_states_local :
    Fintype.card (PositiveLabels 3) = 6 ∧ Fintype.card (NegativeLabels 3) = 3 := by
  decide

theorem regression_three_states_two_pairs :
    Fintype.card {word : Fin 2 → Fin 3 × Fin 3 // swapWeight word = 1} = 36 := by
  decide

/-! ## General binomial second moment and the interval tail -/

/-- Finite expectation for a binomial parameter `θ`; no special value of
the parameter is built into the recurrence or moment identity. -/
def binomialExpectation (θ : ℚ) (q : ℕ) (f : ℕ → ℚ) : ℚ :=
  ∑ w ∈ Finset.range (q + 1),
    (q.choose w : ℚ) * (1 - θ) ^ (q - w) * θ ^ w * f w

theorem binomialExpectation_add (θ : ℚ) (q : ℕ) (f g : ℕ → ℚ) :
    binomialExpectation θ q (fun w => f w + g w) =
      binomialExpectation θ q f + binomialExpectation θ q g := by
  simp [binomialExpectation, mul_add, Finset.sum_add_distrib]

theorem binomialExpectation_const_mul (θ c : ℚ) (q : ℕ) (f : ℕ → ℚ) :
    binomialExpectation θ q (fun w => c * f w) =
      c * binomialExpectation θ q f := by
  simp [binomialExpectation, mul_left_comm, ← Finset.mul_sum]

/-- Adding one independent Bernoulli coordinate, proved by Pascal's identity. -/
theorem binomialExpectation_succ (θ : ℚ) (q : ℕ) (f : ℕ → ℚ) :
    binomialExpectation θ (q + 1) f =
      binomialExpectation θ q (fun w => (1 - θ) * f w + θ * f (w + 1)) := by
  unfold binomialExpectation
  simp only [mul_assoc]
  rw [Finset.sum_choose_succ_mul (fun i j => (1 - θ) ^ j * (θ ^ i * f i)) q]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  have hwle : w ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hw)
  have he : q + 1 - w = q - w + 1 := by omega
  rw [he, pow_succ, pow_succ]
  ring

theorem binomialExpectation_mass (θ : ℚ) (q : ℕ) :
    binomialExpectation θ q (fun _ => 1) = 1 := by
  induction q with
  | zero => simp [binomialExpectation]
  | succ q ih =>
      rw [binomialExpectation_succ]
      have hfun : (fun _ : ℕ => (1 - θ) * 1 + θ * 1) = (fun _ : ℕ => 1) := by
        funext w
        ring
      rw [hfun, ih]

/-- The exact central second moment for every rational parameter. -/
theorem binomialExpectation_centered_square (θ : ℚ) (q : ℕ) :
    binomialExpectation θ q (fun w => ((w : ℚ) - q * θ) ^ 2) =
      q * θ * (1 - θ) := by
  induction q with
  | zero => simp [binomialExpectation]
  | succ q ih =>
      rw [binomialExpectation_succ]
      have hfun :
          (fun w : ℕ => (1 - θ) * ((w : ℚ) - (q + 1 : ℕ) * θ) ^ 2 +
            θ * ((w + 1 : ℕ) - (q + 1 : ℕ) * θ : ℚ) ^ 2) =
          (fun w : ℕ => ((w : ℚ) - q * θ) ^ 2 + (θ * (1 - θ)) * 1) := by
        funext w
        push_cast
        ring
      rw [hfun, binomialExpectation_add, binomialExpectation_const_mul,
        binomialExpectation_mass, ih]
      push_cast
      ring

theorem swap_centered_second_moment (r q : ℕ) (hr : 0 < r) :
    (∑ w ∈ Finset.range (q + 1), swapProbability r q w *
      ((w : ℚ) - q * negativeProbability r) ^ 2) =
        q * negativeProbability r * (1 - negativeProbability r) := by
  calc
    _ = binomialExpectation (negativeProbability r) q
        (fun w => ((w : ℚ) - q * negativeProbability r) ^ 2) := by
      unfold binomialExpectation
      apply Finset.sum_congr rfl
      intro w _
      rw [swapProbability_eq_binomial r q w hr]
      ring
    _ = _ := binomialExpectation_centered_square _ _

/-- A finite Chebyshev inequality for the actual swap probabilities. The
geometric hypothesis says every omitted weight is at least `R/4` from the
actual mean, in squared form. -/
theorem tail_second_moment (r q A R : ℕ) (hr : 0 < r)
    (hsep : ∀ w ∈ Finset.range (q + 1), w ∉ Finset.Ico A (A + R) →
      (R : ℚ) ^ 2 ≤ 16 * ((w : ℚ) - q * negativeProbability r) ^ 2) :
    (R : ℚ) ^ 2 * (∑ w ∈ Finset.range (q + 1),
      if w ∈ Finset.Ico A (A + R) then 0 else swapProbability r q w) ≤
        16 * q * negativeProbability r * (1 - negativeProbability r) := by
  calc
    _ ≤ 16 * (∑ w ∈ Finset.range (q + 1), swapProbability r q w *
        ((w : ℚ) - q * negativeProbability r) ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro w hw
      by_cases hin : w ∈ Finset.Ico A (A + R)
      · simp only [ite_eq_left hin, mul_zero]
        exact mul_nonneg (by norm_num)
          (mul_nonneg (swapProbability_nonneg r q w) (sq_nonneg _))
      · simp only [ite_eq_right hin]
        have h := mul_le_mul_of_nonneg_left (hsep w hw hin) (swapProbability_nonneg r q w)
        simpa only [mul_comm, mul_left_comm, mul_assoc] using h
    _ = _ := by rw [swap_centered_second_moment r q hr]; ring

/-- The uniform variance bound `θ(1-θ) ≤ 1/4` loses no dependence on `r`. -/
theorem tail_chebyshev (r q A R : ℕ) (hr : 0 < r)
    (hsep : ∀ w ∈ Finset.range (q + 1), w ∉ Finset.Ico A (A + R) →
      (R : ℚ) ^ 2 ≤ 16 * ((w : ℚ) - q * negativeProbability r) ^ 2) :
    (R : ℚ) ^ 2 * (∑ w ∈ Finset.range (q + 1),
      if w ∈ Finset.Ico A (A + R) then 0 else swapProbability r q w) ≤ 4 * q := by
  have hvar : negativeProbability r * (1 - negativeProbability r) ≤ (1 / 4 : ℚ) := by
    nlinarith [sq_nonneg (negativeProbability r - 1 / 2)]
  calc
    _ ≤ 16 * q * negativeProbability r * (1 - negativeProbability r) :=
      tail_second_moment r q A R hr hsep
    _ = (16 * q) * (negativeProbability r * (1 - negativeProbability r)) := by ring
    _ ≤ (16 * q) * (1 / 4 : ℚ) :=
      mul_le_mul_of_nonneg_left hvar (by positivity)
    _ = 4 * q := by ring

/-- The source's arithmetic budget implies the required normalized tail,
once the interval geometry is supplied. All parameters remain explicit. -/
theorem tail_bound_of_budget (r Q A R Δ s : ℕ)
    (hr : 0 < r) (hR : 0 < R) (hΔ : 0 < Δ) (hs : 0 < s)
    (hbudget : 16 * Q * Δ * s ≤ R ^ 2)
    (hsep : ∀ w ∈ Finset.range ((Q - 1) + 1), w ∉ Finset.Ico A (A + R) →
      (R : ℚ) ^ 2 ≤ 16 * ((w : ℚ) - (Q - 1 : ℕ) * negativeProbability r) ^ 2) :
    (∑ w ∈ Finset.range ((Q - 1) + 1),
      if w ∈ Finset.Ico A (A + R) then 0 else swapProbability r (Q - 1) w) ≤
        1 / ((s : ℚ) * Δ) := by
  let T : ℚ := ∑ w ∈ Finset.range ((Q - 1) + 1),
    if w ∈ Finset.Ico A (A + R) then 0 else swapProbability r (Q - 1) w
  change T ≤ 1 / ((s : ℚ) * Δ)
  have hsd : (0 : ℚ) < (s : ℚ) * Δ := by positivity
  have hR2 : (0 : ℚ) < (R : ℚ) ^ 2 := by positivity
  have hm : (R : ℚ) ^ 2 * T ≤ 16 * Q := by
    have hm' := tail_chebyshev r (Q - 1) A R hr hsep
    have hq : ((Q - 1 : ℕ) : ℚ) ≤ Q := by exact_mod_cast Nat.sub_le Q 1
    have hQ0 : (0 : ℚ) ≤ Q := Nat.cast_nonneg _
    dsimp [T]
    calc
      _ ≤ 4 * ((Q - 1 : ℕ) : ℚ) := hm'
      _ ≤ 16 * Q := by nlinarith
  have hb : (16 : ℚ) * Q * Δ * s ≤ (R : ℚ) ^ 2 := by exact_mod_cast hbudget
  have hmul : (R : ℚ) ^ 2 * (T * ((s : ℚ) * Δ)) ≤ (R : ℚ) ^ 2 * 1 := by
    calc
      _ = ((R : ℚ) ^ 2 * T) * ((s : ℚ) * Δ) := by ring
      _ ≤ (16 * Q) * ((s : ℚ) * Δ) := mul_le_mul_of_nonneg_right hm hsd.le
      _ ≤ (R : ℚ) ^ 2 * 1 := by
        simpa only [mul_one, mul_assoc, mul_comm, mul_left_comm] using hb
  exact (le_div_iff₀ hsd).mpr (le_of_mul_le_mul_left hmul hR2)

end SubexponentialSAT.SubexpSwapMultiplicity

end OAI.Algorithms
