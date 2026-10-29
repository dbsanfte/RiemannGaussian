import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Exact multiplicities for the four-state local eigenbasis

The main count is proved for any finite alphabet with one distinguished state.
It is a genuine cardinality theorem, obtained by recording the distinguished
support and choosing a non-distinguished label on its complement.
-/

namespace SubexponentialSAT.BinomialMultiplicity

open scoped BigOperators

section Alphabet

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- Positions at which a word takes the distinguished negative label. -/
def negativeSupport (negative : α) (word : ι → α) : Finset ι :=
  Finset.univ.filter fun l => word l = negative

/-- The number of negative local basis labels in a word. -/
def weight (negative : α) (word : ι → α) : ℕ :=
  (negativeSupport negative word).card

omit [DecidableEq ι] [Fintype α] in
@[simp] theorem mem_negativeSupport (negative : α) (word : ι → α) (l : ι) :
    l ∈ negativeSupport negative word ↔ word l = negative := by
  simp [negativeSupport]

omit [DecidableEq ι] [Fintype α] in
theorem weight_le (negative : α) (word : ι → α) :
    weight negative word ≤ Fintype.card ι := by
  exact Finset.card_filter_le _ _

/-- A word with prescribed negative support is exactly an assignment of
nonnegative labels on the complementary positions. -/
noncomputable def supportFiberEquiv (negative : α) (s : Finset ι) :
    {word : ι → α // negativeSupport negative word = s} ≃
      ({l : ι // l ∉ s} → {a : α // a ≠ negative}) := by
  classical
  refine
    { toFun := fun word l => ⟨word.1 l.1, ?_⟩
      invFun := fun labels => ⟨fun l => if h : l ∈ s then negative else labels ⟨l, h⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro h
    apply l.2
    simpa only [word.2] using (mem_negativeSupport negative word.1 l.1).mpr h
  · apply Finset.ext
    intro l
    by_cases hl : l ∈ s
    · simp [negativeSupport, hl]
    · simp [negativeSupport, hl, (labels ⟨l, hl⟩).2]
  · intro word
    apply Subtype.ext
    funext l
    by_cases hl : l ∈ s
    · have hlabel : word.1 l = negative := by
        apply (mem_negativeSupport negative word.1 l).mp
        rw [word.2]
        exact hl
      simp [hl, hlabel]
    · simp [hl]
  · intro labels
    funext l
    apply Subtype.ext
    simp [l.2]

theorem card_support_fiber (negative : α) (s : Finset ι) :
    Fintype.card {word : ι → α // negativeSupport negative word = s} =
      (Fintype.card α - 1) ^ (Fintype.card ι - s.card) := by
  classical
  rw [Fintype.card_congr (supportFiberEquiv negative s), Fintype.card_fun]
  have hlabels : Fintype.card {a : α // a ≠ negative} = Fintype.card α - 1 := by
    simp
  have hpositions : Fintype.card {l : ι // l ∉ s} = Fintype.card ι - s.card := by
    simp
  rw [hlabels, hpositions]

/-- Exact binomial multiplicity for an arbitrary finite alphabet. -/
theorem card_weight (negative : α) (w : ℕ) :
    Fintype.card {word : ι → α // weight negative word = w} =
      (Fintype.card ι).choose w * (Fintype.card α - 1) ^ (Fintype.card ι - w) := by
  classical
  let e := Equiv.sigmaSubtypeFiberEquivSubtype (negativeSupport (ι := ι) negative)
    (p := fun word => weight negative word = w)
    (q := fun s : Finset ι => s.card = w) (fun _ => Iff.rfl)
  rw [← Fintype.card_congr e, Fintype.card_sigma]
  calc
    (∑ s : {s : Finset ι // s.card = w},
      Fintype.card {word : ι → α // negativeSupport negative word = s.1}) =
        ∑ _s : {s : Finset ι // s.card = w},
          (Fintype.card α - 1) ^ (Fintype.card ι - w) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [card_support_fiber, s.2]
    _ = _ := by simp

end Alphabet

section PairStates

variable {ι υ : Type*} [Fintype ι] [DecidableEq ι]

/-- The exact weight convention used by the tensor product local eigenbasis. -/
abbrev pairWeight (word : ι → Bool × Bool) : ℕ := weight (true, true) word

omit [DecidableEq ι] in
theorem pairWeight_le (word : ι → Bool × Bool) :
    pairWeight word ≤ Fintype.card ι := weight_le _ _

/-- Three positive local basis labels and one negative label give the claimed
`choose(q,w) * 3^(q-w)` multiplicity. -/
theorem card_pair_weight (w : ℕ) :
    Fintype.card {word : ι → Bool × Bool // pairWeight word = w} =
      (Fintype.card ι).choose w * 3 ^ (Fintype.card ι - w) := by
  simpa [Fintype.card_prod] using card_weight (ι := ι) (true, true) w

theorem card_pair_weight_fin (q w : ℕ) :
    Fintype.card {word : Fin q → Bool × Bool // pairWeight word = w} =
      q.choose w * 3 ^ (q - w) := by
  simpa using card_pair_weight (ι := Fin q) w

/-- Extra independent labels contribute their full cardinality at every weight. -/
noncomputable def weightedProductEquiv (w : ℕ) :
    {x : (ι → Bool × Bool) × υ // pairWeight x.1 = w} ≃
      {word : ι → Bool × Bool // pairWeight word = w} × υ where
  toFun x := (⟨x.1.1, x.2⟩, x.1.2)
  invFun x := ⟨(x.1.1, x.2), x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_pair_weight_with_unused [Fintype υ] (w : ℕ) :
    Fintype.card {x : (ι → Bool × Bool) × υ // pairWeight x.1 = w} =
      Fintype.card υ * (Fintype.card ι).choose w * 3 ^ (Fintype.card ι - w) := by
  rw [Fintype.card_congr (weightedProductEquiv (ι := ι) (υ := υ) w),
    Fintype.card_prod, card_pair_weight]
  simp only [Nat.mul_comm, Nat.mul_assoc]

/-- The same decomposition with the spectator label first, as in the explicit
spectator eigenbasis. -/
noncomputable def weightedProductLeftEquiv (w : ℕ) :
    {x : υ × (ι → Bool × Bool) // pairWeight x.2 = w} ≃
      υ × {word : ι → Bool × Bool // pairWeight word = w} where
  toFun x := (x.1.1, ⟨x.1.2, x.2⟩)
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_pair_weight_with_unused_left [Fintype υ] (w : ℕ) :
    Fintype.card {x : υ × (ι → Bool × Bool) // pairWeight x.2 = w} =
      Fintype.card υ * (Fintype.card ι).choose w * 3 ^ (Fintype.card ι - w) := by
  rw [Fintype.card_congr (weightedProductLeftEquiv (ι := ι) (υ := υ) w),
    Fintype.card_prod, card_pair_weight, Nat.mul_assoc]

theorem card_pair_weight_with_unused_bits (q r w : ℕ) :
    Fintype.card {x : (Fin q → Bool × Bool) × (Fin r → Bool) // pairWeight x.1 = w} =
      2 ^ r * q.choose w * 3 ^ (q - w) := by
  simpa [Fintype.card_fun] using
    card_pair_weight_with_unused (ι := Fin q) (υ := Fin r → Bool) w

theorem card_pair_words : Fintype.card (ι → Bool × Bool) = 4 ^ Fintype.card ι := by
  simp [ Fintype.card_prod]

end PairStates

/-- Summing every weight multiplicity recovers all four-state words. -/
theorem sum_multiplicities (q : ℕ) :
    (∑ w ∈ Finset.range (q + 1), q.choose w * 3 ^ (q - w)) = 4 ^ q := by
  simpa [Nat.mul_comm] using (add_pow (1 : ℕ) 3 q).symm

/-- The same total with independent unused bits. -/
theorem sum_multiplicities_with_unused_bits (q r : ℕ) :
    (∑ w ∈ Finset.range (q + 1), 2 ^ r * q.choose w * 3 ^ (q - w)) =
      2 ^ r * 4 ^ q := by
  simp_rw [Nat.mul_assoc]
  rw [← Finset.mul_sum, sum_multiplicities]

/-- Small enumeration computed by the kernel, independently of the general
cardinality formula. -/
theorem regression_two_positions_one_negative :
    Fintype.card {word : Fin 2 → Bool × Bool // pairWeight word = 1} = 6 := by
  decide

/-- The independent unused bit doubles the six words in the preceding example. -/
theorem regression_two_positions_one_unused_bit :
    Fintype.card {x : (Fin 2 → Bool × Bool) × (Fin 1 → Bool) //
      pairWeight x.1 = 1} = 12 := by
  decide

end SubexponentialSAT.BinomialMultiplicity

end OAI.Algorithms
