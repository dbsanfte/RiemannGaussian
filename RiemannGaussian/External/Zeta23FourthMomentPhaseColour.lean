import Mathlib

/-!
# Fourth-root phase colouring for quartic correlations

This file proves the finite cancellation identity behind logarithmic-support
phase colouring.  Averaging independent fourth-root colours retains a
quartic monomial precisely when every colour occurs equally often on its two
orientations.  Thus unequal-product four-cycles are removed without taking
an absolute value and without discarding their phase first.
-/

namespace RiemannGaussian

noncomputable section

open Complex Finset
open scoped BigOperators ComplexConjugate

/-- The four unit phases `1, i, -1, -i`. -/
def quarterPhase (r : Fin 4) : ℂ := Complex.I ^ (r : ℕ)

lemma quarterPhase_norm (r : Fin 4) : ‖quarterPhase r‖ = 1 := by
  simp [quarterPhase]

lemma sum_quarterPhase_pow_conj_pow {p q : ℕ} (hp : p ≤ 2) (hq : q ≤ 2) :
    (∑ r : Fin 4, quarterPhase r ^ p * conj (quarterPhase r) ^ q) =
      if p = q then 4 else 0 := by
  interval_cases p <;> interval_cases q <;>
    norm_num [quarterPhase, Fin.sum_univ_four, pow_succ, Complex.I_mul_I]

/-- Number of occurrences of `i` in an ordered pair. -/
def pairMultiplicity [DecidableEq ι] (i a b : ι) : ℕ :=
  (if i = a then 1 else 0) + (if i = b then 1 else 0)

lemma pairMultiplicity_le_two [DecidableEq ι] (i a b : ι) :
    pairMultiplicity i a b ≤ 2 := by
  simp only [pairMultiplicity]
  split_ifs <;> omega

/-- The local phase contributed at colour site `i` by the oriented quartic
`ξ_a ξ_b conj(ξ_c) conj(ξ_d)`. -/
def quarticLocalPhase [DecidableEq ι] (a b c d i : ι) (r : Fin 4) : ℂ :=
  (if i = a then quarterPhase r else 1) *
  (if i = b then quarterPhase r else 1) *
  (if i = c then conj (quarterPhase r) else 1) *
  (if i = d then conj (quarterPhase r) else 1)

lemma quarticLocalPhase_eq_pow [DecidableEq ι] (a b c d i : ι) (r : Fin 4) :
    quarticLocalPhase a b c d i r =
      quarterPhase r ^ pairMultiplicity i a b *
        conj (quarterPhase r) ^ pairMultiplicity i c d := by
  simp only [quarticLocalPhase, pairMultiplicity]
  split_ifs <;> ring

lemma sum_quarticLocalPhase [DecidableEq ι] (a b c d i : ι) :
    (∑ r : Fin 4, quarticLocalPhase a b c d i r) =
      if pairMultiplicity i a b = pairMultiplicity i c d then 4 else 0 := by
  simp_rw [quarticLocalPhase_eq_pow]
  exact sum_quarterPhase_pow_conj_pow
    (pairMultiplicity_le_two i a b) (pairMultiplicity_le_two i c d)

/-- The two oriented pairs have the same colour content. -/
def QuarticColourBalanced [DecidableEq ι] (a b c d : ι) : Prop :=
  ∀ i, pairMultiplicity i a b = pairMultiplicity i c d

instance quarticColourBalancedDecidable [Fintype ι] [DecidableEq ι]
    (a b c d : ι) : Decidable (QuarticColourBalanced a b c d) := by
  unfold QuarticColourBalanced
  infer_instance

lemma quarticColourBalanced_iff [DecidableEq ι] (a b c d : ι) :
    QuarticColourBalanced a b c d ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    by_cases hab : a = b
    · subst b
      have ha := h a
      by_cases hac : a = c
      · subst c
        by_cases had : a = d
        · subst d
          exact Or.inl ⟨rfl, rfl⟩
        · simp [pairMultiplicity, had] at ha
      · by_cases had : a = d
        · subst d
          simp [pairMultiplicity, hac] at ha
        · simp [pairMultiplicity, hac, had] at ha
    · have hba : b ≠ a := Ne.symm hab
      have ha := h a
      by_cases hac : a = c
      · subst c
        have had : a ≠ d := by
          intro had
          subst d
          simp [pairMultiplicity, hab] at ha
        have hb := h b
        have hbd : b = d := by
          by_contra hbd
          simp [pairMultiplicity, hba, hbd] at hb
        exact Or.inl ⟨rfl, hbd⟩
      · have had : a = d := by
          by_contra had
          simp [pairMultiplicity, hab, hac, had] at ha
        subst d
        have hb := h b
        have hbc : b = c := by
          by_contra hbc
          simp [pairMultiplicity, hba, hbc] at hb
        exact Or.inr ⟨rfl, hbc⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      intro i <;> simp [pairMultiplicity, add_comm]

/-- Product form of the quartic colour assigned by `χ`. -/
def quarticColour (a b c d : ι) (χ : ι → Fin 4) : ℂ :=
  quarterPhase (χ a) * quarterPhase (χ b) *
    conj (quarterPhase (χ c)) * conj (quarterPhase (χ d))

lemma prod_quarticLocalPhase [Fintype ι] [DecidableEq ι]
    (a b c d : ι) (χ : ι → Fin 4) :
    (∏ i, quarticLocalPhase a b c d i (χ i)) = quarticColour a b c d χ := by
  simp_rw [quarticLocalPhase, Finset.prod_mul_distrib]
  simp [quarticColour]

/-- Independent fourth-root colouring annihilates exactly the unbalanced
oriented quartic monomials.  No probabilistic axiom is used: this is the
literal finite sum over all `4 ^ card ι` colourings. -/
theorem sum_quarticColour [Fintype ι] [DecidableEq ι]
    (a b c d : ι) :
    (∑ χ : ι → Fin 4, quarticColour a b c d χ) =
      if QuarticColourBalanced a b c d then 4 ^ Fintype.card ι else 0 := by
  classical
  have hfactor :
      (∑ χ : ι → Fin 4, ∏ i, quarticLocalPhase a b c d i (χ i)) =
        ∏ i, ∑ r : Fin 4, quarticLocalPhase a b c d i r := by
    simpa using (Finset.sum_prod_piFinset (R := ℂ) (s := Finset.univ)
      (g := fun i r => quarticLocalPhase a b c d i r))
  calc
    (∑ χ : ι → Fin 4, quarticColour a b c d χ) =
        ∑ χ : ι → Fin 4, ∏ i, quarticLocalPhase a b c d i (χ i) := by
      apply Finset.sum_congr rfl
      intro χ _
      exact (prod_quarticLocalPhase a b c d χ).symm
    _ = ∏ i, ∑ r : Fin 4, quarticLocalPhase a b c d i r := hfactor
    _ = if QuarticColourBalanced a b c d then 4 ^ Fintype.card ι else 0 := by
      by_cases hbal : QuarticColourBalanced a b c d
      · rw [if_pos hbal]
        simp_rw [sum_quarticLocalPhase, if_pos (hbal _)]
        simp
      · rw [if_neg hbal]
        have hnot : ¬ ∀ i, pairMultiplicity i a b = pairMultiplicity i c d := by
          simpa [QuarticColourBalanced] using hbal
        obtain ⟨i, hi⟩ := not_forall.mp hnot
        have hzero : (∑ r : Fin 4, quarticLocalPhase a b c d i r) = 0 := by
          rw [sum_quarticLocalPhase, if_neg hi]
        rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero]

/-- Pairing form of the selector: the surviving monomials are exactly the
two possible oriented pairings. -/
theorem sum_quarticColour_eq_pairing [Fintype ι] [DecidableEq ι]
    (a b c d : ι) :
    (∑ χ : ι → Fin 4, quarticColour a b c d χ) =
      if (a = c ∧ b = d) ∨ (a = d ∧ b = c) then
        4 ^ Fintype.card ι else 0 := by
  simpa only [quarticColourBalanced_iff] using sum_quarticColour a b c d

/-- Weighted finite-sum form used by a four-cycle ledger.  Colour averaging
is exactly a projection onto the balanced cells; all unbalanced coefficients
vanish before any triangle inequality is applied. -/
theorem sum_weighted_quarticColour
    [Fintype ι] [DecidableEq ι]
    (s : Finset κ) (w : κ → ℂ) (a b c d : κ → ι) :
    (∑ χ : ι → Fin 4, ∑ x ∈ s,
        w x * quarticColour (a x) (b x) (c x) (d x) χ) =
      (4 ^ Fintype.card ι : ℂ) *
        ∑ x ∈ s.filter (fun x => QuarticColourBalanced
          (a x) (b x) (c x) (d x)), w x := by
  classical
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_quarticColour]
  rw [Finset.mul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hbal : QuarticColourBalanced (a x) (b x) (c x) (d x)
  · simp [hbal, mul_comm]
  · simp [hbal]

end

end RiemannGaussian
