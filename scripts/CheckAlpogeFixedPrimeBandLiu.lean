import CheckAlpogeFixedPrimeBandCenteredBounds
import CheckLiuCofactor

/-! # Fixed-band mass on power windows from Baiying Liu's limiting half-plane -/

namespace RiemannGaussian.AlpogeMined
open Filter

/-- Strictly above this exponent the bound holds on every sufficiently late window
of a suitable fixed width. -/
theorem fixedBandMass_liu {α : ℝ} (hα : 1499828077680395788 / 10^18 < α) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ᶠ m : ℕ in atTop,
      fixedBandMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α := by
  apply fixedBandMass_eventually_le_of_zero_bound (B := 874957019420098947 / 10^18)
    (by norm_num) _ (by linarith only [hα])
  intro ρ
  exact (LiuCofactor.zero_re_le_limit ρ).trans CombineV22ExplicitRoot.boundary_decimal_bracket.2.le

/-- The same threshold holds for the remaining signed Möbius sum on arbitrarily
late windows of a fixed width. -/
theorem fixedBandMobiusMass_liu {α : ℝ} (hα : 1499828077680395788 / 10^18 < α) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandMobiusMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α := by
  let β := (α+1499828077680395788/10^18)/2
  have hβ : 1499828077680395788/10^18 < β := by dsimp [β]; linarith
  obtain ⟨δ,hδ,hδ₁,hw⟩ := fixedBandMass_liu hβ
  exact ⟨δ,hδ,hδ₁,fixedBandMobiusMass_of_prime_windows (by linarith only [hβ])
    (by dsimp [β]; linarith) hδ₁ (fun A => ((eventually_ge_atTop A).and hw).exists)⟩

/-- The centered cubic tail and the quadratic form meet Liu's exponent on the
same cofinal windows. -/
theorem fixedBandCenteredQuadratic_liu {α : ℝ} (hα : 1499828077680395788 / 10^18 < α) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ A : ℕ, ∃ m ≥ A,
      let b := ⌈(m:ℝ)^(1+δ)⌉₊
      max (fixedBandCenteredMass m b) (fixedBandQuadraticMass m b) ≤ (m:ℝ)^α := by
  let β := (α+1499828077680395788/10^18)/2
  have hβ : 1499828077680395788/10^18 < β := by dsimp [β]; linarith
  obtain ⟨δ,hδ,hδ₁,hw⟩ := fixedBandMass_liu hβ
  obtain ⟨C,hC,hc⟩ := fixedBandCenteredMass_error
  obtain ⟨K,hK,hk⟩ := fixedBandQuadraticMass_error
  refine ⟨δ,hδ,hδ₁,fixedBand_cofinal_mass_transfer
    (fun m b => max (fixedBandCenteredMass m b) (fixedBandQuadraticMass m b))
    fixedBandMass (C := max C K) (le_max_of_le_left hC) ?_ (by linarith only [hβ])
    (by dsimp [β]; linarith : β < α) hδ₁ (fun A => ((eventually_ge_atTop A).and hw).exists)⟩
  intro m b hm
  have hlog := Real.log_natCast_nonneg b
  have h₁ := (abs_le.mp (hc (b := b) hm)).1
  have h₂ := (abs_le.mp (hk (b := b) hm)).1
  apply sub_le_iff_le_add.mpr
  apply max_le
  · linarith only [h₁,mul_le_mul_of_nonneg_right (le_max_left C K) (sq_nonneg (1+Real.log b))]
  · have hpow : 1+Real.log b ≤ (1+Real.log b)^2 := by nlinarith only [hlog,sq_nonneg (Real.log b)]
    linarith only [h₂,mul_le_mul (le_max_right C K) hpow (by linarith : 0 ≤ 1+Real.log b) (le_max_of_le_left hC)]

/-- Liu's same exponent also holds after trimming the square-root boundary. -/
theorem fixedBandTrimmedMass_liu {α : ℝ} (hα : 1499828077680395788 / 10^18 < α) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandTrimmedMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α := by
  let β := (α+1499828077680395788/10^18)/2
  have hβ : 1499828077680395788/10^18 < β := by dsimp [β]; linarith
  obtain ⟨δ,hδ,hδ₁,hw⟩ := fixedBandMass_liu hβ
  obtain ⟨C,hC,he⟩ := fixedBandTrimmedMass_error
  refine ⟨δ,hδ,hδ₁,fixedBand_cofinal_mass_transfer fixedBandTrimmedMass fixedBandMass hC
    (fun {m b} hm => ?_) (by linarith only [hβ]) (by dsimp [β]; linarith : β < α) hδ₁
    (fun A => ((eventually_ge_atTop A).and hw).exists)⟩
  have h := (abs_le.mp (he (b := b) hm)).1
  linarith only [h,mul_le_mul_of_nonneg_left (by nlinarith only [Real.log_natCast_nonneg b,sq_nonneg (Real.log b)] :
    1+Real.log b ≤ (1+Real.log b)^2) hC]

theorem fixedBandMinMass_liu {α : ℝ} (hα : 1499828077680395788 / 10^18 < α) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandMinMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α := by
  obtain ⟨δ,hδ,hδ₁,hw⟩ := fixedBandCenteredQuadratic_liu hα
  refine ⟨δ,hδ,hδ₁,fun A => ?_⟩
  obtain ⟨m,hm,h⟩ := hw A
  exact ⟨m,hm,(fixedBandMinMass_le_quadratic _ _).trans ((le_max_right _ _).trans h)⟩

end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.fixedBandMass_liu,
      ``RiemannGaussian.AlpogeMined.fixedBandMobiusMass_liu,
      ``RiemannGaussian.AlpogeMined.fixedBandCenteredQuadratic_liu,
      ``RiemannGaussian.AlpogeMined.fixedBandTrimmedMass_liu,
      ``RiemannGaussian.AlpogeMined.fixedBandMinMass_liu] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
