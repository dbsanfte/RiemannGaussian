/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovCriticalExponent
import RiemannGaussian.VinogradovKorobovMoment

/-!
# Both critical moments in the actual Korobov product sum

A frequency-preserving embedding retains every original collision when a
finite positive set is included in an interval. Its moment is bounded using
the containing interval length, without replacing that length by cardinality.
The actual product sum then receives both proved critical moment exponents
plus epsilon, retaining the exact phase coefficients, whole attainable
support, quartered Gaussian smoothing cost and joint resonance envelope.

The remaining resonance envelope and uniform quantitative parameter costs
still need estimates before this becomes a zeta growth or zero-free theorem.
Constants and terminal thresholds are not numerically evaluated.
-/

namespace RiemannGaussian.VinogradovCriticalKorobov
noncomputable section
open scoped Classical BigOperators
open VinogradovMeanValue VinogradovShiftedMoment VinogradovKorobovBilinearPhase
open VinogradovMomentReduction VinogradovKorobovMoment

/-- A genuine frequency-preserving index embedding retains every original equal-frequency moment solution. -/
theorem moment_le_of_frequency_embedding {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (r : ℕ) (v : ι → d → ℤ) (w : κ → d → ℤ) (e : ι ↪ κ) (he : ∀ i, w (e i) = v i) :
    moment r v ≤ moment r w := by
  simp only [VinogradovInitialExceptional.moment_eq_crossCount]
  apply Nat.cast_le.mpr
  let E : (Fin r → ι) ↪ (Fin r → κ) := ⟨fun x j => e (x j), by
    intro x y h
    funext j
    exact e.injective (congrArg (fun z => z j) h)⟩
  apply VinogradovFirstExponent.crossCount_le_of_embedding _ _ E
  intro x
  funext j
  simp only [tupleFrequency, Finset.sum_apply]
  change (∑ l : Fin r, w (e (x l)) j) = ∑ l : Fin r, v (x l) j
  simp only [he]

/-- The moment on an actual positive finite subset is bounded by its containing interval, retaining the interval length rather than substituting cardinality. -/
theorem finite_moment_le_interval (r k Y : ℕ) (B : Finset ℕ)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ Y) :
    moment r (fun b : B => monomialFrequency k b.val) ≤ meanValue r k Y := by
  let e : B ↪ Fin Y := ⟨fun b => ⟨b.val - 1, by have h := hB b.val b.property; omega⟩, by
    intro b c h
    have hv := congrArg Fin.val h
    have hb := (hB b.val b.property).1
    have hc := (hB c.val c.property).1
    apply Subtype.ext
    dsimp only at hv
    omega⟩
  apply moment_le_of_frequency_embedding r _ _ e
  intro b
  change monomialFrequency k (b.val - 1 + 1) = monomialFrequency k b.val
  rw [Nat.sub_add_cancel (hB b.val b.property).1]

/-- Both actual Korobov product-sum moments receive the proved critical exponent plus epsilon, retaining the complete joint Gaussian resonance and quartered smoothing cost. -/
theorem exists_critical_product_bound (k u v : ℕ) (hk : 2 ≤ k) (hu : k ≤ u) (hv : k ≤ v)
    (eps : ℝ) (heps : 0 < eps) :
    let r := (u + 1) * k
    let s := (v + 1) * k
    let lamr := 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eps
    let lams := 2 * (k : ℝ) * ((v : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eps
    ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, ∃ D : ℝ, 0 < D ∧ ∃ Y₀ : ℕ,
      ∀ M Y : ℕ, M₀ ≤ M → Y₀ ≤ Y → ∀ (t z : ℝ) (B : Finset ℕ),
      (∀ b ∈ B, 1 ≤ b ∧ b ≤ Y) → ∀ a : Fin k → ℝ, (∀ j, 0 < a j) →
      ‖∑ b : Fin M, ∑ c ∈ B,
          polynomialPhase k t z ((b.val + 1 : ℕ) : ℝ) c‖ ^ (2 * r * s) ≤
        (B.card : ℝ) ^ ((r - 1) * (2 * s)) * (M : ℝ) ^ (r * (2 * s - 2)) *
          (C * (M : ℝ) ^ lamr) *
          Real.exp (VinogradovGaussianKernel.supportCost a
            (frequencySupport (tupleFrequency r (fun b : Fin M => monomialFrequency k (b.val + 1)))) / 4) *
          (D * (Y : ℝ) ^ lams) *
          VinogradovGaussianBounds.resonanceEnvelope s a (phaseCoefficients k t z)
            (fun b : B => monomialFrequency k b.val) := by
  obtain ⟨C, hC, M₀, hJ⟩ :=
    VinogradovCriticalExponent.exists_global_critical_exponent k u hk hu eps heps
  obtain ⟨D, hD, Y₀, hK⟩ :=
    VinogradovCriticalExponent.exists_global_critical_exponent k v hk hv eps heps
  refine ⟨C, hC, max M₀ 1, D, hD, Y₀, ?_⟩
  intro M Y hM hY t z B hB a ha
  have hMpos : 0 < M := by have h := (le_max_right M₀ 1).trans hM; omega
  have hr : 1 ≤ (u + 1) * k := by nlinarith
  have hs : 1 ≤ (v + 1) * k := by nlinarith
  have hK0 : 0 ≤ moment ((v + 1) * k) (fun b : B => monomialFrequency k b.val) :=
    MeasureTheory.integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  have hE := VinogradovGaussianBounds.resonanceEnvelope_nonneg ((v + 1) * k) ha
    (phaseCoefficients k t z) (fun b : B => monomialFrequency k b.val)
  have hsecond := (finite_moment_le_interval ((v + 1) * k) k Y B hB).trans (hK Y hY)
  apply (interval_quarter_envelope_bound k hMpos t z B hr hs a ha).trans
  gcongr
  · exact hJ M ((le_max_left _ _).trans hM)

end
end RiemannGaussian.VinogradovCriticalKorobov
