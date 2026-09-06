import RiemannGaussian.FiniteCircleEnergy

/-!
# Exact Fourier coefficients of literal periodic sequences

The coefficients are those of the original complex sequence on its full
integer period. Inversion recovers every sample, and an additional literal
period forces each nonzero coefficient into its exact annihilator. No
spectral support assumption is introduced for the arithmetic application.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

variable {Q : ℕ} [NeZero Q]

/-- The normalized finite Fourier coefficient of the literal sequence. -/
def finitePeriodicFourierCoefficient (f : ℕ → ℂ) (k : ZMod Q) : ℂ :=
  ZMod.dft (fun j : ZMod Q ↦ f j.val) k / Q

/-- The coefficient of a finite sum retains every complex component. -/
theorem finitePeriodicFourierCoefficient_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℕ → ℂ) (k : ZMod Q) :
    finitePeriodicFourierCoefficient (fun n ↦ ∑ i ∈ s, f i n) k =
      ∑ i ∈ s, finitePeriodicFourierCoefficient (f i) k := by
  simp only [finitePeriodicFourierCoefficient, ZMod.dft_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]

/-- The coefficient retains the complete physical period and conjugate wave. -/
theorem finitePeriodicFourierCoefficient_eq_sum (f : ℕ → ℂ)
    (hf : Function.Periodic f Q) (k : ZMod Q) :
    finitePeriodicFourierCoefficient f k =
      (∑ n ∈ Finset.range Q, f n * starRingEnd ℂ (finiteCircleWave k n)) / Q := by
  unfold finitePeriodicFourierCoefficient
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  rw [← sum_range_natCast_eq_sum_zmod
    (fun j : ZMod Q ↦ ZMod.stdAddChar (-(j * k)) * f j.val)]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [ZMod.val_natCast, hf.map_mod_nat]
  simp only [finiteCircleWave, stdAddChar_neg_eq_conj, mul_comm]

/-- Exact inversion recovers the original complex sequence at every
integer sample, including samples beyond the chosen auxiliary period. -/
theorem finitePeriodicFourierCoefficient_synthesis (f : ℕ → ℂ)
    (hf : Function.Periodic f Q) (n : ℕ) :
    finiteCircleSynthesis Finset.univ id (finitePeriodicFourierCoefficient f : ZMod Q → ℂ) n =
      f n := by
  have h := congrFun (ZMod.dft.symm_apply_apply (fun j : ZMod Q ↦ f j.val)) (n : ZMod Q)
  rw [ZMod.invDFT_apply] at h
  simp only [smul_eq_mul] at h
  calc
    _ = (Q : ℂ)⁻¹ * ∑ k : ZMod Q,
        ZMod.stdAddChar (k * (n : ZMod Q)) * ZMod.dft (fun j : ZMod Q ↦ f j.val) k := by
      unfold finiteCircleSynthesis finitePeriodicFourierCoefficient finiteCircleWave
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [id_eq, mul_comm k (n : ZMod Q)]
      ring
    _ = f (n : ZMod Q).val := h
    _ = f n := by rw [ZMod.val_natCast, hf.map_mod_nat]

/-- The exact coefficient square sum equals the sequence's complete
period energy divided by that period. -/
theorem sum_finitePeriodicFourierCoefficient_norm_sq (f : ℕ → ℂ)
    (hf : Function.Periodic f Q) :
    (∑ k : ZMod Q, ‖finitePeriodicFourierCoefficient f k‖ ^ 2) =
      (∑ n ∈ Finset.range Q, ‖f n‖ ^ 2) / Q := by
  have h := sum_range_finiteCircleSynthesis_norm_sq (Q := Q) Finset.univ id
    (finitePeriodicFourierCoefficient f) (fun _ _ _ _ h ↦ h)
  simp_rw [finitePeriodicFourierCoefficient_synthesis f hf] at h
  apply (eq_div_iff (by exact_mod_cast (NeZero.ne Q) : (Q : ℝ) ≠ 0)).mpr
  simpa only [mul_comm] using h.symm

/-- A second exact integer period forces every nonzero coefficient
into its annihilator on the finite circle. -/
theorem finitePeriodicFourierCoefficient_eq_zero_of_period (f : ℕ → ℂ)
    (hf : Function.Periodic f Q) {p : ℕ} (hp : Function.Periodic f p)
    (k : ZMod Q) (hk : (p : ZMod Q) * k ≠ 0) :
    finitePeriodicFourierCoefficient f k = 0 := by
  have hg : Function.Periodic (fun n ↦ f n * starRingEnd ℂ (finiteCircleWave k n)) Q := by
    intro n
    change f (n + Q) * starRingEnd ℂ (finiteCircleWave k (n + Q)) = _
    rw [hf n, finiteCircleWave_periodic k n]
  have hs : (∑ n ∈ Finset.range Q, f n * starRingEnd ℂ (finiteCircleWave k n)) =
      starRingEnd ℂ (finiteCircleWave k p) *
        (∑ n ∈ Finset.range Q, f n * starRingEnd ℂ (finiteCircleWave k n)) := by
    calc
      _ = ∑ n ∈ Finset.range Q, f (p + n) *
          starRingEnd ℂ (finiteCircleWave k (p + n)) :=
        (sum_range_nat_periodic_shift hg p).symm
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [Nat.add_comm p n, hp n, finiteCircleWave_add, map_mul]
        ring
  have hchar : starRingEnd ℂ (finiteCircleWave k p) ≠ 1 := by
    intro h
    have h' := congrArg (starRingEnd ℂ) h
    simp only [map_one, starRingEnd_self_apply] at h'
    apply hk
    apply ZMod.injective_stdAddChar
    simpa only [finiteCircleWave, AddChar.map_zero_eq_one] using h'
  have hz : (∑ n ∈ Finset.range Q, f n * starRingEnd ℂ (finiteCircleWave k n)) = 0 := by
    by_contra hne
    apply hchar
    apply mul_right_cancel₀ hne
    simpa only [one_mul] using hs.symm
  rw [finitePeriodicFourierCoefficient_eq_sum f hf, hz, zero_div]

end

end RiemannGaussian
