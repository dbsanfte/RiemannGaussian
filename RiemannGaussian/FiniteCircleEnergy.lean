import RiemannGaussian.FiniteCircleFourier

/-!
# Complete complex energy of finite circle synthesis

The mixed synthesis identity retains both coefficient families and every
frequency coincidence. Only when the actual frequencies are distinct does
it reduce to the diagonal square sum. Exact finite Fourier inversion then
connects these waves to arbitrary literal periodic data.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

variable {Q : ℕ} [NeZero Q]

/-- A finite complex frequency family with all original coefficients. -/
def finiteCircleSynthesis {ι : Type*} (s : Finset ι) (ν : ι → ZMod Q) (b : ι → ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ s, b i * finiteCircleWave (ν i) n

/-- The complete mixed synthesis product retains all pairs before
averaging or taking a scalar energy. -/
theorem finiteCircleSynthesis_mul_conj {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (ν : ι → ZMod Q) (ω : κ → ZMod Q) (b : ι → ℂ) (c : κ → ℂ) (n : ℕ) :
    finiteCircleSynthesis s ν b n * starRingEnd ℂ (finiteCircleSynthesis t ω c n) =
      ∑ i ∈ s, ∑ j ∈ t, (b i * starRingEnd ℂ (c j)) *
        (finiteCircleWave (ν i) n * starRingEnd ℂ (finiteCircleWave (ω j) n)) := by
  simp only [finiteCircleSynthesis, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Complete-period mixed energy keeps every exact frequency coincidence
and both complex coefficients, including repeated frequencies. -/
theorem sum_range_finiteCircleSynthesis_mul_conj {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (ν : ι → ZMod Q) (ω : κ → ZMod Q)
    (b : ι → ℂ) (c : κ → ℂ) :
    (∑ n ∈ Finset.range Q,
      finiteCircleSynthesis s ν b n * starRingEnd ℂ (finiteCircleSynthesis t ω c n)) =
      (Q : ℂ) * ∑ i ∈ s, ∑ j ∈ t,
        if ν i = ω j then b i * starRingEnd ℂ (c j) else 0 := by
  simp_rw [finiteCircleSynthesis_mul_conj]
  calc
    _ = ∑ i ∈ s, ∑ j ∈ t, (b i * starRingEnd ℂ (c j)) *
        (∑ n ∈ Finset.range Q,
          finiteCircleWave (ν i) n * starRingEnd ℂ (finiteCircleWave (ω j) n)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
    _ = _ := by
      simp_rw [sum_range_finiteCircleWave_mul_conj]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> ring

/-- At distinct residue frequencies the exact complex energy is the
diagonal coefficient square sum times the literal period. -/
theorem sum_range_finiteCircleSynthesis_norm_sq {ι : Type*} (s : Finset ι)
    (ν : ι → ZMod Q) (b : ι → ℂ) (hν : Set.InjOn ν s) :
    (∑ n ∈ Finset.range Q, ‖finiteCircleSynthesis s ν b n‖ ^ 2) =
      (Q : ℝ) * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  have h := sum_range_finiteCircleSynthesis_mul_conj s s ν ν b b
  have hdiag (i : ι) (hi : i ∈ s) :
      (∑ j ∈ s, if ν i = ν j then b i * starRingEnd ℂ (b j) else 0) =
        (‖b i‖ : ℂ) ^ 2 := by
    have heq : (∑ j ∈ s, if ν i = ν j then b i * starRingEnd ℂ (b j) else 0) =
        ∑ j ∈ s, if i = j then b i * starRingEnd ℂ (b j) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [show (ν i = ν j) ↔ i = j from ⟨fun h ↦ hν hi hj h, congrArg ν⟩]
    rw [heq, Finset.sum_ite_eq_of_mem s i (fun j ↦ b i * starRingEnd ℂ (b j)) hi,
      Complex.mul_conj']
  simp_rw [Complex.mul_conj'] at h
  rw [Finset.sum_congr rfl hdiag] at h
  exact_mod_cast h

/-- Finite synthesis retains the exact integer period of all its waves. -/
theorem finiteCircleSynthesis_periodic {ι : Type*} (s : Finset ι)
    (ν : ι → ZMod Q) (b : ι → ℂ) : Function.Periodic (finiteCircleSynthesis s ν b) Q := by
  intro n
  unfold finiteCircleSynthesis
  apply Finset.sum_congr rfl
  intro i hi
  rw [finiteCircleWave_periodic (ν i) n]

/-- The full forward difference is synthesis with the original complex
frequency multipliers, before estimating their moduli. -/
theorem finiteCircleSynthesis_forward_difference {ι : Type*} (s : Finset ι)
    (ν : ι → ZMod Q) (b : ι → ℂ) (n : ℕ) :
    finiteCircleSynthesis s ν b (n + 1) - finiteCircleSynthesis s ν b n =
      finiteCircleSynthesis s ν (fun i ↦ b i * (ZMod.stdAddChar (ν i) - 1)) n := by
  unfold finiteCircleSynthesis
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [finiteCircleWave_succ]
  ring

end

end RiemannGaussian
