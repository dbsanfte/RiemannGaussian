/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovGaussianResonance

/-!
# Centering the Gaussian on the actual frequency support

An integer translation of the full frequency support is transported
exactly into unit phase twists of the original weights. This permits
paying the Gaussian cost relative to an arbitrary integer center while
retaining the signed Gram identity and the canonical weights upstream.
No arithmetic spacing or high-moment estimate is assumed or proved here.
-/

namespace RiemannGaussian.VinogradovGaussianCentering
noncomputable section
open VinogradovGaussianKernel VinogradovGaussianResonance
open VinogradovMomentReduction VinogradovShiftedMoment VinogradovMeanValue
open scoped BigOperators

/-- The lattice phase is a character in its integer frequency vector. -/
theorem latticePhase_frequency_add {k : ℕ} (m n : Fin k → ℤ) (x : Fin k → ℝ) :
    latticePhase (m + n) x = latticePhase m x * latticePhase n x := by
  simp only [latticePhase, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, Int.cast_add]
  ring

/-- Translate the complete frequency support by an integer center. -/
def centeredSupport {k : ℕ} (C : Finset (Fin k → ℤ)) (m : Fin k → ℤ) :
    Finset (Fin k → ℤ) := by
  classical
  exact C.image (fun n => n - m)

/-- The canonical integer midpoint of two integer coordinate endpoints. -/
def integerMidpoint (L U : ℤ) : ℤ := (L + U) / 2

/-- Centering an integer interval pays half its diameter plus at most
one half for parity. The complete integer rounding cost is explicit. -/
theorem midpoint_distance_le {L U n : ℤ} (hL : L ≤ n) (hU : n ≤ U) :
    |(n : ℝ) - (integerMidpoint L U : ℝ)| ≤ ((U : ℝ) - L + 1) / 2 := by
  have hm₀ : L + U - 1 ≤ 2 * integerMidpoint L U := by
    unfold integerMidpoint
    omega
  have hm₁ : 2 * integerMidpoint L U ≤ L + U := by
    unfold integerMidpoint
    omega
  have hL' : (L : ℝ) ≤ n := by exact_mod_cast hL
  have hU' : (n : ℝ) ≤ U := by exact_mod_cast hU
  have hm₀' : (L : ℝ) + U - 1 ≤ 2 * (integerMidpoint L U : ℝ) := by exact_mod_cast hm₀
  have hm₁' : 2 * (integerMidpoint L U : ℝ) ≤ (L : ℝ) + U := by exact_mod_cast hm₁
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The exact centered support cost is bounded using coordinate radii.
The support itself is retained; only its Gaussian exponent is majorized. -/
theorem centered_cost_le {k : ℕ} {a : Fin k → ℝ} (ha : ∀ j, 0 ≤ a j)
    (C : Finset (Fin k → ℤ)) (m : Fin k → ℤ) (R : Fin k → ℝ)
    (hR : ∀ n ∈ C, ∀ j, |(n j : ℝ) - (m j : ℝ)| ≤ R j) :
    supportCost a (centeredSupport C m) ≤ ∑ j, Real.pi * a j * (R j) ^ 2 := by
  classical
  unfold supportCost
  apply Finset.max'_le
  intro c hc
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (mul_nonneg Real.pi_pos.le (ha j))
      (sq_nonneg _))
  · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hn
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg Real.pi_pos.le (ha j))
    simpa only [Pi.sub_apply, Int.cast_sub, sq_abs] using
      pow_le_pow_left₀ (abs_nonneg ((u j : ℝ) - m j)) (hR u hu j) 2

/-- A canonical center pays squared half-diameters, including the exact
integer-parity allowance, instead of distances from the origin. -/
theorem midpoint_cost_le {k : ℕ} {a : Fin k → ℝ} (ha : ∀ j, 0 ≤ a j)
    (C : Finset (Fin k → ℤ)) (L U : Fin k → ℤ)
    (hC : ∀ n ∈ C, ∀ j, L j ≤ n j ∧ n j ≤ U j) :
    supportCost a (centeredSupport C (fun j => integerMidpoint (L j) (U j))) ≤
      ∑ j, Real.pi * a j * (((U j : ℝ) - L j + 1) / 2) ^ 2 := by
  apply centered_cost_le ha
  intro n hn j
  exact midpoint_distance_le (hC n hn j).1 (hC n hn j).2

/-- The exact unit phase twist forced by a translation of frequencies. -/
def phaseTwist {k : ℕ} {ι : Type*}
    (m : Fin k → ℤ) (x : ι → Fin k → ℝ) (w : ι → ℂ) (b : ι) : ℂ :=
  w b * latticePhase m (x b)

/-- Centering changes no weight norm, including at a zero alignment weight. -/
theorem norm_phaseTwist {k : ℕ} {ι : Type*}
    (m : Fin k → ℤ) (x : ι → Fin k → ℝ) (w : ι → ℂ) (b : ι) :
    ‖phaseTwist m x w b‖ = ‖w b‖ := by
  simp only [phaseTwist, norm_mul, norm_latticePhase, mul_one]

/-- Translating a frequency and twisting each actual weight preserve the
entire complex sample sum, before norms or powers are taken. -/
theorem sample_eq_centered {k : ℕ} {ι : Type*} [Fintype ι]
    (m n : Fin k → ℤ) (x : ι → Fin k → ℝ) (w : ι → ℂ) :
    (∑ b, phaseTwist m x w b * latticePhase (n - m) (x b)) =
      ∑ b, w b * latticePhase n (x b) := by
  apply Finset.sum_congr rfl
  intro b hb
  rw [phaseTwist, mul_assoc, ← latticePhase_frequency_add]
  congr 2
  abel

/-- The full even moment has a Gaussian bound centered at any integer
vector. Every frequency is translated, every phase twist is retained,
and the exact maximum cost on the translated support is paid. -/
theorem finite_moment_le_centered_gram {k : ℕ} {ι : Type*} [Fintype ι]
    (s : ℕ) (C : Finset (Fin k → ℤ)) (m : Fin k → ℤ)
    (x : ι → Fin k → ℝ) (w : ι → ℂ)
    {a : Fin k → ℝ} (ha : ∀ j, 0 < a j) :
    (∑ n ∈ C, ‖∑ b, w b * latticePhase n (x b)‖ ^ (2 * s)) ≤
      Real.exp (supportCost a (centeredSupport C m)) *
        (momentGram s a x (phaseTwist m x w)).re := by
  classical
  have h := finite_energy_le_gram ha (fun b : Fin s → ι => ∑ j, x (b j))
    (tupleWeight s (phaseTwist m x w)) (centeredSupport C m)
    (fun _ hn => frequencyCost_le_supportCost a _ hn)
  apply le_trans (le_of_eq ?_) h
  simp_rw [← sample_power_expansion, norm_pow, ← pow_mul, Nat.mul_comm s 2]
  unfold centeredSupport
  rw [Finset.sum_image (fun n _ p _ hnp => sub_left_inj.mp hnp)]
  simp only [sample_eq_centered]

/-- The actual two-Hölder dual moment may use a centered Gaussian. Its
original weights acquire the exact center-dependent phase twists. -/
theorem dualMoment_le_centered_gram {k : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r s : ℕ) (v : ι → Fin k → ℤ) (x : κ → Fin k → ℝ) (w : κ → ℂ)
    (m : Fin k → ℤ) {a : Fin k → ℝ} (ha : ∀ j, 0 < a j) :
    dualMoment r s v (fun b j => (x b j : UnitAddCircle)) w ≤
      Real.exp (supportCost a (centeredSupport (frequencySupport (tupleFrequency r v)) m)) *
        (momentGram s a x (phaseTwist m x w)).re := by
  simpa only [dualMoment, latticePhase_eq_mFourier] using
    finite_moment_le_centered_gram s (frequencySupport (tupleFrequency r v)) m x w ha

/-- After the exact centered Gram identity, bounded weights give the
same complete joint resonance sum with the smaller centered support cost
whenever that cost is smaller. No special weight family is required. -/
theorem dualMoment_le_centered_resonance {k : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r s : ℕ) (v : ι → Fin k → ℤ) (u : κ → Fin k → ℤ) (γ : Fin k → ℝ)
    (w : κ → ℂ) (hw : ∀ b, ‖w b‖ ≤ 1) (m : Fin k → ℤ)
    {a : Fin k → ℝ} (ha : ∀ j, 0 < a j) :
    dualMoment r s v (fun b j => (linearSample γ (u b) j : UnitAddCircle)) w ≤
      Real.exp (supportCost a (centeredSupport (frequencySupport (tupleFrequency r v)) m)) *
        moment s u * resonanceSum s a γ u := by
  apply (dualMoment_le_centered_gram r s v (fun b => linearSample γ (u b)) w m ha).trans
  have h := momentGram_re_le s ha γ u
    (phaseTwist m (fun b => linearSample γ (u b)) w)
    (fun b => (norm_phaseTwist _ _ _ b).trans_le (hw b))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

end
end RiemannGaussian.VinogradovGaussianCentering
