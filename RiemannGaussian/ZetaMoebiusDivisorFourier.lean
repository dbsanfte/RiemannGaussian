/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusCenteredResonance
import RiemannGaussian.ZetaMoebiusDivisorBoundary

/-!
# Signed divisor cancellation inside the complete Fourier products

The entire centered Fourier kernel is first reconstructed as a complex
weight at each original arithmetic product. Complete coprime divisor fibres
can then cancel without changing that weight. The finite band splits exactly
into the resulting boundary fibres and the unaltered complementary products.
Neither frequency phases nor the complementary arithmetic terms are dropped.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- Divisor cancellation commutes with every finite complex weight family.
The products lacking the chosen coprime factor remain explicitly present. -/
theorem sum_zetaMoebiusLogTailCoefficient_eq_boundary_add_compl
    (D : ℕ) {P : ℕ} (hP : P ≠ 1) (hprime : ¬IsPrimePow P)
    (S : Finset ℕ) (w : ℕ → ℂ) :
    (∑ m ∈ S, zetaMoebiusLogTailCoefficient D m * w m) =
      (∑ m ∈ S.filter (fun m ↦ P ∣ m ∧ P.Coprime (m / P)),
        (∑ d ∈ (m / P).divisors.filter (fun d ↦ d ≤ D ∧ D < P * d),
          (μ d : ℂ) * zetaMoebiusLogDivisorFibre D P (m / P) d) * w m) +
      ∑ m ∈ S.filter (fun m ↦ ¬(P ∣ m ∧ P.Coprime (m / P))),
        zetaMoebiusLogTailCoefficient D m * w m := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun m ↦ P ∣ m ∧ P.Coprime (m / P))]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  obtain ⟨hdiv, hcop⟩ := (Finset.mem_filter.mp hm).2
  have he := zetaMoebiusLogTailCoefficient_eq_boundary D hcop hP hprime
  rw [Nat.mul_div_cancel' hdiv] at he
  rw [he]

/-- The full centered Fourier products as one physical complex weight.
The sum is taken before its magnitude, preserving all inter-mode phases. -/
def zetaMoebiusCenteredPhysicalWeight (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (S : Finset (ZMod (2 ^ (32 * N) + 1))) (n : ℕ) : ℂ :=
  zetaPrimeFeature (5 / 4) n * (((2 ^ (32 * N) + 1 : ℕ) : ℂ)⁻¹ *
    ∑ k ∈ S, (ZMod.stdAddChar k ^ n - 1) * ZMod.dft (zetaQuarterKernelSamples p N y) k)

/-- Exact reconstruction of the full signed carrier in the original
product coordinate; all sums are finite and no analytic interchange is used. -/
theorem zetaMoebiusCenteredFourierPart_eq_physical (p : Polynomial ℂ) (D N : ℕ)
    (y : ℝ) (S : Finset (ZMod (2 ^ (32 * N) + 1))) :
    zetaMoebiusCenteredFourierPart p D N y S =
      ∑ n ∈ zetaPrimeLogBand N,
        zetaMoebiusLogTailCoefficient D n * zetaMoebiusCenteredPhysicalWeight p N y S n := by
  unfold zetaMoebiusCenteredFourierPart centeredFourierPart zetaMoebiusCenteredPhysicalWeight
  simp_rw [zetaMoebiusWeightedDFT_sub_zero_eq]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The actual centered carrier retains its entire Fourier interaction
while complete divisor fibres cancel on any chosen mixed-prime factor. -/
theorem zetaMoebiusCenteredFourierPart_eq_boundary_add_compl (p : Polynomial ℂ)
    (D N : ℕ) (y : ℝ) (S : Finset (ZMod (2 ^ (32 * N) + 1)))
    {P : ℕ} (hP : P ≠ 1) (hprime : ¬IsPrimePow P) :
    zetaMoebiusCenteredFourierPart p D N y S =
      (∑ m ∈ (zetaPrimeLogBand N).filter (fun m ↦ P ∣ m ∧ P.Coprime (m / P)),
        (∑ d ∈ (m / P).divisors.filter (fun d ↦ d ≤ D ∧ D < P * d),
          (μ d : ℂ) * zetaMoebiusLogDivisorFibre D P (m / P) d) *
            zetaMoebiusCenteredPhysicalWeight p N y S m) +
      ∑ m ∈ (zetaPrimeLogBand N).filter (fun m ↦ ¬(P ∣ m ∧ P.Coprime (m / P))),
        zetaMoebiusLogTailCoefficient D m * zetaMoebiusCenteredPhysicalWeight p N y S m := by
  rw [zetaMoebiusCenteredFourierPart_eq_physical]
  exact sum_zetaMoebiusLogTailCoefficient_eq_boundary_add_compl D hP hprime _ _

/-- The reconstruction preserves the previously proved source at every
hypothetical right-half zero. The new arithmetic boundary is still signed. -/
theorem tendsto_zetaRightHalfMoebius_centered_physical (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ∑ n ∈ zetaPrimeLogBand N,
        zetaMoebiusLogTailCoefficient
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) n *
          zetaMoebiusCenteredPhysicalWeight (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
            (zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N)) n)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  simpa only [zetaMoebiusCenteredFourierPart_eq_physical] using
    tendsto_zetaRightHalfMoebius_centered_resonance rho hrho

end
end RiemannGaussian
