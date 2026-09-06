import RiemannGaussian.EtaDivisorFourierGrid
import RiemannGaussian.EtaMoebiusDivisorCorrelation

/-!
# The proved Fourier support of literal completed eta phases

Every Fourier coefficient comes from the original Möbius sign, completion
factor, and integer quotient parity. Literal periodicity proves spectral
support, and exact inversion reconstructs the full family before its
complete energy is evaluated. No support premise is assumed for eta.
-/

open Complex
open scoped Classical ComplexConjugate ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The original leading parity family keeps every Möbius coefficient
and the full complex completion factor. -/
def pairedEtaCompletedMoebiusParityFamily (rho : NontrivialZetaZero) (M D : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 D, pairedEtaCompletedMoebiusParityPhase rho M d

/-- A literal quotient-parity column has its exact divisor period. -/
theorem pairedEtaCompletedMoebiusParityPhase_periodic (rho : NontrivialZetaZero)
    {d : ℕ} (hd : 0 < d) :
    Function.Periodic (fun M ↦ pairedEtaCompletedMoebiusParityPhase rho M d) (2 * d) := by
  intro M
  change pairedEtaCompletedMoebiusParityPhase rho (M + 2 * d) d =
    pairedEtaCompletedMoebiusParityPhase rho M d
  unfold pairedEtaCompletedMoebiusParityPhase
  rw [show 2 * d = d * 2 by omega, Nat.add_mul_div_left M 2 hd,
    pairedEtaDirichletSign_add_even _ _ (by decide : Even 2)]

/-- Every multiple of an exact integer period is again a period. -/
theorem periodic_nat_of_dvd {α : Type*} {f : ℕ → α} {p Q : ℕ}
    (hp : Function.Periodic f p) (hpQ : p ∣ Q) : Function.Periodic f Q := by
  simpa only [Nat.cast_id, Nat.div_mul_cancel hpQ] using hp.nat_mul (Q / p)

/-- The literal column keeps its divisor period at every starting cutoff. -/
theorem pairedEtaCompletedMoebiusParityPhase_shift_periodic (rho : NontrivialZetaZero)
    (A : ℕ) {d : ℕ} (hd : 0 < d) :
    Function.Periodic (fun n ↦ pairedEtaCompletedMoebiusParityPhase rho (A + n) d) (2 * d) := by
  intro n
  simpa only [Nat.add_assoc] using pairedEtaCompletedMoebiusParityPhase_periodic rho hd (A + n)

/-- Any common multiple of all literal divisor periods is a period
of the complete family, at every physical starting cutoff. -/
theorem pairedEtaCompletedMoebiusParityFamily_periodic (rho : NontrivialZetaZero)
    (A D Q : ℕ) (hQ : ∀ d ∈ Finset.Icc 1 D, 2 * d ∣ Q) :
    Function.Periodic (fun n ↦ pairedEtaCompletedMoebiusParityFamily rho (A + n) D) Q := by
  intro n
  unfold pairedEtaCompletedMoebiusParityFamily
  apply Finset.sum_congr rfl
  intro d hd
  exact periodic_nat_of_dvd
    (pairedEtaCompletedMoebiusParityPhase_shift_periodic rho A (Finset.mem_Icc.mp hd).1)
    (hQ d hd) n

variable {Q : ℕ} [NeZero Q]

/-- The literal finite Fourier coefficient vanishes outside the proved
arithmetic divisor spectrum, retaining the full complex family in its definition. -/
theorem pairedEtaCompletedMoebiusParityFamily_fourier_eq_zero
    (rho : NontrivialZetaZero) (A D : ℕ)
    (hQ : ∀ d ∈ Finset.Icc 1 D, 2 * d ∣ Q) (k : ZMod Q)
    (hk : k ∉ pairedEtaDivisorFourierSpectrum D Q) :
    finitePeriodicFourierCoefficient
      (fun n ↦ pairedEtaCompletedMoebiusParityFamily rho (A + n) D) k = 0 := by
  unfold pairedEtaCompletedMoebiusParityFamily
  rw [finitePeriodicFourierCoefficient_sum]
  apply Finset.sum_eq_zero
  intro d hd
  have hp := pairedEtaCompletedMoebiusParityPhase_shift_periodic rho A (Finset.mem_Icc.mp hd).1
  apply finitePeriodicFourierCoefficient_eq_zero_of_period _ (periodic_nat_of_dvd hp (hQ d hd)) hp
  intro hz
  exact hk ((mem_pairedEtaDivisorFourierSpectrum D k).mpr ⟨d, hd, hz⟩)

/-- Exact synthesis on the proved arithmetic spectrum reconstructs
every physical sample of the original leading parity family. -/
theorem pairedEtaCompletedMoebiusParityFamily_eq_fourier (rho : NontrivialZetaZero)
    (A D : ℕ) (hQ : ∀ d ∈ Finset.Icc 1 D, 2 * d ∣ Q) (n : ℕ) :
    finiteCircleSynthesis (pairedEtaDivisorFourierSpectrum D Q) id
      (finitePeriodicFourierCoefficient
        (fun m ↦ pairedEtaCompletedMoebiusParityFamily rho (A + m) D)) n =
      pairedEtaCompletedMoebiusParityFamily rho (A + n) D := by
  rw [← finitePeriodicFourierCoefficient_synthesis _
    (pairedEtaCompletedMoebiusParityFamily_periodic rho A D Q hQ) n]
  unfold finiteCircleSynthesis
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k hk hknot
  rw [pairedEtaCompletedMoebiusParityFamily_fourier_eq_zero rho A D hQ k hknot, zero_mul]

/-- The exact coefficient energy on the arithmetic spectrum is the
complete-period energy of the original parity family. -/
theorem pairedEtaCompletedMoebiusParityFamily_fourier_energy
    (rho : NontrivialZetaZero) (A D : ℕ)
    (hQ : ∀ d ∈ Finset.Icc 1 D, 2 * d ∣ Q) :
    (∑ k ∈ pairedEtaDivisorFourierSpectrum D Q,
      ‖finitePeriodicFourierCoefficient
        (fun n ↦ pairedEtaCompletedMoebiusParityFamily rho (A + n) D) k‖ ^ 2) =
      (∑ n ∈ Finset.range Q,
        ‖pairedEtaCompletedMoebiusParityFamily rho (A + n) D‖ ^ 2) / Q := by
  rw [← sum_finitePeriodicFourierCoefficient_norm_sq _
    (pairedEtaCompletedMoebiusParityFamily_periodic rho A D Q hQ)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k hk hknot
  rw [pairedEtaCompletedMoebiusParityFamily_fourier_eq_zero rho A D hQ k hknot, norm_zero, zero_pow (by decide)]

end

end RiemannGaussian
