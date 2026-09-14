/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFourierEvaluation
import RiemannGaussian.VinogradovMomentReduction
import RiemannGaussian.ZetaSquarefreeVaughanLogSource

/-!
# Signed Vinogradov conditioned energy for the original Riesz carrier

The full squarefree composite Riesz coefficient and original zeta filter
kernel become complex weights of an auxiliary polynomial Fourier lift.
At phase zero the lift is exactly the original finite arithmetic band.
An exact residue partition and tuple expansion connect it to the actual
signed conditioned-energy theorem, retaining all original signs, phases,
cutoffs, damping, filter coefficients and equal-power-sum cross terms.

Point evaluation pays the number of joint frequencies attained by nonzero
configuration weights. The resulting whole-band bound uses actual mixed
moments and the literal conditioned-block count. A constructive nonempty
block theorem justifies its normalization when the full next-digit window
fits inside the original band endpoint. The original negative-multiplicity
source limit survives at phase zero. No decay of the remaining mixed
moments, independent signed floor, VK region or RH conclusion is asserted.
-/

namespace RiemannGaussian.ZetaRieszConditionedEnergy
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open Filter Topology VinogradovResidueEnergy VinogradovFourierEvaluation
open MeasureTheory UnitAddTorus VinogradovMomentPartition VinogradovPartitionEnergy
open VinogradovConditionedCompletion VinogradovProductEnergy VinogradovShiftedMoment

/-- Use the same normalized Haar measure as the conditioned-energy theorem. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The entire original band summand, including Riesz sign, actual support and complex zeta kernel. -/
def bandWeight (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) (n : ℕ) : ℂ :=
  if n ∈ zetaPrimeLogBand N then SquarefreeVaughanLogSource.coefficient L n *
    zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n else 0


/-- The auxiliary polynomial Fourier lift of one actual positive residue window. -/
def residueLift (p b k : ℕ) (eta : ℤ) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (theta : UnitAddTorus (Fin k)) : ℂ :=
  polynomial (fun n : PrimeTailWindow p b eta (2 ^ (32 * N)) =>
    VinogradovMeanValue.monomialFrequency k (n.val.val + 1))
    (fun n => bandWeight L P N y (n.val.val + 1)) theta

/-- The lift over the full original finite band endpoint, with zero weights outside its actual support. -/
def fullLift (k : ℕ) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (theta : UnitAddTorus (Fin k)) : ℂ :=
  polynomial (fun n : Fin (2 ^ (32 * N)) => VinogradovMeanValue.monomialFrequency k (n.val + 1))
    (fun n => bandWeight L P N y (n.val + 1)) theta

/-- The positive-integer convention agrees exactly with the finite interval sum. -/
theorem sum_positive_window (X : ℕ) (f : ℕ → ℂ) :
    (∑ n : Fin X, f (n.val + 1)) = ∑ n ∈ Finset.Icc 1 X, f n := by
  rw [Fin.sum_univ_eq_sum_range (fun n => f (n + 1)) X]
  have he : Finset.Icc 1 X = Finset.Ico 1 (X + 1) := by ext n; simp
  rw [he, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]

/-- Summing the original complex weights recovers the literal arithmetic band. -/
theorem bandWeight_sum (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    (∑ n : Fin (2 ^ (32 * N)), bandWeight L P N y (n.val + 1)) =
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y := by
  rw [sum_positive_window]
  unfold bandWeight zetaArithmeticBand
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp [zetaPrimeLogBand, and_assoc]
  tauto

/-- The full Fourier lift at phase zero is exactly the original Riesz carrier. -/
theorem fullLift_zero (k : ℕ) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    fullLift k L P N y 0 = zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y := by
  simpa only [fullLift, polynomial, mFourier, ContinuousMap.coe_mk, Pi.zero_apply,
    fourier_eval_zero, Finset.prod_const_one, mul_one] using bandWeight_sum L P N y


/-- Retain the complete original summand on the literal prime-power residue window. -/
def residueWeight (p b : ℕ) (eta : ℤ) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (n : PrimeTailWindow p b eta (2 ^ (32 * N))) : ℂ :=
  bandWeight L P N y (n.val.val + 1)

/-- Every powered residue lift retains products of original complex Riesz weights on complete tuple frequencies. -/
theorem residueLift_power_eq (p b k r : ℕ) (eta : ℤ) (L : ℝ)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) (theta : UnitAddTorus (Fin k)) :
    residueLift p b k eta L P N y theta ^ r =
      polynomial (tailFrequency (k := k) (fun _ : Fin r => 1))
        (tupleWeight r (residueWeight p b eta L P N y)) theta := by
  have hf : tailFrequency (k := k) (fun _ : Fin r => 1) =
      tupleFrequency r (fun n : PrimeTailWindow p b eta (2 ^ (32 * N)) =>
        VinogradovMeanValue.monomialFrequency k (n.val.val + 1)) := by
    funext u i
    simp only [tailFrequency, tupleFrequency, Finset.sum_apply, one_mul,
      VinogradovMeanValue.monomialFrequency, Nat.cast_add, Nat.cast_one]
  rw [hf]
  exact weighted_power_expansion r
    (fun n : PrimeTailWindow p b eta (2 ^ (32 * N)) =>
      VinogradovMeanValue.monomialFrequency k (n.val.val + 1))
    (residueWeight p b eta L P N y) theta

/-- The proved signed congruencing theorem bounds the actual Riesz-weighted conditioned energy by its literal finer mixed-moment maximum. -/
theorem conditioned_riesz_energy_le {p k a b r xi : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a < b) (eta : ℤ)
    (colour : Fin k → Bool) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    (∫ theta : UnitAddTorus (Fin k),
      ‖polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := 2 ^ (32 * N)) colour)
        (fun _ => 1) theta‖ ^ 2 * ‖residueLift p b k eta L P N y theta‖ ^ (2 * r)) ≤
      ((p ^ ((a + b) * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colour : ℕ) : ℝ) *
        ((p ^ (k * b - a)) ^ k : ℕ) *
          fineMomentMaximum (k := k) (fun _ : Fin r => 1)
            (tupleWeight r (residueWeight p b eta L P N y)) := by
  have he := conditioned_product_max_le (xi := xi) hkp hk hab eta colour (fun _ : Fin r => 1)
    (tupleWeight r (residueWeight p b eta L P N y))
  have hn (theta : UnitAddTorus (Fin k)) :
      ‖polynomial (tailFrequency (k := k) (fun _ : Fin r => 1))
        (tupleWeight r (residueWeight p b eta L P N y)) theta‖ ^ 2 =
        ‖residueLift p b k eta L P N y theta‖ ^ (2 * r) := by
    rw [← residueLift_power_eq, norm_pow, ← pow_mul, Nat.mul_comm r 2]
  simpa only [hn] using he


/-- All residue classes partition the complete positive window exactly. -/
theorem sum_residue_windows {q X : ℕ} (hq : 0 < q) (f : Fin X → ℂ) :
    (∑ xi : Fin q, ∑ n : VinogradovResidueMoment.ResidueWindow q xi.val X, f n.val) =
      ∑ n : Fin X, f n := by
  have he (xi : Fin q) :
      (∑ n : VinogradovResidueMoment.ResidueWindow q xi.val X, f n.val) =
      ∑ n : Fin X, if (n.val + 1) % q = xi.val then f n else 0 := by
    rw [← Finset.sum_filter]
    symm
    exact Finset.sum_subtype _ (by simp) f
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  let z : Fin q := ⟨(n.val + 1) % q, Nat.mod_lt _ hq⟩
  change (∑ xi : Fin q, if z.val = xi.val then f n else 0) = f n
  simp only [Fin.val_inj]
  simp

/-- The entire complex lift is the exact sum of its original residue lifts, at every auxiliary phase. -/
theorem fullLift_partition {p : ℕ} [NeZero p] (b k : ℕ)
    (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) (theta : UnitAddTorus (Fin k)) :
    fullLift k L P N y theta =
      ∑ xi : Fin (p ^ b), residueLift p b k (xi.val : ℤ) L P N y theta := by
  have he (xi : Fin (p ^ b)) :
      residueLift p b k (xi.val : ℤ) L P N y theta =
      ∑ n : VinogradovResidueMoment.ResidueWindow (p ^ b) xi.val (2 ^ (32 * N)),
        bandWeight L P N y (n.val.val + 1) *
          mFourier (VinogradovMeanValue.monomialFrequency k (n.val.val + 1)) theta := by
    have hx : (((xi.val : ℤ) : ZMod (p ^ b))).val = xi.val := by
      rw [Int.cast_natCast]
      exact ZMod.val_natCast_of_lt xi.isLt
    unfold residueLift polynomial PrimeTailWindow
    rw [hx]
  simp_rw [he]
  symm
  exact sum_residue_windows (pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) b)
    (fun n => bandWeight L P N y (n.val + 1) *
      mFourier (VinogradovMeanValue.monomialFrequency k (n.val + 1)) theta)

/-- At phase zero the exact residue partition recovers the whole original carrier. -/
theorem actual_band_eq_residue_lifts {p : ℕ} [NeZero p] (b k : ℕ)
    (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y =
      ∑ xi : Fin (p ^ b), residueLift p b k (xi.val : ℤ) L P N y 0 := by
  rw [← fullLift_zero k, fullLift_partition (p := p) b k L P N y 0]

/-- The literal number of admissible original conditioned blocks at the unchanged band endpoint. -/
def blockCount (p k a xi N : ℕ) : ℕ :=
  Fintype.card (ConditionedWindow p k a xi (2 ^ (32 * N)))

/-- The full product of original Riesz weights on a block-and-tail configuration. -/
def configurationWeight {p k a b r xi : ℕ} (eta : ℤ) (L : ℝ)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (z : WindowConfiguration p k a b r xi (2 ^ (32 * N)) eta) : ℂ :=
  tupleWeight r (residueWeight p b eta L P N y) z.2

/-- The number of joint frequencies attained by nonzero original configuration weights, with no rectangular padding. -/
def frequencyCost {p k a b r xi : ℕ} (eta : ℤ) (colour : Fin k → Bool)
    (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) : ℕ :=
  (activeSupport (windowFrequency (p := p) (a := a) (b := b) (xi := xi)
    (X := 2 ^ (32 * N)) (eta := eta) colour (fun _ : Fin r => 1))
    (configurationWeight eta L P N y)).card

/-- The proved signed fibre and finer-residue costs, including the colour factorial. -/
def congruenceCost (p k a b : ℕ) (colour : Fin k → Bool) : ℕ :=
  p ^ ((a + b) * (k * (k - 1) / 2)) *
    VinogradovSignedCongruence.colourFactorial colour * (p ^ (k * b - a)) ^ k

/-- The actual maximum of finer-residue mixed moments with the complete powered Riesz tail. -/
def rieszMomentMaximum (p b k r : ℕ) [NeZero p] (eta : ℤ) (L : ℝ)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) : ℝ :=
  fineMomentMaximum (k := k) (fun _ : Fin r => 1)
    (tupleWeight r (residueWeight p b eta L P N y))

/-- The actual block polynomial at zero is its literal admissible-block count. -/
theorem block_polynomial_zero (p k a xi N : ℕ) (colour : Fin k → Bool) :
    polynomial (blockFrequency (p := p) (a := a) (xi := xi)
      (X := 2 ^ (32 * N)) colour) (fun _ => 1) 0 = (blockCount p k a xi N : ℂ) := by
  simp [polynomial, mFourier, blockCount]

/-- The original full configuration polynomial factors exactly into the signed block and powered Riesz lift. -/
theorem amplified_lift_eq {p k a b r xi : ℕ} (eta : ℤ) (colour : Fin k → Bool)
    (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) (theta : UnitAddTorus (Fin k)) :
    polynomial (windowFrequency (p := p) (a := a) (b := b) (xi := xi)
      (X := 2 ^ (32 * N)) (eta := eta) colour (fun _ : Fin r => 1))
      (configurationWeight eta L P N y) theta =
    polynomial (blockFrequency (p := p) (a := a) (xi := xi)
      (X := 2 ^ (32 * N)) colour) (fun _ => 1) theta *
      residueLift p b k eta L P N y theta ^ r := by
  unfold configurationWeight
  rw [window_polynomial_eq_product, ← residueLift_power_eq]

/-- A genuine pointwise Riesz bound pays the attained-frequency cost and the proved signed congruence cost. -/
theorem residue_sample_bound {p k a b r xi : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a < b) (eta : ℤ)
    (colour : Fin k → Bool) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    (blockCount p k a xi N : ℝ) ^ 2 * ‖residueLift p b k eta L P N y 0‖ ^ (2 * r) ≤
      (frequencyCost (p := p) (a := a) (b := b) (r := r) (xi := xi)
        eta colour L P N y : ℝ) * congruenceCost p k a b colour *
        rieszMomentMaximum p b k r eta L P N y := by
  have hs := active_sample_energy_le
    (windowFrequency (p := p) (a := a) (b := b) (xi := xi)
      (X := 2 ^ (32 * N)) (eta := eta) colour (fun _ : Fin r => 1))
    (configurationWeight eta L P N y) 0
  change _ ≤ (frequencyCost (p := p) (a := a) (b := b) (r := r) (xi := xi)
    eta colour L P N y : ℝ) * _ at hs
  simp only [amplified_lift_eq, norm_mul, mul_pow, norm_pow, ← pow_mul,
    Nat.mul_comm r 2, block_polynomial_zero, Complex.norm_natCast] at hs
  have he := conditioned_riesz_energy_le (xi := xi) (r := r) hkp hk hab eta colour L P N y
  apply hs.trans
  calc
    _ ≤ (frequencyCost (p := p) (a := a) (b := b) (r := r) (xi := xi)
      eta colour L P N y : ℝ) *
      (((p ^ ((a + b) * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colour : ℕ) : ℝ) *
        ((p ^ (k * b - a)) ^ k : ℕ) *
          rieszMomentMaximum p b k r eta L P N y) :=
      mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
    _ = _ := by simp only [congruenceCost, Nat.cast_mul]; ring

/-- The entire original Riesz carrier receives a finite mixed-moment bound with its exact block normalization and explicit residue summation cost. -/
theorem actual_band_conditioned_bound {p k a b r xi : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a < b) (hr : 0 < r)
    (colour : Fin k → Bool) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    (blockCount p k a xi N : ℝ) ^ 2 *
      ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y‖ ^ (2 * r) ≤
    (p ^ b : ℝ) ^ (2 * r - 1) * ∑ eta : Fin (p ^ b),
      (frequencyCost (p := p) (a := a) (b := b) (r := r) (xi := xi)
        (eta.val : ℤ) colour L P N y : ℝ) * congruenceCost p k a b colour *
        rieszMomentMaximum p b k r (eta.val : ℤ) L P N y := by
  have hh := VinogradovMomentReduction.norm_weighted_power_bound Finset.univ
    (fun _ : Fin (p ^ b) => 1)
    (fun eta => residueLift p b k (eta.val : ℤ) L P N y 0) (by simp)
    (p := 2 * r) (by omega)
  simp only [Complex.ofReal_one, one_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow] at hh
  rw [actual_band_eq_residue_lifts (p := p) b k]
  calc
    _ ≤ (blockCount p k a xi N : ℝ) ^ 2 *
        ((p ^ b : ℝ) ^ (2 * r - 1) * ∑ eta : Fin (p ^ b),
          ‖residueLift p b k (eta.val : ℤ) L P N y 0‖ ^ (2 * r)) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = (p ^ b : ℝ) ^ (2 * r - 1) * ∑ eta : Fin (p ^ b),
        (blockCount p k a xi N : ℝ) ^ 2 *
          ‖residueLift p b k (eta.val : ℤ) L P N y 0‖ ^ (2 * r) := by
      rw [← Finset.mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun eta _ => residue_sample_bound hkp hk hab
        (eta.val : ℤ) colour L P N y)) (by positivity)

/-- The exact residue moment retains all complex Riesz cross terms on the complete equal-power-sum fibres. -/
theorem residue_moment_eq_gram (p b k r : ℕ) (eta : ℤ) (L : ℝ)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    ((∫ theta : UnitAddTorus (Fin k), ‖residueLift p b k eta L P N y theta‖ ^ (2 * r) : ℝ) : ℂ) =
      weightedShift (tailFrequency (k := k) (fun _ : Fin r => 1))
        (tupleWeight r (residueWeight p b eta L P N y)) 0 := by
  rw [weightedShift_zero]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with theta
  have he := residueLift_power_eq p b k r eta L P N y theta
  have hn := congrArg (fun z : ℂ => ‖z‖ ^ 2) he
  simpa only [norm_pow, ← pow_mul, Nat.mul_comm r 2, polynomial] using hn

/-- The unchanged negative-multiplicity source survives the exact phase-zero residue partition; its independent upper bound remains open. -/
theorem tendsto_actual_residue_source {p : ℕ} [NeZero p] (b k : ℕ)
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N => (3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
      ∑ eta : Fin (p ^ b), residueLift p b k (eta.val : ℤ)
        (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
        (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im 0)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  simpa only [actual_band_eq_residue_lifts (p := p) b k] using
    SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho

/-- Explicit multiples of the coarse modulus prove the actual normalizing block count is positive. -/
theorem blockCount_pos {p k a N : ℕ} [NeZero p]
    (hkp : k < p) (hX : p ^ (a + 1) ≤ 2 ^ (32 * N)) :
    0 < blockCount p k a 0 N :=
  Fintype.card_pos_iff.mpr (conditionedWindow_nonempty hkp hX)

/-- Normalize the actual whole-carrier bound using a constructively nonzero block count, with no assumed moment budget. -/
theorem actual_band_le_mixed_moments {p k a b r : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a < b) (hr : 0 < r)
    (colour : Fin k → Bool) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (hX : p ^ (a + 1) ≤ 2 ^ (32 * N)) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y‖ ^ (2 * r) ≤
      ((p ^ b : ℝ) ^ (2 * r - 1) * ∑ eta : Fin (p ^ b),
        (frequencyCost (p := p) (a := a) (b := b) (r := r) (xi := 0)
          (eta.val : ℤ) colour L P N y : ℝ) * congruenceCost p k a b colour *
          rieszMomentMaximum p b k r (eta.val : ℤ) L P N y) /
        (blockCount p k a 0 N : ℝ) ^ 2 := by
  have hC : 0 < (blockCount p k a 0 N : ℝ) := by
    exact_mod_cast blockCount_pos hkp hX
  rw [le_div_iff₀ (sq_pos_of_pos hC), mul_comm]
  exact actual_band_conditioned_bound (xi := 0) hkp hk hab hr colour L P N y

/-- The full conditioned energy retains the signed block frequencies and original complex Riesz weights in its exact Gram identity. -/
theorem amplified_moment_eq_gram {p k a b r xi : ℕ} (eta : ℤ)
    (colour : Fin k → Bool) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    ((∫ theta : UnitAddTorus (Fin k),
      ‖polynomial (blockFrequency (p := p) (a := a) (xi := xi)
        (X := 2 ^ (32 * N)) colour) (fun _ => 1) theta‖ ^ 2 *
        ‖residueLift p b k eta L P N y theta‖ ^ (2 * r) : ℝ) : ℂ) =
      weightedShift (windowFrequency (p := p) (a := a) (b := b) (xi := xi)
        (X := 2 ^ (32 * N)) (eta := eta) colour (fun _ : Fin r => 1))
        (configurationWeight eta L P N y) 0 := by
  rw [weightedShift_zero]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with theta
  change _ = ‖polynomial _ _ theta‖ ^ 2
  rw [amplified_lift_eq, norm_mul, mul_pow, norm_pow, ← pow_mul, Nat.mul_comm r 2]

end
end RiemannGaussian.ZetaRieszConditionedEnergy
