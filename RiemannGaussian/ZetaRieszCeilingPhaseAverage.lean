/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJoinedPhysical
import RiemannGaussian.NatDivisorSquareDirichlet
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Common-height cancellation in the entire literal core

The squared coefficient mass of the ORIGINAL signed core decays geometrically.
All labels and masks are retained. Orthogonality of their distinct logarithms
identifies that mass with the long-height mean square, with an explicit finite
window error. This is an averaged arithmetic bound, NOT a pointwise ceiling at
the ordinate of a hypothetical zero. The order and height limits cannot be
exchanged without paying the window error.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Complex Real Filter Topology MeasureTheory
open scoped BigOperators Classical ComplexConjugate
namespace RiemannGaussian.ZetaRieszCeilingPhaseAverage
open ZetaRieszJointAllocation ZetaRieszParityPacket ZetaRieszAnnulusJoint
open ZetaRieszWideOwnerAudit

/-- The original common height phase, without a separate phase for each prime. -/
def character (n : ℕ) (y : ℝ) : ℂ := exp (-I*(y : ℂ)*(Real.log n : ℂ))

theorem character_norm (n : ℕ) (y : ℝ) : ‖character n y‖ = 1 := by
  simp only [character, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
    Complex.I_re, Complex.ofReal_re, Complex.ofReal_im,
    neg_zero, zero_mul, mul_zero, sub_zero, Real.exp_zero]

theorem character_mul_conj (m n : ℕ) (y : ℝ) :
    character m y*conj (character n y) =
      exp ((-I*(Real.log m-Real.log n : ℝ))*y) := by
  rw [character, character, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem character_add (n : ℕ) (x y : ℝ) :
    character n (x+y)=character n x*character n y := by
  rw [character, character, character, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Only a different representation of each original atom, with no completion. -/
def amplitude (u : ℝ) (N n : ℕ) : ℂ :=
  (u : ℂ)^(N+1)*
    residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
      zetaPrimeLogKernel N (3/2) n

theorem kernel_eq_real_mul_character (N n : ℕ) (y : ℝ) :
    zetaPrimeLogKernel N (3/2+I*y) n =
      zetaPrimeLogKernel N (3/2) n*character n y := by
  unfold zetaPrimeLogKernel zetaPrimeFeature character
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem scaled_core_eq_character_sum (u y : ℝ) (N K : ℕ) :
    (u : ℂ)^(N+1)*coreResponse u y N K =
      ∑ n ∈ coreBand u N K, amplitude u N n*character n y := by
  simp only [coreResponse, Finset.mul_sum, amplitude, kernel_eq_real_mul_character]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Join every count and incidence in the original coefficient before squaring. -/
def coefficientEnergy (u : ℝ) (N K : ℕ) : ℝ :=
  ∑ n ∈ coreBand u N K, ‖amplitude u N n‖^2

/-- A complete arithmetic mass; this is not a prime sample. -/
def energyConstant : ℝ := 32*divisorSquareDirichletMass (5/4)

theorem energyConstant_nonneg : 0 <= energyConstant := by
  exact mul_nonneg (by norm_num) (divisorSquareDirichletMass_nonneg _)

theorem majorant_le_divisor_log (n : ℕ) :
    zetaMoebiusLogMajorant n <= (n.divisors.card : ℝ)*Real.log n := by
  have hinj : Set.InjOn Prod.snd (n.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
    intro a ha b hb he
    have ha' := Nat.mem_divisorsAntidiagonal.mp ha
    have hb' := Nat.mem_divisorsAntidiagonal.mp hb
    have hp := Nat.right_ne_zero_of_mem_divisorsAntidiagonal ha
    apply Prod.ext _ he
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hp)
    simpa only [he] using ha'.1.trans hb'.1.symm
  have hc : n.divisorsAntidiagonal.card = n.divisors.card := by
    rw [← Nat.image_snd_divisorsAntidiagonal]
    exact (Finset.card_image_iff.mpr hinj).symm
  unfold zetaMoebiusLogMajorant
  calc
    _ <= ∑ _a ∈ n.divisorsAntidiagonal, Real.log n := by
      apply Finset.sum_le_sum
      intro a ha
      have h := Nat.mem_divisorsAntidiagonal.mp ha
      have hd : a.2 ∣ n := ⟨a.1, by simpa only [mul_comm] using h.1.symm⟩
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero h.2) hd
      exact Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero
        (Nat.right_ne_zero_of_mem_divisorsAntidiagonal ha))) (by exact_mod_cast hle)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hc]

/-- Squaring the genuine divisor coefficient leaves a summable complete mass. -/
theorem majorant_square_bound (n : ℕ) :
    (zetaMoebiusLogMajorant n)^2*zetaPrimeExpWeight (3/2) n <=
      32*(n.divisors.card : ℝ)^2*(n : ℝ)^(-(5/4 : ℝ)) := by
  by_cases hn : n=0
  · subst n
    simp [zetaMoebiusLogMajorant]
  have hnR : (0 : ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hmaj := pow_le_pow_left₀ (zetaMoebiusLogMajorant_nonneg n)
    (majorant_le_divisor_log n) 2
  have hk := logMoment_exp_envelope 2 (Real.log_natCast_nonneg n)
    (by norm_num : (0 : ℝ)<1/4) (3/2)
  norm_num only [Nat.factorial_two, inv_div, one_div, one_pow, div_one] at hk
  have he : zetaPrimeExpWeight (5/4) n=(n : ℝ)^(-(5/4 : ℝ)) := by
    rw [zetaPrimeExpWeight, Real.rpow_def_of_pos hnR]
    congr 1
    ring
  calc
    _ <= ((n.divisors.card : ℝ)*Real.log n)^2*zetaPrimeExpWeight (3/2) n :=
      mul_le_mul_of_nonneg_right hmaj (Real.exp_pos _).le
    _ = (n.divisors.card : ℝ)^2*((Real.log n)^2*Real.exp (-(3/2)*Real.log n)) := by
      unfold zetaPrimeExpWeight
      ring
    _ <= (n.divisors.card : ℝ)^2*(32*zetaPrimeExpWeight (5/4) n) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      unfold zetaPrimeExpWeight
      linarith only [hk]
    _ = _ := by rw [he]; ring

theorem norm_amplitude_le {u : ℝ} (hu : 0<=u) (N n : ℕ) :
    ‖amplitude u N n‖ <=
      u*(4*u/3)^N*zetaMoebiusLogMajorant n*zetaPrimeExpWeight (3/4) n := by
  have hc := norm_residualCoefficient_le (intermediatePrimes u N)
    (SquarefreeVaughanLogSource.length_pos u N) N n
  have hk : ‖zetaPrimeLogKernel N (3/2) n‖ <=
      (4/3 : ℝ)^N*zetaPrimeExpWeight (3/4) n := by
    convert norm_zetaPrimeLogKernel_le N (3/2) n
      (by norm_num : (0 : ℝ)<3/4) using 1
    norm_num
  unfold amplitude
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu]
  calc
    _ <= u^(N+1)*zetaMoebiusLogMajorant n*
        ((4/3 : ℝ)^N*zetaPrimeExpWeight (3/4) n) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hc (pow_nonneg hu _)) hk
        (norm_nonneg _) (mul_nonneg (pow_nonneg hu _) (zetaMoebiusLogMajorant_nonneg n))
    _ = _ := by rw [pow_succ, show 4*u/3=(4/3)*u by ring, mul_pow]; ring

/-- A geometric bound for the FULL literal core's squared coefficient mass.
No count, geometry, phase or allocation hypothesis has been added. -/
theorem coefficientEnergy_bound {u : ℝ} (hu : 0<=u) (N K : ℕ) :
    coefficientEnergy u N K <= energyConstant*u^2*(4*u/3)^(2*N) := by
  unfold coefficientEnergy
  calc
    _ <= ∑ n ∈ coreBand u N K,
        (u*(4*u/3)^N)^2*((zetaMoebiusLogMajorant n)^2*zetaPrimeExpWeight (3/2) n) := by
      apply Finset.sum_le_sum
      intro n _
      have h := pow_le_pow_left₀ (norm_nonneg (amplitude u N n)) (norm_amplitude_le hu N n) 2
      have he : (zetaPrimeExpWeight (3/4) n)^2=zetaPrimeExpWeight (3/2) n := by
        unfold zetaPrimeExpWeight
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      simpa only [mul_pow, mul_assoc, he] using h
    _ <= (u*(4*u/3)^N)^2*
        (32*divisorSquareDirichletMass (5/4)) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      calc
        _ <= ∑ n ∈ coreBand u N K,
            32*(n.divisors.card : ℝ)^2*(n : ℝ)^(-(5/4 : ℝ)) :=
          Finset.sum_le_sum (fun n _ => majorant_square_bound n)
        _ <= _ := by
          simp only [mul_assoc, ← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left
            ((summable_card_divisors_sq_mul_rpow_neg (by norm_num : (1 : ℝ)<5/4)).sum_le_tsum _
              (fun n _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
            (by norm_num)
    _ = _ := by rw [energyConstant, mul_pow, ← pow_mul]; ring

/-- A uniform original-radius rate, strictly below one. -/
theorem coefficientEnergy_uniform {u : ℝ} (hu : 0<=u) (hU : u<=radiusCeiling) (N K : ℕ) :
    coefficientEnergy u N K <= energyConstant*radiusCeiling^2*(10001/15000 : ℝ)^(2*N) := by
  have hp : 4*u/3 <= (10001/15000 : ℝ) := by
    norm_num [radiusCeiling] at hU
    linarith only [hU]
  exact (coefficientEnergy_bound hu N K).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu hU 2) energyConstant_nonneg)
      (pow_le_pow_left₀ (by positivity : 0<=4*u/3) hp (2*N)) (by positivity)
      (mul_nonneg energyConstant_nonneg (sq_nonneg _)))

theorem coefficientEnergy_tendsto {u : ℝ} (hu : 0<=u) (hU : u<=radiusCeiling)
    (counts : ℕ → ℕ) :
    Tendsto (fun N => coefficientEnergy u N (counts N)) atTop (𝓝 0) := by
  have hrate : Tendsto (fun N : ℕ => (10001/15000 : ℝ)^(2*N)) atTop (𝓝 0) := by
    simpa only [pow_mul] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ)<=(10001/15000)^2)
      (by norm_num : (10001/15000 : ℝ)^2<1)
  apply squeeze_zero (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (fun N => coefficientEnergy_uniform hu hU N (counts N))
  simpa only [mul_zero] using hrate.const_mul (energyConstant*radiusCeiling^2)

/-- A finite sum on the original logarithmic frequencies. -/
def signal (S : Finset ℕ) (c : ℕ → ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ S, c n*character n y

/-- Actual continuous height average, not an independent-prime phase model. -/
def heightMean (S : Finset ℕ) (c : ℕ → ℂ) (T : ℝ) : ℝ :=
  T⁻¹*(∫ y in (0 : ℝ)..T, ‖signal S c y‖^2)

/-- The exact averaged character of a pair of original integer labels. -/
def pairMean (m n : ℕ) (T : ℝ) : ℂ :=
  (T : ℂ)⁻¹*(∫ y in (0 : ℝ)..T,
    exp ((-I*(Real.log m-Real.log n : ℝ))*y))

/-- The diagonal is retained exactly once. -/
theorem pairMean_self (m : ℕ) {T : ℝ} (hT : T≠0) : pairMean m m T=1 := by
  simp [pairMean, hT]

theorem log_difference_ne {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m≠n) :
    Real.log m-Real.log n≠0 := by
  intro h
  have he : Real.log (m : ℝ)=Real.log n := sub_eq_zero.mp h
  have hmR : (m : ℝ) ∈ Set.Ioi 0 := by
    simp only [Set.mem_Ioi]
    exact_mod_cast hm
  have hnR : (n : ℝ) ∈ Set.Ioi 0 := by
    simp only [Set.mem_Ioi]
    exact_mod_cast hn
  have hc := Real.log_injOn_pos hmR hnR he
  exact hmn (by exact_mod_cast hc)

/-- Only distinct-label cross terms are estimated. The selected signed sum
is squared BEFORE the frequency calculation. -/
theorem norm_pairMean_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m≠n)
    {T : ℝ} (hT : 0<T) :
    ‖pairMean m n T‖ <= 2/(T*|Real.log m-Real.log n|) := by
  have hd := log_difference_ne hm hn hmn
  have hc : (-I*((Real.log m-Real.log n : ℝ) : ℂ))≠0 := by
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by exact_mod_cast hd)
  rw [pairMean, integral_exp_mul_complex hc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, norm_mul, norm_inv, norm_div,
    Complex.norm_real, Real.norm_of_nonneg hT.le, norm_neg, Complex.norm_I, one_mul]
  rw [Real.norm_eq_abs]
  have he : ‖exp ((-I*((Real.log m-Real.log n : ℝ) : ℂ))*(T : ℂ))-1‖<=2 := by
    apply (norm_sub_le _ _).trans_eq
    simp only [Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, mul_zero,
      sub_zero, Real.exp_zero, norm_one]
    norm_num
  have hdi : 0 < |Real.log m-Real.log n| := abs_pos.mpr hd
  calc
    _ <= T⁻¹*(2/|Real.log m-Real.log n|) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he hdi.le) (inv_nonneg.mpr hT.le)
    _ = _ := by field_simp

theorem signal_square_eq (S : Finset ℕ) (c : ℕ → ℂ) (y : ℝ) :
    ((‖signal S c y‖^2 : ℝ) : ℂ) =
      ∑ m ∈ S, ∑ n ∈ S, c m*conj (c n)*
        exp ((-I*(Real.log m-Real.log n : ℝ))*y) := by
  simp only [Complex.ofReal_pow]
  rw [← Complex.mul_conj', signal]
  simp only [map_sum, map_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [← character_mul_conj]
  ring

/-- Exact common-height orthogonality bookkeeping for the WHOLE finite sum. -/
theorem heightMean_eq_pairs (S : Finset ℕ) (c : ℕ → ℂ) (T : ℝ) :
    (heightMean S c T : ℂ) = ∑ m ∈ S, ∑ n ∈ S, c m*conj (c n)*pairMean m n T := by
  unfold heightMean
  push_cast
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [signal_square_eq]
  rw [intervalIntegral.integral_finsetSum (fun m _ =>
    (show Continuous (fun x : ℝ => ∑ n ∈ S,
      c m*conj (c n)*exp ((-I*(Real.log m-Real.log n : ℝ))*x)) by fun_prop).intervalIntegrable 0 T)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [intervalIntegral.integral_finsetSum (fun n _ =>
    (show Continuous (fun x : ℝ =>
      c m*conj (c n)*exp ((-I*(Real.log m-Real.log n : ℝ))*x)) by fun_prop).intervalIntegrable 0 T)]
  simp only [Finset.mul_sum, intervalIntegral.integral_const_mul, pairMean]
  exact Finset.sum_congr rfl (fun n _ => by ring)

/-- The finite-window off-diagonal cost, with every distinct-label pair
and actual logarithmic spacing retained. It is not a paid pointwise cost. -/
def crossingCost (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ m ∈ S, ∑ n ∈ S.erase m, 2*‖c m‖*‖c n‖/|Real.log m-Real.log n|

theorem crossingCost_nonneg (S : Finset ℕ) (c : ℕ → ℂ) : 0<=crossingCost S c := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))

/-- Exact diagonal/crossing split, after joining all signed coefficients. -/
theorem heightMean_eq_energy_add_crossing (S : Finset ℕ) (c : ℕ → ℂ)
    {T : ℝ} (hT : T≠0) :
    (heightMean S c T : ℂ) = ((∑ m ∈ S, ‖c m‖^2 : ℝ) : ℂ)+
      ∑ m ∈ S, ∑ n ∈ S.erase m, c m*conj (c n)*pairMean m n T := by
  rw [heightMean_eq_pairs]
  push_cast
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.add_sum_erase S (fun n => c m*conj (c n)*pairMean m n T) hm,
    pairMean_self m hT, mul_one, Complex.mul_conj']

/-- An unconditional finite-window bound on the original common phase.
Its window cost is explicit and is NOT assumed small at a fixed height. -/
theorem heightMean_error_bound (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) {T : ℝ} (hT : 0<T) :
    |heightMean S c T-∑ n ∈ S, ‖c n‖^2| <= crossingCost S c/T := by
  have he := heightMean_eq_energy_add_crossing S c hT.ne'
  have hn : ‖((heightMean S c T-∑ n ∈ S, ‖c n‖^2 : ℝ) : ℂ)‖ <= crossingCost S c/T := by
    rw [Complex.ofReal_sub, he, add_sub_cancel_left]
    calc
      _ <= ∑ m ∈ S, ∑ n ∈ S.erase m, ‖c m*conj (c n)*pairMean m n T‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
      _ <= ∑ m ∈ S, ∑ n ∈ S.erase m,
          2*‖c m‖*‖c n‖/|Real.log m-Real.log n|/T := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro n hn
        have hb := norm_pairMean_le (hS m hm) (hS n (Finset.mem_erase.mp hn).2)
          (Ne.symm (Finset.mem_erase.mp hn).1) hT
        rw [norm_mul, norm_mul, norm_conj]
        exact (mul_le_mul_of_nonneg_left hb (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq
          (by ring)
      _ = _ := by simp only [crossingCost, Finset.sum_div]
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hn

theorem heightMean_upper (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) {T : ℝ} (hT : 0<T) :
    heightMean S c T <= (∑ n ∈ S, ‖c n‖^2)+crossingCost S c/T := by
  have hb := (le_abs_self _).trans (heightMean_error_bound S c hS hT)
  linarith only [hb]

/-- The height limit comes FIRST, at each fixed original order. -/
theorem heightMean_tendsto (S : Finset ℕ) (c : ℕ → ℂ) (hS : ∀ n ∈ S, 0 < n) :
    Tendsto (heightMean S c) atTop (𝓝 (∑ n ∈ S, ‖c n‖^2)) := by
  have he : Tendsto (fun T : ℝ => heightMean S c T-∑ n ∈ S, ‖c n‖^2) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      simpa only [Real.norm_eq_abs, id_eq] using heightMean_error_bound S c hS hT)
      (tendsto_id.const_div_atTop (crossingCost S c))
  have h := he.add_const (∑ n ∈ S, ‖c n‖^2)
  simp only [zero_add] at h
  exact h.congr (fun T => by ring)

theorem core_label_pos {u : ℝ} {N K n : ℕ} (hn : n ∈ coreBand u N K) : 0 < n := by
  have hc := ZetaRieszJointPrimeEnergy.core_count hn
  by_contra h
  have he : n=0 := by omega
  simp only [he, Nat.primeFactors_zero, Finset.card_empty] at hc
  omega

/-- Exact mean square of the ACTUAL whole source-normalized literal core. -/
theorem core_heightMean_tendsto (u : ℝ) (N K : ℕ) :
    Tendsto (fun T : ℝ => T⁻¹*(∫ y in (0 : ℝ)..T,
      ‖(u : ℂ)^(N+1)*coreResponse u y N K‖^2)) atTop (𝓝 (coefficientEnergy u N K)) := by
  have h := heightMean_tendsto (coreBand u N K) (amplitude u N) (fun _ hn => core_label_pos hn)
  change Tendsto (fun T => T⁻¹*(∫ y in (0 : ℝ)..T,
    ‖signal (coreBand u N K) (amplitude u N) y‖^2)) atTop (𝓝 (coefficientEnergy u N K)) at h
  simpa only [signal, scaled_core_eq_character_sum] using h

/-- A concrete signed-core estimate, with the exact finite-window cost retained. -/
theorem core_heightMean_bound {u : ℝ} (hu : 0<=u) (hU : u<=radiusCeiling)
    (N K : ℕ) {T : ℝ} (hT : 0<T) :
    T⁻¹*(∫ y in (0 : ℝ)..T, ‖(u : ℂ)^(N+1)*coreResponse u y N K‖^2) <=
      energyConstant*radiusCeiling^2*(10001/15000 : ℝ)^(2*N)+
        crossingCost (coreBand u N K) (amplitude u N)/T := by
  have hb := heightMean_upper (coreBand u N K) (amplitude u N) (fun _ hn => core_label_pos hn) hT
  change heightMean _ _ T <= coefficientEnergy u N K+_ at hb
  have hc : T⁻¹*(∫ y in (0 : ℝ)..T, ‖(u : ℂ)^(N+1)*coreResponse u y N K‖^2) <=
      coefficientEnergy u N K+crossingCost (coreBand u N K) (amplitude u N)/T := by
    simpa only [heightMean, signal, scaled_core_eq_character_sum] using hb
  exact hc.trans
    (add_le_add (coefficientEnergy_uniform hu hU N K) le_rfl)

/-- Precisely the remaining literal multiplier in joinedPhysical. -/
def joinedMultiplier (u : ℝ) (N K n : ℕ) : ℝ :=
  if n ∈ ZetaRieszGammaJoint.saturatedBand u N K then 1
  else 1-ZetaRieszLeastBoundary.selection u N K n

theorem joinedMultiplier_bounds (u : ℝ) (N K n : ℕ) :
    0<=joinedMultiplier u N K n ∧ joinedMultiplier u N K n<=1 := by
  unfold joinedMultiplier
  split_ifs
  · norm_num
  · have h := ZetaRieszLeastBoundary.selection_bounds u N K n
    constructor <;> linarith only [h.1,h.2]

/-- The full native joined coefficient, including the unmatched selection complement. -/
def joinedAmplitude (u : ℝ) (N K n : ℕ) : ℂ :=
  (joinedMultiplier u N K n : ℂ)*amplitude u N n

theorem norm_joinedAmplitude_le (u : ℝ) (N K n : ℕ) :
    ‖joinedAmplitude u N K n‖ <= ‖amplitude u N n‖ := by
  rw [joinedAmplitude, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (joinedMultiplier_bounds u N K n).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (joinedMultiplier_bounds u N K n).2

/-- Exact evaluation of the EXISTING joinedPhysical carrier on its integer
frequencies, including the unmatched signed complement. -/
theorem scaled_joined_eq_signal (u y : ℝ) (N K : ℕ) :
    (u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K =
      signal (coreBand u N K) (joinedAmplitude u N K) y := by
  have hD : ZetaRieszGammaJoint.saturatedBand u N K ⊆ coreBand u N K :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  unfold ZetaRieszGammaJoint.joinedPhysical signal
  rw [← Finset.sum_sdiff hD]
  simp only [mul_add, Finset.mul_sum]
  conv_rhs => rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    rw [ZetaRieszGammaJoint.translatedAtom_eq_original hn y,
      kernel_eq_real_mul_character]
    simp only [joinedAmplitude, joinedMultiplier, if_pos hn, Complex.ofReal_one,
      one_mul, amplitude]
    ring
  · apply Finset.sum_congr rfl
    intro n hn
    rw [kernel_eq_real_mul_character]
    simp only [joinedAmplitude, joinedMultiplier, if_neg (Finset.mem_sdiff.mp hn).2, amplitude]
    ring

/-- Squared coefficient mass of the existing joinedPhysical carrier. -/
def joinedCoefficientEnergy (u : ℝ) (N K : ℕ) : ℝ :=
  ∑ n ∈ coreBand u N K, ‖joinedAmplitude u N K n‖^2

theorem joinedCoefficientEnergy_le (u : ℝ) (N K : ℕ) :
    joinedCoefficientEnergy u N K <= coefficientEnergy u N K := by
  exact Finset.sum_le_sum (fun n _ => pow_le_pow_left₀
    (norm_nonneg _) (norm_joinedAmplitude_le u N K n) 2)

theorem joinedCoefficientEnergy_uniform {u : ℝ} (hu : 0<=u)
    (hU : u<=radiusCeiling) (N K : ℕ) :
    joinedCoefficientEnergy u N K <=
      energyConstant*radiusCeiling^2*(10001/15000 : ℝ)^(2*N) :=
  (joinedCoefficientEnergy_le u N K).trans (coefficientEnergy_uniform hu hU N K)

theorem joinedCoefficientEnergy_tendsto {u : ℝ} (hu : 0<=u)
    (hU : u<=radiusCeiling) (counts : ℕ → ℕ) :
    Tendsto (fun N => joinedCoefficientEnergy u N (counts N)) atTop (𝓝 0) := by
  exact squeeze_zero (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (fun N => joinedCoefficientEnergy_le u N (counts N)) (coefficientEnergy_tendsto hu hU counts)

/-- Entire native carrier, with no exposed-zero or multiplicity premise. -/
theorem joined_heightMean_tendsto (u : ℝ) (N K : ℕ) :
    Tendsto (fun T : ℝ => T⁻¹*(∫ y in (0 : ℝ)..T,
      ‖(u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K‖^2)) atTop
        (𝓝 (joinedCoefficientEnergy u N K)) := by
  have h := heightMean_tendsto (coreBand u N K) (joinedAmplitude u N K) (fun _ hn => core_label_pos hn)
  change Tendsto (fun T => T⁻¹*(∫ y in (0 : ℝ)..T,
    ‖signal (coreBand u N K) (joinedAmplitude u N K) y‖^2)) atTop (𝓝 (joinedCoefficientEnergy u N K)) at h
  simpa only [scaled_joined_eq_signal] using h

/-- Concrete common-height mean-square saving for the SAME native carrier.
The finite-window cost remains explicit; no fixed-height bound is inferred. -/
theorem joined_heightMean_bound {u : ℝ} (hu : 0<=u) (hU : u<=radiusCeiling)
    (N K : ℕ) {T : ℝ} (hT : 0<T) :
    T⁻¹*(∫ y in (0 : ℝ)..T, ‖(u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K‖^2) <=
      energyConstant*radiusCeiling^2*(10001/15000 : ℝ)^(2*N)+
        crossingCost (coreBand u N K) (joinedAmplitude u N K)/T := by
  have hb := heightMean_upper (coreBand u N K) (joinedAmplitude u N K)
    (fun _ hn => core_label_pos hn) hT
  change heightMean _ _ T <= joinedCoefficientEnergy u N K+_ at hb
  have hc : T⁻¹*(∫ y in (0 : ℝ)..T,
      ‖(u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K‖^2) <=
      joinedCoefficientEnergy u N K+crossingCost (coreBand u N K) (joinedAmplitude u N K)/T := by
    simpa only [heightMean, scaled_joined_eq_signal] using hb
  exact hc.trans (add_le_add (joinedCoefficientEnergy_uniform hu hU N K) le_rfl)

/-- Translation keeps the SAME single common height phase. -/
def rotatedCoefficients (c : ℕ → ℂ) (H : ℝ) (n : ℕ) : ℂ := c n*character n H

theorem norm_rotatedCoefficients (c : ℕ → ℂ) (H : ℝ) (n : ℕ) :
    ‖rotatedCoefficients c H n‖=‖c n‖ := by
  simp only [rotatedCoefficients, norm_mul, character_norm, mul_one]

theorem signal_rotate (S : Finset ℕ) (c : ℕ → ℂ) (H y : ℝ) :
    signal S (rotatedCoefficients c H) y=signal S c (H+y) := by
  simp only [signal, rotatedCoefficients, character_add, mul_assoc]

theorem crossingCost_rotate (S : Finset ℕ) (c : ℕ → ℂ) (H : ℝ) :
    crossingCost S (rotatedCoefficients c H)=crossingCost S c := by
  simp only [crossingCost, norm_rotatedCoefficients]

/-- A quantitative native mean-square bound in EVERY translated height window.
It still averages an interval; it does not bound its chosen starting ordinate. -/
theorem joined_translated_heightMean_bound {u : ℝ} (hu : 0<=u) (hU : u<=radiusCeiling)
    (N K : ℕ) (H : ℝ) {T : ℝ} (hT : 0<T) :
    T⁻¹*(∫ y in (0 : ℝ)..T,
      ‖(u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u (H+y) N K‖^2) <=
      energyConstant*radiusCeiling^2*(10001/15000 : ℝ)^(2*N)+
        crossingCost (coreBand u N K) (joinedAmplitude u N K)/T := by
  have hb := heightMean_upper (coreBand u N K)
    (rotatedCoefficients (joinedAmplitude u N K) H) (fun _ hn => core_label_pos hn) hT
  simp only [heightMean, norm_rotatedCoefficients, crossingCost_rotate, signal_rotate,
    ← scaled_joined_eq_signal] at hb
  exact hb.trans (add_le_add (joinedCoefficientEnergy_uniform hu hU N K) le_rfl)

/-- No simultaneous or reversed order/height limit is asserted. The native
long-height mean square, taken first, has a uniform cofinal geometric saving. -/
theorem joined_mean_square_cofinal {u : ℝ} (hu : 0<=u) (hU : u<=radiusCeiling)
    (counts : ℕ → ℕ) :
    ∃ E : ℕ → ℝ,
      (∀ N, Tendsto (fun T : ℝ => T⁻¹*(∫ y in (0 : ℝ)..T,
        ‖(u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (counts N)‖^2))
          atTop (𝓝 (E N))) ∧
      (∀ N, 0<=E N ∧ E N<=energyConstant*radiusCeiling^2*(10001/15000 : ℝ)^(2*N)) ∧
      Tendsto E atTop (𝓝 0) := by
  refine ⟨fun N => joinedCoefficientEnergy u N (counts N),
    fun N => joined_heightMean_tendsto u N (counts N), ?_,
    joinedCoefficientEnergy_tendsto hu hU counts⟩
  intro N
  exact ⟨Finset.sum_nonneg (fun _ _ => sq_nonneg _), joinedCoefficientEnergy_uniform hu hU N (counts N)⟩

end RiemannGaussian.ZetaRieszCeilingPhaseAverage
end
