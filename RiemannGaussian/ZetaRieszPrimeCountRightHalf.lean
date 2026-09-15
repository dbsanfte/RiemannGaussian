/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeCountMass
import RiemannGaussian.ZetaRieszGeneralCofactorTilt

/-!
# Full prime-count deletion throughout the right half of the strip

Trade the moment order against the prime-count threshold while retaining the
complete signed integer response and its original factorial filter.
-/

namespace RiemannGaussian.ZetaRieszPrimeCountRightHalf
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeCountFrequency ZetaRieszPrimeCountMass

/-- A shorter moment schedule exchanges the size of the deleted integer
class for a larger source-radius range. -/
def rightHalfOrder (j : ℕ) : ℕ := (j + 4) * dyadicPrimeCount j

/-- These orders are cofinal, preserving every original source limit. -/
theorem tendsto_rightHalfOrder : Tendsto rightHalfOrder atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro j
  have hp := four_le_dyadicPrimeCount j
  dsimp [rightHalfOrder]
  nlinarith

/-- Every geometric rate below two is eventually paid by the complete
prime-count power on the shorter cofinal moment schedule. -/
theorem eventually_count_power_saving {A : ℝ} (hA : 0 < A) (hA2 : A < 2) :
    ∀ᶠ j : ℕ in atTop, A ^ rightHalfOrder j ≤
      (dyadicPrimeCount j : ℝ) ^ dyadicPrimeCount j := by
  have ht : Tendsto (fun j : ℕ => (A ^ 4 / 8) * (A / 2) ^ j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ A / 2)
        (by linarith : A / 2 < 1)).const_mul (A ^ 4 / 8)
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with j hj
  have he : A ^ (j + 4) / (2 : ℝ) ^ (j + 3) = (A ^ 4 / 8) * (A / 2) ^ j := by
    rw [pow_add A, pow_add (2 : ℝ), div_pow]
    norm_num
    ring
  have hb : A ^ (j + 4) ≤ (2 : ℝ) ^ (j + 3) := by
    apply (div_le_one (by positivity)).mp
    rw [he]
    exact hj.le
  have hp := pow_le_pow_left₀ (by positivity) hb (dyadicPrimeCount j)
  simpa only [← pow_mul, rightHalfOrder, dyadicPrimeCount, Nat.cast_pow,
    Nat.cast_ofNat] using hp

/-- The complete Euler-product allowance is subexponential on the
shorter schedule too; no prime-count cost is discarded. -/
theorem eventually_exp_count_le (C : ℝ) {s : ℝ} (hs : 1 < s) :
    ∀ᶠ j : ℕ in atTop, Real.exp (C * (dyadicPrimeCount j : ℝ)) ≤ s ^ rightHalfOrder j := by
  have hlog : 0 < Real.log s := Real.log_pos hs
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_ge_atTop (C / Real.log s))] with j hj
  have hC : C ≤ ((j : ℝ) + 4) * Real.log s := by
    have h := (div_le_iff₀ hlog).mp hj
    nlinarith
  have hN : (rightHalfOrder j : ℝ) = ((j : ℝ) + 4) * (dyadicPrimeCount j : ℝ) := by
    simp [rightHalfOrder]
  calc
    _ ≤ Real.exp ((rightHalfOrder j : ℝ) * Real.log s) := by
      apply Real.exp_le_exp.mpr
      rw [hN]
      exact (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _)).trans_eq (by ring)
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by linarith : 0 < s)]

/-- Every fixed source radius below one admits a genuinely summable
factorial tilt and a strict geometric margin below the count-power rate. -/
theorem exists_right_half_tilt {U : ℝ} (hU : 0 < U) (hU1 : U < 1) :
    ∃ A q : ℝ, 0 < A ∧ A < 2 ∧ 0 < q ∧ q < 1 / 2 ∧ U < q * A := by
  let A : ℝ := 1 + U
  have hA : 0 < A := by dsimp [A]; linarith
  have hUhalf : U / A < 1 / 2 := by
    apply (div_lt_iff₀ hA).mpr
    dsimp [A]
    linarith
  obtain ⟨q, hqU, hqhalf⟩ := exists_between hUhalf
  refine ⟨A, q, hA, ?_, ?_, hqhalf, ?_⟩
  · dsimp [A]; linarith
  · exact (div_pos hU hA).trans hqU
  · exact (div_lt_iff₀ hA).mp hqU

/-- A count-power saving bounds the entire original-band integer sum,
with its full Euler mass and factorial-filter cost still explicit. -/
theorem norm_many_sum_le_rate (D : Finset ℕ) (P : Polynomial ℂ) (j : ℕ) (y : ℝ)
    {L u U q A : ℝ} (hL : 0 < L) (hu : 0 ≤ u) (huU : u ≤ U)
    (hq : 0 < q) (hqhalf : q < 1 / 2) (hA : 0 < A)
    (hsave : A ^ rightHalfOrder j ≤ (dyadicPrimeCount j : ℝ) ^ dyadicPrimeCount j)
    (hD : ∀ n ∈ D, Squarefree n) (hband : D ⊆ zetaPrimeLogBand (rightHalfOrder j))
    (hK : ∀ n ∈ D, dyadicPrimeCount j ≤ n.primeFactors.card) :
    ‖(u : ℂ) ^ (rightHalfOrder j + 1) * ∑ n ∈ D,
      SquarefreeVaughanLogSource.coefficient L n *
        zetaPrimeFilterKernel P (rightHalfOrder j) (3 / 2 + Complex.I * y) n‖ ≤
      (32 * U * Real.log 2 * ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        ((rightHalfOrder j : ℝ) * (U / (q * A)) ^ rightHalfOrder j) *
          Real.exp (2 * (dyadicPrimeCount j : ℝ) * countMass (3 / 2 - q)) := by
  have hr : (1 : ℝ) ≤ dyadicPrimeCount j := by
    exact_mod_cast (show 1 ≤ dyadicPrimeCount j by have := four_le_dyadicPrimeCount j; omega)
  have hU := hu.trans huU
  have hF : 0 ≤ ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k := Finset.sum_nonneg fun _ _ => by positivity
  apply (norm_normalized_many_sum_le D P (rightHalfOrder j) y hL hu huU hq hqhalf hr hD hband hK).trans
  calc
    _ ≤ (32 * U * Real.log 2 * ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        ((rightHalfOrder j : ℝ) * (U / q) ^ rightHalfOrder j) *
          Real.exp (2 * (dyadicPrimeCount j : ℝ) * countMass (3 / 2 - q)) /
            A ^ rightHalfOrder j :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hsave
    _ = _ := by
      rw [show U / (q * A) = (U / q) / A by field_simp]
      simp only [div_pow, inv_pow, mul_comm]
      ring

/-- Every moving many-prime squarefree subband has a vanishing complete
response for all radii in any fixed [0,U] with U<1. Heights and positive
lengths may vary arbitrarily, and no zero or source assumption is used. -/
theorem tendsto_many_sum_right_half (P : Polynomial ℂ) (D : ℕ → Finset ℕ)
    (u y L : ℕ → ℝ) {U : ℝ} (hu : ∀ j, 0 ≤ u j) (huU : ∀ j, u j ≤ U)
    (hU : 0 < U) (hU1 : U < 1) (hL : ∀ j, 0 < L j)
    (hD : ∀ j, ∀ n ∈ D j, Squarefree n)
    (hband : ∀ j, D j ⊆ zetaPrimeLogBand (rightHalfOrder j))
    (hK : ∀ j, ∀ n ∈ D j, dyadicPrimeCount j ≤ n.primeFactors.card) :
    Tendsto (fun j => (u j : ℂ) ^ (rightHalfOrder j + 1) * ∑ n ∈ D j,
      SquarefreeVaughanLogSource.coefficient (L j) n *
        zetaPrimeFilterKernel P (rightHalfOrder j) (3 / 2 + Complex.I * y j) n)
      atTop (𝓝 0) := by
  obtain ⟨A, q, hA, hA2, hq, hqhalf, hrate⟩ := exists_right_half_tilt hU hU1
  let R : ℝ := U / (q * A)
  let C : ℝ := 32 * U * Real.log 2 * ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : R < 1 := (div_lt_one (by positivity)).mpr hrate
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
  let s : ℝ := (1 + R) / (2 * R)
  have hs : 1 < s := by
    apply (lt_div_iff₀ (by positivity : 0 < 2 * R)).mpr
    linarith
  have hRs : R * s = (1 + R) / 2 := by dsimp [s]; field_simp
  have hRs0 : 0 < R * s := mul_pos hR (by linarith)
  have hRs1 : R * s < 1 := by rw [hRs]; linarith
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1 hRs0 hRs1).comp
    tendsto_rightHalfOrder
  have hl : Tendsto (fun j => C * (((rightHalfOrder j : ℝ) + 1) *
      (R * s) ^ rightHalfOrder j)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, pow_one, mul_zero] using ht.const_mul C
  apply squeeze_zero_norm' (a := fun j => C * (((rightHalfOrder j : ℝ) + 1) *
    (R * s) ^ rightHalfOrder j)) _ hl
  filter_upwards [eventually_count_power_saving hA hA2,
    eventually_exp_count_le (2 * countMass (3 / 2 - q)) hs] with j hsave hj
  have hb := norm_many_sum_le_rate (D j) P j (y j) (hL j) (hu j) (huU j)
    hq hqhalf hA hsave (hD j) (hband j) (hK j)
  have he : Real.exp (2 * (dyadicPrimeCount j : ℝ) * countMass (3 / 2 - q)) ≤
      s ^ rightHalfOrder j := by simpa only [mul_assoc, mul_left_comm, mul_comm] using hj
  apply hb.trans
  calc
    _ ≤ C * ((rightHalfOrder j : ℝ) * R ^ rightHalfOrder j) * s ^ rightHalfOrder j :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = C * ((rightHalfOrder j : ℝ) * (R * s) ^ rightHalfOrder j) := by rw [mul_pow]; ring
    _ ≤ _ := by gcongr; linarith

/-- The exact many-prime squarefree selection from an arbitrary retained
integer band. No earlier arithmetic support restriction is undone. -/
def manyCountBand (D : Finset ℕ) (K : ℕ) : Finset ℕ :=
  D.filter (fun n => Squarefree n ∧ K ≤ n.primeFactors.card)

/-- The complementary smaller prime counts, with the original coefficient
still enforcing squarefreeness and the ordinary-prime deletion. -/
def fewCountBand (D : Finset ℕ) (K : ℕ) : Finset ℕ :=
  D.filter (fun n => n.primeFactors.card < K)

/-- An exact signed count partition for every retained arithmetic band.
Nonsquarefree integers contribute zero through the original coefficient. -/
theorem sum_eq_few_add_many (D : Finset ℕ) (K N : ℕ) (P : Polynomial ℂ) (L y : ℝ) :
    (∑ n ∈ D, SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
    (∑ n ∈ fewCountBand D K, SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) +
    ∑ n ∈ manyCountBand D K, SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  simp only [fewCountBand, manyCountBand, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : Squarefree n
  · by_cases hk : n.primeFactors.card < K
    · simp [hn, hk, show ¬ K ≤ n.primeFactors.card by omega]
    · simp [hn, hk, show K ≤ n.primeFactors.card by omega]
  · simp [SquarefreeVaughanLogSource.coefficient, hn]

/-- The actual high-count selection decays for every changing subband
of the original support, uniformly over bounded source radii below one. -/
theorem tendsto_manyCountBand (P : Polynomial ℂ) (D : ℕ → Finset ℕ)
    (u y L : ℕ → ℝ) {U : ℝ} (hu : ∀ j, 0 ≤ u j) (huU : ∀ j, u j ≤ U)
    (hU : 0 < U) (hU1 : U < 1) (hL : ∀ j, 0 < L j)
    (hband : ∀ j, D j ⊆ zetaPrimeLogBand (rightHalfOrder j)) :
    Tendsto (fun j => (u j : ℂ) ^ (rightHalfOrder j + 1) *
      ∑ n ∈ manyCountBand (D j) (dyadicPrimeCount j),
        SquarefreeVaughanLogSource.coefficient (L j) n *
          zetaPrimeFilterKernel P (rightHalfOrder j) (3 / 2 + Complex.I * y j) n)
      atTop (𝓝 0) := by
  exact tendsto_many_sum_right_half P (fun j => manyCountBand (D j) (dyadicPrimeCount j))
    u y L hu huU hU hU1 hL
    (fun _ _ hn => (Finset.mem_filter.mp hn).2.1)
    (fun j _ hn => hband j (Finset.mem_filter.mp hn).1)
    (fun _ _ hn => (Finset.mem_filter.mp hn).2.2)

/-- The optimized cofactor deletion retains a literal subset of the
original band, including its exceptional scalar contact. -/
theorem optimizedReducedBand_subset_original (u : ℝ) (N : ℕ) :
    ZetaRieszGeneralCofactorTilt.optimizedReducedBand u N ⊆ zetaPrimeLogBand N := by
  unfold ZetaRieszGeneralCofactorTilt.optimizedReducedBand
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.filter_subset _ _

/-- The full negative-multiplicity source now survives entirely among
smaller prime counts after the earlier optimized cofactor deletion. This
holds for every right-half zero, with no exposure or simplicity assumption.
The independent bound for this remaining signed sum is still open. -/
theorem tendsto_few_optimized_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun j => (3 / 2 - rho.1.re : ℂ) ^ (rightHalfOrder j + 1) *
      ∑ n ∈ fewCountBand
        (ZetaRieszGeneralCofactorTilt.optimizedReducedBand (3 / 2 - rho.1.re) (rightHalfOrder j))
        (dyadicPrimeCount j),
        SquarefreeVaughanLogSource.coefficient
          (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) (rightHalfOrder j)) n *
          zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) (rightHalfOrder j)
            (3 / 2 + Complex.I * rho.1.im) n)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : (0 : ℝ) < 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  have hd := tendsto_manyCountBand (zetaRightHalfPoleJetFilter rho hrho)
    (fun j => ZetaRieszGeneralCofactorTilt.optimizedReducedBand (3 / 2 - rho.1.re) (rightHalfOrder j))
    (fun _ => 3 / 2 - rho.1.re) (fun _ => rho.1.im)
    (fun j => SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) (rightHalfOrder j))
    (fun _ => hu.le) (fun _ => le_rfl) hu hu1
    (fun _ => SquarefreeVaughanLogSource.length_pos _ _)
    (fun _ => optimizedReducedBand_subset_original _ _)
  have hs := (ZetaRieszGeneralCofactorTilt.tendsto_optimized_reduced_source rho hrho).comp
    tendsto_rightHalfOrder
  have h := hs.sub hd
  simp only [Function.comp_apply, sub_zero] at h
  apply h.congr'
  filter_upwards [] with j
  have hcast : ((3 / 2 - rho.1.re : ℝ) : ℂ) = (3 / 2 - rho.1.re : ℂ) := by
    push_cast
    rfl
  rw [hcast, sum_eq_few_add_many, mul_add, add_sub_cancel_right]

end
end RiemannGaussian.ZetaRieszPrimeCountRightHalf
