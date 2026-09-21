/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPairDiscrepancy

/-!
# A quantitative go/no-go test, with the arithmetic input explicit

The hypothesis is a fixed 1/1000 power saving for the literal masked signed
prime-pair discrepancy on each unit logarithmic cell. The factorial kernel
is normalized by an explicit positive cell envelope, not discarded.
The conclusion is an eventual independent floor for the original carrier.
No theorem in this file proves the Type-II hypothesis.
-/

namespace RiemannGaussian.ZetaRieszTypeII
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszDominantAllocation ZetaRieszJointAllocation ZetaRieszPrimeCountFrequency

/-- The exact product localization e^k <= n < e^(k+1), inside all old masks. -/
def cellBand (u : ℝ) (N K k : ℕ) : Finset ℕ :=
  (narrowBand u N K).filter (fun n => ⌊Real.log n⌋₊ = k)

/-- A positive envelope for the original factorial kernel on one log cell. -/
def cellScale (N k : ℕ) : ℝ :=
  (k + 1 : ℝ) ^ N / (N.factorial : ℝ) * Real.exp (-(3 / 2 : ℝ) * k)

/-- The cell normalization is never singular, including order zero. -/
theorem cellScale_pos (N k : ℕ) : 0 < cellScale N k := by
  unfold cellScale
  positivity

/-- The literal factorial kernel divided by its explicit cell scale.
In particular its full phase n^(-iy) remains inside the arithmetic sum. -/
def cellKernel (N k : ℕ) (y : ℝ) (n : ℕ) : ℂ :=
  zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n / (cellScale N k : ℂ)

/-- Restoring the scale recovers the exact original kernel, not an approximation. -/
theorem cellScale_mul_kernel (N k : ℕ) (y : ℝ) (n : ℕ) :
    (cellScale N k : ℂ) * cellKernel N k y n =
      zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n := by
  have h : (cellScale N k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (cellScale_pos N k).ne'
  rw [cellKernel, mul_div_cancel₀ _ h]

/-- The normalization leaves a bounded weight on its cell. This does not
bound the signed discrepancy multiplying that weight. -/
theorem norm_cellKernel_le_one {N k n : ℕ} (y : ℝ)
    (hk : ⌊Real.log n⌋₊ = k) : ‖cellKernel N k y n‖ ≤ 1 := by
  have hlo : (k : ℝ) ≤ Real.log n := by
    rw [← hk]; exact Nat.floor_le (Real.log_natCast_nonneg n)
  have hhi : Real.log n ≤ (k + 1 : ℝ) := by
    rw [← hk]; exact (Nat.lt_floor_add_one (Real.log n)).le
  rw [cellKernel, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (cellScale_pos N k).le, div_le_one (cellScale_pos N k),
    norm_zetaPrimeLogKernel]
  have hsre : (3 / 2 + Complex.I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
  rw [hsre]
  unfold cellScale zetaPrimeExpWeight
  apply mul_le_mul
  · exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (Real.log_natCast_nonneg n) hhi N) (by positivity)
  · apply Real.exp_le_exp.mpr
    linarith
  · positivity
  · positivity

/-- The single literal localized trilinear form required by the test. -/
def localizedTypeII (u y : ℝ) (N K k : ℕ) : ℂ :=
  pairForm u N (cellBand u N K k) (cellKernel N k y)

/-- Every cell retains exactly the same coefficients as the actual carrier. -/
theorem localizedTypeII_eq_sum (u y : ℝ) (N K k : ℕ) :
    localizedTypeII u y N K k =
      ∑ n ∈ cellBand u N K k,
        residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n * cellKernel N k y n := by
  exact pairForm_eq_sum u N _ _
    (fun _ hn => narrowBand_prime_count (Finset.mem_filter.mp hn).1)

/-- Only linearly many unit log cells meet the requested narrow window. -/
theorem cell_index_lt {u : ℝ} {N K n : ℕ} (hn : n ∈ narrowBand u N K) :
    ⌊Real.log n⌋₊ < 3 * N + 1 := by
  apply (Nat.floor_lt (Real.log_natCast_nonneg n)).mpr
  have hh := (Finset.mem_filter.mp hn).2.2
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Exact reconstruction from localized forms. The norms are taken only
after each full signed cell has been assembled. -/
theorem narrowResponse_eq_cells (u y : ℝ) (N K : ℕ) :
    narrowResponse u y N K = ∑ k ∈ Finset.range (3 * N + 1),
      (cellScale N k : ℂ) * localizedTypeII u y N K k := by
  have h := Finset.sum_fiberwise_of_maps_to
    (s := narrowBand u N K) (t := Finset.range (3 * N + 1))
    (fun n hn => Finset.mem_range.mpr (cell_index_lt hn))
    (fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length u N) N n *
        zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n)
  change (∑ k ∈ Finset.range (3 * N + 1), ∑ n ∈ cellBand u N K k, _) =
    narrowResponse u y N K at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro k _
  rw [localizedTypeII_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_left_comm, cellScale_mul_kernel]

/-- The factorial envelope turns a length-scale 1/1000 saving into a
strict geometric improvement. No Stirling asymptotic or numerical oracle is used. -/
theorem cellScale_power_saving (N k : ℕ) :
    cellScale N k * Real.exp ((999 / 1000 : ℝ) * k) ≤
      Real.exp (501 / 1000 : ℝ) * (1000 / 501 : ℝ) ^ N := by
  have h := logMoment_exp_envelope N (by positivity : (0 : ℝ) ≤ (k + 1 : ℝ))
    (by norm_num : (0 : ℝ) < 501 / 1000) (501 / 1000 : ℝ)
  norm_num only [sub_self, neg_zero, zero_mul, Real.exp_zero, mul_one] at h
  calc
    _ = Real.exp (501 / 1000 : ℝ) *
        ((k + 1 : ℝ) ^ N / (N.factorial : ℝ) *
          Real.exp (-(501 / 1000 : ℝ) * (k + 1))) := by
      unfold cellScale
      rw [mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (501 / 1000 : ℝ) * ((1000 / 501 : ℝ) ^ N) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-- The fixed normalized ratio is strictly below one even at u=0.5001. -/
theorem normalized_ratio :
    radiusCeiling * (1000 / 501 : ℝ) = 1667 / 1670 ∧
      (0 : ℝ) < 1667 / 1670 ∧ (1667 / 1670 : ℝ) < 1 := by
  norm_num [radiusCeiling]

/-- The precise unproved arithmetic input. C and A are fixed as j grows;
the estimate applies to the actual coefficients, all log cells and original
count schedule. With x=e^k the right side is C(N+1)^A x^(1-1/1000). -/
def LocalizedTypeIIBound (u y : ℝ) : Prop :=
  ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ᶠ j in atTop,
    ∀ k < 3 * dyadicMomentOrder j + 1,
      ‖localizedTypeII u y (dyadicMomentOrder j) (dyadicPrimeCount j) k‖ ≤
        C * (dyadicMomentOrder j + 1 : ℝ) ^ A * Real.exp ((999 / 1000 : ℝ) * k)

/-- The numerical transport from one actual localized arithmetic estimate.
All constants and the strict geometric ratio are explicit; the only unproved
input is `hII`, an estimate of the literal form above. -/
theorem norm_narrow_of_typeII (u y : ℝ) (N K A : ℕ) {C : ℝ}
    (hC : 0 ≤ C) (hu : 0 ≤ u) (huU : u ≤ radiusCeiling)
    (hII : ∀ k < 3 * N + 1, ‖localizedTypeII u y N K k‖ ≤
      C * (N + 1 : ℝ) ^ A * Real.exp ((999 / 1000 : ℝ) * k)) :
    ‖(u : ℂ) ^ (N + 1) * narrowResponse u y N K‖ ≤
      (3 * C * radiusCeiling * Real.exp (501 / 1000 : ℝ)) *
        (N + 1 : ℝ) ^ (A + 1) * (1667 / 1670 : ℝ) ^ N := by
  let B := C * (N + 1 : ℝ) ^ A * Real.exp (501 / 1000 : ℝ) * (1000 / 501 : ℝ) ^ N
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hU0 : 0 ≤ radiusCeiling := by norm_num [radiusCeiling]
  have hsum : ‖narrowResponse u y N K‖ ≤ (3 * N + 1 : ℝ) * B := by
    rw [narrowResponse_eq_cells]
    calc
      _ ≤ ∑ k ∈ Finset.range (3 * N + 1),
          ‖(cellScale N k : ℂ) * localizedTypeII u y N K k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range (3 * N + 1), B := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (cellScale_pos N k).le]
        calc
          _ ≤ cellScale N k * (C * (N + 1 : ℝ) ^ A *
              Real.exp ((999 / 1000 : ℝ) * k)) :=
            mul_le_mul_of_nonneg_left (hII k (Finset.mem_range.mp hk)) (cellScale_pos N k).le
          _ = (C * (N + 1 : ℝ) ^ A) *
              (cellScale N k * Real.exp ((999 / 1000 : ℝ) * k)) := by ring
          _ ≤ B := by
            dsimp [B]
            have h := mul_le_mul_of_nonneg_left (cellScale_power_saving N k)
              (by positivity : 0 ≤ C * (N + 1 : ℝ) ^ A)
            simpa only [mul_assoc] using h
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu]
  calc
    _ ≤ radiusCeiling ^ (N + 1) * ((3 * N + 1 : ℝ) * B) :=
      mul_le_mul (pow_le_pow_left₀ hu huU _) hsum (norm_nonneg _) (pow_nonneg hU0 _)
    _ ≤ radiusCeiling ^ (N + 1) * ((3 * (N + 1) : ℝ) * B) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by linarith : (3 * N + 1 : ℝ) ≤ 3 * (N + 1)) hB)
        (pow_nonneg hU0 _)
    _ = _ := by
      rw [← normalized_ratio.1, mul_pow, pow_succ radiusCeiling, pow_succ (N + 1 : ℝ)]
      dsimp [B]
      ring

/-- Conditional decay of the narrowed carrier. The Type-II hypothesis
remains visible and is not discharged by this transport. -/
theorem tendsto_narrow_of_typeII {u y : ℝ} (hu : 0 ≤ u)
    (huU : u ≤ radiusCeiling) (hII : LocalizedTypeIIBound u y) :
    Tendsto (narrowRemainder u y) atTop (𝓝 0) := by
  obtain ⟨C, A, hC, hII⟩ := hII
  have ht := ((ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric (A + 1)
    normalized_ratio.2.1 normalized_ratio.2.2).const_mul
      (3 * C * radiusCeiling * Real.exp (501 / 1000 : ℝ))).comp tendsto_dyadicMomentOrder
  simp only [Function.comp_def, mul_zero] at ht
  apply squeeze_zero_norm' (a := fun j =>
    (3 * C * radiusCeiling * Real.exp (501 / 1000 : ℝ)) *
      ((dyadicMomentOrder j + 1 : ℝ) ^ (A + 1) *
        (1667 / 1670 : ℝ) ^ dyadicMomentOrder j)) ?_ ht
  filter_upwards [hII] with j hj
  simpa only [narrowRemainder, mul_assoc] using
    norm_narrow_of_typeII u y (dyadicMomentOrder j) (dyadicPrimeCount j) A hC hu huU hj

/-- The explicit localized estimate controls the entire original surviving
carrier, because the only localization error was independently paid. -/
theorem tendsto_nondominant_of_typeII {u y : ℝ} (hu : 0 ≤ u)
    (huU : u ≤ radiusCeiling) (hII : LocalizedTypeIIBound u y) :
    Tendsto (nondominantRemainder u y) atTop (𝓝 0) := by
  have ht := (tendsto_nondominant_sub_narrow hu huU y).add
    (tendsto_narrow_of_typeII hu huU hII)
  simpa only [sub_add_cancel, add_zero] using ht

/-- The requested eventual signed floor for the actual carrier follows
from precisely the named, unproved Type-II estimate. -/
theorem eventually_signed_floor_of_typeII {u y : ℝ} (hu : 0 ≤ u)
    (huU : u ≤ radiusCeiling) (hII : LocalizedTypeIIBound u y) :
    ∀ᶠ j in atTop, -(3 / 40 : ℝ) ≤ (nondominantRemainder u y j).re := by
  have ht := Complex.continuous_re.tendsto 0 |>.comp
    (tendsto_nondominant_of_typeII hu huU hII)
  have he := ht.eventually (eventually_gt_nhds (by norm_num : -(3 / 40 : ℝ) < (0 : ℂ).re))
  exact he.mono (fun _ h => h.le)

/-- A simple exposed zero in the test interval contradicts the exact
Type-II hypothesis. This is a conditional exclusion, not a proved zero-free region. -/
theorem not_typeII_of_simple_exposed_zero (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huU : 3 / 2 - rho.1.re ≤ radiusCeiling)
    (hsimple : analyticZetaZeroMultiplicity rho = 1) :
    ¬LocalizedTypeIIBound (3 / 2 - rho.1.re) rho.1.im := by
  intro hII
  have hu : 0 ≤ (3 / 2 : ℝ) - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hlo := eventually_signed_floor_of_typeII hu huU hII
  have hhi := eventually_nondominant_re_lt_neg_three_fortieths rho hrho hexposed
    (huU.trans_lt radiusCeiling_lt_source_ceiling) hsimple
  obtain ⟨j, hjlo, hjhi⟩ := (hlo.and hhi).exists
  exact (not_lt_of_ge hjlo) hjhi

end
end RiemannGaussian.ZetaRieszTypeII
