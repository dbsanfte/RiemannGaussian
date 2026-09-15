/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLowHeadPrefix
import RiemannGaussian.ZetaRieszMatchedMiddle

/-!
# Completion of every moving low-head selection

The original complete complementary leg is retained while both omitted prime corrections are paid. Its source-phase hypotheses are explicitly discharged under the exposed-zero assumptions.
-/

namespace RiemannGaussian.ZetaRieszLowHeadCorrection
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaExposedPrimeMoments ZetaRieszPrimeCompletion
open ZetaRieszMatchedMiddle ZetaRieszLowHeadPrefix

/-- The original derivative head applied to a moment array, keeping its
complete complementary prime moment and selected order set. -/
def headArray (u y : ℝ) (N : ℕ) (S : Finset ℕ) (A : ℕ → ℂ) : ℂ :=
  -((N + 1 : ℕ) : ℂ) * (1 / (SquarefreeVaughanLogSource.length u N : ℂ)) *
    ∑ k ∈ S, ((k + 1 : ℕ) : ℂ) * A (k + 1) *
      ordinaryPrimeMoment (N + 1 - k) (3 / 2 + Complex.I * y)

/-- The two weighted factors retain the exact extra derivative and
source power; the complementary-order denominator is explicit. -/
theorem normalized_head_atom (u L r : ℝ) (k l : ℕ) (a b : ℂ)
    (hu : u ≠ 0) (hL : L ≠ 0) (hl : l ≠ 0) :
    (u : ℂ) ^ (k + l) * (-((r : ℂ) / L) * ((k + 1 : ℕ) : ℂ) * a * b) =
      (-(r / (u * L * l) : ℝ) : ℂ) *
        (((k + 1 : ℕ) : ℂ) * ((u : ℂ) ^ (k + 1) * a)) *
        ((l : ℂ) * ((u : ℂ) ^ l * b)) := by
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu
  have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  have hlC : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hl
  push_cast
  rw [pow_add, pow_succ]
  field_simp

/-- An entire low-order head array is bounded using one complete-leg
bound and the sum of its derivative-weighted first legs. The original
length factor is retained and no order-count loss is introduced. -/
theorem norm_headArray_le (u y : ℝ) (N : ℕ) (S : Finset ℕ) (A : ℕ → ℂ)
    (hu : 0 < u) {C : ℝ}
    (hS : ∀ k ∈ S, 8 * k ≤ N + 1)
    (hB : ∀ k ∈ S, ‖weightedComplete u y (N + 1 - k)‖ ≤ C) :
    ‖(u : ℂ) ^ (N + 1) * headArray u y N S A‖ ≤
      (2 * C / (u * SquarefreeVaughanLogSource.length u N)) *
        ∑ k ∈ S, ‖((k + 1 : ℕ) : ℂ) * ((u : ℂ) ^ (k + 1) * A (k + 1))‖ := by
  let L := SquarefreeVaughanLogSource.length u N
  have hL : 0 < L := SquarefreeVaughanLogSource.length_pos u N
  unfold headArray
  simp only [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  have hkM : k ≤ N + 1 := by have hh := hS k hk; omega
  have hl : 0 < N + 1 - k := by have hh := hS k hk; omega
  have hratio : ((N + 1 : ℕ) : ℝ) / (u * L * (N + 1 - k : ℕ)) ≤ 2 / (u * L) := by
    have hc : ((N + 1 : ℕ) : ℝ) ≤ 2 * ((N + 1 - k : ℕ) : ℝ) := by
      exact_mod_cast (by have hh := hS k hk; omega : N + 1 ≤ 2 * (N + 1 - k))
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (mul_pos hu hL).le]
  have he := normalized_head_atom u L ((N + 1 : ℕ) : ℝ) k (N + 1 - k)
    (A (k + 1)) (ordinaryPrimeMoment (N + 1 - k) (3 / 2 + Complex.I * y))
    hu.ne' hL.ne' (by omega)
  rw [show k + (N + 1 - k) = N + 1 by omega] at he
  have ht : (u : ℂ) ^ (N + 1) *
      (-((N + 1 : ℕ) : ℂ) * (1 / (L : ℂ)) *
        (((k + 1 : ℕ) : ℂ) * A (k + 1) *
          ordinaryPrimeMoment (N + 1 - k) (3 / 2 + Complex.I * y))) =
      ((-(((N + 1 : ℕ) : ℝ) / (u * L * (N + 1 - k : ℕ))) : ℝ) : ℂ) *
        (((k + 1 : ℕ) : ℂ) * ((u : ℂ) ^ (k + 1) * A (k + 1))) *
          weightedComplete u y (N + 1 - k) := by
    convert! he using 1 <;>
      simp only [weightedComplete, Complex.ofReal_natCast, Complex.ofReal_neg]
    ring
  change ‖(u : ℂ) ^ (N + 1) *
      (-((N + 1 : ℕ) : ℂ) * (1 / (L : ℂ)) *
        (((k + 1 : ℕ) : ℂ) * A (k + 1) *
          ordinaryPrimeMoment (N + 1 - k) (3 / 2 + Complex.I * y)))‖ ≤ _
  rw [ht, norm_mul, norm_mul, Complex.ofReal_neg, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (2 / (u * L)) *
        ‖((k + 1 : ℕ) : ℂ) * ((u : ℂ) ^ (k + 1) * A (k + 1))‖ * C :=
      mul_le_mul (mul_le_mul_of_nonneg_right hratio (norm_nonneg _))
        (hB k hk) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The actual small-prime completion correction in every selected low
head has a square-root numerator, with no growing order-count factor. -/
theorem norm_smallPrefix_headArray_le (u y : ℝ) (N : ℕ) (S : Finset ℕ)
    (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    {C : ℝ} (hC : 0 ≤ C) (hS : ∀ k ∈ S, 8 * k ≤ N + 1)
    (hB : ∀ k ∈ S, ‖weightedComplete u y (N + 1 - k)‖ ≤ C) :
    ‖(u : ℂ) ^ (N + 1) * headArray u y N S (fun k => smallPrimeMoment N k y)‖ ≤
      (1200 * C / u) * (Real.sqrt (N + 1) / SquarefreeVaughanLogSource.length u N) *
        ∑' n, zetaPrimeExpWeight (1025 / 1024) n := by
  have hL := SquarefreeVaughanLogSource.length_pos u N
  have hsum := sum_norm_weighted_smallPrimeMoment N (S.image Nat.succ) y hu.le huh
  rw [Finset.sum_image (fun _ _ _ _ h => Nat.succ_injective h)] at hsum
  have hb := norm_headArray_le u y N S (fun k => smallPrimeMoment N k y) hu hS hB
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ 2 * C / (u * SquarefreeVaughanLogSource.length u N))
  exact hh.trans_eq (by ring)

/-- The actual floor-defined length dominates the square-root prefix
allowance. Its decay does not require a zero hypothesis. -/
theorem tendsto_sqrt_div_length {u : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => Real.sqrt (N + 1) / SquarefreeVaughanLogSource.length u N)
      atTop (nhds 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hb := (Real.tendsto_sqrt_atTop.comp hn).const_div_atTop 2
  apply squeeze_zero' (Eventually.of_forall (fun N =>
    div_nonneg (Real.sqrt_nonneg _) (SquarefreeVaughanLogSource.length_pos u N).le))
    _ hb
  filter_upwards [ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu
    (by norm_num : (0 : ℝ) ≤ 2 / 3) huh, eventually_ge_atTop 1] with N hL hN
  have hLpos := SquarefreeVaughanLogSource.length_pos u N
  have hs : 0 < Real.sqrt (N + 1) := Real.sqrt_pos.mpr (by positivity)
  apply (div_le_div_iff₀ hLpos hs).mpr
  have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N + 1)
  have hNc : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

/-- The complete complementary leg is uniformly bounded on every low
head order, using the already proved exposed-zero phase limit. -/
theorem eventually_complete_low_leg_norm (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, 8 * k ≤ N + 1 →
      ‖weightedComplete (3 / 2 - rho.1.re) rho.1.im (N + 1 - k)‖ ≤
        2 * (analyticZetaZeroMultiplicity rho : ℝ) := by
  have hm : (0 : ℝ) < analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  filter_upwards [eventually_uniform_complete_phase rho hrho hexposed hm] with N hN
  intro k hk
  have he := hN (N + 1 - k) (by omega)
  calc
    _ = ‖(weightedComplete (3 / 2 - rho.1.re) rho.1.im (N + 1 - k) +
          (analyticZetaZeroMultiplicity rho : ℂ)) - analyticZetaZeroMultiplicity rho‖ := by
      congr 1
      ring
    _ ≤ ‖weightedComplete (3 / 2 - rho.1.re) rho.1.im (N + 1 - k) +
          (analyticZetaZeroMultiplicity rho : ℂ)‖ + ‖(analyticZetaZeroMultiplicity rho : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ _ := by rw [Complex.norm_natCast]; linarith

/-- The whole actual small-prime correction in every moving low-head
order set vanishes at the original product scale. All complete-leg
hypotheses are discharged by the explicit exposed-zero premises. -/
theorem tendsto_smallPrefix_headArray_exposed (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ)))
    (S : ℕ → Finset ℕ) (hS : ∀ᶠ N : ℕ in atTop, ∀ k ∈ S N, 8 * k ≤ N + 1) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      headArray (3 / 2 - rho.1.re) rho.1.im N (S N)
        (fun k => smallPrimeMoment N k rho.1.im)) atTop (nhds 0) := by
  have hu : (0 : ℝ) < 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  let C : ℝ := 2 * analyticZetaZeroMultiplicity rho
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  apply squeeze_zero_norm' (a := fun N : ℕ => (1200 * C / (3 / 2 - rho.1.re)) *
    (Real.sqrt (N + 1) / SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) *
      ∑' n, zetaPrimeExpWeight (1025 / 1024) n) (by
    filter_upwards [eventually_complete_low_leg_norm rho hrho hexposed, hS] with N hB hSN
    exact norm_smallPrefix_headArray_le _ _ N (S N) hu huh hC hSN (fun k hk => hB k (hSN k hk)))
  simpa only [mul_zero, zero_mul] using
    ((tendsto_sqrt_div_length hu huh).const_mul (1200 * C / (3 / 2 - rho.1.re))).mul_const
      (∑' n, zetaPrimeExpWeight (1025 / 1024) n)

/-- The complete upper-prime correction is geometrically small after
summing every low head order and its derivative weight, uniformly in height. -/
theorem eventually_sum_norm_physicalTail_low {u : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ, (∀ k ∈ S, 8 * k ≤ N + 1) → ∀ y : ℝ,
      (∑ k ∈ S, ‖((k + 1 : ℕ) : ℂ) *
        ((u : ℂ) ^ (k + 1) * physicalPrimeTail u N (k + 1) y)‖) ≤
        4 * (N + 1 : ℝ) ^ 2 * Real.exp (-(17 / 12288 : ℝ) * N) *
          ∑' n, zetaPrimeExpWeight (1025 / 1024) n := by
  filter_upwards [eventually_norm_physicalPrimeTail_le hu huh, eventually_ge_atTop 3]
    with N htail hN
  intro S hS y
  have hsub : S ⊆ Finset.range (N + 2) := by
    intro k hk
    exact Finset.mem_range.mpr (by have hh := hS k hk; omega)
  have hc : (S.card : ℝ) ≤ N + 2 := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range (N + 2))
  let Z : ℝ := ∑' n, zetaPrimeExpWeight (1025 / 1024) n
  have hZ : 0 ≤ Z := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  have hterm (k : ℕ) (hk : k ∈ S) :
      ‖((k + 1 : ℕ) : ℂ) * ((u : ℂ) ^ (k + 1) * physicalPrimeTail u N (k + 1) y)‖ ≤
        (N + 2 : ℝ) * Real.exp (-(17 / 12288 : ℝ) * N) * Z := by
    have hh := htail (k + 1) (by have hh := hS k hk; omega) y
    have hkN : ((k + 1 : ℕ) : ℝ) ≤ N + 2 := by
      exact_mod_cast (by have hh := hS k hk; omega : k + 1 ≤ N + 2)
    rw [norm_mul, Complex.norm_natCast]
    calc
      _ ≤ ((k + 1 : ℕ) : ℝ) *
          (Real.exp (-(17 / 12288 : ℝ) * N) * Z) :=
        mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) _)
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hkN (by positivity)
  calc
    _ ≤ ∑ _k ∈ S, (N + 2 : ℝ) * Real.exp (-(17 / 12288 : ℝ) * N) * Z :=
      Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * ((N + 2 : ℝ) * Real.exp (-(17 / 12288 : ℝ) * N) * Z) := by simp
    _ ≤ (N + 2 : ℝ) ^ 2 * Real.exp (-(17 / 12288 : ℝ) * N) * Z := by
      have hh := mul_le_mul_of_nonneg_right hc
        (by positivity : 0 ≤ (N + 2 : ℝ) * Real.exp (-(17 / 12288 : ℝ) * N) * Z)
      exact hh.trans_eq (by ring)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hZ
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- The actual infinite upper-prime correction in every moving low
head vanishes, including the complete complementary leg and all original
weights. Its complete-leg bound is discharged by the exposed-zero theorem. -/
theorem tendsto_physicalTail_headArray_exposed (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ)))
    (S : ℕ → Finset ℕ) (hS : ∀ᶠ N : ℕ in atTop, ∀ k ∈ S N, 8 * k ≤ N + 1) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      headArray (3 / 2 - rho.1.re) rho.1.im N (S N)
        (fun k => physicalPrimeTail (3 / 2 - rho.1.re) N k rho.1.im)) atTop (nhds 0) := by
  let u : ℝ := 3 / 2 - rho.1.re
  let C : ℝ := 2 * analyticZetaZeroMultiplicity rho
  let Z : ℝ := ∑' n, zetaPrimeExpWeight (1025 / 1024) n
  let r : ℝ := Real.exp (-(17 / 12288 : ℝ))
  have hu : 0 < u := by dsimp only [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hZ : 0 ≤ Z := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have he (N : ℕ) : Real.exp (-(17 / 12288 : ℝ) * N) = r ^ N := by
    rw [mul_comm, Real.exp_nat_mul]
  apply squeeze_zero_norm' (a := fun N : ℕ => (N + 1 : ℝ) ^ 2 * r ^ N * (8 * C / u * Z)) (by
    filter_upwards [eventually_sum_norm_physicalTail_low hu huh,
      eventually_complete_low_leg_norm rho hrho hexposed, hS,
      ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu
        (by norm_num : (0 : ℝ) ≤ 2 / 3) huh, eventually_ge_atTop 1]
        with N htail hB hSN hL hN
    have hL1 : 1 ≤ SquarefreeVaughanLogSource.length u N := by
      have hNc : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
    have hLp := SquarefreeVaughanLogSource.length_pos u N
    have hb := norm_headArray_le u rho.1.im N (S N)
      (fun k => physicalPrimeTail u N k rho.1.im) hu hSN (fun k hk => hB k (hSN k hk))
    have ht := htail (S N) hSN rho.1.im
    rw [he] at ht
    have hp : 2 * C / (u * SquarefreeVaughanLogSource.length u N) ≤ 2 * C / u := by
      apply div_le_div_of_nonneg_left (by positivity) hu
      nlinarith
    apply hb.trans
    have hh := mul_le_mul hp ht (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
    exact hh.trans_eq (by ring))
  simpa only [zero_mul] using
    (ZetaRieszShiftedHeadBudget.tendsto_quadratic_geometric hr0 hr1).mul_const (8 * C / u * Z)

/-- The head is linear in its retained first moment array. Its
complete complementary leg is unchanged by this identity. -/
theorem headArray_add (u y : ℝ) (N : ℕ) (S : Finset ℕ) (A B : ℕ → ℂ) :
    headArray u y N S (fun k => A k + B k) = headArray u y N S A + headArray u y N S B := by
  simp only [headArray, mul_add, add_mul, Finset.sum_add_distrib]

/-- Completing the low head has vanishing total error for every moving
eligible order set. Both literal omitted prime ranges are paid; the
negative complete-head product remains in the signed source. -/
theorem tendsto_finite_headArray_sub_complete_exposed (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ)))
    (S : ℕ → Finset ℕ) (hS : ∀ᶠ N : ℕ in atTop, ∀ k ∈ S N, 8 * k ≤ N + 1) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      (headArray (3 / 2 - rho.1.re) rho.1.im N (S N)
        (fun k => ZetaRieszPrimePairConvolution.finiteMoment
          (ZetaRieszAnnulusJoint.intermediatePrimes (3 / 2 - rho.1.re) N) k
            (3 / 2 + Complex.I * (rho.1.im : ℂ))) -
       headArray (3 / 2 - rho.1.re) rho.1.im N (S N)
         (fun k => ordinaryPrimeMoment k (3 / 2 + Complex.I * (rho.1.im : ℂ)))))
      atTop (nhds 0) := by
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : 0 < u := by dsimp only [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := huh.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  have h := ((tendsto_smallPrefix_headArray_exposed rho hrho hexposed huh S hS).add
    (tendsto_physicalTail_headArray_exposed rho hrho hexposed huh S hS)).neg
  simp only [add_zero, neg_zero] at h
  apply h.congr'
  filter_upwards [ZetaRieszSemiprimeSupport.eventually_quadratic_head_lt_physical hu hu1]
    with N hNX
  have hf : (fun k => ordinaryPrimeMoment k (3 / 2 + Complex.I * (rho.1.im : ℂ))) =
      (fun k => (smallPrimeMoment N k rho.1.im +
        ZetaRieszPrimePairConvolution.finiteMoment (ZetaRieszAnnulusJoint.intermediatePrimes u N) k
          (3 / 2 + Complex.I * (rho.1.im : ℂ))) + physicalPrimeTail u N k rho.1.im) := by
    funext k
    exact ordinaryPrimeMoment_eq_actual_split u N k rho.1.im hNX
  rw [hf, headArray_add, headArray_add]
  ring

end
end RiemannGaussian.ZetaRieszLowHeadCorrection
