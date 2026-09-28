/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.NatDivisorSquareMean
import RiemannGaussian.ZetaRieszFiveNegativeHead
import Mathlib.Data.Nat.Log

/-!
# A logarithmic prime-count tail costs a vanishing fraction of signed supply

The complete second divisor moment pays all high prime counts at once.
The original residual coefficient, phase and factorial kernel are kept.
The saving is relative to the existing four-prime supply, not a claim
that this tail vanishes after source normalization on its own.
-/

namespace RiemannGaussian.ZetaRieszLogCountBudget
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic
open ZetaRieszRadialCompensation ZetaRieszTriplePrime
open ZetaRieszBandCompensation ZetaRieszSmallPrimeCompensation
open ZetaRieszFiveNegativeHead

/-- An explicit logarithmic threshold, rounded upward in base two. -/
def countThreshold (N : ℕ) : ℕ := 8*Nat.clog 2 (N+1)

/-- The count tilt buys eight powers of the factorial order. -/
theorem threshold_power (N : ℕ) :
    ((N : ℝ)+1)^8 ≤ (2 : ℝ)^countThreshold N := by
  have h := pow_le_pow_left₀ (Nat.zero_le (N+1))
    (Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) (N+1)) 8
  have he : (2^Nat.clog 2 (N+1))^8 = 2^countThreshold N := by
    rw [← pow_mul,countThreshold,Nat.mul_comm 8]
  rw [he] at h
  exact_mod_cast h

/-- The new tail is disjoint from every previously paid count 3--6. -/
theorem eight_le_threshold {N : ℕ} (hN : 1 ≤ N) : 8 ≤ countThreshold N := by
  have h := Nat.clog_pos (by norm_num : 1 < (2 : ℕ)) (show 1 < N+1 by omega)
  unfold countThreshold
  omega

/-- Keep the full divisor coefficient until its squarefree count tilt.
This bounds every finite selected set, with no distribution hypothesis. -/
theorem selected_count_mass_le (S : Finset ℕ) {X K : ℕ}
    (hS : ∀ n ∈ S, Squarefree n ∧ n ≤ X ∧ K ≤ n.primeFactors.card) :
    (∑ n ∈ S, (2 : ℝ)^n.primeFactors.card) ≤
      (X : ℝ)*(1+Real.log X)^3/(2 : ℝ)^K := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2^K)).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ n ∈ S, (n.divisors.card : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro n hn
      rw [ZetaRieszSmoothHead.card_divisors_of_squarefree (hS n hn).1,
        Nat.cast_pow,Nat.cast_ofNat,pow_two]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (hS n hn).2.2) (by positivity)
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (n.divisors.card : ℝ)^2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero (hS n hn).1.ne_zero,(hS n hn).2.1⟩
      · intro n _ _
        positivity
    _ ≤ _ := sum_Icc_card_divisors_sq_le_log_cube X

/-- A literal logarithmic slab has a polynomial count cost. This is a
finite arithmetic sum, not a prime-density or continuum approximation. -/
theorem slab_count_mass_le (S : Finset ℕ) {M K : ℕ}
    (hS : ∀ n ∈ S, Squarefree n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
      K ≤ n.primeFactors.card) :
    (∑ n ∈ S, (2 : ℝ)^n.primeFactors.card) ≤
      Real.exp (2*(M : ℝ)+2)*(2*(M : ℝ)+3)^3/(2 : ℝ)^K := by
  let X : ℕ := ⌊Real.exp (2*(M : ℝ)+2)⌋₊
  have hX : (X : ℝ) ≤ Real.exp (2*(M : ℝ)+2) := Nat.floor_le (Real.exp_nonneg _)
  have hX1 : 1 ≤ X := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_exp (show 0 ≤ 2*(M : ℝ)+2 by positivity)
  have hlog : Real.log X ≤ 2*(M : ℝ)+2 := by
    have hx0 : (0 : ℝ) < X := by exact_mod_cast hX1
    simpa only [Real.log_exp] using Real.log_le_log hx0 hX
  have hs := selected_count_mass_le (X := X) S (by
    intro n hn
    obtain ⟨hn0,hnlog,hk⟩ := hS n hn
    refine ⟨hn0,Nat.le_floor ?_,hk⟩
    have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0.ne_zero
    simpa only [Real.exp_log hnR] using Real.exp_le_exp.mpr hnlog)
  apply hs.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul hX
  · exact pow_le_pow_left₀ (by positivity [Real.log_natCast_nonneg X]) (by linarith) 3
  · positivity [Real.log_natCast_nonneg X]
  · positivity

/-- All counts above K obey the same literal slab bound. Allocation is
only used as its proved contraction; every complex phase is included. -/
theorem high_count_norm_upper (S A : Finset ℕ) {N M K : ℕ}
    (hM : 0 < M) (hNM : N ≤ 2*M) {L : ℝ} (hL : 0 < L) (y : ℝ)
    (hS : ∀ n ∈ S, Squarefree n ∧ 2*(M : ℝ) ≤ Real.log n ∧
      Real.log n ≤ 2*(M : ℝ)+2 ∧ K ≤ n.primeFactors.card) :
    ‖∑ n ∈ S, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      Real.exp 4*(2*(M : ℝ)+2)*(2*(M : ℝ)+3)^3/(2 : ℝ)^K*
        Real.exp (2*(M : ℝ))*radialEnvelope N M := by
  have hp (n : ℕ) (hn : n ∈ S) :
      ‖residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        ((2*(M : ℝ)+2)*Real.exp 2*radialEnvelope N M)*(2 : ℝ)^n.primeFactors.card := by
    obtain ⟨hs,hlo,hhi,_⟩ := hS n hn
    have hc := (ZetaRieszJointCountFloor.norm_residual_le A L N n).trans
      ((SquarefreeVaughanLogSource.norm_coefficient_le hL n).trans
        (ZetaRieszSmoothHead.logMajorant_le_prime_count hs))
    have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ = amplitude N n := by
      rw [norm_zetaPrimeLogKernel]
      norm_num [zetaPrimeExpWeight,amplitude]
      ring
    rw [norm_mul,hk]
    have hc' := hc.trans (mul_le_mul_of_nonneg_right hhi (by positivity : (0 : ℝ) ≤ 2^n.primeFactors.card))
    exact (mul_le_mul hc' (amplitude_le_radial hM hNM hlo hhi)
      (by unfold amplitude; positivity) (by positivity)).trans_eq (by ring)
  have hm := slab_count_mass_le S (fun n hn => ⟨(hS n hn).1,(hS n hn).2.2⟩)
  have hs := (norm_sum_le _ _).trans (Finset.sum_le_sum hp)
  rw [← Finset.mul_sum] at hs
  refine hs.trans ((mul_le_mul_of_nonneg_left hm
    (by positivity [radialEnvelope_nonneg N M])).trans_eq ?_)
  rw [Real.exp_add]
  have he : Real.exp (2 : ℝ)*Real.exp 2 = Real.exp 4 := by rw [← Real.exp_add]; norm_num
  calc
    _ = (Real.exp 2*Real.exp 2)*(2*(M : ℝ)+2)*(2*(M : ℝ)+3)^3/(2 : ℝ)^K*
        Real.exp (2*(M : ℝ))*radialEnvelope N M := by ring
    _ = _ := by rw [he]

/-- Explicit vanishing relative charge for the whole logarithmic tail. -/
def relativeCost (N : ℕ) : ℝ := 512*Real.exp 4/((N : ℝ)+1)^4

/-- Across the actual radial range, the logarithmic count tail costs
O(N^-4) of the existing supply scale, uniformly in all heights and masks. -/
theorem logarithmic_count_norm_upper (S A : Finset ℕ) {N M : ℕ}
    (hM : 0 < M) (hNM : N ≤ 2*M) (hMN : M ≤ 2*N) {L : ℝ} (hL : 0 < L) (y : ℝ)
    (hS : ∀ n ∈ S, Squarefree n ∧ 2*(M : ℝ) ≤ Real.log n ∧
      Real.log n ≤ 2*(M : ℝ)+2 ∧ countThreshold N ≤ n.primeFactors.card) :
    ‖∑ n ∈ S, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      relativeCost N*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hmn : (M : ℝ) ≤ 2*N := by exact_mod_cast hMN
  have hx : 0 < (N : ℝ)+1 := by positivity
  have hpoly : (2*(M : ℝ)+2)*(2*(M : ℝ)+3)^3 ≤ 256*((N : ℝ)+1)^4 := by
    calc
      _ ≤ (4*((N : ℝ)+1))*(4*((N : ℝ)+1))^3 := by gcongr <;> linarith
      _ = _ := by ring
  have hdiv : Real.exp 4*(2*(M : ℝ)+2)*(2*(M : ℝ)+3)^3/(2 : ℝ)^countThreshold N ≤
      256*Real.exp 4/((N : ℝ)+1)^4 := by
    calc
      _ ≤ Real.exp 4*(256*((N : ℝ)+1)^4)/((N : ℝ)+1)^8 := by
        apply div_le_div₀ (by positivity) (by nlinarith only [mul_le_mul_of_nonneg_left hpoly (Real.exp_nonneg 4)])
          (by positivity) (threshold_power N)
      _ = _ := by field_simp
  have hratio : (1/2 : ℝ) ≤ (M : ℝ)/((M : ℝ)+1) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hcost : 256*Real.exp 4/((N : ℝ)+1)^4 ≤ relativeCost N*(M : ℝ)/((M : ℝ)+1) := by
    have hh := mul_le_mul_of_nonneg_left hratio (show 0 ≤ relativeCost N by unfold relativeCost; positivity)
    calc
      _ = relativeCost N*(1/2 : ℝ) := by unfold relativeCost; ring
      _ ≤ relativeCost N*((M : ℝ)/((M : ℝ)+1)) := hh
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_right (hdiv.trans hcost)
    (show 0 ≤ Real.exp (2*(M : ℝ))*radialEnvelope N M by positivity [radialEnvelope_nonneg N M])
  apply (high_count_norm_upper S A hM hNM hL y hS).trans
  convert hh using 1 <;> ring

/-- The relative cost tends to zero independently of height or zeros. -/
theorem tendsto_relativeCost : Tendsto relativeCost atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 4
  have hh := h.const_mul (512*Real.exp 4)
  change Tendsto (fun N : ℕ => 512*Real.exp 4/((N : ℝ)+1)^4) atTop (𝓝 0)
  simpa [div_eq_mul_inv] using hh

/-- The count tail costs any fixed fraction of the old supply scale
eventually; the assertion is uniform over all selected arithmetic sets. -/
theorem eventually_logarithmic_count_cost {b : ℝ} (hb : 0 < b) :
    ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (S A : Finset ℕ) (L y : ℝ),
      N ≤ 2*M → M ≤ 2*N → 0 < L →
      (∀ n ∈ S, Squarefree n ∧ 2*(M : ℝ) ≤ Real.log n ∧
        Real.log n ≤ 2*(M : ℝ)+2 ∧ countThreshold N ≤ n.primeFactors.card) →
      ‖∑ n ∈ S, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        b*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by
  filter_upwards [tendsto_relativeCost.eventually_lt_const hb,eventually_ge_atTop (1 : ℕ)]
    with N hcost hN M S A L y hNM hMN hL hS
  apply (logarithmic_count_norm_upper S A (by omega) hNM hMN hL y hS).trans
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcost.le (Nat.cast_nonneg M))
        (Real.exp_nonneg _)) (by positivity)) (radialEnvelope_nonneg N M)

/-- One positive four-prime supply simultaneously pays all old heads and
the entire logarithmic count tail. Only one sixty-fourth is added; the
prior widths, signs and three-thirty-seconds mixed-head charge survive. -/
theorem eventually_joint_slabs_floor_with_count_tail {y : ℝ} (hy : 16 ≤ |y|) :
    ∃ η h δ ε ζ : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧ 0 < ζ ∧ ζ ≤ 1/128 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (M Q P V : ℕ) (D S H F G T A : Finset ℕ) (L : ℝ),
        N ≤ 2*M → M ≤ 2*N → Real.log Q ≤ δ*N → Real.log P ≤ ε*N → Real.log V ≤ ζ*N → 0 < L → (271/200 : ℝ)*M ≤ L → L ≤ (143/100 : ℝ)*M →
        (∀ n ∈ H, Squarefree n ∧ n.primeFactors.card = 4 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ ∃ r ∈ n.primeFactors, r ≤ Q) →
        (∀ n ∈ F, Squarefree n ∧ n.primeFactors.card = 5 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ (∃ r ∈ n.primeFactors, r ≤ Q) ∧
          0 < (SquarefreeVaughanLogSource.coefficient L n).re) →
        (∀ n ∈ G, Squarefree n ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          headCondition L P V n) →
        (∀ n ∈ T, Squarefree n ∧ 2*(M : ℝ) ≤ Real.log n ∧
          Real.log n ≤ 2*(M : ℝ)+2 ∧ countThreshold N ≤ n.primeFactors.card) →
        ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1/2 ∧
          let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
          let Y := (∑ n ∈ supply M h v, f n).re
          0 < Y ∧
            ‖∑ n ∈ slabTriples D M η, f n‖ ≤ (1/2 : ℝ)*Y ∧
            ‖∑ n ∈ smallTriples S M Q, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ H, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ F, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ G, f n‖ ≤ (3/32 : ℝ)*Y ∧
            ‖∑ n ∈ T, f n‖ ≤ (1/64 : ℝ)*Y := by
  obtain ⟨η,h,δ,c,hη,hηu,hh,hhu,hδ,hδu,hc,hpay⟩ :=
    ZetaRieszFivePositiveHead.eventually_joint_slabs_spending_log_head_with_scale hy
  obtain ⟨ε,ζ,hε,hεu,hζ,hζu,hsmall⟩ := eventually_mixed_log_cost
    (show 0 < 3*c/32 by positivity)
  refine ⟨η,h,δ,ε,ζ,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,?_⟩
  have htail := eventually_logarithmic_count_cost (show 0 < c/64 by positivity)
  filter_upwards [hpay,hsmall,htail]
    with N hpay hsmall htail M Q P V D S H F G T A L hNM hMN hQ hP hV hL0 hL hLu hH hF hG hT
  obtain ⟨v,hv,hvu,hscale,hY,hX,hZ,hHpay,hFpay⟩ :=
    hpay M Q D S H F A L hNM hQ hL0 hL hLu hH hF
  refine ⟨v,hv,hvu,hY,hX,hZ,hHpay,hFpay,?_,?_⟩
  · have hGpay := hsmall M P V G A L y hNM hP hV hL0 hL hG
    have h := mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 3/32)
    apply hGpay.trans
    convert h using 1
    ring
  · have hTpay := htail M T A L y hNM hMN hL0 hT
    have h := mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 1/64)
    apply hTpay.trans
    convert h using 1
    ring

/-- The same high-count population is paid in the opposite phase orientation
for the multiple-zero ceiling. It is not added to the positive supply. -/
theorem eventually_joint_slabs_ceiling_with_count_tail {y : ℝ} (hy : 16 ≤ |y|) :
    ∃ η h δ ε ζ : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧ 0 < ζ ∧ ζ ≤ 1/128 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (M Q P V : ℕ) (D S H F G T A : Finset ℕ) (L : ℝ),
        N ≤ 2*M → M ≤ 2*N → Real.log Q ≤ δ*N → Real.log P ≤ ε*N → Real.log V ≤ ζ*N → 0 < L → (271/200 : ℝ)*M ≤ L → L ≤ (143/100 : ℝ)*M →
        (∀ n ∈ H, Squarefree n ∧ n.primeFactors.card = 4 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ ∃ r ∈ n.primeFactors, r ≤ Q) →
        (∀ n ∈ F, Squarefree n ∧ n.primeFactors.card = 5 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ (∃ r ∈ n.primeFactors, r ≤ Q) ∧
          0 < (SquarefreeVaughanLogSource.coefficient L n).re) →
        (∀ n ∈ G, Squarefree n ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          headCondition L P V n) →
        (∀ n ∈ T, Squarefree n ∧ 2*(M : ℝ) ≤ Real.log n ∧
          Real.log n ≤ 2*(M : ℝ)+2 ∧ countThreshold N ≤ n.primeFactors.card) →
        ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1/2 ∧
          let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
          let Y := -(∑ n ∈ supply M h v, f n).re
          0 < Y ∧
            ‖∑ n ∈ slabTriples D M η, f n‖ ≤ (1/2 : ℝ)*Y ∧
            ‖∑ n ∈ smallTriples S M Q, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ H, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ F, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ G, f n‖ ≤ (3/32 : ℝ)*Y ∧
            ‖∑ n ∈ T, f n‖ ≤ (1/64 : ℝ)*Y := by
  obtain ⟨η,h,δ,c,hη,hηu,hh,hhu,hδ,hδu,hc,hpay⟩ :=
    ZetaRieszHeadCeiling.eventually_joint_slabs_upper_log_head_with_scale hy
  obtain ⟨ε,ζ,hε,hεu,hζ,hζu,hsmall⟩ := eventually_mixed_log_cost
    (show 0 < 3*c/32 by positivity)
  refine ⟨η,h,δ,ε,ζ,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,?_⟩
  have htail := eventually_logarithmic_count_cost (show 0 < c/64 by positivity)
  filter_upwards [hpay,hsmall,htail]
    with N hpay hsmall htail M Q P V D S H F G T A L hNM hMN hQ hP hV hL0 hL hLu hH hF hG hT
  obtain ⟨v,hv,hvu,hscale,hY,hX,hZ,hHpay,hFpay⟩ :=
    hpay M Q D S H F A L hNM hQ hL0 hL hLu hH hF
  refine ⟨v,hv,hvu,hY,hX,hZ,hHpay,hFpay,?_,?_⟩
  · have hGpay := hsmall M P V G A L y hNM hP hV hL0 hL hG
    have h := mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 3/32)
    apply hGpay.trans
    convert h using 1
    ring
  · have hTpay := htail M T A L y hNM hMN hL0 hT
    have h := mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 1/64)
    apply hTpay.trans
    convert h using 1
    ring

/-- Spend one sixty-fourth on the count tail while keeping the previous
payments, every favorable observation and one exact signed rest. -/
theorem re_sum_ge_joint_spending {D X Z H F G T Y : Finset ℕ} (f : ℕ → ℂ)
    (hsub : X ∪ Z ∪ H ∪ Y ∪ F ∪ G ∪ T ⊆ D) (hXZ : Disjoint X Z)
    (hXH : Disjoint X H) (hZH : Disjoint Z H)
    (hXY : Disjoint X Y) (hZY : Disjoint Z Y) (hHY : Disjoint H Y)
    (hF : Disjoint F (X ∪ Z ∪ H ∪ Y))
    (hG : Disjoint G (X ∪ Z ∪ H ∪ Y ∪ F))
    (hT : Disjoint T (X ∪ Z ∪ H ∪ Y ∪ F ∪ G))
    (hXcost : ‖∑ n ∈ X, f n‖ ≤ (1/2 : ℝ)*(∑ n ∈ Y, f n).re)
    (hZcost : ‖∑ n ∈ Z, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ Y, f n).re)
    (hHcost : ‖∑ n ∈ H, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ Y, f n).re)
    (hFcost : ‖∑ n ∈ F, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ Y, f n).re)
    (hGcost : ‖∑ n ∈ G, f n‖ ≤ (3/32 : ℝ)*(∑ n ∈ Y, f n).re)
    (hTcost : ‖∑ n ∈ T, f n‖ ≤ (1/64 : ℝ)*(∑ n ∈ Y, f n).re) :
    (∑ n ∈ D\(X ∪ Z ∪ H ∪ Y ∪ F ∪ G ∪ T), f n).re+
      max (∑ n ∈ X, f n).re 0+max (∑ n ∈ Z, f n).re 0+
      max (∑ n ∈ H, f n).re 0+max (∑ n ∈ F, f n).re 0+
      max (∑ n ∈ G, f n).re 0+max (∑ n ∈ T, f n).re 0+
      (∑ n ∈ Y, f n).re/64 ≤ (∑ n ∈ D, f n).re := by
  have hsub' : X ∪ Z ∪ H ∪ Y ∪ F ∪ G ⊆ D\T := by
    intro n hn
    exact Finset.mem_sdiff.mpr ⟨hsub (Finset.mem_union_left T hn),
      fun hnT => Finset.disjoint_left.mp hT hnT hn⟩
  have htSub : T ⊆ D := fun _ hn => hsub (Finset.mem_union_right _ hn)
  have hledger := ZetaRieszFiveNegativeHead.re_sum_ge_joint_spending f hsub'
    hXZ hXH hZH hXY hZY hHY hF hG hXcost hZcost hHcost hFcost hGcost
  have he : (D\T)\(X ∪ Z ∪ H ∪ Y ∪ F ∪ G) = D\(X ∪ Z ∪ H ∪ Y ∪ F ∪ G ∪ T) := by
    ext n
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  rw [he] at hledger
  have hsum := congrArg Complex.re (Finset.sum_sdiff (f := f) htSub)
  simp only [Complex.add_re] at hsum
  have ht := (abs_le.mp ((Complex.abs_re_le_norm _).trans hTcost)).1
  have hy : 0 ≤ (∑ n ∈ Y, f n).re := by nlinarith [norm_nonneg (∑ n ∈ T, f n)]
  rcases le_total (∑ n ∈ T, f n).re 0 with ht' | ht'
  · rw [max_eq_right ht']
    linarith
  · rw [max_eq_left ht']
    linarith

/-- The opposite signed spending inequality preserves the negative
supply and favorable negative observations for the multiplicity ceiling. -/
theorem re_sum_le_joint_spending {D X Z H F G T Y : Finset ℕ} (f : ℕ → ℂ)
    (hsub : X ∪ Z ∪ H ∪ Y ∪ F ∪ G ∪ T ⊆ D) (hXZ : Disjoint X Z)
    (hXH : Disjoint X H) (hZH : Disjoint Z H)
    (hXY : Disjoint X Y) (hZY : Disjoint Z Y) (hHY : Disjoint H Y)
    (hF : Disjoint F (X ∪ Z ∪ H ∪ Y))
    (hG : Disjoint G (X ∪ Z ∪ H ∪ Y ∪ F))
    (hT : Disjoint T (X ∪ Z ∪ H ∪ Y ∪ F ∪ G))
    (hXcost : ‖∑ n ∈ X, f n‖ ≤ (1/2 : ℝ)*(-(∑ n ∈ Y, f n).re))
    (hZcost : ‖∑ n ∈ Z, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ Y, f n).re))
    (hHcost : ‖∑ n ∈ H, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ Y, f n).re))
    (hFcost : ‖∑ n ∈ F, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ Y, f n).re))
    (hGcost : ‖∑ n ∈ G, f n‖ ≤ (3/32 : ℝ)*(-(∑ n ∈ Y, f n).re))
    (hTcost : ‖∑ n ∈ T, f n‖ ≤ (1/64 : ℝ)*(-(∑ n ∈ Y, f n).re)) :
    (∑ n ∈ D, f n).re ≤ (∑ n ∈ D\(X ∪ Z ∪ H ∪ Y ∪ F ∪ G ∪ T), f n).re+
      min (∑ n ∈ X, f n).re 0+min (∑ n ∈ Z, f n).re 0+
      min (∑ n ∈ H, f n).re 0+min (∑ n ∈ F, f n).re 0+
      min (∑ n ∈ G, f n).re 0+min (∑ n ∈ T, f n).re 0+
      (∑ n ∈ Y, f n).re/64 := by
  have h := re_sum_ge_joint_spending (fun n => -f n) hsub hXZ hXH hZH hXY hZY hHY hF hG hT
    (by simpa using hXcost) (by simpa using hZcost) (by simpa using hHcost)
    (by simpa using hFcost) (by simpa using hGcost) (by simpa using hTcost)
  have hm (a : ℝ) : max (-a) 0 = -min a 0 := by
    simp only [min_def,max_def]
    split_ifs <;> linarith
  simp only [Finset.sum_neg_distrib,Complex.neg_re,hm] at h
  linarith only [h]

end
end RiemannGaussian.ZetaRieszLogCountBudget
