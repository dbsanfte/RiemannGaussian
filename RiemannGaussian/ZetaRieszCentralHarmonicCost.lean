/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszHeadHarmonicAsymptotic
import RiemannGaussian.FiniteWeightedUniformConvergence
import RiemannGaussian.ZetaRieszCentralProductPhase
import RiemannGaussian.RieszHarmonicCostBounds

/-!
# The exact central block and combined harmonic cost

The actual symmetric central interval and uniformly controlled product errors give an exact signed cost. Together with the complete head, this leaves exactly three unpaid arithmetic components with full multiplicity and source hypotheses.
-/

namespace RiemannGaussian.ZetaRieszCentralHarmonicCost
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszReflectedCarrier ZetaRieszReflectedCompletion
open ZetaRieszHeadHarmonicAsymptotic HarmonicIntervalLimit
open RieszHarmonicCostBounds

/-- The actual central complement is one symmetric closed integer
interval; neither boundary fibre is rounded away. -/
theorem centralOrders_eq_Icc (N : ℕ) (hN : 256 ≤ N) :
    centralOrders N = Finset.Icc ((15 * N + 64) / 32 + 1) (complementaryEndpoint N) := by
  ext k
  constructor
  · intro hk
    obtain ⟨hm, hn⟩ := Finset.mem_sdiff.mp hk
    obtain ⟨hkr, hkl, hkh⟩ := Finset.mem_filter.mp hm
    have hkM := Finset.mem_range.mp hkr
    have hlo : (15 * N + 64) / 32 < k := by
      by_contra h
      apply hn
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hm, by omega⟩)
    have hhi : (15 * N + 64) / 32 < N + 1 - k := by
      by_contra h
      apply hn
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨N + 1 - k, ?_, by omega⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, by omega⟩,
          by omega⟩
    rw [Finset.mem_Icc]
    unfold complementaryEndpoint
    omega
  · rw [Finset.mem_Icc]
    intro hk
    have hk' : (15 * N + 64) / 32 + 1 ≤ k ∧ k ≤ N - (15 * N + 64) / 32 := hk
    have hm : k ∈ ZetaRieszPairOrders.middleOrders (N + 1) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by omega), by omega, by omega⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨hm, ?_⟩
    intro hw
    rcases Finset.mem_union.mp hw with hl | hr
    · have hlk := (Finset.mem_filter.mp hl).2
      omega
    · obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hr
      obtain ⟨hjm, hjl⟩ := Finset.mem_filter.mp hj
      have hjr := Finset.mem_range.mp (Finset.mem_filter.mp hjm).1
      omega

/-- Reflection preserves every actual central order. -/
theorem reflected_mem_centralOrders (N : ℕ) (hN : 256 ≤ N) {k : ℕ}
    (hk : k ∈ centralOrders N) : N + 1 - k ∈ centralOrders N := by
  rw [centralOrders_eq_Icc N hN, Finset.mem_Icc] at hk ⊢
  unfold complementaryEndpoint at hk ⊢
  omega

/-- The central reciprocal sum retains exact reflection symmetry,
so its two partial-fraction marginals coincide without any norm estimate. -/
theorem central_sum_reflection {α : Type*} [AddCommMonoid α]
    (N : ℕ) (hN : 256 ≤ N) (f : ℕ → α) :
    (∑ k ∈ centralOrders N, f (N + 1 - k)) = ∑ k ∈ centralOrders N, f k := by
  apply Finset.sum_bij (fun k _ => N + 1 - k)
  · intro k hk
    exact reflected_mem_centralOrders N hN hk
  · intro a ha b hb he
    have ha' := (Finset.mem_Icc.mp ((centralOrders_eq_Icc N hN) ▸ ha)).2
    have hb' := (Finset.mem_Icc.mp ((centralOrders_eq_Icc N hN) ▸ hb)).2
    unfold complementaryEndpoint at ha' hb'
    omega
  · intro k hk
    refine ⟨N + 1 - k, reflected_mem_centralOrders N hN hk, ?_⟩
    have hk' := (Finset.mem_Icc.mp ((centralOrders_eq_Icc N hN) ▸ hk)).2
    unfold complementaryEndpoint at hk'
    omega
  · intro k _
    rfl

/-- The central reciprocal mass is an exact harmonic difference,
including both boundaries left by the actual reflected completion. -/
theorem central_reciprocal_eq_harmonic (N : ℕ) (hN : 256 ≤ N) :
    (∑ k ∈ centralOrders N, (1 : ℝ) / k) =
      (harmonic (complementaryEndpoint N) : ℝ) - (harmonic ((15 * N + 64) / 32) : ℝ) := by
  have hKB : (15 * N + 64) / 32 ≤ complementaryEndpoint N := by
    unfold complementaryEndpoint
    omega
  have hsub : Finset.Icc 1 ((15 * N + 64) / 32) ⊆ Finset.Icc 1 (complementaryEndpoint N) := by
    intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    omega
  have hs : Finset.Icc 1 (complementaryEndpoint N) \ Finset.Icc 1 ((15 * N + 64) / 32) =
      centralOrders N := by
    rw [centralOrders_eq_Icc N hN]
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_Icc]
    omega
  have hh := Finset.sum_sdiff (f := fun k : ℕ => (1 : ℝ) / k) hsub
  rw [hs] at hh
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  simpa only [one_div] using (eq_sub_iff_add_eq.mpr hh)

/-- The lower integer endpoint occupies exactly fifteen thirty-seconds
of the full order in the limit, with the original floor still present. -/
theorem tendsto_lower_endpoint_ratio :
    Tendsto (fun N : ℕ => (((15 * N + 64) / 32 : ℕ) : ℝ) / (N + 1))
      atTop (nhds (15 / 32)) := by
  have hm : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hm.const_div_atTop 1)).sub
    tendsto_complementaryEndpoint_ratio
  norm_num only at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 256] with N hN
  have hn : (15 * N + 64) / 32 + complementaryEndpoint N = N := by
    unfold complementaryEndpoint
    omega
  have hnr : (((15 * N + 64) / 32 : ℕ) : ℝ) + complementaryEndpoint N = N := by
    exact_mod_cast hn
  have hm0 : (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  linarith

/-- The actual lower harmonic endpoint diverges. -/
theorem tendsto_lower_endpoint_atTop :
    Tendsto (fun N : ℕ => (15 * N + 64) / 32) atTop atTop := by
  refine tendsto_atTop.2 (fun b => ?_)
  filter_upwards [eventually_ge_atTop (3 * b)] with N hN
  omega

/-- The central order mass tends to the exact logarithm of its endpoint
ratio, without imposing any prime or hypothetical-zero condition. -/
theorem tendsto_central_reciprocal :
    Tendsto (fun N : ℕ => ∑ k ∈ centralOrders N, (1 : ℝ) / k)
      atTop (nhds (Real.log (17 / 15))) := by
  have hr : Tendsto (fun N : ℕ => (complementaryEndpoint N : ℝ) /
      (((15 * N + 64) / 32 : ℕ) : ℝ)) atTop (nhds (17 / 15)) := by
    have h := tendsto_complementaryEndpoint_ratio.div tendsto_lower_endpoint_ratio (by norm_num)
    norm_num only at h
    apply h.congr'
    filter_upwards [] with N
    dsimp only [Pi.div_apply]
    have hm : (N : ℝ) + 1 ≠ 0 := by positivity
    have hk0 : ((((15 * N + 64) / 32 : ℕ) : ℝ)) ≠ 0 := by
      exact_mod_cast (by omega : (15 * N + 64) / 32 ≠ 0)
    field_simp
  have h := tendsto_harmonic_difference complementaryEndpoint
    (fun N => (15 * N + 64) / 32) tendsto_complementaryEndpoint_atTop
    tendsto_lower_endpoint_atTop (by norm_num) hr
  apply h.congr'
  filter_upwards [eventually_ge_atTop 256] with N hN
  exact (central_reciprocal_eq_harmonic N hN).symm

/-- The positive central pair weight after the exact source
normalization; the factor one half is kept. -/
def centralPairWeight (N k : ℕ) : ℝ :=
  ((N + 1 : ℕ) : ℝ) / (2 * (k : ℝ) * ((N + 1 - k : ℕ) : ℝ))

/-- The positive size of the negative central head weight; the sign
will be retained explicitly in the complete paired response. -/
def centralHeadWeight (u : ℝ) (N k : ℕ) : ℝ :=
  ((N + 1 : ℕ) : ℝ) / (u * SquarefreeVaughanLogSource.length u N) *
    (1 / ((N + 1 - k : ℕ) : ℝ))

/-- The scalar pair weights are nonnegative at every order. -/
theorem centralPairWeight_nonneg (N k : ℕ) : 0 ≤ centralPairWeight N k := by
  unfold centralPairWeight
  positivity

/-- The head weights are nonnegative at every positive source radius. -/
theorem centralHeadWeight_nonneg {u : ℝ} (hu : 0 < u) (N k : ℕ) :
    0 ≤ centralHeadWeight u N k := by
  have hL := SquarefreeVaughanLogSource.length_pos u N
  unfold centralHeadWeight
  positivity

/-- Partial fractions retain both reflected reciprocal marginals of
the central pair, instead of taking an absolute product estimate. -/
theorem centralPairWeight_eq (N : ℕ) (hN : 256 ≤ N) {k : ℕ}
    (hk : k ∈ centralOrders N) : centralPairWeight N k =
      (1 / 2 : ℝ) * (1 / (k : ℝ) + 1 / ((N + 1 - k : ℕ) : ℝ)) := by
  obtain ⟨hkp, hlp⟩ := ZetaRieszWiderMatched.matchedOrders_pos (by omega)
    (centralOrders_subset_wider N hk)
  have hkM : k ≤ N + 1 := by omega
  have he : (k : ℝ) + ((N + 1 - k : ℕ) : ℝ) = ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show k + (N + 1 - k) = N + 1 by omega)
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hl0 : ((N + 1 - k : ℕ) : ℝ) ≠ 0 := by positivity
  unfold centralPairWeight
  field_simp
  linarith

/-- The pair's two reciprocal marginals combine into exactly one
central harmonic mass, with the factor one half paid by reflection. -/
theorem sum_centralPairWeight (N : ℕ) (hN : 256 ≤ N) :
    (∑ k ∈ centralOrders N, centralPairWeight N k) = ∑ k ∈ centralOrders N, (1 : ℝ) / k := by
  have hterms : (∑ k ∈ centralOrders N, centralPairWeight N k) =
      ∑ k ∈ centralOrders N, (1 / 2 : ℝ) *
        (1 / (k : ℝ) + 1 / ((N + 1 - k : ℕ) : ℝ)) := by
    exact Finset.sum_congr rfl (fun k hk => centralPairWeight_eq N hN hk)
  rw [hterms, ← Finset.mul_sum, Finset.sum_add_distrib,
    central_sum_reflection N hN (fun k => (1 : ℝ) / k)]
  ring

/-- The complete central head weight has the same harmonic mass as
the pair, times the original source-length prefactor. -/
theorem sum_centralHeadWeight (u : ℝ) (N : ℕ) (hN : 256 ≤ N) :
    (∑ k ∈ centralOrders N, centralHeadWeight u N k) =
      ((N + 1 : ℕ) : ℝ) / (u * SquarefreeVaughanLogSource.length u N) *
        ∑ k ∈ centralOrders N, (1 : ℝ) / k := by
  unfold centralHeadWeight
  rw [← Finset.mul_sum, central_sum_reflection N hN (fun k => (1 : ℝ) / k)]

/-- The full central pair weight has an exact logarithmic mass limit,
without any prime-distribution or zero-exposure assumption. -/
theorem tendsto_sum_centralPairWeight :
    Tendsto (fun N : ℕ => ∑ k ∈ centralOrders N, centralPairWeight N k)
      atTop (nhds (Real.log (17 / 15))) := by
  apply tendsto_central_reciprocal.congr'
  filter_upwards [eventually_ge_atTop 256] with N hN
  exact (sum_centralPairWeight N hN).symm

/-- The full central head weight has an exact logarithmic mass limit,
with the original physical length still controlling its prefactor. -/
theorem tendsto_sum_centralHeadWeight {u : ℝ} (hu : 0 < u) (huq : u ≤ 3 / 5) :
    Tendsto (fun N : ℕ => ∑ k ∈ centralOrders N, centralHeadWeight u N k)
      atTop (nhds (Real.log (17 / 15) / (-2 * u * Real.log u))) := by
  have h := (ZetaRieszLengthAsymptotic.tendsto_head_length_factor hu huq).mul
    tendsto_central_reciprocal
  rw [one_div, inv_mul_eq_div] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 256] with N hN
  simpa only [Nat.cast_add, Nat.cast_one] using (sum_centralHeadWeight u N hN).symm

/-- The entire actual central block is the difference of two weighted
complex prime-product sums. Both phases and the negative head sign survive. -/
theorem normalized_centralBlock_eq (u y : ℝ) (N : ℕ) (hu : 0 < u) (hN : 256 ≤ N) :
    (u : ℂ) ^ (N + 1) * centralBlock u y N =
      (∑ k ∈ centralOrders N, (centralPairWeight N k : ℂ) *
        (ZetaRieszMatchedMiddle.weightedFinite u y N k *
          ZetaRieszMatchedMiddle.weightedFinite u y N (N + 1 - k))) -
      ∑ k ∈ centralOrders N, (centralHeadWeight u N k : ℂ) *
        (ZetaRieszMatchedMiddle.weightedFinite u y N (k + 1) *
          ZetaRieszMatchedMiddle.weightedComplete u y (N + 1 - k)) := by
  simp only [centralBlock, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨hkp, hlp⟩ := ZetaRieszWiderMatched.matchedOrders_pos (by omega)
    (centralOrders_subset_wider N hk)
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hkp.ne'
  have hl0 : ((N + 1 - k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hlp.ne'
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hL0 : (SquarefreeVaughanLogSource.length u N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (SquarefreeVaughanLogSource.length_pos u N).ne'
  have he := ZetaRieszMatchedMiddle.normalized_sharedAtom_eq u y N k (N + 1 - k) hu.ne'
  rw [show k + (N + 1 - k) = N + 1 by omega] at he
  calc
    _ = (((N + 1 : ℕ) : ℂ) / ((k : ℂ) * ((N + 1 - k : ℕ) : ℂ))) *
        ((k : ℂ) * ((N + 1 - k : ℕ) : ℂ) * (u : ℂ) ^ (N + 1) *
          ZetaRieszMatchedMiddle.sharedAtom u y N k (N + 1 - k)) := by
      field_simp
    _ = _ := by
      rw [he]
      unfold centralPairWeight centralHeadWeight
      push_cast
      field_simp

/-- The actual central block has an exact limiting signed cost. The
uniform prime-product errors are paid at arbitrary precision before the
finite order mass is evaluated. All zero-exposure assumptions remain explicit. -/
theorem tendsto_centralBlock_exact_cost (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      centralBlock (3 / 2 - rho.1.re) rho.1.im N)
      atTop (nhds ((analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
        ((Real.log (17 / 15) *
          (1 - 1 / (-2 * (3 / 2 - rho.1.re) * Real.log (3 / 2 - rho.1.re))) : ℝ) : ℂ))) := by
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : 0 < u := by dsimp only [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hup : u ≤ 3 / 5 := ZetaRieszHeadAdaptive.annular_radius_le_three_fifths huh
  have hp := FiniteWeightedUniformConvergence.tendsto_nonneg_weighted_sum
    centralOrders centralPairWeight
    (fun N k => ZetaRieszMatchedMiddle.weightedFinite u rho.1.im N k *
      ZetaRieszMatchedMiddle.weightedFinite u rho.1.im N (N + 1 - k))
    (b := (analyticZetaZeroMultiplicity rho : ℂ) ^ 2)
    (Eventually.of_forall fun N k _ => centralPairWeight_nonneg N k)
    tendsto_sum_centralPairWeight (fun ε hε =>
      (ZetaRieszCentralProductPhase.eventually_central_product_errors
        rho hrho hexposed huh hε).mono fun N h k hk => (h k hk).1)
  have hh := FiniteWeightedUniformConvergence.tendsto_nonneg_weighted_sum
    centralOrders (centralHeadWeight u)
    (fun N k => ZetaRieszMatchedMiddle.weightedFinite u rho.1.im N (k + 1) *
      ZetaRieszMatchedMiddle.weightedComplete u rho.1.im (N + 1 - k))
    (b := (analyticZetaZeroMultiplicity rho : ℂ) ^ 2)
    (Eventually.of_forall fun N k _ => centralHeadWeight_nonneg hu N k)
    (tendsto_sum_centralHeadWeight hu hup) (fun ε hε =>
      (ZetaRieszCentralProductPhase.eventually_central_product_errors
        rho hrho hexposed huh hε).mono fun N h k hk => (h k hk).2)
  have h := hp.sub hh
  have he : (Real.log (17 / 15) : ℂ) * (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 -
      ((Real.log (17 / 15) / (-2 * u * Real.log u) : ℝ) : ℂ) *
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 =
      (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
        ((Real.log (17 / 15) * (1 - 1 / (-2 * u * Real.log u)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 256] with N hN
  exact (normalized_centralBlock_eq u rho.1.im N hu hN).symm

/-- The complete head and the entire central matched block combine
into one exact negative harmonic cost, with no double-counted orders. -/
theorem tendsto_head_add_central_exact_cost (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      (ZetaRieszCompletedCarrier.completeHead (3 / 2 - rho.1.re) rho.1.im N +
        centralBlock (3 / 2 - rho.1.re) rho.1.im N))
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
        (paidHarmonicCost (3 / 2 - rho.1.re) : ℂ))) := by
  let u : ℝ := 3 / 2 - rho.1.re
  have hlog : Real.log (32 / 17 : ℝ) + Real.log (17 / 15 : ℝ) = Real.log (32 / 15 : ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    congr 1
    ring
  have he : -Real.log (32 / 17) / (-2 * u * Real.log u) +
      Real.log (17 / 15) * (1 - 1 / (-2 * u * Real.log u)) = -paidHarmonicCost u := by
    unfold paidHarmonicCost
    rw [← hlog]
    ring
  have hec := congrArg Complex.ofReal he
  dsimp only [u] at hec
  push_cast at hec
  have h := (tendsto_completeHead_exact_cost rho hrho hexposed
    (ZetaRieszHeadAdaptive.annular_radius_le_three_fifths huh)).add
    (tendsto_centralBlock_exact_cost rho hrho hexposed huh)
  convert! h using 1
  · funext N
    ring
  · congr 1
    push_cast
    linear_combination -(analyticZetaZeroMultiplicity rho : ℂ) ^ 2 * hec

/-- The two paid components have eventual real cost strictly below
the full multiplicity square. The source itself is linear in multiplicity;
this statement does not replace it by a square or assume simplicity. -/
theorem eventually_head_central_gt_neg_multiplicity_square (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, -(analyticZetaZeroMultiplicity rho : ℝ) ^ 2 <
      (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        (ZetaRieszCompletedCarrier.completeHead (3 / 2 - rho.1.re) rho.1.im N +
          centralBlock (3 / 2 - rho.1.re) rho.1.im N)).re := by
  have hu : (1 / 2 : ℝ) ≤ 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hc := paidHarmonicCost_lt_one hu huh
  have hm : (0 : ℝ) < analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have h := (Complex.continuous_re.tendsto _).comp
    (tendsto_head_add_central_exact_cost rho hrho hexposed huh)
  have he : (-(analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
      (paidHarmonicCost (3 / 2 - rho.1.re) : ℂ)).re =
      -(analyticZetaZeroMultiplicity rho : ℝ) ^ 2 * paidHarmonicCost (3 / 2 - rho.1.re) := by
    simp only [pow_two, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.natCast_re, Complex.natCast_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, add_zero, sub_zero, neg_zero]
  rw [he] at h
  have hgap : -(analyticZetaZeroMultiplicity rho : ℝ) ^ 2 <
      -(analyticZetaZeroMultiplicity rho : ℝ) ^ 2 * paidHarmonicCost (3 / 2 - rho.1.re) := by
    nlinarith [mul_pos (sq_pos_of_pos hm) (sub_pos.mpr hc)]
  exact h.eventually (eventually_gt_nhds hgap)

/-- After both evaluated components are removed, the original full
source is carried by exactly the actual three-prime sum, four-or-more-prime
sum and tapered wing. Their joint independent signed floor remains open. -/
theorem tendsto_three_unpaid_exact_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      (ZetaRieszCentralPrimeLayers.centralThreePrimeResponse 1 (3 / 2 - rho.1.re) rho.1.im N +
       ZetaRieszCentralPrimeLayers.centralHigherPrimeResponse 1 (3 / 2 - rho.1.re) rho.1.im N +
       ZetaRieszCompletedCarrier.taperedWing (3 / 2 - rho.1.re) rho.1.im N))
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ) +
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 * (paidHarmonicCost (3 / 2 - rho.1.re) : ℂ))) := by
  have hu : (0 : ℝ) < 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (ZetaRieszCompletedCarrier.tendsto_completedCarrier_exposed rho hrho hexposed huh).sub
    (tendsto_head_add_central_exact_cost rho hrho hexposed huh)
  have he : -(analyticZetaZeroMultiplicity rho : ℂ) -
      -(analyticZetaZeroMultiplicity rho : ℂ) ^ 2 * (paidHarmonicCost (3 / 2 - rho.1.re) : ℂ) =
      -(analyticZetaZeroMultiplicity rho : ℂ) +
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 * (paidHarmonicCost (3 / 2 - rho.1.re) : ℂ) := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards [ZetaRieszCompletedCarrier.eventually_completedCarrier_eq_prime_layers
    rho.1.im hu huh] with N hN
  rw [hN]
  ring

end
end RiemannGaussian.ZetaRieszCentralHarmonicCost
