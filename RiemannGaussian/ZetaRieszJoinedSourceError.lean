/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJoinedPhaseRadius
import RiemannGaussian.ZetaExposedMovingModes

/-!
# Quantitative payment of the whole joined source error

At an exposed zero, the genuine ordinary-prime array differs from its
selected constant source by an absolutely summable array. All competing
direct modes, reflected error modes, the pole, the analytic residual and
proper prime powers are included, also at logged orders zero and one.

The existing joined four-slot inequality then pays their entire insertion
at inverse order. The selected constant-array evaluation stays explicit.
This is a conditional source-error payment, not the independent 399/5000
upper bound needed by the floor.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszJoinedSourceError
open ZetaRieszPairPrimePowerPayment ZetaRieszSelbergSourceAudit
open ZetaRieszPairPrefixPayment

private theorem summable_norm_mode (c z : ℂ) (hz : ‖z‖<1) :
    Summable (fun n : ℕ => ‖c*z^(n+1)‖) := by
  have hs := summable_geometric_of_lt_one (norm_nonneg z) hz
  apply (hs.mul_left (‖c‖*‖z‖)).congr
  intro n
  rw [norm_mul,norm_pow,pow_succ]
  ring

private theorem summable_norm_finite_modes (S : Finset ℂ) (c z : ℂ→ℂ)
    (hz : ∀ i∈S,‖z i‖<1) :
    Summable (fun n : ℕ => ‖∑ i∈S,c i*z i^(n+1)‖) := by
  have hs : Summable (fun n : ℕ => ∑ i∈S,‖c i*z i^(n+1)‖) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      exact (summable_norm_mode (c i) (z i) (hz i (Finset.mem_insert_self _ _))).add
        (ih (fun j hj => hz j (Finset.mem_insert_of_mem hj)))
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => norm_sum_le _ _) hs

private theorem summable_norm_scaled_residual (r : Set.Ico (3/4 : ℝ) 1)
    (y : ℝ) {u : ℝ} (hu : 0<u) (hR : u<adaptiveZetaCanonicalRadius r y) :
    Summable (fun n : ℕ => ‖(u : ℂ)^(n+1)*adaptiveZetaResidualMoment r y n‖) := by
  obtain ⟨q,huq,hqR⟩ := exists_between hR
  have hq : 0<q := hu.trans huq
  have hr : 0≤u/q := div_nonneg hu.le hq.le
  have hr1 : u/q<1 := (div_lt_one hq).mpr huq
  let C := u*(8*localZetaLogHeight y/(adaptiveZetaCanonicalRadius r y-q))
  have hs : Summable (fun n : ℕ => C*((n : ℝ)*(u/q)^n+(u/q)^n)) := by
    have hg := summable_geometric_of_lt_one hr hr1
    have hn := summable_pow_mul_geometric_of_norm_lt_one (r := u/q) 1
      (by simpa only [Real.norm_of_nonneg hr] using hr1)
    simpa only [pow_one] using (hn.add hg).mul_left C
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hs
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu.le]
  apply (mul_le_mul_of_nonneg_left (norm_adaptiveZetaResidualMoment_le r y n hq hqR)
    (pow_nonneg hu.le _)).trans_eq
  dsimp only [C]
  rw [div_pow,pow_succ]
  ring

/-- The selected source is retained exactly. Only the genuine complete
von Mangoldt array's difference from it is absolutely summable. -/
theorem summable_mangoldt_source_error (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖) :
    Summable (fun n : ℕ => ‖mangoldtArray (3/2-rho.1.re) rho.1.im n+
      (analyticZetaZeroMultiplicity rho : ℂ)‖) := by
  let r := zetaRightHalfDiscParameter rho hrho
  let u : ℝ := 3/2-rho.1.re
  let S := adaptiveZetaZeroSupport r rho.1.im
  let d := fun z : ℂ => (MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
    (Metric.ball 0 (adaptiveZetaCanonicalRadius r rho.1.im)) z : ℂ)
  have hu : 0<u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u<1 := by dsimp [u]; linarith only [hrho]
  have hR : u<adaptiveZetaCanonicalRadius r rho.1.im := by
    have hh := (adaptiveZetaCanonicalRadius_spec r rho.1.im).1
    change 5/4-rho.1.re/2<_ at hh
    dsimp [u]
    linarith only [hh,hrho]
  have huC : ‖(u : ℂ)‖=u := by
    rw [Complex.norm_real,Real.norm_of_nonneg hu.le]
  have hs : Summable (fun n : ℕ =>
      ‖∑ z∈S.erase (-(u : ℂ)),d z*((u : ℂ)*(-z⁻¹))^(n+1)‖) := by
    apply summable_norm_finite_modes
    intro z hz
    obtain ⟨hne,hzS⟩ := Finset.mem_erase.mp hz
    have hdist := ZetaExposedPrimeFilter.canonical_support_norm_gt_exposed
      hexposed r hzS (by
        intro he
        apply hne
        rw [he]
        dsimp [u]
        push_cast
        ring)
    rw [norm_mul,norm_neg,norm_inv,huC,←div_eq_mul_inv]
    exact (div_lt_one (hu.trans hdist)).mpr hdist
  have hp : Summable (fun n : ℕ =>
      ‖((u : ℂ)*(1/2+Complex.I*(rho.1.im : ℂ))⁻¹)^(n+1)‖) := by
    have hy : 1<‖(1/2+Complex.I*(rho.1.im : ℂ))‖ :=
      (nontrivialZetaZero_one_lt_abs_im rho).trans_le (by
        simpa using Complex.abs_im_le_norm (1/2+Complex.I*(rho.1.im : ℂ)))
    have hmode : ‖(u : ℂ)*(1/2+Complex.I*(rho.1.im : ℂ))⁻¹‖<1 := by
      rw [norm_mul,norm_inv,huC,←div_eq_mul_inv]
      exact (div_lt_one (by linarith only [hy])).mpr (hu1.trans hy)
    simpa only [one_mul] using summable_norm_mode 1 _ hmode
  have hres := summable_norm_scaled_residual r rho.1.im hu hR
  have href : Summable (fun n : ℕ =>
      ‖∑ z∈S,d z*((u : ℂ)*(-starRingEnd ℂ z/
        (adaptiveZetaCanonicalRadius r rho.1.im : ℂ)^2))^(n+1)‖) := by
    exact summable_norm_finite_modes S d _ (fun z hz =>
      norm_mul_adaptiveZetaReflectedMode_lt_one r rho.1.im (by rw [huC]; exact hR) hz)
  have hsupport : (1 : Polynomial ℂ).support={0} := by
    ext k
    by_cases hk : k=0 <;> simp [Polynomial.mem_support_iff,Polynomial.coeff_one,hk]
  have he n : mangoldtArray u rho.1.im n+(analyticZetaZeroMultiplicity rho : ℂ)=
      -(∑ z∈S.erase (-(u : ℂ)),d z*((u : ℂ)*(-z⁻¹))^(n+1))+
        ((u : ℂ)*(1/2+Complex.I*(rho.1.im : ℂ))⁻¹)^(n+1)-
        (u : ℂ)^(n+1)*adaptiveZetaResidualMoment r rho.1.im n+
        ∑ z∈S,d z*((u : ℂ)*(-starRingEnd ℂ z/
          (adaptiveZetaCanonicalRadius r rho.1.im : ℂ)^2))^(n+1) := by
    have ht := ZetaExposedMovingModes.primeFilter_selected_split rho hrho (1 : Polynomial ℂ) n
    dsimp only at ht
    simp only [zetaPrimeLogFilter,adaptiveZetaResidualFilter,hsupport,Finset.sum_singleton,
      Polynomial.coeff_one_zero,one_mul,Nat.add_zero,Polynomial.eval_one,mul_one] at ht
    change mangoldtArray u rho.1.im n=_ at ht
    have hreflect : (u : ℂ)^(n+1)*adaptiveZetaReflectedFilter r rho.1.im 1 n=
        ∑ z∈S,d z*((u : ℂ)*(-starRingEnd ℂ z/
          (adaptiveZetaCanonicalRadius r rho.1.im : ℂ)^2))^(n+1) := by
      simp only [adaptiveZetaReflectedFilter,Polynomial.eval_one,mul_one,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      dsimp only [d]
      rw [mul_pow]
      ring
    rw [ht]
    change -(analyticZetaZeroMultiplicity rho : ℂ)-
      (∑ z∈S.erase (-(u : ℂ)),d z*((u : ℂ)*(-z⁻¹))^(n+1))+
      (u : ℂ)^(n+1)*((1/2+Complex.I*(rho.1.im : ℂ))⁻¹^(n+1)-
        adaptiveZetaResidualMoment r rho.1.im n+adaptiveZetaReflectedFilter r rho.1.im 1 n)+
      (analyticZetaZeroMultiplicity rho : ℂ)=_
    rw [mul_add,mul_sub,hreflect,mul_pow]
    ring
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (((hs.add hp).add hres).add href)
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add _ le_rfl
  apply (norm_sub_le _ _).trans
  apply add_le_add _ le_rfl
  simpa only [norm_neg] using norm_add_le
    (-(∑ z∈S.erase (-(u : ℂ)),d z*((u : ℂ)*(-z⁻¹))^(n+1)))
    (((u : ℂ)*(1/2+Complex.I*(rho.1.im : ℂ))⁻¹)^(n+1))

/-- Proper prime powers have their independent geometric price. The
ordinary-prime source error includes every low logged order as well. -/
theorem summable_ordinary_source_error (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    Summable (fun n : ℕ => ‖ordinaryArray (3/2-rho.1.re) rho.1.im n+
      (analyticZetaZeroMultiplicity rho : ℂ)‖) := by
  let u := 3/2-rho.1.re
  have hu : 0≤u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hd : Summable (fun n : ℕ =>
      ‖ordinaryArray u rho.1.im n-mangoldtArray u rho.1.im n‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_array_difference_le hu hU rho.1.im n)
    exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ)≤10001/15000)
      (by norm_num : (10001/15000 : ℝ)<1)).mul_left _
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (hd.add (summable_mangoldt_source_error rho hrho hexposed))
  have he : ordinaryArray u rho.1.im n+(analyticZetaZeroMultiplicity rho : ℂ)=
      (ordinaryArray u rho.1.im n-mangoldtArray u rho.1.im n)+
        (mangoldtArray u rho.1.im n+(analyticZetaZeroMultiplicity rho : ℂ)) := by ring
  rw [he]
  exact norm_add_le _ _

/-- One finite price for every genuine ordinary-prime source-error
order. Its finiteness as a norm sum is proved under exposure above. -/
def sourceErrorMass (rho : NontrivialZetaZero) : ℝ :=
  ∑' n : ℕ,‖ordinaryArray (3/2-rho.1.re) rho.1.im n+
    (analyticZetaZeroMultiplicity rho : ℂ)‖

theorem sourceErrorMass_nonneg (rho : NontrivialZetaZero) : 0 ≤ sourceErrorMass rho :=
  tsum_nonneg (fun _ => norm_nonneg _)

/-- No low logged order is discarded: every finite prefix is bounded
by the same full source-error mass. -/
theorem sum_source_error_le (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling) (S : Finset ℕ) :
    (∑ n∈S,‖ordinaryArray (3/2-rho.1.re) rho.1.im n+
      (analyticZetaZeroMultiplicity rho : ℂ)‖) ≤ sourceErrorMass rho :=
  (summable_ordinary_source_error rho hrho hexposed hU).sum_le_tsum S
    (fun _ _ => norm_nonneg _)

/-- The entire joined four-slot difference has an explicit inverse-order
price. It retains the selected source, arbitrary multiplicity and all
logged orders; no complete-leg inference through a hard mask is used. -/
theorem norm_joined_sub_selected_le (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    {N : ℕ} (hN : 65536≤N) :
    ‖harmonicEvaluation (ordinaryArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re) N-
      harmonicEvaluation (fun _ => -(analyticZetaZeroMultiplicity rho : ℂ))
        (3/2-rho.1.re) N‖≤
      22*((analyticZetaZeroMultiplicity rho : ℝ)+sourceErrorMass rho)*
        sourceErrorMass rho/(N : ℝ) := by
  let m := analyticZetaZeroMultiplicity rho
  let D := sourceErrorMass rho
  have hD : 0≤D := sourceErrorMass_nonneg rho
  have hC : 0≤(m : ℝ)+D := add_nonneg (Nat.cast_nonneg _) hD
  have ho k : ‖ordinaryArray (3/2-rho.1.re) rho.1.im k‖≤(m : ℝ)+D := by
    have he := sum_source_error_le rho hrho hexposed hU {k}
    simp only [Finset.sum_singleton] at he
    have hi : ordinaryArray (3/2-rho.1.re) rho.1.im k=
        (ordinaryArray (3/2-rho.1.re) rho.1.im k+(m : ℂ))-(m : ℂ) := by ring
    rw [hi]
    apply ((norm_sub_le _ _).trans (add_le_add he le_rfl)).trans_eq
    rw [Complex.norm_natCast]
    ring
  have hm : ∀ _ : ℕ,‖(-(m : ℂ))‖≤(m : ℝ)+D := by
    intro _
    rw [norm_neg,Complex.norm_natCast]
    linarith only [hD]
  have hu : 1/2≤3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  exact (norm_harmonicEvaluation_sub_le _ _ hC ho hm hu hU hN).trans
    ((mul_le_mul_of_nonneg_left (by
      simpa only [sub_neg_eq_add] using sum_source_error_le rho hrho hexposed hU
        (Finset.range (N+2))) (by positivity)).trans_eq (by dsimp only [m,D]; ring))

/-- The SAME literal retained signed main is controlled around its
selected-source evaluation. Whole completion and the square diagonal
are spent once; the rest is the joint inverse-order source-error cost. -/
theorem norm_prefix_sub_selected_le (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|rho.1.im|) {N : ℕ} (hN : 65536≤N) :
    ‖prefixPairDefect (3/2-rho.1.re) rho.1.im N-
      harmonicEvaluation (fun _ => -(analyticZetaZeroMultiplicity rho : ℂ))
        (3/2-rho.1.re) N‖≤
      ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
        ZetaRieszPairJointQuadratic.squareBudget (3/2-rho.1.re) N+
        22*((analyticZetaZeroMultiplicity rho : ℝ)+sourceErrorMass rho)*
          sourceErrorMass rho/(N : ℝ) := by
  have hu : 1/2≤3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (harmonicEvaluation (ordinaryArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re) N) _).trans
      (add_le_add (ZetaRieszJoinedPhaseRadius.norm_prefix_sub_ordinary_le hu hU hy hN)
        (norm_joined_sub_selected_le rho hrho hexposed hU hN))

/-- Two-sided REAL control of the whole retained main. The selected
evaluation remains signed; this does not assert the independent floor. -/
theorem abs_re_prefix_sub_selected_le (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|rho.1.im|) {N : ℕ} (hN : 65536≤N) :
    |(prefixPairDefect (3/2-rho.1.re) rho.1.im N).re-
      (harmonicEvaluation (fun _ => -(analyticZetaZeroMultiplicity rho : ℂ))
        (3/2-rho.1.re) N).re|≤
      ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
        ZetaRieszPairJointQuadratic.squareBudget (3/2-rho.1.re) N+
        22*((analyticZetaZeroMultiplicity rho : ℝ)+sourceErrorMass rho)*
          sourceErrorMass rho/(N : ℝ) := by
  simpa only [Complex.sub_re] using (Complex.abs_re_le_norm _).trans
    (norm_prefix_sub_selected_le rho hrho hexposed hU hy hN)

/-- The new source-error price vanishes at the explicit inverse-order
rate. Its unknown height-dependent mass is NOT certified as a small
numeric constant. -/
theorem tendsto_source_error_price (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ =>
      22*((analyticZetaZeroMultiplicity rho : ℝ)+sourceErrorMass rho)*
        sourceErrorMass rho/(N : ℝ)) atTop (𝓝 0) := by
  simpa only [mul_zero,div_eq_mul_inv,one_div,one_mul] using
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (22*((analyticZetaZeroMultiplicity rho : ℝ)+sourceErrorMass rho)*sourceErrorMass rho)

end RiemannGaussian.ZetaRieszJoinedSourceError
