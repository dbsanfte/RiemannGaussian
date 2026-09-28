/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMultiPeriodSix
import RiemannGaussian.ZetaRieszPositiveFiveInterior
import RiemannGaussian.ZetaRieszSaddleCredit

/-!
# Uniform signed payments on a growing factorial saddle band

The original populations and their literal allocation are unchanged. These
estimates allow their disjoint phase-period credits to be accumulated across
a square-root width, rather than paying a fixed number of periods.
-/

namespace RiemannGaussian.ZetaRieszSaddleBand
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszCapacityPhaseBudget

/-- The square-root band and its fixed boundary offsets are sublinear. -/
theorem eventually_sqrt_add_one_le_mul {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.sqrt N+1 ≤ ε*N := by
  have ht := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [ht.eventually_ge_atTop (max 1 (2/ε))] with N hN
  have hs1 : 1 ≤ Real.sqrt N := (le_max_left _ _).trans hN
  have hsε : 2 ≤ ε*Real.sqrt N := by
    have hh := (div_le_iff₀ hε).mp (show 2/ε ≤ Real.sqrt N from (le_max_right _ _).trans hN)
    nlinarith only [hh]
  have hh := mul_le_mul_of_nonneg_right hsε (Real.sqrt_nonneg (N : ℝ))
  rw [mul_assoc,Real.mul_self_sqrt (Nat.cast_nonneg N)] at hh
  linarith only [hs1,hh]

/-- The literal factorial weight varies little over each short interval,
uniformly throughout a square-root saddle band. -/
theorem weight_ratio {N : ℕ} {η a b : ℝ}
    (hη : 0 < η) (hηu : η ≤ 1)
    (hN : 100*(Real.sqrt N+1) ≤ η*N)
    (ha : 2*N-1 ≤ a) (hau : a ≤ 2*N+Real.sqrt N+1)
    (hb : 2*N-1 ≤ b) (_hbu : b ≤ 2*N+Real.sqrt N+1)
    (hab : |b-a| ≤ 2) :
    Real.exp (-b/2)*b^(N+1)/N.factorial ≤
      (1+η)*(Real.exp (-a/2)*a^(N+1)/N.factorial) := by
  have hs : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hn : (100 : ℝ) ≤ N := by nlinarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hNa : η*(N : ℝ) ≤ η*a := mul_le_mul_of_nonneg_left (by linarith : (N : ℝ) ≤ a) hη.le
  have hl : -η/4 ≤ ((N : ℝ)+1)/a-1/2 := by
    have hh : 1/2-η/4 ≤ ((N : ℝ)+1)/a := (le_div_iff₀ ha0).mpr (by nlinarith)
    linarith
  have hu : ((N : ℝ)+1)/a-1/2 ≤ η/4 := by
    have hh : ((N : ℝ)+1)/a ≤ 1/2+η/4 := (div_le_iff₀ ha0).mpr (by nlinarith)
    linarith
  have hlog := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hb0 ha0)) (show 0 ≤ (N : ℝ)+1 by positivity)
  rw [Real.log_div hb0.ne' ha0.ne'] at hlog
  have he : (b-a)*(((N : ℝ)+1)/a-1/2) ≤ η/2 := by
    have hh := mul_le_mul hab (abs_le.mpr ⟨by linarith only [hl],hu⟩)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    rw [← abs_mul] at hh
    exact (le_abs_self _).trans (by nlinarith only [hh])
  have halg : ((N : ℝ)+1)*(b/a-1)-(b-a)/2 =
      (b-a)*(((N : ℝ)+1)/a-1/2) := by field_simp
  have hexp : -b/2+((N : ℝ)+1)*Real.log b ≤
      η/2+(-a/2+((N : ℝ)+1)*Real.log a) := by linarith
  have hsmall : Real.exp (η/2) ≤ 1+η := by
    apply (Real.exp_bound_div_one_sub_of_interval (by positivity : 0 ≤ η/2)
      (by linarith : η/2 < 1)).trans
    apply (div_le_iff₀ (by linarith : 0 < 1-η/2)).mpr
    nlinarith
  have hpow (x : ℝ) (hx : 0 < x) : x^(N+1) = Real.exp (((N : ℝ)+1)*Real.log x) := by
    rw [← Nat.cast_add_one,Real.exp_nat_mul,Real.exp_log hx]
  rw [hpow a ha0,hpow b hb0,← Real.exp_add,← Real.exp_add]
  calc
    _ ≤ Real.exp (η/2+(-a/2+((N : ℝ)+1)*Real.log a))/N.factorial :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = Real.exp (η/2)*(Real.exp (-a/2+((N : ℝ)+1)*Real.log a)/N.factorial) := by
      rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (by positivity)

/-- The same narrow rational cutoff bin holds across the growing band. -/
theorem eventually_cutoff_ratio {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 2*(N : ℝ)-1 ≤ t → t ≤ 2*N+Real.sqrt N+1 →
      (693/1000 : ℝ) ≤ SquarefreeVaughanLogSource.length u N/t ∧
      SquarefreeVaughanLogSource.length u N/t ≤ 1733/2500 := by
  have hUr : ZetaRieszWideOwnerAudit.radiusCeiling < Real.exp (-(27721/40000 : ℝ)) := by
    apply (Real.log_lt_iff_lt_exp (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])).mp
    have h := Real.log_le_sub_one_of_pos
      (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
        (0 : ℝ) < 2*ZetaRieszWideOwnerAudit.radiusCeiling)
    rw [Real.log_mul (by norm_num) (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])] at h
    dsimp [ZetaRieszWideOwnerAudit.radiusCeiling] at h ⊢
    linarith [Real.log_two_gt_d9]
  filter_upwards [ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (show 0 < u by linarith) (by norm_num : (0 : ℝ) ≤ 27721/40000)
    (hU.trans_lt hUr),eventually_ge_atTop (20000 : ℕ),
    eventually_sqrt_add_one_le_mul (by norm_num : (0 : ℝ) < 1/20000)] with N hlo hN hs t ht htu
  have hn : (20000 : ℝ) ≤ N := by exact_mod_cast hN
  have ht0 : 0 < t := by linarith
  have hhi := ZetaRieszHeadOrders.length_le_two_log_two hu (show 2 ≤ N by omega)
  constructor
  · apply (le_div_iff₀ ht0).mpr
    nlinarith only [hlo,htu,hs]
  · apply (div_le_iff₀ ht0).mpr
    nlinarith [Real.log_two_lt_d9]

/-- A quadratic logarithm bound retains the Gaussian saddle width. -/
theorem log_one_add_lower {x : ℝ} (hx : 0 ≤ x) :
    x-x^2/2 ≤ Real.log (1+x) := by
  apply le_trans _ (Real.le_log_one_add_of_nonneg hx)
  apply (le_div_iff₀ (by linarith : 0 < x+2)).mpr
  nlinarith [mul_nonneg hx (sq_nonneg x)]

/-- The old radial source credit remains valid across a full square-root width. -/
theorem radial_lower {N : ℕ} (hN : 1 ≤ N) {v : ℝ}
    (hv : (2 : ℝ)*N ≤ v) (hvu : v ≤ 2*N+Real.sqrt N) :
    Real.exp (-1)*(2 : ℝ)^N/(3*Real.sqrt N) ≤
      Real.exp (-v/2)*v^N/N.factorial := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hv0 : 0 < v := by linarith
  have hs := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hdiff : 0 ≤ v-2*(N : ℝ) := by linarith
  have hsq : (v-2*(N : ℝ))^2 ≤ N := by
    have h := pow_le_pow_left₀ hdiff (show v-2*(N : ℝ) ≤ Real.sqrt N by linarith) 2
    nlinarith only [h,hs]
  have hx : 0 ≤ (v-2*(N : ℝ))/(2*N) := by positivity
  have hlog := mul_le_mul_of_nonneg_left (log_one_add_lower hx) hn.le
  have harg : 1+(v-2*(N : ℝ))/(2*N) = v/(2*N) := by field_simp; ring
  rw [harg,Real.log_div hv0.ne' (by positivity : (2*(N : ℝ)) ≠ 0)] at hlog
  have halg : (N : ℝ)*((v-2*N)/(2*N)-((v-2*N)/(2*N))^2/2) =
      (v-2*N)/2-(v-2*N)^2/(8*N) := by field_simp; ring
  have hsave : (v-2*(N : ℝ))^2/(8*N) ≤ 1/8 :=
    (div_le_iff₀ (by positivity : 0 < 8*(N : ℝ))).mpr (by linarith)
  have hexp : -1+(-(N : ℝ)+(N : ℝ)*Real.log (2*N)) ≤ -v/2+(N : ℝ)*Real.log v := by
    rw [halg] at hlog
    linarith
  have hfac := ZetaRieszSaddleCredit.factorial_upper hN
  have heN : (Real.exp 1)^N = Real.exp (N : ℝ) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hprod : (Real.exp (-(N : ℝ))*(2*(N : ℝ))^N)*(3*Real.sqrt N) =
      (2 : ℝ)^N*(3*Real.sqrt N*((N : ℝ)/Real.exp 1)^N) := by
    rw [div_pow,heN,Real.exp_neg,mul_pow]
    ring
  have hbase : (2 : ℝ)^N/(3*Real.sqrt N) ≤
      Real.exp (-(N : ℝ))*(2*N)^N/N.factorial := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [hprod]
    exact mul_le_mul_of_nonneg_left hfac (by positivity)
  have hpow (x : ℝ) (hx : 0 < x) : x^N = Real.exp ((N : ℝ)*Real.log x) := by
    rw [Real.exp_nat_mul,Real.exp_log hx]
  have hweight : Real.exp (-1)*(Real.exp (-(N : ℝ))*(2*N)^N/N.factorial) ≤
      Real.exp (-v/2)*v^N/N.factorial := by
    rw [hpow _ (by positivity),hpow v hv0]
    calc
      _ = Real.exp (-1+(-(N : ℝ)+(N : ℝ)*Real.log (2*N)))/N.factorial := by
        simp only [Real.exp_add]; ring
      _ ≤ _ := by rw [← Real.exp_add]; exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexp) (by positivity)
  simpa only [mul_div_assoc] using
    (mul_le_mul_of_nonneg_left hbase (Real.exp_nonneg (-1))).trans hweight

/-- The moving factorial saddle gives an arbitrarily precise signed
prime period and an unsigned bound for coefficient variation. -/
theorem eventually_factorial_period {m : ℕ} (hm : 0 < m)
    {y α η : ℝ} (hy : 54 ≤ |y|) (hα : 0 < α)
    (hη : 0 < η) (hηu : η ≤ 1/100)
    (hsmall : Real.pi/(4*m*|y|) ≤ η/10)
    (hphase : |y| * (Real.pi/(4*m*|y|)) ≤ η) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ,
      2*(N : ℝ) ≤ v → v ≤ 2*N+Real.sqrt N → Real.cos (y*v) = -1 →
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (1+η)*V ∧
      ∀ b : ℝ, α*N+1 ≤ v-b →
      let w := fun p : ℕ => Real.exp (-(Real.log p+b)/2)*
        (Real.log p+b)^(N+1)/N.factorial
      let D := logPrimes (v-Real.pi/|y|-b) (2*Real.pi/|y|)
      |∑ p ∈ D, w p*(p : ℝ)⁻¹*Real.cos (y*(Real.log p+b))| ≤
        (64*η)*m*V*v*(Real.pi/(4*m*|y|))/(v-b) ∧
      (∑ p ∈ D, w p*(p : ℝ)⁻¹) ≤
        16*m*V*v*(Real.pi/(4*m*|y|))/(v-b) := by
  have hy0 : 0 < |y| := by linarith
  have hπ : Real.pi/|y| ≤ 1 := (div_le_iff₀ hy0).mpr (by linarith [Real.pi_lt_four])
  filter_upwards [ZetaRieszSaddlePeriod.eventually_weighted_period hm hy hα hη hηu hsmall hphase,
    eventually_sqrt_add_one_le_mul (by positivity : 0 < η/100),
    eventually_ge_atTop (1000 : ℕ)] with N hN hgap hlarge v hv hvu hpeak
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hratio : 100*(Real.sqrt N+1) ≤ η*N := by nlinarith only [hgap]
  have hv0 : 0 < v := by linarith
  let W : ℝ → ℝ := fun x => Real.exp (-(v+x/|y|)/2)*(v+x/|y|)^(N+1)/N.factorial
  have hb (x : ℝ) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
      2*(N : ℝ)-1 ≤ v+x/|y| ∧ v+x/|y| ≤ 2*N+Real.sqrt N+1 := by
    have hl := div_le_div_of_nonneg_right hx.1 hy0.le
    have hu := div_le_div_of_nonneg_right hx.2 hy0.le
    rw [neg_div] at hl
    constructor <;> linarith
  have hlocal (x : ℝ) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
      v-1 ≤ v+x/|y| ∧ v+x/|y| ≤ v+1 := by
    have hl := div_le_div_of_nonneg_right hx.1 hy0.le
    have hu := div_le_div_of_nonneg_right hx.2 hy0.le
    rw [neg_div] at hl
    constructor <;> linarith
  have hcont : Continuous W := by dsimp [W]; fun_prop
  obtain ⟨x₀,hx₀,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc (-Real.pi) Real.pi).Nonempty from ⟨0,by
      constructor <;> linarith [Real.pi_pos]⟩) hcont.continuousOn
  have hW : 0 < W x₀ := by
    have hpos : 0 < v+x₀/|y| := by linarith [(hb x₀ hx₀).1]
    dsimp [W]; positivity
  have hrad (x : ℝ) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
      W x₀ ≤ W x ∧ W x ≤ (1+η)*W x₀ :=
    ⟨hmin hx,weight_ratio hη (by linarith) hratio
      (hb x₀ hx₀).1 (hb x₀ hx₀).2 (hb x hx).1 (hb x hx).2
      (abs_le.mpr ⟨by linarith [(hlocal x hx).1,(hlocal x₀ hx₀).2],
        by linarith [(hlocal x hx).2,(hlocal x₀ hx₀).1]⟩)⟩
  let V := W x₀/v
  have hzero := hrad 0 (by constructor <;> linarith [Real.pi_pos])
  have he : W 0 = (Real.exp (-v/2)*v^N/N.factorial)*v := by
    dsimp [W]; rw [zero_div,add_zero,pow_succ]; ring
  rw [he] at hzero
  have hVeq : V*v = W x₀ := div_mul_cancel₀ _ hv0.ne'
  refine ⟨V,by dsimp [V]; positivity,?_,?_,?_⟩
  · exact (div_le_iff₀ hv0).mpr hzero.1
  · apply (mul_le_mul_iff_right₀ hv0).mp
    rw [← hVeq] at hzero
    nlinarith only [hzero.2]
  intro b hab
  dsimp only
  let w := fun p : ℕ => Real.exp (-(Real.log p+b)/2)*(Real.log p+b)^(N+1)/N.factorial
  have hh := hN v b (W x₀) w hpeak hab hW.le (by
    intro i hi p hp
    have hc := period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have hp' := (logPrimes_bounds hp).2
    let T := Real.log p+b
    have hTl : v-Real.pi/|y| ≤ T := by dsimp [T]; linarith [hc.1,hp'.1]
    have hTu : T ≤ v+Real.pi/|y| := by dsimp [T]; linarith [hc.2,hp'.2]
    have hx : (T-v)*|y| ∈ Set.Icc (-Real.pi) Real.pi := by
      constructor
      · have h := mul_le_mul_of_nonneg_right hTl hy0.le
        rw [sub_mul,div_mul_cancel₀ _ hy0.ne'] at h
        nlinarith only [h]
      · have h := mul_le_mul_of_nonneg_right hTu hy0.le
        rw [add_mul v (Real.pi/|y|),div_mul_cancel₀ _ hy0.ne'] at h
        nlinarith only [h]
    have hh := hrad ((T-v)*|y|) hx
    simpa only [W,mul_div_cancel_right₀ _ hy0.ne',add_sub_cancel,T] using hh)
  rw [← ZetaRieszPrimePeriodCancellation.sum_prime_period _ hm v b y hy0,← ZetaRieszPrimePeriodCancellation.sum_prime_period _ hm v b y hy0] at hh
  rw [← hVeq] at hh
  constructor
  · convert hh.1 using 1; ring
  · convert hh.2 using 1; ring

/-- Recovering the missing square-root factor strengthens the existing
source credit; no new carrier or changed arithmetic support is introduced. -/
theorem sourceCredit_le_scaled_margin {u y : ℝ} (hu : 0 ≤ u) (hy : y ≠ 0)
    {N m : ℕ} (hN : 1 ≤ N) (hm : 0 < m) {v : ℝ}
    (hv : (2 : ℝ)*N ≤ v) (hvu : v ≤ 2*N+Real.sqrt N) :
    2*Real.sqrt ((N : ℝ)+1)*ZetaRieszCentralReserve.sourceCredit u y N ≤
      u^(N+1)*((m : ℝ)/1000*(Real.exp (-v/2)*v^N/N.factorial)*
        (Real.pi/(4*m*|y|))) := by
  have hy0 : 0 < |y| := abs_pos.mpr hy
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hroot : Real.sqrt ((N : ℝ)+1)*Real.sqrt N ≤ (N : ℝ)+1 := by
    calc
      _ ≤ Real.sqrt ((N : ℝ)+1)*Real.sqrt ((N : ℝ)+1) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (by positivity)
  have hcompare : 2*Real.sqrt ((N : ℝ)+1)*
      (Real.exp (-1)*(2 : ℝ)^N/(6*((N : ℝ)+1))) ≤
      Real.exp (-1)*(2 : ℝ)^N/(3*Real.sqrt N) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_left hroot
      (show 0 ≤ 6*Real.exp (-1)*(2 : ℝ)^N by positivity)
    nlinarith only [h]
  have hs := mul_le_mul_of_nonneg_left
    (hcompare.trans (radial_lower hN hv hvu))
    (show 0 ≤ u^(N+1)*(m : ℝ)*(Real.pi/(4*m*|y|))/1000 by positivity)
  convert hs using 1 <;>
    (try simp only [ZetaRieszCentralReserve.sourceCredit]) <;>
    (try rw [pow_succ,mul_pow]) <;> (try field_simp) <;> first | rfl | ring


open ZetaRieszTransitionSixPeriod

private theorem cofactor_log_upper {v : ℝ} {a : ℕ} (ha : a ∈ cofactors v) :
    Real.log a ≤ (133/200 : ℝ)*v := by
  rcases Finset.mem_union.mp ha with ha | ha
  · obtain ⟨ha,_⟩ := Finset.mem_filter.mp ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have h := ZetaRieszBroadSixPeriod.cofactor_geometry ha
      have hv : 0 ≤ v := by nlinarith [Real.log_natCast_nonneg a,h.2.2.2.2.1]
      nlinarith [h.2.2.2.2.1]
    · have h := ZetaRieszBroadSixPeriod.cofactor_geometry ha
      have hv : 0 ≤ v := by nlinarith [Real.log_natCast_nonneg a,h.2.2.2.2.1]
      nlinarith [h.2.2.2.2.1]
  · obtain ⟨ha,_,_⟩ := Finset.mem_filter.mp ha
    have h := ZetaRieszBroadSixPeriod.cofactor_geometry ha
    nlinarith [h.2.2.2.2.1]

/-- The entire allocated six-prime residual has arbitrarily small signed
cost uniformly at every center of the growing saddle band. -/
theorem eventually_six_residual_small {y ε : ℝ} (hy : 54 ≤ |y|) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (v L : ℝ),
      2*(N : ℝ) ≤ v → v ≤ 2*N+Real.sqrt N → Real.cos (y*v) = -1 →
      (67/100 : ℝ)*v ≤ L →
      (∀ a ∈ cofactors v, ∀ p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|), p ∈ A) →
      |(∑ n ∈ population v y, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤
        ε*(Real.pi/(4*|y|))*(Real.exp (-v/2)*v^N/N.factorial) := by
  have hC : 0 < logMassConstant ∧ 0 < variationConstant := by
    have h := ZetaRieszBroadSixPeriod.mass_constants_pos
    exact ⟨mul_pos (by norm_num) h.1,mul_pos (by norm_num) h.2⟩
  have hCl := hC.1
  have hCv := hC.2
  let η := min (1/10000 : ℝ) (ε/(4000*logMassConstant))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηu : η ≤ 1/100 := (min_le_left _ _).trans (by norm_num)
  have hηε : 1000*η*logMassConstant ≤ ε/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4000*logMassConstant)).mp (min_le_right _ _ : η ≤ _)
    nlinarith only [hh]
  obtain ⟨m,hm,hsmall,hphase⟩ := ZetaRieszBroadSixPeriod.exists_precise_mesh hy hη
  have hr : Tendsto (fun v : ℝ => (720*logMassConstant+100*variationConstant)*v^(-(1/2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).const_mul
      (720*logMassConstant+100*variationConstant)
  obtain ⟨v₀,hv₀⟩ := eventually_atTop.mp (hr.eventually_lt_const (show 0 < ε/2 by positivity))
  filter_upwards [eventually_factorial_period hm hy
      (by norm_num : (0 : ℝ) < 1/2) hη hηu hsmall hphase,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop v₀,
    eventually_ge_atTop (1000 : ℕ)] with N hN hNv hlarge A v L hv hvu hpeak hLl hA
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hv100 : 100 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hvlarge : v₀ ≤ v := by linarith
  obtain ⟨V,hV,hbase,_,hperiod⟩ := hN v hv hvu hpeak
  let h := Real.pi/(4*m*|y|)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hy0 : 0 < |y| := by linarith
  have hh : 0 < h := by dsimp [h]; positivity
  have hrow (a : ℕ) (ha : a ∈ cofactors v) := fibre_bound A (N := N) hv100 hy hLl hV.le hη.le ha (hA a ha)
    (hperiod (Real.log a) (by have hd := cofactor_log_upper ha; linarith))
  have hsum : |(∑ n ∈ population v y, ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤
      ((m : ℝ)*V*h)*((1000*η/v+720*Real.sqrt (N+1)/v^2)*(logMassConstant*v)+
        (100/v)*(variationConstant*v^(1/2 : ℝ))) := by
    rw [sum_population hv100 hy,Complex.re_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum hrow).trans
    rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (mul_le_mul_of_nonneg_left (cofactor_log_mass hv0) (by positivity))
      (mul_le_mul_of_nonneg_left (cofactor_mass hv0) (by positivity))
  have hrat : v^(1/2 : ℝ)/v = v^(-(1/2 : ℝ)) := by
    have hh := Real.rpow_sub hv0 (1/2 : ℝ) 1
    norm_num at hh
    exact hh.symm
  have hroot : Real.sqrt (N+1)/v ≤ v^(-(1/2 : ℝ)) := by
    have hs : Real.sqrt (N+1) ≤ Real.sqrt v := Real.sqrt_le_sqrt (by linarith)
    have hh := div_le_div_of_nonneg_right hs hv0.le
    rw [Real.sqrt_eq_rpow v,hrat] at hh
    exact hh
  have hbudget : (1000*η/v+720*Real.sqrt (N+1)/v^2)*(logMassConstant*v)+
      (100/v)*(variationConstant*v^(1/2 : ℝ)) ≤ ε := by
    have he : (1000*η/v+720*Real.sqrt (N+1)/v^2)*(logMassConstant*v)+
        (100/v)*(variationConstant*v^(1/2 : ℝ)) =
        1000*η*logMassConstant+720*logMassConstant*(Real.sqrt (N+1)/v)+
          100*variationConstant*(v^(1/2 : ℝ)/v) := by field_simp
    rw [he,hrat]
    have hh := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 720*logMassConstant by positivity)
    have ht := hv₀ v hvlarge
    ring_nf at hh ht hηε ⊢
    linarith only [hh,ht,hηε,hε]
  apply hsum.trans
  have he : (m : ℝ)*h = Real.pi/(4*|y|) := by dsimp [h]; field_simp
  calc
    _ ≤ ((m : ℝ)*V*h)*ε := mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = ε*(Real.pi/(4*|y|))*V := by rw [← he]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbase (by positivity)
/-- Every moving owner stays in the original intermediate-prime mask. -/
theorem eventually_six_owner_mem {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ |y|) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, 2*(N : ℝ) ≤ v → v ≤ 2*N+Real.sqrt N →
      ∀ a ∈ cofactors v, ∀ p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|),
        p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N := by
  have hroom : u < Real.exp (-(137/200 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans (Real.exp_lt_exp.mpr (by norm_num)))
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)/(N : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,pow_one,one_mul,add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hl.eventually_lt_const (by norm_num : (0 : ℝ) < 1/4),
    ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
      (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200) hroom,
    eventually_sqrt_add_one_le_mul (by norm_num : (0 : ℝ) < 1/1000),
    eventually_ge_atTop (1000 : ℕ)] with N hlog hL hwide hN v hv hvu a ha p hp
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hgeo := fibre_geometry (by linarith : 100 ≤ v) hy ha hp
  have hd := cofactor_log_upper ha
  have hpb := logPrimes_bounds hp
  have hpi : Real.pi/|y| ≤ 1/16 :=
    (div_le_iff₀ (by linarith : 0 < |y|)).mpr (by nlinarith [Real.pi_lt_d4])
  apply (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mpr
  refine ⟨hgeo.1,?_,?_⟩
  · have hlg : 2*Real.log (N : ℝ) < (N : ℝ)/2 := by
      have hh := (div_lt_iff₀ hN0).mp hlog
      linarith only [hh]
    have hh : Real.log ((N^2 : ℕ) : ℝ) < Real.log p := by
      rw [Nat.cast_pow,Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [hpb.2.1,hd]
    exact_mod_cast (Real.log_lt_log_iff (by positivity : (0 : ℝ) < (N^2 : ℕ))
      (by exact_mod_cast hgeo.1.pos)).mp hh
  · have hpp : p ∈ (p*a).primeFactors := hgeo.1.mem_primeFactors (dvd_mul_right p a) hgeo.2.2.1.ne_zero
    have hm := hgeo.2.2.2.2.2.2 p hpp
    have htop : Real.log p < SquarefreeVaughanLogSource.length u N := by
      nlinarith [hgeo.2.2.2.2.2.1]
    have he : Real.log (((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) : ℝ) =
        SquarefreeVaughanLogSource.length u N := by
      simp only [SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hgeo.1.pos) (by positivity)).mp (he ▸ htop)

/-- The wider population is paid in the actual coupled residual carrier,
with its allocation cost absorbed locally. No separate source-scale
allocation error is needed for this population. -/
theorem eventually_six_population_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {m : ℕ} (hm : 0 < m)
    {y : ℝ} (hy : 54 ≤ |y|)
    (_hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (_hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      Real.cos (y*v) = -1 → 2*(N : ℝ) ≤ v → v ≤ 2*N+Real.sqrt N →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      population v y ⊆ ZetaRieszParityPacket.coreBand u N K ∧
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        |u^(N+1)*(∑ n ∈ population v y,
          ZetaRieszJointAllocation.residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
            (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤
          u^(N+1)*((m : ℝ)/100000*V*(Real.pi/(4*m*|y|))) := by
  have hroom : u < Real.exp (-(137/200 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans
      (Real.exp_lt_exp.mpr (by norm_num)))
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_six_residual_small hy (by norm_num : (0 : ℝ) < 1/100000)),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200) hroom),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually (eventually_six_owner_mem hu hU hy),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1000 : ℕ)),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_sqrt_add_one_le_mul (by norm_num : (0 : ℝ) < 1/1000)),
    eventually_ge_atTop (32 : ℕ)] with j hraw hL hA hN hwide hj
  intro v
  dsimp only
  intro hv hslo hshi hlo hhi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hv0 : 0 < v := by change 2*(N : ℝ) ≤ v at hslo; linarith
  have hv100 : 100 ≤ v := by change 2*(N : ℝ) ≤ v at hslo; linarith
  change 2*(137/200 : ℝ)*N ≤ L at hL
  have hLl : (67/100 : ℝ)*v ≤ L := by change v ≤ 2*(N : ℝ)+Real.sqrt N at hshi; linarith
  have hcore := population_subset_core j hj hu hU hy hv100 (by linarith) hlo hhi
  let V := Real.exp (-v/2)*v^N/N.factorial
  have hV : 0 < V := by dsimp [V]; positivity
  refine ⟨hcore,V,hV,le_rfl,?_⟩
  have hb := hraw (ZetaRieszAnnulusJoint.intermediatePrimes u N) v L hslo hshi hv hLl (hA v hslo hshi)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hy0 : 0 < |y| := by linarith
  rw [abs_mul,abs_of_nonneg (pow_nonneg (show 0 ≤ u by linarith) _)]
  apply (mul_le_mul_of_nonneg_left hb (pow_nonneg (show 0 ≤ u by linarith) _)).trans_eq
  congr 1
  dsimp only [V]
  field_simp
  dsimp only [N]
  ring


end
end RiemannGaussian.ZetaRieszSaddleBand
