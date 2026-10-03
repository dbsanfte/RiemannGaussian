/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszGlobalHeadCentralPayment

/-!
# Fund partial phase periods for the whole retained signed boundary

Only constant-width total-log edges are norm-paid. The complete interior
periods retain all counts, raw unallocated high owners and the SAME head
with their full phases. No bound for that interior signed sum is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszGlobalPeriodEdgePayment
open LogarithmicDeviation ZetaArithmeticLogWindow
open ZetaRieszGlobalCentralPayment ZetaRieszGlobalBoundaryPruning
open ZetaRieszGlobalHeadCentralPayment ZetaRieszBalancedRadialPayment
open ZetaRieszPrimeCountFrequency

/-- Tilt bound with a FIXED additive displacement in total logarithm.
The displacement changes only the finite constant, not the geometric rate. -/
theorem norm_normalized_sum_with_offset (S : Finset ℕ) (a : ℕ→ℂ)
    (ha : ∀ n∈S,‖a n‖≤zetaMoebiusLogMajorant n)
    {N : ℕ} (hN : 0<N) (y : ℝ) {U x σ D : ℝ}
    (hU : 0<U) (hx : 0<x) (hσ : 1<σ)
    (hlog : ∀ n∈S,(σ-3/2+x⁻¹)*log n≤
      (N : ℝ)*((σ-3/2+x⁻¹)*x)+D) :
    ‖(U : ℂ)^(N+1)*∑ n∈S,a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖≤
      (U*(x*exp ((σ-3/2+x⁻¹)*x)))^N*
        (exp D*(U*tiltConstant (1 : Polynomial ℂ) x⁻¹ σ)) := by
  have hNr : (N : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
  have hb := norm_sum_filter_of_log_bound S a ha (1 : Polynomial ℂ) N y σ x⁻¹
    (((σ-3/2+x⁻¹)*x)+D/N) hσ (inv_pos.mpr hx) (by
      intro n hn
      convert hlog n hn using 1
      field_simp [hNr])
  simp only [SquarefreeEulerQuadratic.primeFilterKernel_one,inv_inv] at hb
  have he : (exp (((σ-3/2+x⁻¹)*x)+D/N))^N=
      (exp ((σ-3/2+x⁻¹)*x))^N*exp D := by
    rw [←exp_nat_mul,←exp_nat_mul,←exp_add]
    congr 1
    field_simp [hNr]
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hU.le]
  have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg hU.le (N+1))
  apply hm.trans_eq
  rw [pow_succ,mul_pow,he,mul_pow]
  ring

/-- Remove at most one unit of total logarithm at either central edge.
The two intervals are exact; no factorial allocation or prime mask changes. -/
def interiorLabels (S : Finset ℕ) (N : ℕ) : Finset ℕ :=
  S.filter (fun n => (1971/1000 : ℝ)*N+1<log n ∧
    log n≤(2029/1000 : ℝ)*N-1)

/-- ONE constant pays both displaced edges uniformly over all heights,
counts, coefficients and support masks. This estimates ONLY the edges. -/
theorem exists_displaced_edge_bound :
    ∃ C : ℝ,0≤C ∧ ∀ (N : ℕ) (S : Finset ℕ) (a : ℕ→ℂ),
      64≤N → (∀ n∈S,‖a n‖≤zetaMoebiusLogMajorant n) →
      ∀ (y u : ℝ),0≤u → u≤ZetaRieszWideOwnerAudit.radiusCeiling →
        ‖(u : ℂ)^(N+1)*((∑ n∈S,a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
          ∑ n∈interiorLabels S N,a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)‖≤
            ZetaRieszLargeOrderCore.rate^N*C := by
  let U := ZetaRieszWideOwnerAudit.radiusCeiling
  let σ := ZetaRieszLargeOrderCore.sigma
  let b₀ : ℝ := 1971/1000
  let b₁ : ℝ := 2029/1000
  let a₀ := σ-3/2+b₀⁻¹
  let a₁ := σ-3/2+b₁⁻¹
  let C₀ := exp a₀*(U*tiltConstant (1 : Polynomial ℂ) b₀⁻¹ σ)
  let C₁ := exp (-a₁)*(U*tiltConstant (1 : Polynomial ℂ) b₁⁻¹ σ)
  have hU : 0<U := by norm_num [U,ZetaRieszWideOwnerAudit.radiusCeiling]
  have hσ : 1<σ := by norm_num [σ,ZetaRieszLargeOrderCore.sigma]
  have hC₀ : 0≤C₀ := by
    dsimp only [C₀]
    exact mul_nonneg (exp_pos _).le (mul_nonneg hU.le (tiltConstant_nonneg _ (by norm_num [b₀])))
  have hC₁ : 0≤C₁ := by
    dsimp only [C₁]
    exact mul_nonneg (exp_pos _).le (mul_nonneg hU.le (tiltConstant_nonneg _ (by norm_num [b₁])))
  refine ⟨C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro N S a hN ha y u hu huU
  let low : Finset ℕ := S.filter (fun n => log (n : ℝ)≤b₀*N+1)
  let high : Finset ℕ := S.filter (fun n => b₁*N-1<log (n : ℝ))
  have hl := norm_normalized_sum_with_offset low a
    (fun n hn => ha n (Finset.mem_filter.mp hn).1) (by omega : 0<N) y hU
    (by norm_num [b₀] : 0<b₀) hσ (D:=a₀) (by
      intro n hn
      have h := mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hn).2
        (by norm_num [a₀,b₀,σ,ZetaRieszLargeOrderCore.sigma] : 0≤a₀)
      change a₀*log n≤(N : ℝ)*(a₀*b₀)+a₀
      nlinarith only [h])
  have hh := norm_normalized_sum_with_offset high a
    (fun n hn => ha n (Finset.mem_filter.mp hn).1) (by omega : 0<N) y hU
    (by norm_num [b₁] : 0<b₁) hσ (D:=-a₁) (by
      intro n hn
      have h := mul_le_mul_of_nonpos_left (Finset.mem_filter.mp hn).2.le
        (by norm_num [a₁,b₁,σ,ZetaRieszLargeOrderCore.sigma] : a₁≤0)
      change a₁*log n≤(N : ℝ)*(a₁*b₁)-a₁
      nlinarith only [h])
  have he : (∑ n∈S,a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
      ∑ n∈interiorLabels S N,a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n=
        (∑ n∈low,a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)+
        ∑ n∈high,a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
    have hn : (64 : ℝ)≤N := by exact_mod_cast hN
    have hn0 : (N : ℝ)≠0 := by linarith only [hn]
    have h₀ : (b₀+1/(N : ℝ))*N=b₀*N+1 := by field_simp
    have h₁ : (b₁-1/(N : ℝ))*N=b₁*N-1 := by field_simp
    have hab : b₀+1/(N : ℝ)≤b₁-1/(N : ℝ) := by
      apply (mul_le_mul_iff_left₀ (show (0 : ℝ)<N by linarith only [hn])).mp
      rw [h₀,h₁]
      dsimp only [b₀,b₁]
      nlinarith only [hn]
    have he := sum_sub_deviationBand S
      (fun n => a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n) hab N
    simpa only [interiorLabels,low,high,deviationBand,h₀,h₁,b₀,b₁] using he
  apply (sourceScale_norm_mono hu huU N _).trans
  rw [he,mul_add]
  apply (norm_add_le _ _).trans
  have h₀ := pow_le_pow_left₀ (by positivity) ZetaRieszLargeOrderCore.lower_rate_lt.le N
  have h₁ := pow_le_pow_left₀ (by positivity) ZetaRieszLargeOrderCore.upper_rate_lt.le N
  calc
    _ ≤ _ := add_le_add hl hh
    _ ≤ ZetaRieszLargeOrderCore.rate^N*C₀+ZetaRieszLargeOrderCore.rate^N*C₁ :=
      add_le_add (mul_le_mul_of_nonneg_right h₀ hC₀) (mul_le_mul_of_nonneg_right h₁ hC₁)
    _ = _ := by ring

/-- Full logarithmic period of the literal phase, for either ordinate sign. -/
def periodWidth (y : ℝ) : ℝ := 2*Real.pi/|y|

/-- Deterministic left endpoint of the period containing an integer label. -/
def periodLower (y : ℝ) (n : ℕ) : ℝ :=
  (⌊log (n : ℝ)/periodWidth y⌋ : ℤ)*periodWidth y

/-- Deterministic right endpoint; no phase is frozen inside a period. -/
def periodUpper (y : ℝ) (n : ℕ) : ℝ := periodLower y n+periodWidth y

/-- Retain complete periods contained in the ORIGINAL central window.
Every prime/count/physical/factorial mask stays in the input support. -/
def completePeriodLabels (S : Finset ℕ) (N : ℕ) (y : ℝ) : Finset ℕ :=
  S.filter (fun n => (1971/1000 : ℝ)*N≤periodLower y n ∧
    periodUpper y n≤(2029/1000 : ℝ)*N)

theorem periodWidth_bounds {y : ℝ} (hy : 54≤|y|) :
    0<periodWidth y ∧ periodWidth y≤1 := by
  have ha : 0 < |y| := by linarith only [hy]
  unfold periodWidth
  refine ⟨div_pos (by positivity) ha,?_⟩
  apply (div_le_one ha).mpr
  linarith only [pi_lt_four,hy]

/-- Exact phase-period bracket, keeping the actual logarithm in the phase. -/
theorem period_log_bracket {y : ℝ} (hy : 54≤|y|) (n : ℕ) :
    periodLower y n≤log n ∧ log n<periodUpper y n := by
  have hw := (periodWidth_bounds hy).1
  have hl := mul_le_mul_of_nonneg_right (Int.floor_le (log (n : ℝ)/periodWidth y)) hw.le
  have hh := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (log (n : ℝ)/periodWidth y)) hw
  rw [div_mul_cancel₀ _ hw.ne'] at hl hh
  exact ⟨hl,by simpa only [periodUpper,periodLower,add_mul,one_mul] using hh⟩

/-- Every label a unit away from the two central edges belongs to a
complete phase period. This applies simultaneously to ALL count classes. -/
theorem interiorLabels_subset_completePeriods (S : Finset ℕ) (N : ℕ)
    {y : ℝ} (hy : 54≤|y|) :
    interiorLabels S N⊆completePeriodLabels S N y := by
  intro n hn
  obtain ⟨hn,hl,hh⟩ := Finset.mem_filter.mp hn
  have hw := (periodWidth_bounds hy).2
  have hp := period_log_bracket hy n
  refine Finset.mem_filter.mpr ⟨hn,?_,?_⟩
  · unfold periodUpper at hp
    linarith only [hp.2,hl,hw]
  · unfold periodUpper
    linarith only [hp.1,hh,hw]

/-- Partial periods and every exterior endpoint have a single uniform
geometric payment. No norm is taken on any complete interior period. -/
theorem exists_whole_period_edge_bound :
    ∃ C : ℝ,0≤C ∧ ∀ (N : ℕ) (S : Finset ℕ) (a : ℕ→ℂ),
      64≤N → (∀ n∈S,‖a n‖≤zetaMoebiusLogMajorant n) →
      ∀ (y u : ℝ),54≤|y| → 0≤u → u≤ZetaRieszWideOwnerAudit.radiusCeiling →
        ‖(u : ℂ)^(N+1)*((∑ n∈S,a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
          ∑ n∈completePeriodLabels S N y,a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)‖≤
            ZetaRieszLargeOrderCore.rate^N*C := by
  obtain ⟨C,hC,hb⟩ := exists_displaced_edge_bound
  refine ⟨C,hC,?_⟩
  intro N S a hN ha y u hy hu hU
  let E := S\completePeriodLabels S N y
  have he : interiorLabels E N=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    obtain ⟨hn,hl,hh⟩ := Finset.mem_filter.mp hn
    have hd := Finset.mem_sdiff.mp hn
    have hi : n∈interiorLabels S N := Finset.mem_filter.mpr ⟨hd.1,hl,hh⟩
    exact hd.2 (interiorLabels_subset_completePeriods S N hy hi)
  have hp := hb N E a hN (fun n hn => ha n (Finset.mem_sdiff.mp hn).1) y u hu hU
  rw [he,Finset.sum_empty,sub_zero] at hp
  have hs := Finset.sum_sdiff (show completePeriodLabels S N y⊆S from Finset.filter_subset _ _)
    (f:=fun n => a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)
  have hs' : (∑ n∈S,a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
      (∑ n∈completePeriodLabels S N y,a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)=
        ∑ n∈E,a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
    exact (eq_sub_of_add_eq hs).symm
  rw [hs']
  exact hp

/-- The finite constant in the uniform partial-period theorem. -/
def periodEdgeConstant : ℝ := Classical.choose exists_whole_period_edge_bound

theorem periodEdgeConstant_nonneg : 0≤periodEdgeConstant :=
  (Classical.choose_spec exists_whole_period_edge_bound).1

/-- Whole retained signed boundary on complete interior periods, including
ordinary primes, semiprimes, raw high owners at ALL counts and SAME head.
Only exterior/partial periods are omitted, with a separate proved payment. -/
def wholePeriodBoundary (u y : ℝ) (j : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  (completionTerm u y N (completePeriodLabels (primeLabels N) N y)+
    completionTerm u y N (completePeriodLabels (semiprimeLabels N) N y)+
    completionTerm u y N (completePeriodLabels (rawHighLabels j) N y)+
    (u : ℂ)^(N+1)*∑ n∈completePeriodLabels (headLabels u N) N y,
      headCoefficient u N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re

/-- The new budget pays FOUR literal edge families once each and never
prices their complete-period interior. Its constant is not numerically set. -/
def wholePeriodBudget (j : ℕ) : ℝ :=
  4*(ZetaRieszLargeOrderCore.rate^(dyadicMomentOrder j)*periodEdgeConstant)

theorem wholePeriodBudget_tendsto : Tendsto wholePeriodBudget atTop (𝓝 0) := by
  change Tendsto (fun j => 4*(ZetaRieszLargeOrderCore.rate^(dyadicMomentOrder j)*
    periodEdgeConstant)) atTop (𝓝 0)
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one
    ZetaRieszLargeOrderCore.rate_bounds.1.le ZetaRieszLargeOrderCore.rate_bounds.2).mul_const
      periodEdgeConstant).comp tendsto_dyadicMomentOrder
  simpa only [wholePeriodBudget,Function.comp_def,zero_mul,mul_zero] using h.const_mul 4

/-- Direct signed control of every partial-period boundary in the actual
pruned source ledger. Count classes and head remain joined in the interior. -/
theorem pruned_sub_wholePeriod_bound {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {j : ℕ}
    (hN : 65536≤dyadicMomentOrder j) {y : ℝ} (hy : 54≤|y|) :
    |(prunedBoundary u y j).re-wholePeriodBoundary u y j|≤wholePeriodBudget j := by
  let N := dyadicMomentOrder j
  let e := ZetaRieszLargeOrderCore.rate^N*periodEdgeConstant
  have hb := (Classical.choose_spec exists_whole_period_edge_bound).2
  have hp (S : Finset ℕ) :
      |(completionTerm u y N S).re-
        (completionTerm u y N (completePeriodLabels S N y)).re|≤e := by
    have h := hb N S (ZetaRieszGlobalBulkPayment.completedCoefficient
      (SquarefreeVaughanLogSource.length u N)) (by omega : 64≤N)
      (fun n _ => completedCoefficient_norm_le (SquarefreeVaughanLogSource.length_pos u N) n)
      y u hy (by linarith : 0≤u) hU
    have he := (Complex.abs_re_le_norm _).trans h
    simpa only [completionTerm,mul_sub,Complex.sub_re,e,periodEdgeConstant] using he
  have hh := hb N (headLabels u N) (headCoefficient u N) (by omega : 64≤N)
    (fun n hn => headCoefficient_majorant hu hU hN hn) y u hy (by linarith : 0≤u) hU
  rw [mul_sub,←ZetaRieszGlobalHeadCentralPayment.originalHead_eq_label_sum
    (by omega : 64≤N) y] at hh
  have hr := (Complex.abs_re_le_norm _).trans hh
  simp only [Complex.sub_re,ZetaRieszPrimeHeadPolePayment.originalHead_re] at hr
  have hp₁ := hp (primeLabels N)
  have hp₂ := hp (semiprimeLabels N)
  have hp₃ := hp (rawHighLabels j)
  apply abs_le.mpr
  unfold prunedBoundary wholePeriodBoundary wholePeriodBudget
  simp only [Complex.add_re,Complex.ofReal_re]
  dsimp only [e,N,periodEdgeConstant] at hp₁ hp₂ hp₃ hr ⊢
  constructor <;> linarith only [(abs_le.mp hp₁).1,(abs_le.mp hp₁).2,
    (abs_le.mp hp₂).1,(abs_le.mp hp₂).2,(abs_le.mp hp₃).1,(abs_le.mp hp₃).2,
    (abs_le.mp hr).1,(abs_le.mp hr).2]

/-- Spend the global partial-period saving inside the ORIGINAL native
floor. The exact remaining arithmetic target is the signed complete-period
boundary <=399/5000+o(1); that inequality is NOT assumed here. -/
theorem eventually_native_wholePeriod_bound {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      |((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
          (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re+
        wholePeriodBoundary u y j|≤nativePrunedBudget u y j+wholePeriodBudget j := by
  filter_upwards [eventually_native_pruned_bound hu hU hy,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (65536 : ℕ))] with j hn hj
  have hp := pruned_sub_wholePeriod_bound (by linarith : 1/2≤u) hU hj hy
  apply abs_le.mpr
  constructor <;> linarith only [(abs_le.mp hn).1,(abs_le.mp hn).2,
    (abs_le.mp hp).1,(abs_le.mp hp).2]

/-- The period boundary is source-equivalent to the SAME native joint
carrier with opposite sign; only the proved errors tend to zero. -/
theorem tendsto_native_plus_wholePeriodBoundary {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (fun j =>
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
        (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re+
          wholePeriodBoundary u y j) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (by
    simpa only [add_zero] using (nativePrunedBudget_tendsto u y).add wholePeriodBudget_tendsto)
  simpa only [Real.norm_eq_abs] using eventually_native_wholePeriod_bound hu hU hy

/-- Explicit current floor ledger after every incomplete phase period
has been paid. A cofinal bound on the complete-period scalar remains OPEN. -/
theorem eventually_native_wholePeriod_floor {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      -wholePeriodBoundary u y j-(nativePrunedBudget u y j+wholePeriodBudget j)≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
          (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  filter_upwards [eventually_native_wholePeriod_bound hu hU hy] with j hj
  linarith only [(abs_le.mp hj).1]

end RiemannGaussian.ZetaRieszGlobalPeriodEdgePayment
