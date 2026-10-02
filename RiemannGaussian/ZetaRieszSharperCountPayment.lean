/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszReducedCountPayment
import RiemannGaussian.ZetaRieszDirectPhaseFloor

/-!
# A global count payment below the previously retained ceiling

On the original schedule the full count tilt has logarithmic rate at
least 1/12 per moment order. This pays every count with 768*omega >= K,
including all physical/share/radial/allocation masks and all heights.
The cost is eventually C*(N+1)*exp(-N/200000), independently of zeros.

The original joined floor is compared directly with the remaining whole
signed sum below this ceiling. No favorable count credit or supply debit
is spent. The independent signed energy estimate below the ceiling is
still open; this is a paid population, not a proof of the numerical floor.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszSharperCountPayment
open ZetaRieszPrimeCountFrequency ZetaRieszPrimeCountMass
open ZetaRieszJointAllocation ZetaRieszAnnulusJoint ZetaRieszParityPacket
open ZetaRieszWideOwnerAudit ZetaRieszCofactorPhaseEnergy
open ZetaRieszPhaseOrbitPayment ZetaRieszCutoffPeriodFloor

/-- Sharper logarithmic count saving on the UNCHANGED dyadic schedule. -/
theorem dyadic_log_count_lower (j : ℕ) (hj : 64 ≤ j) :
    (dyadicMomentOrder j : ℝ)/12 ≤
      (dyadicPrimeCount j : ℝ)*log (dyadicPrimeCount j : ℝ) := by
  have htwo : (693/1000 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  have hjR : (64 : ℝ) ≤ j := by exact_mod_cast hj
  have hm := mul_le_mul_of_nonneg_left htwo
    (show (0 : ℝ) ≤ (j : ℝ)+3 by positivity)
  have hbase : (8 : ℝ)*((j : ℝ)+4)/12 ≤ ((j : ℝ)+3)*log 2 := by
    linarith only [hm,hjR]
  have hlog : log (dyadicPrimeCount j : ℝ) = ((j : ℝ)+3)*log 2 := by
    simp only [dyadicPrimeCount,Nat.cast_pow,Nat.cast_ofNat,log_pow,Nat.cast_add]
  have hN : (dyadicMomentOrder j : ℝ) =
      8*((j : ℝ)+4)*(dyadicPrimeCount j : ℝ) := by
    simp only [dyadicMomentOrder,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
  rw [hN,hlog]
  nlinarith only [mul_le_mul_of_nonneg_right hbase
    (Nat.cast_nonneg (α := ℝ) (dyadicPrimeCount j))]

/-- Every selected integer retains this fixed exponential count saving. -/
theorem sharper_count_power_saving (j k : ℕ) (hj : 64 ≤ j)
    (hk : dyadicPrimeCount j ≤ 768*k) :
    exp ((dyadicMomentOrder j : ℝ)/9216) ≤ (dyadicPrimeCount j : ℝ)^k := by
  have hK : (1 : ℝ) ≤ dyadicPrimeCount j := by
    exact_mod_cast (show 1 ≤ dyadicPrimeCount j by
      have := four_le_dyadicPrimeCount j; omega)
  have hlog := log_nonneg hK
  have hkR : (dyadicPrimeCount j : ℝ) ≤ 768*(k : ℝ) := by exact_mod_cast hk
  have hm := mul_le_mul_of_nonneg_right hkR hlog
  have hl : (dyadicMomentOrder j : ℝ)/9216 ≤
      (k : ℝ)*log (dyadicPrimeCount j : ℝ) := by
    linarith only [dyadic_log_count_lower j hj,hm]
  calc
    _ ≤ exp ((k : ℝ)*log (dyadicPrimeCount j : ℝ)) := exp_le_exp.mpr hl
    _ = _ := by rw [exp_nat_mul,exp_log (by linarith : (0 : ℝ)<dyadicPrimeCount j)]

/-- Join every selected label inside the tilted count moment first. -/
theorem sharper_count_mass_bound (S : Finset ℕ) (j : ℕ) (hj : 64 ≤ j)
    (hS : ∀ n ∈ S, Squarefree n)
    (hcount : ∀ n ∈ S, dyadicPrimeCount j ≤ 768*n.primeFactors.card)
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑ n ∈ S,(2 : ℝ)^n.primeFactors.card*exp (-sigma*log n)) ≤
      exp (2*(dyadicPrimeCount j : ℝ)*countMass sigma)/
        exp ((dyadicMomentOrder j : ℝ)/9216) := by
  apply (le_div_iff₀ (exp_pos _)).mpr
  calc
    _ = ∑ n ∈ S,(exp ((dyadicMomentOrder j : ℝ)/9216)*
        (2 : ℝ)^n.primeFactors.card)*exp (-sigma*log n) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ ∑ n ∈ S,((dyadicPrimeCount j : ℝ)^n.primeFactors.card*
        (2 : ℝ)^n.primeFactors.card)*exp (-sigma*log n) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (sharper_count_power_saving j _ hj (hcount n hn)) (by positivity)) (exp_pos _).le
    _ = ∑ n ∈ S,(2*(dyadicPrimeCount j : ℝ))^n.primeFactors.card*
        exp (-sigma*log n) := by
      exact Finset.sum_congr rfl (fun _ _ => by rw [mul_pow]; ring)
    _ ≤ _ := squarefree_count_mass_le_exp S hS hsigma (by positivity)

/-- The exact source, summable tilt and Euler slack have a negative
rate. This is a rational certificate, not a floating exponent check. -/
theorem count_rate_bound :
    (radiusCeiling/(499999/1000000 : ℝ))*exp (-1/9216+1/1000000) ≤
      exp (-1/200000 : ℝ) := by
  have hpos : (0 : ℝ) < radiusCeiling/(499999/1000000) := by norm_num [radiusCeiling]
  have hlog := log_le_sub_one_of_pos hpos
  have hr : radiusCeiling/(499999/1000000 : ℝ)-1-1/9216+1/1000000 ≤
      -(1/200000 : ℝ) := by norm_num [radiusCeiling]
  calc
    _ = exp (log (radiusCeiling/(499999/1000000 : ℝ))-1/9216+1/1000000) := by
      symm
      rw [show log (radiusCeiling/(499999/1000000 : ℝ))-1/9216+1/1000000 =
        log (radiusCeiling/(499999/1000000 : ℝ))+(-1/9216+1/1000000) by ring,
        exp_add,exp_log hpos]
    _ ≤ _ := exp_le_exp.mpr (by linarith only [hlog,hr])

/-- Independently pay the ENTIRE selected high-count sum, with arbitrary
correlated coefficients dominated by the existing literal majorant.
The eventual start is not evaluated; heights are unrestricted. -/
theorem eventually_sharper_count_sum_bound :
    ∀ᶠ j : ℕ in atTop, ∀ (S : Finset ℕ) (a : ℕ → ℂ) (y u : ℝ),
      0 ≤ u → u ≤ radiusCeiling →
      (∀ n ∈ S, ‖a n‖ ≤ 2*zetaMoebiusLogMajorant n) →
      (∀ n ∈ S, Squarefree n) →
      (∀ n ∈ S, log n ≤ (203/100 : ℝ)*dyadicMomentOrder j) →
      (∀ n ∈ S, dyadicPrimeCount j ≤ 768*n.primeFactors.card) →
      ‖(u : ℂ)^(dyadicMomentOrder j+1)*∑ n ∈ S,
        a n*zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n‖ ≤
        ((203/50 : ℝ)*radiusCeiling)*((dyadicMomentOrder j : ℝ)+1)*
          exp (-(dyadicMomentOrder j : ℝ)/200000) := by
  have hslack : 1 < exp (1/1000000 : ℝ) := by rw [one_lt_exp_iff]; norm_num
  filter_upwards [eventually_ge_atTop (64 : ℕ),
    eventually_exp_count_le_geometric (2*countMass (1000001/1000000)) hslack]
    with j hj hEuler S a y u hu hU ha hS hlog hcount
  let N := dyadicMomentOrder j
  have hU0 : 0 ≤ radiusCeiling := by norm_num [radiusCeiling]
  have hk := ZetaRieszReducedCountPayment.norm_partial_sum_mass_bound S a N y ha hS hlog
    (by norm_num : (0 : ℝ)<499999/1000000)
  have hm := sharper_count_mass_bound S j hj hS hcount
    (by norm_num : (1 : ℝ)<1000001/1000000)
  have hsigma : (3/2 : ℝ)-499999/1000000=1000001/1000000 := by norm_num
  rw [hsigma] at hk
  have hE : exp (2*(dyadicPrimeCount j : ℝ)*countMass (1000001/1000000)) ≤
      exp ((N : ℝ)/1000000) := by
    simpa only [N,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm,one_mul,← exp_nat_mul] using hEuler
  have hmain := hk.trans (mul_le_mul_of_nonneg_left hm (by positivity))
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu]
  apply (mul_le_mul_of_nonneg_left hmain (pow_nonneg hu _)).trans
  calc
    _ ≤ radiusCeiling^(N+1)*(((203/50 : ℝ)*(N : ℝ)*(499999/1000000 : ℝ)⁻¹^N)*
        (exp ((N : ℝ)/1000000)/exp ((N : ℝ)/9216))) := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ hu hU _
      · exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hE (exp_pos _).le) (by positivity)
      · positivity
      · norm_num [radiusCeiling]
    _ = ((203/50 : ℝ)*radiusCeiling)*(N : ℝ)*
        ((radiusCeiling/(499999/1000000 : ℝ))*exp (-1/9216+1/1000000))^N := by
      rw [← exp_sub,mul_pow,div_pow,← exp_nat_mul]
      rw [show (N : ℝ)*(-1/9216+1/1000000)=(N : ℝ)/1000000-(N : ℝ)/9216 by ring]
      simp only [pow_succ,inv_pow]
      ring
    _ ≤ ((203/50 : ℝ)*radiusCeiling)*(N : ℝ)*exp (-1/200000 : ℝ)^N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) count_rate_bound _) (by positivity)
    _ ≤ _ := by
      rw [← exp_nat_mul,show (N : ℝ)*(-1/200000)=-(N : ℝ)/200000 by ring]
      gcongr
      dsimp [N]
      linarith

/-- Exact integer endpoint; no original physical mask changes. -/
def countCeiling (j : ℕ) : ℕ := dyadicPrimeCount j/768+1

theorem countCeiling_bounds (j : ℕ) :
    dyadicPrimeCount j < 768*countCeiling j ∧ countCeiling j ≤ dyadicPrimeCount j := by
  have := four_le_dyadicPrimeCount j
  dsimp [countCeiling]
  omega

/-- Two-thirds of the formerly retained K/512 endpoint, with exact rounding. -/
theorem countCeiling_comparison (j : ℕ) (hj : 9 ≤ j) :
    3*(countCeiling j-1) ≤ 2*dyadicPrimeCount (j-9) ∧
      2*dyadicPrimeCount (j-9) < 3*countCeiling j := by
  have hfactor := ZetaRieszJointCountFloor.reduced_count_factor j hj
  dsimp [countCeiling]
  omega

/-- The new whole-population error tends to zero at source scale. -/
def allowance (j : ℕ) : ℝ :=
  ((203/50 : ℝ)*radiusCeiling)*((dyadicMomentOrder j : ℝ)+1)*
    exp (-(dyadicMomentOrder j : ℝ)/200000)

theorem allowance_nonneg (j : ℕ) : 0 ≤ allowance j := by
  unfold allowance radiusCeiling
  positivity

theorem tendsto_allowance : Tendsto allowance atTop (𝓝 0) := by
  have h0 : 0 < exp (-1/200000 : ℝ) := exp_pos _
  have h1 : exp (-1/200000 : ℝ) < 1 := by rw [exp_lt_one_iff]; norm_num
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1 h0 h1).comp
    tendsto_dyadicMomentOrder
  have h := ht.const_mul ((203/50 : ℝ)*radiusCeiling)
  have he (j : ℕ) : exp (-1/200000 : ℝ)^dyadicMomentOrder j =
      exp (-(dyadicMomentOrder j : ℝ)/200000) := by
    rw [← exp_nat_mul]
    congr 1
    ring
  simp only [Function.comp_def,pow_one,he,mul_zero] at h
  change Tendsto (fun j => ((203/50 : ℝ)*radiusCeiling)*
    ((dyadicMomentOrder j : ℝ)+1)*exp (-(dyadicMomentOrder j : ℝ)/200000)) atTop (𝓝 0)
  simpa only [mul_assoc] using h

/-- Pay the exact difference of the two EXISTING core responses.
All original phases, squarefree conditions and allocation weights remain. -/
theorem eventually_norm_core_count_change_le :
    ∀ᶠ j : ℕ in atTop, ∀ u y : ℝ, 0 ≤ u → u ≤ radiusCeiling →
      ‖(u : ℂ)^(dyadicMomentOrder j+1)*
        (coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
          coreResponse u y (dyadicMomentOrder j) (countCeiling j))‖ ≤ allowance j := by
  filter_upwards [eventually_sharper_count_sum_bound] with j hj u y hu hU
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let D := (coreBand u N (dyadicPrimeCount j)).filter (fun n => countCeiling j ≤ n.primeFactors.card)
  let S := D.filter Squarefree
  rw [ZetaRieszJointCountFloor.coreResponse_sub_count u y N _ _ (countCeiling_bounds j).2]
  have heq : (∑ n ∈ D,residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      ∑ n ∈ S,residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hout
    have hns : ¬Squarefree n := fun hs => hout (Finset.mem_filter.mpr ⟨hn,hs⟩)
    simp [residualCoefficient,SquarefreeVaughanLogSource.coefficient,hns]
  change ‖(u : ℂ)^(N+1)*∑ n ∈ D,
    residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤ allowance j
  rw [heq]
  apply hj S (residualCoefficient A L N) y u hu hU
  · intro n _
    have h := (ZetaRieszJointCountFloor.norm_residual_le A L N n).trans
      (SquarefreeVaughanLogSource.norm_coefficient_le (SquarefreeVaughanLogSource.length_pos u N) n)
    have hp : 0 ≤ zetaMoebiusLogMajorant n := by
      unfold zetaMoebiusLogMajorant
      positivity
    linarith only [h,hp]
  · exact fun _ hn => (Finset.mem_filter.mp hn).2
  · intro n hn
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1).2.2
  · intro n hn
    have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
    have hb := (countCeiling_bounds j).1
    omega

theorem tendsto_core_count_change (u y : ℕ → ℝ)
    (hu : ∀ j, 0 ≤ u j) (hU : ∀ j, u j ≤ radiusCeiling) :
    Tendsto (fun j => (u j : ℂ)^(dyadicMomentOrder j+1)*
      (coreResponse (u j) (y j) (dyadicMomentOrder j) (dyadicPrimeCount j)-
        coreResponse (u j) (y j) (dyadicMomentOrder j) (countCeiling j))) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ tendsto_allowance
  filter_upwards [eventually_norm_core_count_change_le] with j hj
  exact hj (u j) (y j) (hu j) (hU j)

/-- One original joined bridge and the independently paid count tail. -/
def joinedError (u y : ℝ) (j : ℕ) : ℝ :=
  ZetaRieszDirectPhaseFloor.joinedError u y (dyadicMomentOrder j) (dyadicPrimeCount j)+allowance j

theorem tendsto_joinedError {u : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling) (y : ℝ) :
    Tendsto (joinedError u y) atTop (𝓝 0) := by
  change Tendsto (fun j => ZetaRieszDirectPhaseFloor.joinedError u y
    (dyadicMomentOrder j) (dyadicPrimeCount j)+allowance j) atTop (𝓝 0)
  simpa only [add_zero] using
    (ZetaRieszDirectPhaseFloor.tendsto_joinedError hu hU y dyadicMomentOrder dyadicPrimeCount
      tendsto_dyadicMomentOrder).add tendsto_allowance

/-- The numerical floor target is UNCHANGED. Its remaining signed
energy now contains only counts BELOW K/768, with every other original
mask retained. No small bound on this energy is assumed or asserted. -/
theorem eventually_joined_floor {u y : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling)
    (hy : 54 ≤ y) :
    ∀ᶠ j : ℕ in atTop,
      let N := dyadicMomentOrder j
      let A := intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let S := coreBand u N (countCeiling j)
      let X := max 1 (S.sup id)
      let f := correctedProfile X L 1 0
      let w := fun n => u^(N+1)*ZetaRieszJointPrimeEnergy.primeWeight A L y N n 1;
      -sqrt (max (nonOrbitEnergy X N (S.filter Squarefree) w f y) 0*((129/200 : ℝ)*N))-
        joinedError u y j ≤
          ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_norm_core_count_change_le,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (65536 : ℕ))] with j hj hN
  have hfloor := ZetaRieszDirectPhaseFloor.core_floor hu hU
    (by rw [abs_of_pos (by linarith : 0 < y)]; linarith) hN (countCeiling j)
  have htail := hj u y hu.le hU
  rw [mul_sub] at htail
  have hr := (abs_le.mp (Complex.abs_re_le_norm ((u : ℂ)^(dyadicMomentOrder j+1)*
    (coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
      coreResponse u y (dyadicMomentOrder j) (countCeiling j))))).1
  rw [mul_sub,Complex.sub_re] at hr
  have hbridge := Complex.re_le_norm ((u : ℂ)^(dyadicMomentOrder j+1)*
    (coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)))
  rw [mul_sub,Complex.sub_re] at hbridge
  dsimp only at hfloor ⊢
  unfold joinedError ZetaRieszDirectPhaseFloor.joinedError
  rw [mul_sub]
  linarith only [hfloor,htail,hr,hbridge]

end RiemannGaussian.ZetaRieszSharperCountPayment
