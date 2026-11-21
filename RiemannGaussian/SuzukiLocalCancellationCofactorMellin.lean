import RiemannGaussian.SuzukiLocalCancellationCofactorTail
import RiemannGaussian.SuzukiLocalCancellationKernel
import RiemannGaussian.SuzukiLocalCancellationMoment
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.Convex

/-! # The Mellin transform of the signed proper-cofactor sum -/

namespace RiemannGaussian
noncomputable section
open Set MeasureTheory Filter
open scoped Topology

/-- The sum of the dilates of the unit packet over every cofactor at least two. -/
def suzukiLocalCofactorProfile (v : ℝ) : ℝ :=
  ∑' n : ℕ, suzukiLocalPhysicalKernel 1 (v * (n + 2))

private theorem profile_eq_prefix {v : ℝ} (hv : 0 < v) {N : ℕ} (hN : 8 / v ≤ N) :
    suzukiLocalCofactorProfile v =
      ∑ n ∈ Finset.range N, suzukiLocalPhysicalKernel 1 (v * (n + 2)) := by
  apply tsum_eq_sum
  intro n hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_not_gt (Finset.mem_range.not.mp hn))
  apply suzukiLocalPhysicalKernel_eq_zero_of_eight_mul_le (by norm_num)
  have h := (div_le_iff₀ hv).mp (hN.trans hn')
  nlinarith

/-- The infinite-sum definition agrees with the literal finite row of the prime sum. -/
theorem suzukiLocalCofactorProfile_eq_row {v : ℝ} (hv : 0 < v) :
    suzukiLocalCofactorProfile v =
      ∑ k ∈ Finset.Ioc 1 ⌊8/v⌋₊, suzukiLocalPhysicalKernel 1 (v * k) := by
  let N := ⌊8/v⌋₊
  have hI : Finset.Ioc 1 N = Finset.Ico 2 (N+1) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  change _ = ∑ k ∈ Finset.Ioc 1 N, _
  rw [hI, Finset.sum_Ico_eq_sum_range]
  apply (tsum_eq_sum ?_).trans
  · apply Finset.sum_congr rfl
    intro n _
    simp only [Nat.cast_add, Nat.cast_ofNat]
    ring_nf
  · intro n hn
    have hn' := Nat.le_of_not_gt (Finset.mem_range.not.mp hn)
    have hN : N < n+2 := by omega
    have hlt := (Nat.floor_lt (by positivity : 0 ≤ 8/v)).mp hN
    apply suzukiLocalPhysicalKernel_eq_zero_of_eight_mul_le (by norm_num)
    push_cast at hlt
    nlinarith [(div_lt_iff₀ hv).mp hlt]

/-- Fine-lattice cancellation controls the row near the origin, where cofactor one vanishes. -/
theorem abs_suzukiLocalCofactorProfile_le {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) :
    |suzukiLocalCofactorProfile v| ≤ 96 * v := by
  have hs := suzukiLocalPhysicalKernel_prefix_sum_abs_le_spacing (X := 1) (by norm_num) hv
  have hI : Finset.Icc 1 ⌊8/v⌋₊ = Finset.Ioc 0 ⌊8/v⌋₊ := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hN : 1 ≤ ⌊8/v⌋₊ := (Nat.le_floor_iff (by positivity)).mpr (by
    norm_num
    exact (one_le_div hv).mpr (by linarith))
  rw [suzukiLocalCofactorProfile_eq_row hv]
  simpa only [mul_one, Real.sqrt_one, div_one, hI,
    ← Finset.sum_Ioc_consecutive _ (by decide : 0 ≤ 1) hN,
    show Finset.Ioc 0 1 = ({1} : Finset ℕ) by decide, Finset.sum_singleton, Nat.cast_one,
    suzukiLocalPhysicalKernel_eq_zero_of_le (by norm_num : (0 : ℝ) < 1) hv1,
    zero_add] using hs

/-- Explicit cost of omitting small positive arguments in the Mellin integral. -/
theorem suzukiLocalCofactorProfile_mellin_cutoff {s : ℂ} (hs : 0 < s.re) {Y : ℝ}
    (hY : 0 ≤ Y) (hY1 : Y ≤ 1) :
    ‖∫ v in (0 : ℝ)..Y, (v : ℂ) ^ (s-1) * (suzukiLocalCofactorProfile v : ℂ)‖ ≤
      96 * Y ^ (s.re+1) / (s.re+1) := by
  calc
    _ ≤ ∫ v in (0 : ℝ)..Y, 96 * v ^ s.re := by
      apply intervalIntegral.norm_integral_le_of_norm_le hY
      · apply Filter.Eventually.of_forall
        intro v hv
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv.1, Complex.sub_re,
          Complex.one_re, Complex.norm_real, Real.norm_eq_abs]
        have he : v ^ (s.re-1) * v = v ^ s.re := by
          rw [← Real.rpow_add_one hv.1.ne', sub_add_cancel]
        calc
          _ ≤ v ^ (s.re-1) * (96*v) := mul_le_mul_of_nonneg_left
            (abs_suzukiLocalCofactorProfile_le hv.1 (hv.2.trans hY1)) (Real.rpow_nonneg hv.1.le _)
          _ = _ := by rw [← he]; ring
      · exact (continuous_const.mul (Real.continuous_rpow_const hs.le)).intervalIntegrable ..
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
        Real.zero_rpow (by linarith : s.re + 1 ≠ 0), sub_zero]
      ring

/-- Positive spacings have a common finite cofactor support locally. -/
theorem suzukiLocalCofactorProfile_continuousAt {v : ℝ} (hv : 0 < v) :
    ContinuousAt suzukiLocalCofactorProfile v := by
  let N := ⌈8/(v/2)⌉₊
  have he : suzukiLocalCofactorProfile =ᶠ[𝓝 v]
      (fun u => ∑ n ∈ Finset.range N, suzukiLocalPhysicalKernel 1 (u * (n+2))) := by
    filter_upwards [lt_mem_nhds (show v/2 < v by linarith)] with u hu
    exact profile_eq_prefix (by linarith) ((div_le_div_of_nonneg_left (by norm_num)
      (by linarith) hu.le).trans (Nat.le_ceil _))
  let F (n : ℕ) (u : ℝ) := suzukiLocalPhysicalKernel 1 (u * (n+2))
  have hc (n : ℕ) : ContinuousAt (F n) v := by
    have hg : ContinuousAt (fun u : ℝ => u * ((n : ℝ)+2)) v := continuousAt_id.mul_const _
    have hp : 0 < v * ((n : ℝ)+2) := mul_pos hv (by positivity)
    exact (continuousAt_suzukiLocalPhysicalKernel (X := 1) (by norm_num) hp).comp
      (f := fun u : ℝ => u * ((n : ℝ)+2)) (x := v) hg
  have hsum : ContinuousAt (fun u => ∑ n ∈ Finset.range N, F n u) v :=
    tendsto_finsetSum (f := F) (a := fun n => F n v) (x := 𝓝 v) (Finset.range N) (fun n _ => hc n)
  exact hsum.congr_of_eventuallyEq he

private theorem mellin_regular {f : ℝ → ℂ} (hc : ContinuousOn f (Ioi 0))
    (ht : ∀ v, 8 ≤ v → f v = 0) (hb : ∀ v, 0 < v → v ≤ 1 → ‖f v‖ ≤ 96)
    {s : ℂ} (hs : 0 < s.re) : MellinConvergent f s ∧
      HasDerivAt (mellin f) (mellin (fun t => Real.log t • f t) s) s := by
  have hf : LocallyIntegrableOn f (Ioi 0) volume := hc.locallyIntegrableOn measurableSet_Ioi
  have ht' : f =O[atTop] (fun v : ℝ => v ^ (-(s.re+1))) := by
    refine Asymptotics.isBigO_iff.mpr ⟨0, ?_⟩
    filter_upwards [eventually_ge_atTop (8 : ℝ)] with v hv
    simp [ht v hv]
  have hb' : f =O[𝓝[>] 0] (fun v : ℝ => v ^ (-(0 : ℝ))) := by
    refine Asymptotics.isBigO_iff.mpr ⟨96, ?_⟩
    filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1)))] with v hv hv1
    simpa using hb v hv (le_of_lt hv1)
  exact ⟨mellinConvergent_of_isBigO_rpow hf ht' (by linarith) hb' hs,
    (mellin_hasDerivAt_of_isBigO_rpow hf ht' (by linarith) hb' hs).2⟩

private theorem atom_regular {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun v => (suzukiLocalPhysicalKernel 1 v : ℂ)) s ∧
      HasDerivAt (mellin (fun v => (suzukiLocalPhysicalKernel 1 v : ℂ)))
        (mellin (fun v => Real.log v • (suzukiLocalPhysicalKernel 1 v : ℂ)) s) s := by
  apply mellin_regular _ _ _ hs
  · exact fun v hv => (Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_suzukiLocalPhysicalKernel (by norm_num) hv)).continuousWithinAt
  · intro v hv
    simp [suzukiLocalPhysicalKernel_eq_zero_of_eight_mul_le (by norm_num : (0:ℝ) < 1)
      (by linarith : 8 * 1 ≤ v)]
  · intro v _ hv
    simp [suzukiLocalPhysicalKernel_eq_zero_of_le (by norm_num : (0:ℝ) < 1) hv]

private theorem profile_regular {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun v => (suzukiLocalCofactorProfile v : ℂ)) s ∧
      HasDerivAt (mellin (fun v => (suzukiLocalCofactorProfile v : ℂ)))
        (mellin (fun v => Real.log v • (suzukiLocalCofactorProfile v : ℂ)) s) s := by
  apply mellin_regular _ _ _ hs
  · exact fun v hv => (Complex.continuous_ofReal.continuousAt.comp
      (suzukiLocalCofactorProfile_continuousAt hv)).continuousWithinAt
  · intro v hv
    apply Complex.ofReal_eq_zero.mpr
    unfold suzukiLocalCofactorProfile
    have hz (n : ℕ) : suzukiLocalPhysicalKernel 1 (v * (n+2)) = 0 := by
      apply suzukiLocalPhysicalKernel_eq_zero_of_eight_mul_le (by norm_num)
      nlinarith [mul_nonneg (by linarith : 0 ≤ v) (Nat.cast_nonneg n)]
    simp [hz]
  · intro v hv hv1
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_suzukiLocalCofactorProfile_le hv hv1).trans (by linarith)

private theorem integral_norm_dilate (f : ℝ → ℂ) (s : ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s-1) * f (a*t)‖) =
      a ^ (-s.re) * ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s-1) * f t‖ := by
  let g (v : ℝ) := ‖(v : ℂ) ^ (s-1) * f v‖
  have he (v : ℝ) (hv : 0 < v) :
      ‖(v : ℂ) ^ (s-1) * f (a*v)‖ = a ^ (1-s.re) * g (a*v) := by
    simp only [g, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv,
      Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos ha hv), Complex.sub_re, Complex.one_re,
      Real.mul_rpow ha.le hv.le]
    rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add ha, show 1-s.re+(s.re-1)=0 by ring,
      Real.rpow_zero, one_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul,
    integral_comp_mul_left_Ioi g 0 ha, mul_zero, smul_eq_mul,
    ← mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add ha]
  congr 2
  ring

private theorem profile_mellin_right {s : ℂ} (hs : 1 < s.re) :
    mellin (fun v => (suzukiLocalCofactorProfile v : ℂ)) s =
      (riemannZeta s-1) * mellin (fun v => (suzukiLocalPhysicalKernel 1 v : ℂ)) s := by
  let f (t : ℝ) : ℂ := suzukiLocalPhysicalKernel 1 t
  let a (n : ℕ) : ℝ := n+2
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  let F (n : ℕ) (t : ℝ) := (t : ℂ) ^ (s-1) * f (a n * t)
  have hFi (n : ℕ) : Integrable (F n) (volume.restrict (Ioi 0)) :=
    (MellinConvergent.comp_mul_left (f := f) (s := s) (ha n)).mpr
      (atom_regular (by linarith : 0 < s.re)).1
  have hsumm : Summable (fun n : ℕ => a n ^ (-s.re)) := by
    simpa [a] using (summable_nat_add_iff 2).mpr (Real.summable_nat_rpow.mpr
      (by linarith : -s.re < -1))
  have hFn : Summable (fun n : ℕ => ∫ t in Ioi 0, ‖F n t‖) := by
    simpa only [F, integral_norm_dilate f s (ha _)] using
      hsumm.mul_right (∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s-1) * f t‖)
  have hm := hasSum_integral_of_summable_integral_norm hFi hFn
  have hi (n : ℕ) : (∫ t in Ioi 0, F n t) = (a n : ℂ) ^ (-s) * mellin f s :=
    mellin_comp_mul_left f s (ha n)
  have ht (t : ℝ) : (∑' n : ℕ, F n t) =
      (t : ℂ) ^ (s-1) * (suzukiLocalCofactorProfile t : ℂ) := by
    simp [F, a, f, suzukiLocalCofactorProfile, Complex.ofReal_tsum, tsum_mul_left, mul_comm t]
  simp only [hi, ht] at hm
  have hz1 : HasSum (fun n : ℕ => ((n+1 : ℂ)) ^ (-s)) (riemannZeta s) := by
    have h := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    simpa [one_div, Complex.cpow_neg] using h.hasSum
  have hz2 : HasSum (fun n : ℕ => (a n : ℂ) ^ (-s)) (riemannZeta s-1) := by
    have hh := (hasSum_nat_add_iff' 1).mpr hz1
    convert hh using 1
    · ext n
      simp [a]
      ring_nf
    · simp
  exact hm.unique (hz2.mul_right _)

private theorem pole_removed_identity {s : ℂ} (hs : 0 < s.re) :
    (s-1) * mellin (fun v => (suzukiLocalCofactorProfile v : ℂ)) s =
      (riemannZeta₁ s-(s-1)) * mellin (fun v => (suzukiLocalPhysicalKernel 1 v : ℂ)) s := by
  let A := mellin (fun v => (suzukiLocalPhysicalKernel 1 v : ℂ))
  let P := mellin (fun v => (suzukiLocalCofactorProfile v : ℂ))
  let l (z : ℂ) := (z-1) * P z
  let r (z : ℂ) := (riemannZeta₁ z - (z-1)) * A z
  have hl : AnalyticOnNhd ℂ l {z : ℂ | 0 < z.re} := by
    apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt 0)
    intro z hz
    exact ((differentiableAt_id.sub_const _).mul (profile_regular hz).2.differentiableAt).differentiableWithinAt
  have hr : AnalyticOnNhd ℂ r {z : ℂ | 0 < z.re} := by
    apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt 0)
    intro z hz
    exact (((differentiable_riemannZeta₁ z).sub (differentiableAt_id.sub_const _)).mul
      (atom_regular hz).2.differentiableAt).differentiableWithinAt
  have hzeta {z : ℂ} (hne : z ≠ 1) : riemannZeta₁ z = (z-1) * riemannZeta z := by
    rw [riemannZeta_eq_inv_sub_mul hne, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hne), one_mul]
  have he : l =ᶠ[𝓝 (2 : ℂ)] r := by
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})]
      with z hz
    have hne : z ≠ 1 := by rintro rfl; norm_num at hz
    dsimp [l, r, A, P]
    rw [profile_mellin_right hz, hzeta hne]
    ring
  exact hl.eqOn_of_preconnected_of_eventuallyEq hr (convex_halfSpace_re_gt 0).isPreconnected
    (by norm_num : (2 : ℂ) ∈ {z : ℂ | 0 < z.re}) he hs

/-- In the right half-plane the multiplier of the entire proper-cofactor row is
zeta minus one. The formula uses ordinary zeta away from its pole. -/
theorem suzukiLocalCofactorProfile_mellin {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    mellin (fun v => (suzukiLocalCofactorProfile v : ℂ)) s =
      (riemannZeta s-1) * mellin (fun v => (suzukiLocalPhysicalKernel 1 v : ℂ)) s := by
  have h := pole_removed_identity hs
  have hzeta := riemannZeta_eq_inv_sub_mul hs1
  have he : riemannZeta₁ s = (s-1) * riemannZeta s := by
    rw [hzeta, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs1), one_mul]
  rw [he] at h
  apply mul_left_cancel₀ (sub_ne_zero.mpr hs1)
  linear_combination h

/-- Passing to logarithmic coordinates keeps the removable central value. -/
theorem suzukiLocalPhysicalKernel_mellin_log (s : ℂ) :
    mellin (fun v => (suzukiLocalPhysicalKernel 1 v : ℂ)) s =
      ∫ v : ℝ, Complex.exp ((s-1/2) * (v : ℂ)) * (suzukiLocalSignedKernel v : ℂ) := by
  rw [mellin, ← integral_comp_exp]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  have hj := suzukiLocalPhysicalKernel_exp_jacobian (X := 1) (by norm_num) v
  simp only [one_mul, Real.sqrt_one] at hj
  have hjc := congrArg Complex.ofReal hj
  simp only [Complex.ofReal_mul] at hjc
  have hcp : (Real.exp v : ℂ) ^ (s-1) = Complex.exp ((v : ℂ) * (s-1)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  simp only [Complex.real_smul, smul_eq_mul, hcp]
  rw [mul_left_comm, mul_comm (Real.exp v : ℂ), hjc, Complex.ofReal_exp,
    ← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

private theorem atom_mellin_eq (s : ℂ) (hne : s - 1/2 ≠ 0) :
    mellin (fun v => (suzukiLocalPhysicalKernel 1 v : ℂ)) s =
      -suzukiLocalModeMultiplier (s-1/2) / (s-1/2)^2 := by
  rw [suzukiLocalPhysicalKernel_mellin_log, suzukiLocalSignedKernel_transform hne, suzukiLocalModeMultiplier]
  ring

/-- A hypothetical right-of-line zero gives a nonzero Mellin integral for
the sum over all proper cofactors. -/
theorem suzukiLocalCofactorProfile_mellin_ne_zero_at_zero {s : ℂ}
    (hs : 1/2 < s.re) (hs' : s.re < 1) (hz : riemannZeta s = 0) :
    mellin (fun v => (suzukiLocalCofactorProfile v : ℂ)) s ≠ 0 := by
  have ha : 0 < (s-1/2).re := by simp; linarith
  have hb : (s-1/2).re < 1/2 := by simp; linarith
  have hne : s-1/2 ≠ 0 := by intro h; rw [h] at ha; exact (lt_irrefl 0) ha
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs'
  rw [suzukiLocalCofactorProfile_mellin (by linarith) hs1, hz, atom_mellin_eq s hne]
  exact mul_ne_zero (by norm_num) (div_ne_zero (neg_ne_zero.mpr
    (suzukiLocalModeMultiplier_ne_zero ha hb)) (pow_ne_zero _ hne))

/-- The integral of all signed proper-cofactor rows against constant density is
the first logarithmic moment of the original packet. -/
theorem suzukiLocalCofactorProfile_integral :
    (∫ v : ℝ in Ioi 0, suzukiLocalCofactorProfile v) =
      -4 * Real.log 2 * Real.sqrt 2 * (Real.sqrt 2-1)^2 := by
  let A := mellin (fun v => (suzukiLocalPhysicalKernel 1 v : ℂ))
  let P := mellin (fun v => (suzukiLocalCofactorProfile v : ℂ))
  have h0 : A 1 = 0 := by
    simpa [A] using (pole_removed_identity (s := 1) (by norm_num)).symm
  have he : (fun z : ℂ => (z-1) * P z) =ᶠ[𝓝 1] fun z => (riemannZeta₁ z - (z-1)) * A z := by
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds (by norm_num : (1 : ℂ) ∈ {z : ℂ | 0 < z.re})]
      with z hz
    exact pole_removed_identity hz
  have hl := ((hasDerivAt_id (1:ℂ)).sub_const 1).mul (profile_regular (s := 1) (by norm_num)).2
  have hr := ((differentiable_riemannZeta₁ 1).hasDerivAt.sub
    ((hasDerivAt_id (1:ℂ)).sub_const 1)).mul (atom_regular (s := 1) (by norm_num)).2
  have hd := hl.unique (hr.congr_of_eventuallyEq he)
  change mellin (fun v => (suzukiLocalPhysicalKernel 1 v : ℂ)) 1 = 0 at h0
  simp only [Pi.sub_apply, id_eq, sub_self, zero_mul, riemannZeta₁_one, sub_zero, one_mul,
    h0, mul_zero, zero_add, add_zero] at hd
  simp only [mellin, sub_self, Complex.cpow_zero, one_smul, Complex.real_smul, ← Complex.ofReal_mul,
    integral_complex_ofReal, Complex.ofReal_inj] at hd
  rw [hd]
  have hs : Ioc (1:ℝ) 8 ⊆ Ioi 0 := fun _ h => zero_lt_one.trans h.1
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hs, ←
    intervalIntegral.integral_of_le (by norm_num : (1:ℝ) ≤ 8)]
  · simpa [mul_comm (Real.log _) _, mul_one] using
      suzukiLocalPhysicalKernel_log_integral (X := 1) (d := 1) (by norm_num) (by norm_num)
  · intro x hx
    by_cases h : x ≤ 1
    · simp [suzukiLocalPhysicalKernel_eq_zero_of_le (by norm_num : (0:ℝ)<1) h]
    · have h8 : 8 ≤ x := by
        by_contra! hn
        exact hx.2 ⟨lt_of_not_ge h, hn.le⟩
      simp [suzukiLocalPhysicalKernel_eq_zero_of_eight_mul_le (by norm_num : (0:ℝ)<1)
        (by linarith : 8 * 1 ≤ x)]

/-- The unit-profile integral above a positive cutoff differs from its limiting
density by at most 48 times the square of the cutoff. -/
theorem suzukiLocalCofactorProfile_density_error {Y : ℝ} (hY : 0 ≤ Y) (hY1 : Y ≤ 1) :
    |(∫ v : ℝ in Ioi Y, suzukiLocalCofactorProfile v) -
      (-4 * Real.log 2 * Real.sqrt 2 * (Real.sqrt 2-1)^2)| ≤ 48 * Y^2 := by
  have hconv := (profile_regular (s := 1) (by norm_num)).1
  simp only [MellinConvergent, sub_self, Complex.cpow_zero, one_smul] at hconv
  have hi : IntegrableOn suzukiLocalCofactorProfile (Ioi 0) := by
    simpa using hconv.re
  have hsum := intervalIntegral.integral_interval_add_Ioi hi (hi.mono_set (Ioi_subset_Ioi hY))
  rw [suzukiLocalCofactorProfile_integral] at hsum
  have hc := suzukiLocalCofactorProfile_mellin_cutoff (s := 1) (by norm_num) hY hY1
  norm_num [intervalIntegral.integral_ofReal, Complex.norm_real, Real.norm_eq_abs] at hc
  rw [show (∫ v : ℝ in Ioi Y, suzukiLocalCofactorProfile v) -
      (-4 * Real.log 2 * Real.sqrt 2 * (Real.sqrt 2-1)^2) =
      -(∫ v in (0 : ℝ)..Y, suzukiLocalCofactorProfile v) by linarith, abs_neg]
  linarith

/-- The prime sum with its continuous density subtracted on the same truncated interval. -/
def suzukiLocalPrimeCofactorDiscrepancy (X : ℝ) : ℝ :=
  (Real.sqrt X)⁻¹ * (∑ p ∈ (Finset.Ioc ⌊X ^ (3/4 : ℝ)⌋₊ ⌊8*X⌋₊).filter Nat.Prime,
    Real.log p * suzukiLocalCofactorProfile (p/X)) -
  Real.sqrt X * ∫ v in Ioi (X ^ (-(1/4 : ℝ))), suzukiLocalCofactorProfile v

/-- Rescaling an entire nonunit cofactor row retains its exact integer endpoint. -/
theorem suzukiLocalCofactorProfile_scaled_row {X d : ℝ} (hx : 0 < X) (hd : 0 < d) :
    (Real.sqrt X)⁻¹ * suzukiLocalCofactorProfile (d/X) =
      ∑ k ∈ Finset.Ioc 1 ⌊8*X/d⌋₊, suzukiLocalPhysicalKernel X (d*k) := by
  rw [suzukiLocalCofactorProfile_eq_row (div_pos hd hx),
    show 8/(d/X) = 8*X/d by field, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hh := suzukiLocalPhysicalKernel_mul_eq (X := X) hx hx (d/X*(k:ℝ))
  rw [div_self hx.ne', show X*(d/X*k) = d*k by field] at hh
  exact hh.symm

/-- The centered arithmetic sum differs from the actual prime-minus-density
discrepancy by a numerical constant at every real cutoff. -/
theorem abs_suzukiLocalPrimeCofactorDiscrepancy_sub_tail_le {X : ℝ} (hX : 1 ≤ X) :
    |suzukiLocalPrimeCofactorDiscrepancy X - suzukiLocalCenteredPrimeCofactorTail X| ≤ 48 := by
  have hx := zero_lt_one.trans_le hX
  let Y := X ^ (-(1/4 : ℝ))
  have hy : 0 ≤ Y := Real.rpow_nonneg hx.le _
  have hy1 : Y ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX (by norm_num)
  have hY : Real.sqrt X * Y^2 = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le,
      ← Real.rpow_add hx]
    norm_num
  have hc := suzukiLocalCofactorProfile_density_error hy hy1
  have hm := mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg X)
  rw [show Real.sqrt X * (48 * Y ^ 2) = 48 by rw [mul_left_comm, hY, mul_one]] at hm
  unfold suzukiLocalPrimeCofactorDiscrepancy suzukiLocalCenteredPrimeCofactorTail
  rw [Finset.mul_sum]
  simp_rw [mul_left_comm (Real.sqrt X)⁻¹ (Real.log _)]
  let S := (Finset.Ioc ⌊X ^ (3/4 : ℝ)⌋₊ ⌊8*X⌋₊).filter Nat.Prime
  have hs : (∑ p ∈ S, Real.log p * ((Real.sqrt X)⁻¹ * suzukiLocalCofactorProfile (p/X))) =
      ∑ p ∈ S, Real.log p *
        ∑ k ∈ Finset.Ioc 1 ⌊8 * X / p⌋₊, suzukiLocalPhysicalKernel X ((p : ℝ)*k) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact congrArg (Real.log p * ·) (suzukiLocalCofactorProfile_scaled_row hx
      (by exact_mod_cast (Finset.mem_filter.mp hp).2.pos))
  rw [hs]
  calc
    _ = |-(Real.sqrt X * ((∫ v in Ioi Y, suzukiLocalCofactorProfile v) -
        (-4 * Real.log 2 * Real.sqrt 2 * (Real.sqrt 2-1)^2)))| := by
      congr 1
      dsimp only [Y, S]
      ring
    _ ≤ _ := by rwa [abs_neg, abs_mul, abs_of_nonneg (Real.sqrt_nonneg X)]

/-- A uniform one-sided bound on the exact prime-minus-continuous-density
discrepancy is equivalent to the literal Riemann hypothesis. -/
theorem riemannHypothesis_iff_primeCofactorDiscrepancy_eventually_le :
    RiemannHypothesis ↔ ∃ X₀ : ℝ, 2 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      suzukiLocalPrimeCofactorDiscrepancy X ≤ 4248 := by
  constructor
  · intro h
    obtain ⟨X₀,hX₀,ht⟩ := riemannHypothesis_iff_centeredPrimeCofactorTail_eventually_le.mp h
    refine ⟨X₀,hX₀, fun X hX => ?_⟩
    have hb := (abs_le.mp (abs_suzukiLocalPrimeCofactorDiscrepancy_sub_tail_le
      (show 1 ≤ X by linarith))).2
    linarith [ht X hX]
  · rintro ⟨X₀,hX₀,hd⟩
    by_contra hn
    obtain ⟨ε,hε,he⟩ := exists_centeredPrimeCofactorTail_excursions_of_not_rh hn
    obtain ⟨X,hX,ht⟩ := he 4296 (by norm_num) X₀ hX₀
    have h1 : 1 ≤ X := by linarith
    have hb := (abs_le.mp (abs_suzukiLocalPrimeCofactorDiscrepancy_sub_tail_le h1)).1
    linarith [hd X hX, Real.one_le_rpow h1 hε.le]

end
end RiemannGaussian
