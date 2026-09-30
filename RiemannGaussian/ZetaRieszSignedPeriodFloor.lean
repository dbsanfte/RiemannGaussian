/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszQuantitativePrimePeriod
import RiemannGaussian.ZetaRieszWeightedPrimeTail
import RiemannGaussian.ZetaRieszFixedCountPeriod

/-!
# One-sided prime-period payment with the radial drift retained

A positive cosine peak has a nonpositive full-period integral against a
convex amplitude. Only negative curvature costs the upper bound. The actual
prime comparison retains both endpoints; its error is paid locally, not by
claiming a source-scale prime-density approximation.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators Classical ContDiff
namespace RiemannGaussian.ZetaRieszSignedPeriodFloor

/-- Two integrations by parts preserve the favorable convex drift. The
boundary primitive vanishes at BOTH ends of the complete period. -/
theorem centered_period_curvature_eq (f g g' : ℝ → ℝ) {v y : ℝ} (hy : 0 < y)
    (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hc : Continuous g') :
    (∫ t in v-Real.pi/y..v+Real.pi/y, f t*Real.cos (y*(t-v))) =
      -(∫ t in v-Real.pi/y..v+Real.pi/y,
        g' t*(1+Real.cos (y*(t-v))))/y^2 := by
  let Q := fun t => f t*Real.sin (y*(t-v))/y+
    g t*(1+Real.cos (y*(t-v)))/y^2
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt)
  have hgc : Continuous g := continuous_iff_continuousAt.mpr (fun t => (hg t).continuousAt)
  have hQ t : HasDerivAt Q
      (f t*Real.cos (y*(t-v))+g' t*(1+Real.cos (y*(t-v)))/y^2) t := by
    have h := (((hf t).mul ((((hasDerivAt_id t).sub_const v).const_mul y).sin)).div_const y).add
      (((hg t).mul (((((hasDerivAt_id t).sub_const v).const_mul y).cos).const_add 1)).div_const (y^2))
    apply h.congr_deriv
    simp only [id_eq,mul_one]
    field_simp
    ring
  have hargL : y*(v-Real.pi/y-v) = -Real.pi := by field_simp; ring
  have hargR : y*(v+Real.pi/y-v) = Real.pi := by field_simp; ring
  have he : Q (v+Real.pi/y)-Q (v-Real.pi/y) = 0 := by
    dsimp only [Q]
    rw [hargL,hargR]
    simp
  have hi₀ : IntervalIntegrable (fun t => f t*Real.cos (y*(t-v))) volume
      (v-Real.pi/y) (v+Real.pi/y) := (hfc.mul (by fun_prop)).intervalIntegrable _ _
  have hi₁ : IntervalIntegrable (fun t => g' t*(1+Real.cos (y*(t-v)))) volume
      (v-Real.pi/y) (v+Real.pi/y) := (hc.mul (by fun_prop)).intervalIntegrable _ _
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hQ t)
    (hi₀.add (hi₁.div_const (y^2)))
  rw [he,intervalIntegral.integral_add hi₀ (hi₁.div_const (y^2)),
    intervalIntegral.integral_div] at heq
  rw [neg_div]
  linarith only [heq]

/-- A one-sided curvature bound suffices: positive curvature is never
charged. No near-constant-amplitude hypothesis is used. -/
theorem centered_period_upper (f g g' : ℝ → ℝ) {v y D : ℝ} (hy : 0 < y)
    (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hc : Continuous g')
    (hl : ∀ t ∈ Icc (v-Real.pi/y) (v+Real.pi/y), -D ≤ g' t) :
    (∫ t in v-Real.pi/y..v+Real.pi/y, f t*Real.cos (y*(t-v))) ≤
      (2*Real.pi/y)*D/y^2 := by
  have hab : v-Real.pi/y ≤ v+Real.pi/y := by linarith [div_pos Real.pi_pos hy]
  have hcos : Continuous (fun t => 1+Real.cos (y*(t-v))) := by fun_prop
  have hi : (∫ t in v-Real.pi/y..v+Real.pi/y,
      (-D)*(1+Real.cos (y*(t-v)))) ≤
      ∫ t in v-Real.pi/y..v+Real.pi/y, g' t*(1+Real.cos (y*(t-v))) := by
    apply intervalIntegral.integral_mono_on hab
      ((hcos.const_mul (-D)).intervalIntegrable _ _)
      ((hc.mul hcos).intervalIntegrable _ _)
    intro t ht
    exact mul_le_mul_of_nonneg_right (hl t ht) (by linarith [Real.neg_one_le_cos (y*(t-v))])
  have hzero : (∫ t in v-Real.pi/y..v+Real.pi/y, Real.cos (y*(t-v))) = 0 := by
    have hd t : HasDerivAt (fun t => Real.sin (y*(t-v))/y) (Real.cos (y*(t-v))) t := by
      apply ((((hasDerivAt_id t).sub_const v).const_mul y).sin.div_const y).congr_deriv
      simp [hy.ne']
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((by fun_prop : Continuous (fun t => Real.cos (y*(t-v)))).intervalIntegrable _ _)]
    have hargL : y*(v-Real.pi/y-v) = -Real.pi := by field_simp; ring
    have hargR : y*(v+Real.pi/y-v) = Real.pi := by field_simp; ring
    rw [hargL,hargR]
    simp
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
    intervalIntegrable_const ((by fun_prop : Continuous (fun t => Real.cos (y*(t-v)))).intervalIntegrable _ _),
    intervalIntegral.integral_const,hzero] at hi
  rw [centered_period_curvature_eq f g g' hy hf hg hc]
  have hh := div_le_div_of_nonneg_right (neg_le_neg hi) (sq_nonneg y)
  exact hh.trans_eq (by simp only [smul_eq_mul]; ring)

/-- Literal finite primes inherit the one-sided signed gain. The explicit
inverse-square endpoint/discrepancy cost is kept in full. -/
theorem prime_period_upper (f g g' : ℝ → ℝ) {a v y W V D : ℝ}
    (ha : 5000 ≤ a) (hy : 0 < y) (hW : 0 ≤ W) (hV : 0 ≤ V)
    (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hc : Continuous g')
    (hfw : ∀ t ∈ Icc (v-Real.pi/y) (v+Real.pi/y), |f t| ≤ W)
    (hgv : ∀ t ∈ Icc (v-Real.pi/y) (v+Real.pi/y), |g t| ≤ V)
    (hcurv : ∀ t ∈ Icc (v-Real.pi/y) (v+Real.pi/y), -D ≤ g' t) :
    (∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/y)⌋₊).filter Nat.Prime,
      f (Real.log p+v-Real.pi/y-a)*Real.cos (y*(Real.log p-Real.pi/y-a))/(p : ℝ)) ≤
      (2*Real.pi/y)*D/(a*y^2)+
        (W*(2*Real.pi/y)^2+(41/100 : ℝ)*(2*W+(V+y*W+2*W)*(2*Real.pi/y)))/a^2 := by
  let F := fun t => f t*Real.cos (y*(t-v))
  let G := fun t => g t*Real.cos (y*(t-v))-y*f t*Real.sin (y*(t-v))
  have hfd t : HasDerivAt F (G t) t := by
    apply ((hf t).mul ((((hasDerivAt_id t).sub_const v).const_mul y).cos)).congr_deriv
    dsimp only [G]
    simp only [id_eq,mul_one]
    ring
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt)
  have hgc : Continuous g := continuous_iff_continuousAt.mpr (fun t => (hg t).continuousAt)
  have hh : 0 ≤ 2*Real.pi/y := by positivity
  have hlo : a+(v-Real.pi/y-a) = v-Real.pi/y := by ring
  have hhi : a+2*Real.pi/y+(v-Real.pi/y-a) = v+Real.pi/y := by ring
  have hF t (ht : t ∈ Icc (v-Real.pi/y) (v+Real.pi/y)) : |F t| ≤ W := by
    dsimp only [F]
    rw [abs_mul]
    exact (mul_le_mul (hfw t ht) (Real.abs_cos_le_one _) (abs_nonneg _) hW).trans_eq (mul_one _)
  have hG t (ht : t ∈ Icc (v-Real.pi/y) (v+Real.pi/y)) : |G t| ≤ V+y*W := by
    dsimp only [G]
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_mul,abs_mul,abs_of_pos hy]
    exact add_le_add
      ((mul_le_mul (hgv t ht) (Real.abs_cos_le_one _) (abs_nonneg _) hV).trans_eq (mul_one _))
      ((mul_le_mul (mul_le_mul_of_nonneg_left (hfw t ht) hy.le)
        (Real.abs_sin_le_one _) (abs_nonneg _) (mul_nonneg hy.le hW)).trans_eq (mul_one _))
  have hb := ZetaRieszQuantitativePrimePeriod.signed_profile_bound F G (v-Real.pi/y-a)
    hfd (by dsimp [G]; fun_prop) ha (show a ≤ a+2*Real.pi/y by linarith)
    hW (by positivity : 0 ≤ V+y*W)
    (by simpa only [hlo,hhi] using hF) (by simpa only [hlo,hhi] using hG)
  rw [hlo,hhi,add_sub_cancel_left] at hb
  have hi := centered_period_upper f g g' hy hf hg hc hcurv
  have ha0 : 0 < a := by linarith
  have hu := (abs_le.mp hb).2
  have hi' := div_le_div_of_nonneg_right hi ha0.le
  have he : (∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/y)⌋₊).filter Nat.Prime,
      F (Real.log p+(v-Real.pi/y-a))/(p : ℝ)) =
      ∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/y)⌋₊).filter Nat.Prime,
        f (Real.log p+v-Real.pi/y-a)*Real.cos (y*(Real.log p-Real.pi/y-a))/(p : ℝ) := by
    apply Finset.sum_congr rfl
    intro p _
    dsimp only [F]
    congr 3 <;> ring
  rw [he] at hu
  dsimp only [F] at hu
  have hnorm : ((2*Real.pi/y)*D/y^2)/a = (2*Real.pi/y)*D/(a*y^2) := by ring
  rw [hnorm] at hi'
  linarith only [hu,hi']

/-- The existing full factorial amplitude, with its original normalization. -/
def amplitude (N : ℕ) (t : ℝ) : ℝ := Real.exp (-t/2)*t^(N+1)/N.factorial

theorem amplitude_contDiff (N : ℕ) : ContDiff ℝ ∞ (amplitude N) := by
  unfold amplitude
  fun_prop

theorem amplitude_nonneg (N : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ amplitude N t := by
  unfold amplitude
  positivity

theorem amplitude_deriv (N : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (amplitude N) ((((N : ℝ)+1)/t-1/2)*amplitude N t) t := by
  have hd := (ZetaRieszWeightedPrimeTail.factorialAmplitude_deriv (N+1) ht).div_const
    (N.factorial : ℝ)
  apply hd.congr_deriv
  simp only [Nat.cast_add,Nat.cast_one,ZetaRieszWeightedPrimeTail.factorialAmplitude,amplitude]
  ring

/-- The square of the radial score has a favorable sign. Only the
`(N+1)/t²` term can make the amplitude concave. -/
theorem amplitude_second (N : ℕ) {t : ℝ} (ht : 0 < t) :
    deriv (deriv (amplitude N)) t =
      (((((N : ℝ)+1)/t-1/2)^2-((N : ℝ)+1)/t^2)*amplitude N t) := by
  have he : deriv (amplitude N) =ᶠ[nhds t]
      (fun x => (((N : ℝ)+1)/x-1/2)*amplitude N x) := by
    filter_upwards [eventually_gt_nhds ht] with x hx
    exact (amplitude_deriv N hx).deriv
  rw [he.deriv_eq]
  have hd := ((((hasDerivAt_const t ((N : ℝ)+1)).div (hasDerivAt_id t) ht.ne').sub_const
    (1/2 : ℝ)).mul (amplitude_deriv N ht)).deriv
  change deriv (fun x => (((N : ℝ)+1)/x-1/2)*amplitude N x) t = _ at hd
  rw [hd]
  dsimp only [id_eq,Pi.div_apply]
  ring

/-- The original factorial kernel needs no square-root saddle restriction.
This numerical upper bound covers every full prime period above order `N+1`.
The radial drift is retained with its sign, before the prime error is paid. -/
theorem factorial_prime_period_upper (N : ℕ) {a v y W : ℝ}
    (ha : 5000 ≤ a) (hy : 54 ≤ y) (hv : (N : ℝ)+2 ≤ v) (hW : 0 ≤ W)
    (hw : ∀ t ∈ Icc (v-Real.pi/y) (v+Real.pi/y), amplitude N t ≤ W) :
    (∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/y)⌋₊).filter Nat.Prime,
      amplitude N (Real.log p+v-Real.pi/y-a)*Real.cos (y*(Real.log p-Real.pi/y-a))/(p : ℝ)) ≤
      W*((2*Real.pi/y)*((N : ℝ)+1)/(a*(v-Real.pi/y)^2*y^2)+4/a^2) := by
  have hy0 : 0 < y := by linarith
  have hπ : 0 < Real.pi/y := div_pos Real.pi_pos hy0
  have hπu : Real.pi/y ≤ 1/16 := (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have ht (t : ℝ) (ht : t ∈ Icc (v-Real.pi/y) (v+Real.pi/y)) :
      (N : ℝ)+1 ≤ t ∧ 0 < t := by constructor <;> linarith [ht.1,Nat.cast_nonneg (α := ℝ) N]
  have hf := amplitude_contDiff N
  have hg := (contDiff_infty_iff_deriv.mp hf).2
  have hgc := (contDiff_infty_iff_deriv.mp hg).2.continuous
  have hder := (contDiff_infty_iff_deriv.mp hf).1
  have hder' := (contDiff_infty_iff_deriv.mp hg).1
  have hfirst (t : ℝ) (hmem : t ∈ Icc (v-Real.pi/y) (v+Real.pi/y)) :
      |deriv (amplitude N) t| ≤ W/2 := by
    rw [(amplitude_deriv N (ht t hmem).2).deriv,abs_mul,
      abs_of_nonneg (amplitude_nonneg N (ht t hmem).2.le)]
    have hs : |((N : ℝ)+1)/t-1/2| ≤ 1/2 := by
      have hlo : 0 ≤ ((N : ℝ)+1)/t := div_nonneg (by positivity) (ht t hmem).2.le
      have hhi : ((N : ℝ)+1)/t ≤ 1 := (div_le_one (ht t hmem).2).mpr (ht t hmem).1
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    exact (mul_le_mul hs (hw t hmem) (amplitude_nonneg N (ht t hmem).2.le)
      (by norm_num : (0 : ℝ) ≤ 1/2)).trans_eq (by ring)
  have hcurv (t : ℝ) (hmem : t ∈ Icc (v-Real.pi/y) (v+Real.pi/y)) :
      -(((N : ℝ)+1)*W/(v-Real.pi/y)^2) ≤ deriv (deriv (amplitude N)) t := by
    rw [amplitude_second N (ht t hmem).2]
    have hv0 : 0 < v-Real.pi/y := by linarith [Nat.cast_nonneg (α := ℝ) N]
    have hsq : (v-Real.pi/y)^2 ≤ t^2 := pow_le_pow_left₀ hv0.le hmem.1 2
    have hratio : ((N : ℝ)+1)/t^2 ≤ ((N : ℝ)+1)/(v-Real.pi/y)^2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hv0) hsq
    have hmul := mul_le_mul hratio (hw t hmem) (amplitude_nonneg N (ht t hmem).2.le)
      (by positivity : 0 ≤ ((N : ℝ)+1)/(v-Real.pi/y)^2)
    have hs := mul_nonneg (sq_nonneg (((N : ℝ)+1)/t-1/2))
      (amplitude_nonneg N (ht t hmem).2.le)
    ring_nf at hmul hs ⊢
    linarith only [hmul,hs]
  have hb := prime_period_upper (amplitude N) (deriv (amplitude N))
    (deriv (deriv (amplitude N))) ha hy0 hW (div_nonneg hW (by norm_num : (0 : ℝ) ≤ 2))
    (fun t => (hder t).hasDerivAt) (fun t => (hder' t).hasDerivAt) hgc
    (fun t hm => by rw [abs_of_nonneg (amplitude_nonneg N (ht t hm).2.le)]; exact hw t hm)
    hfirst hcurv
  have hcost : W*(2*Real.pi/y)^2+(41/100 : ℝ)*(2*W+(W/2+y*W+2*W)*(2*Real.pi/y)) ≤ 4*W := by
    have hh : 2*Real.pi/y ≤ 1/8 := by
      calc
        _ = 2*(Real.pi/y) := by ring
        _ ≤ _ := by linarith
    have hsq : (2*Real.pi/y)^2 ≤ (1/8 : ℝ)^2 := pow_le_pow_left₀ (by positivity) hh 2
    have hprod : y*(2*Real.pi/y) = 2*Real.pi := by field_simp
    have hplain : (2*Real.pi/y)^2+(41/100 : ℝ)*(2+(1/2+y+2)*(2*Real.pi/y)) ≤ 4 := by
      nlinarith [Real.pi_lt_d4]
    have hm := mul_le_mul_of_nonneg_left hplain hW
    ring_nf at hm ⊢
    exact hm
  apply hb.trans
  have he := div_le_div_of_nonneg_right hcost (sq_nonneg a)
  have hden : (2*Real.pi/y)*(((N : ℝ)+1)*W/(v-Real.pi/y)^2)/(a*y^2) =
      W*((2*Real.pi/y)*((N : ℝ)+1)/(a*(v-Real.pi/y)^2*y^2)) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hden]
  calc
    _ ≤ W*((2*Real.pi/y)*((N : ℝ)+1)/(a*(v-Real.pi/y)^2*y^2))+4*W/a^2 :=
      add_le_add le_rfl he
    _ = _ := by ring

/-- A fixed factor of two compares the full factorial weight on a short
period with its central value throughout the linear radial range. -/
theorem amplitude_near (N : ℕ) {v t : ℝ} (hv : (N : ℝ)+1 ≤ v)
    (ht : 0 < t) (hd : |t-v| ≤ 1) : amplitude N t ≤ 2*amplitude N v := by
  have hv0 : 0 < v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hscore : |((N : ℝ)+1)/v-1/2| ≤ 1/2 := by
    have hl : 0 ≤ ((N : ℝ)+1)/v := by positivity
    have hu : ((N : ℝ)+1)/v ≤ 1 := (div_le_one hv0).mpr hv
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hlog := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos ht hv0)) (show 0 ≤ (N : ℝ)+1 by positivity)
  rw [Real.log_div ht.ne' hv0.ne'] at hlog
  have he : (t-v)*(((N : ℝ)+1)/v-1/2) ≤ 1/2 := by
    have hh := mul_le_mul hd hscore (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    rw [← abs_mul] at hh
    exact (le_abs_self _).trans (by simpa only [one_mul] using hh)
  have halg : ((N : ℝ)+1)*(t/v-1)-(t-v)/2 = (t-v)*(((N : ℝ)+1)/v-1/2) := by
    field_simp
  have hexp : -t/2+((N : ℝ)+1)*Real.log t ≤
      1/2+(-v/2+((N : ℝ)+1)*Real.log v) := by linarith
  have hsmall : Real.exp (1/2 : ℝ) ≤ 2 := by
    convert Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1) using 1
    norm_num
  have hpow (x : ℝ) (hx : 0 < x) : x^(N+1) = Real.exp (((N : ℝ)+1)*Real.log x) := by
    rw [← Nat.cast_add_one,Real.exp_nat_mul,Real.exp_log hx]
  unfold amplitude
  rw [hpow t ht,hpow v hv0,← Real.exp_add,← Real.exp_add]
  calc
    _ ≤ Real.exp (1/2+(-v/2+((N : ℝ)+1)*Real.log v))/N.factorial :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = Real.exp (1/2)*(Real.exp (-v/2+((N : ℝ)+1)*Real.log v)/N.factorial) := by
      rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (by positivity)

/-- The unsigned weight is used only for the already explicit cofactor and
allocation variation, not for the central oscillating term. -/
theorem prime_period_mass_bound {a y W : ℝ} (ha : 5000 ≤ a) (hy : 54 ≤ y)
    (hW : 0 ≤ W) (w : ℕ → ℝ)
    (hw : ∀ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/y)⌋₊).filter Nat.Prime,
      w p ≤ W) :
    (∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/y)⌋₊).filter Nat.Prime,
      w p/(p : ℝ)) ≤ W/a := by
  have ha0 : 0 < a := by linarith
  have hy0 : 0 < y := by linarith
  have hh : 0 ≤ 2*Real.pi/y := by positivity
  have hhu : 2*Real.pi/y ≤ 1/8 := (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hb := ZetaRieszQuantitativePrimePeriod.signed_profile_bound
    (fun _ => 1) (fun _ => 0) 0 (fun t => hasDerivAt_const t 1) continuous_const
    ha (show a ≤ a+2*Real.pi/y by linarith)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 0)
    (by intros; norm_num) (by intros; norm_num)
  simp only [add_zero,intervalIntegral.integral_const,smul_eq_mul,mul_one,
    add_sub_cancel_left,zero_add,one_mul] at hb
  have hcost : (2*Real.pi/y)^2+(41/100 : ℝ)*(2+2*(2*Real.pi/y)) ≤ 2 := by
    nlinarith [pow_le_pow_left₀ hh hhu 2]
  have hu := (abs_le.mp hb).2
  have herr := div_le_div_of_nonneg_right hcost (sq_nonneg a)
  have hmain := div_le_div_of_nonneg_right hhu ha0.le
  have hden : (1/8 : ℝ)/a+2/a^2 ≤ 1/a := by
    have hh : 2/a^2 ≤ (7/8 : ℝ)/a :=
      (div_le_div_iff₀ (sq_pos_of_pos ha0) ha0).mpr (by nlinarith)
    have he : (1/8 : ℝ)/a+(7/8 : ℝ)/a = 1/a := by ring
    linarith only [hh,he]
  have hsum : (∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/y)⌋₊).filter Nat.Prime,
      (1 : ℝ)/(p : ℝ)) ≤ 1/a := by linarith only [hu,herr,hmain,hden]
  calc
    _ ≤ ∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/y)⌋₊).filter Nat.Prime,
        W/(p : ℝ) := Finset.sum_le_sum (fun p hp =>
          div_le_div_of_nonneg_right (hw p hp) (Nat.cast_nonneg p))
    _ = W*(∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/y)⌋₊).filter Nat.Prime,
        (1 : ℝ)/(p : ℝ)) := by rw [Finset.mul_sum]; simp only [div_eq_mul_inv,one_mul]
    _ ≤ _ := (mul_le_mul_of_nonneg_left hsum hW).trans_eq (by ring)

/-- Negative curvature and the literal prime endpoints, with the full
radial tilt preserved. The cofactor's logarithm is `b`. -/
def periodCost (N : ℕ) (v y b : ℝ) : ℝ :=
  (2*Real.pi/y)*((N : ℝ)+1)/((v-Real.pi/y-b)*(v-Real.pi/y)^2*y^2)+
    4/(v-Real.pi/y-b)^2

open ZetaRieszAllowancePrimeBoxes

/-- A signed factorial prime period costs an extra inverse radial power
when its center is aligned against the coefficient's sign. This is an
actual prime sum, valid beyond the square-root saddle band. The unsigned
estimate is reserved for cofactor/allocation variation. -/
theorem factorial_period_floor (N : ℕ) {v y b c : ℝ}
    (ha : 5000 ≤ v-Real.pi/y-b) (hy : 54 ≤ y) (hv : (N : ℝ)+2 ≤ v)
    (hpeak : Real.sin (y*v) = 0) (hsign : c*Real.cos (y*v) ≤ 0) :
    -2*|c| *amplitude N v*periodCost N v y b ≤
      c*(∑ p ∈ logPrimes (v-Real.pi/y-b) (2*Real.pi/y),
        amplitude N (Real.log p+b)*(p : ℝ)⁻¹*Real.cos (y*(Real.log p+b))) ∧
    (∑ p ∈ logPrimes (v-Real.pi/y-b) (2*Real.pi/y),
      amplitude N (Real.log p+b)*(p : ℝ)⁻¹) ≤
      2*amplitude N v/(v-Real.pi/y-b) := by
  let a := v-Real.pi/y-b
  let D := logPrimes a (2*Real.pi/y)
  let W := 2*amplitude N v
  have hy0 : 0 < y := by linarith
  have ha0 : 0 < a := by dsimp [a]; linarith
  have hv0 : 0 < v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hW : 0 ≤ W := mul_nonneg (by norm_num) (amplitude_nonneg N hv0.le)
  have hπ : 0 < Real.pi/y := div_pos Real.pi_pos hy0
  have hπu : Real.pi/y ≤ 1/16 := (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hweight (t : ℝ) (ht : t ∈ Icc (v-Real.pi/y) (v+Real.pi/y)) :
      amplitude N t ≤ W := amplitude_near N (by linarith) (by linarith [ht.1,Nat.cast_nonneg (α := ℝ) N])
        (abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  have hset : D = (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/y)⌋₊).filter Nat.Prime := by
    dsimp [D,logPrimes,PrimeWindow.primesInWindow]
    rw [← Real.exp_add,add_comm (2*Real.pi/y) a]
  have hmem (p : ℕ) (hp : p ∈ D) : Real.log p+b ∈ Icc (v-Real.pi/y) (v+Real.pi/y) := by
    have hh := (logPrimes_bounds hp).2
    dsimp [a] at hh
    simp only [mul_div_assoc] at hh
    constructor <;> linarith [hh.1,hh.2]
  have hb := factorial_prime_period_upper N ha hy hv hW hweight
  have he : (∑ p ∈ D,
      amplitude N (Real.log p+b)*(p : ℝ)⁻¹*Real.cos (y*(Real.log p+b-v))) ≤
      W*periodCost N v y b := by
    have harg p : Real.log p+v-Real.pi/y-(v-Real.pi/y-b) = Real.log p+b := by ring
    have harg' p : Real.log p-Real.pi/y-(v-Real.pi/y-b) = Real.log p+b-v := by ring
    simp_rw [harg,harg'] at hb
    change _ ≤ W*periodCost N v y b at hb
    rw [← hset] at hb
    convert hb using 1
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hcost : 0 ≤ W*periodCost N v y b := by
    have hvp : 0 < v-Real.pi/y := by linarith [Nat.cast_nonneg (α := ℝ) N]
    have haa : 0 < v-Real.pi/y-b := ha0
    unfold periodCost
    positivity
  have hphase (t : ℝ) : Real.cos (y*t) = Real.cos (y*v)*Real.cos (y*(t-v)) := by
    rw [show y*t = y*v+y*(t-v) by ring,Real.cos_add,hpeak]
    ring
  have hrewrite : c*(∑ p ∈ D, amplitude N (Real.log p+b)*(p : ℝ)⁻¹*Real.cos (y*(Real.log p+b))) =
      (c*Real.cos (y*v))*(∑ p ∈ D, amplitude N (Real.log p+b)*(p : ℝ)⁻¹*Real.cos (y*(Real.log p+b-v))) := by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [hphase]
    ring
  have hc : -|c| ≤ c*Real.cos (y*v) := by
    have habs : |c*Real.cos (y*v)| ≤ |c| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg c)).trans_eq (mul_one _)
    exact (neg_le_neg habs).trans (neg_abs_le _)
  constructor
  · change _ ≤ c*(∑ p ∈ D, _)
    rw [hrewrite]
    have h₁ := mul_le_mul_of_nonpos_left he hsign
    have h₂ := mul_le_mul_of_nonneg_right hc hcost
    dsimp only [W] at h₁ h₂
    nlinarith only [h₁,h₂]
  · have hh := prime_period_mass_bound ha hy hW (fun p => amplitude N (Real.log p+b))
      (by intro p hp; exact hweight _ (hmem p (hset ▸ hp)))
    rw [← hset] at hh
    simpa only [D,a,W,div_eq_mul_inv] using hh

open ZetaRieszFixedCountPeriod

/-- A floor for the literal allocated cofactor fibre. Its signed central
response uses the one-sided period estimate; only the original cutoff and
allocation variation use the unsigned mass. Every ordinary prime in the
period is retained, and both Riesz hinges remain in `response`. -/
theorem allocated_fibre_floor {k N : ℕ} (hk : 2 ≤ k) (A : Finset ℕ)
    {v y L : ℝ} (hv : 100 ≤ v) (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y)
    (hL : (67/100 : ℝ)*v ≤ L) {a : ℕ} (ha : a ∈ cofactors k v)
    (hlog : 5000 ≤ v-Real.pi/y-Real.log a)
    (hA : ∀ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), p ∈ A)
    (hpeak : Real.sin (y*v) = 0)
    (hsign : ((-1 : ℝ)^(k+1)*(-response L v a))*Real.cos (y*v) ≤ 0) :
    let E := (2 : ℝ)^k+3*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v*Real.log a.minFac;
    -(2*amplitude N v/(L*a))*
        (responseConstant k*Real.log a.minFac*periodCost N v y (Real.log a)+
          E/(v-Real.pi/y-Real.log a)) ≤
      (∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y),
        ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re := by
  let D := logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)
  let R := fun p : ℕ => (1-ZetaRieszJointAllocation.boundedShare A N (p*a))*
    response L (Real.log p+Real.log a) a
  let w := fun p : ℕ => amplitude N (Real.log p+Real.log a)*(p : ℝ)⁻¹
  let g := fun p => w p*Real.cos (y*(Real.log p+Real.log a))
  let E := (2 : ℝ)^k+3*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v*Real.log a.minFac
  let B := responseConstant k*Real.log a.minFac
  let W := 2*amplitude N v
  let σ : ℝ := -(-1 : ℝ)^(k+1)
  let b := v-Real.pi/y-Real.log a
  have hy0 : 0 < y := by linarith
  have hyabs : |y| = y := abs_of_pos hy0
  have hy' : 54 ≤ |y| := by rwa [hyabs]
  have hv0 : 0 < v := by linarith
  have hL0 : 0 < L := by linarith
  have hb0 : 0 < b := by dsimp [b]; linarith
  have hd := cofactor_data ha
  have ha0 : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero hd.1.ne_zero
  have hB : 0 ≤ B := mul_nonneg (responseConstant_pos k).le (Real.log_natCast_nonneg _)
  have hE : 0 ≤ E := by dsimp [E]; positivity [responseConstant_pos k,Real.log_natCast_nonneg a.minFac]
  have hW : 0 ≤ W := mul_nonneg (by norm_num) (amplitude_nonneg N hv0.le)
  have hπ : 0 ≤ Real.pi/y := by positivity
  have hπu : Real.pi/y ≤ 1/16 := (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hcost : 0 ≤ periodCost N v y (Real.log a) := by
    have hb' : 0 < v-Real.pi/y-Real.log a := hb0
    unfold periodCost
    positivity
  change -(W/(L*a))*(B*periodCost N v y (Real.log a)+E/b) ≤ _
  by_cases hDn : D.Nonempty
  swap
  · have he : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hDn
    change -(W/(L*a))*(B*periodCost N v y (Real.log a)+E/b) ≤
      (∑ p ∈ D, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re
    rw [he,Finset.sum_empty,Complex.zero_re]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
  obtain ⟨p₀,hp₀⟩ := hDn
  let R₀ := (1-ZetaRieszJointAllocation.boundedShare A N (p₀*a))*response L v a
  let c := σ*R₀
  have hgeo (p : ℕ) (hp : p ∈ D) := fibre_geometry hv hy' ha (by simpa only [hyabs] using hp)
  have hlogmul (p : ℕ) (hp : p ∈ D) : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast (hgeo p hp).1.ne_zero)
      (by exact_mod_cast hd.1.ne_zero)]
  have hnot (p : ℕ) (hp : p ∈ D) : ¬p ∣ a := by
    intro hh
    exact ((hgeo p hp).2.1 p ((hgeo p hp).1.mem_primeFactors hh hd.1.ne_zero)).false
  have hθ (p : ℕ) : 0 ≤ 1-ZetaRieszJointAllocation.boundedShare A N (p*a) ∧
      1-ZetaRieszJointAllocation.boundedShare A N (p*a) ≤ 1 := by
    have hh := ZetaRieszJointAllocation.boundedShare_bounds A N (p*a)
    constructor <;> linarith
  have hσ : |σ| = 1 := by simp [σ]
  have hc : |c| ≤ B := by
    dsimp only [c,R₀]
    rw [abs_mul,hσ,one_mul,abs_mul,abs_of_nonneg (hθ p₀).1]
    exact (mul_le_mul (hθ p₀).2 (cofactor_response_bound hk ha L v)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)
  have hcphase : c*Real.cos (y*v) ≤ 0 := by
    have hh := mul_nonpos_of_nonneg_of_nonpos (hθ p₀).1 hsign
    dsimp [c,σ,R₀]
    nlinarith only [hh]
  have hperiod := factorial_period_floor N hlog hy hNv hpeak hcphase
  have hw (p : ℕ) (hp : p ∈ D) : 0 ≤ w p := by
    have hb := (logPrimes_bounds hp).2
    have ht : 0 ≤ Real.log p+Real.log a := by linarith [hb.1,Nat.cast_nonneg (α := ℝ) N]
    exact mul_nonneg (amplitude_nonneg N ht) (inv_nonneg.mpr (Nat.cast_nonneg p))
  have hg (p : ℕ) (hp : p ∈ D) : |g p| ≤ w p := by
    dsimp only [g]
    rw [abs_mul,abs_of_nonneg (hw p hp)]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hw p hp)).trans_eq (mul_one _)
  have hR (p : ℕ) (hp : p ∈ D) : |R p-R₀| ≤ E := by
    have hpT := (hgeo p hp).2.2.2.2
    have hqT := (hgeo p₀ hp₀).2.2.2.2
    rw [hyabs] at hpT hqT
    have hdif : |Real.log (p*a : ℕ)-Real.log (p₀*a : ℕ)| ≤ 1/8 :=
      abs_le.mpr ⟨by linarith [hpT.1,hqT.2.1],by linarith [hpT.2.1,hqT.1]⟩
    have hs := ZetaRieszAllocationVariation.boundedShare_fibre_variation_985 A N hd.1 (by omega)
      (hgeo p hp).1 (hnot p hp) (hA p hp) (hgeo p₀ hp₀).1 (hnot p₀ hp₀) (hA p₀ hp₀)
      hv hπ hπu hd.2.2.2.2.1 ⟨hpT.1.le,hpT.2.1⟩ ⟨hqT.1.le,hqT.2.1⟩
    rw [hd.2.1] at hs
    have hshare : |ZetaRieszJointAllocation.boundedShare A N (p*a)-
        ZetaRieszJointAllocation.boundedShare A N (p₀*a)| ≤ 3*((k : ℝ)+1)*Real.sqrt (N+1)/v := by
      apply hs.trans
      have hh := mul_le_mul_of_nonneg_left hdif
        (show 0 ≤ 20*((k : ℝ)+1)*Real.sqrt (N+1)/v by positivity)
      have hz : 0 ≤ ((k : ℝ)+1)*Real.sqrt (N+1)/v := by positivity
      ring_nf at hh hz ⊢
      linarith only [hh,hz]
    have hdifv : |Real.log p+Real.log a-v| ≤ 1 := by
      rw [hlogmul p hp] at hpT
      exact abs_le.mpr ⟨by linarith [hpT.1],by linarith [hpT.2.1]⟩
    have hresp : |response L (Real.log p+Real.log a) a-response L v a| ≤ (2 : ℝ)^k :=
      (cofactor_response_variation hk ha L (Real.log p+Real.log a) v).trans
        ((mul_le_mul_of_nonneg_left hdifv (by positivity : 0 ≤ (2 : ℝ)^k)).trans_eq (mul_one _))
    have he : R p-R₀ = (1-ZetaRieszJointAllocation.boundedShare A N (p*a))*
        (response L (Real.log p+Real.log a) a-response L v a)+
        (ZetaRieszJointAllocation.boundedShare A N (p₀*a)-
          ZetaRieszJointAllocation.boundedShare A N (p*a))*response L v a := by dsimp [R,R₀]; ring
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_of_nonneg (hθ p).1,
      abs_sub_comm (ZetaRieszJointAllocation.boundedShare A N (p₀*a))]
    have h₁ := mul_le_mul (hθ p).2 hresp (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have h₂ := mul_le_mul hshare (cofactor_response_bound hk ha L v) (abs_nonneg _)
      (by positivity : 0 ≤ 3*((k : ℝ)+1)*Real.sqrt (N+1)/v)
    dsimp only [E]
    ring_nf at h₁ h₂ ⊢
    linarith only [h₁,h₂]
  have herr : |σ*(∑ p ∈ D, (R p-R₀)*g p)| ≤ E*(∑ p ∈ D, w p) := by
    rw [abs_mul,hσ,one_mul,Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun p hp => by
      rw [abs_mul]
      exact mul_le_mul (hR p hp) (hg p hp) (abs_nonneg _) hE)
  have hsplit : σ*(∑ p ∈ D, R p*g p) =
      c*(∑ p ∈ D, g p)+σ*(∑ p ∈ D, (R p-R₀)*g p) := by
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    dsimp [c]
    ring
  have hbound : -W*(B*periodCost N v y (Real.log a)+E/b) ≤ σ*(∑ p ∈ D, R p*g p) := by
    have hc' := mul_le_mul_of_nonneg_right hc (mul_nonneg hW hcost)
    have hm := mul_le_mul_of_nonneg_left hperiod.2 hE
    have hs := hperiod.1
    have he := (abs_le.mp herr).1
    change -2*|c| *amplitude N v*periodCost N v y (Real.log a) ≤ c*(∑ p ∈ D, g p) at hs
    change E*(∑ p ∈ D, w p) ≤ E*(W/b) at hm
    rw [hsplit]
    dsimp only [W] at hc' hm ⊢
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith only [hc',hm,hs,he]
  have heq : (∑ p ∈ D, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re =
      (1/L/a)*(σ*(∑ p ∈ D, R p*g p)) := by
    rw [Complex.re_sum,Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [ZetaRieszJointAllocation.residualCoefficient,mul_assoc,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [re_response_atom hk hv hy' hL ha (by simpa only [hyabs] using hp)]
    dsimp [R,g,w,amplitude,σ]
    ring
  change _ ≤ (∑ p ∈ D, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re
  rw [heq]
  have hh := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 1/L/a by positivity)
  calc
    _ = (1/L/a)*(-W*(B*periodCost N v y (Real.log a)+E/b)) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ _ := hh

/-- A numerical inverse-square radial cost holds for every retained
cofactor share, without flattening the factorial amplitude. -/
theorem periodCost_le {N : ℕ} {v y b : ℝ} (hv : 100 ≤ v)
    (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y) (hb : b ≤ (197/200 : ℝ)*v) :
    periodCost N v y b ≤ 50000/v^2 := by
  have hv0 : 0 < v := by linarith
  have hy0 : 0 < y := by linarith
  have hπ : 0 ≤ Real.pi/y := by positivity
  have hπu : Real.pi/y ≤ 1/16 := (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have ha : v/100 ≤ v-Real.pi/y-b := by linarith
  have ha0 : 0 < v-Real.pi/y-b := (by positivity : 0 < v/100).trans_le ha
  have ht : v/2 ≤ v-Real.pi/y := by linarith
  have ht0 : 0 < v-Real.pi/y := (by positivity : 0 < v/2).trans_le ht
  have hh : 0 ≤ 2*Real.pi/y := by positivity
  have hhu : 2*Real.pi/y ≤ 1 := (div_le_iff₀ hy0).mpr (by linarith [Real.pi_lt_four])
  have hnum : (2*Real.pi/y)*((N : ℝ)+1) ≤ v :=
    (mul_le_mul_of_nonneg_right hhu (by positivity)).trans (by linarith)
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ v/2) ht 2
  have hden : v^3/400 ≤ (v-Real.pi/y-b)*(v-Real.pi/y)^2*y^2 := by
    calc
      _ = (v/100)*(v/2)^2 := by ring
      _ ≤ (v-Real.pi/y-b)*(v-Real.pi/y)^2 := mul_le_mul ha hsq (sq_nonneg _) ha0.le
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (by nlinarith : (1 : ℝ) ≤ y^2)
  have h₁ : (2*Real.pi/y)*((N : ℝ)+1)/((v-Real.pi/y-b)*(v-Real.pi/y)^2*y^2) ≤ 400/v^2 := by
    calc
      _ ≤ v/((v-Real.pi/y-b)*(v-Real.pi/y)^2*y^2) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ v/(v^3/400) := div_le_div_of_nonneg_left hv0.le (by positivity) hden
      _ = _ := by field_simp
  have h₂ : 4/(v-Real.pi/y-b)^2 ≤ 40000/v^2 := by
    calc
      _ ≤ 4/(v/100)^2 := div_le_div_of_nonneg_left (by norm_num)
        (by positivity) (pow_le_pow_left₀ (by positivity) ha 2)
      _ = _ := by ring
  unfold periodCost
  calc
    _ ≤ 400/v^2+40000/v^2 := add_le_add h₁ h₂
    _ = 40400/v^2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg v)

/-- The complete literal fibre debit, in the radial units used by the
existing positive supply. The cutoff and allocation errors are included. -/
theorem fibre_floor_radial {k N : ℕ} (hk : 2 ≤ k) (A : Finset ℕ)
    {v y L : ℝ} (hv : 500000 ≤ v) (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y)
    (hL : (67/100 : ℝ)*v ≤ L) {a : ℕ} (ha : a ∈ cofactors k v)
    (hA : ∀ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), p ∈ A)
    (hpeak : Real.sin (y*v) = 0)
    (hsign : ((-1 : ℝ)^(k+1)*(-response L v a))*Real.cos (y*v) ≤ 0) :
    -(amplitude N v/v)*
      ((200000*responseConstant k/v^2+
          1200*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v^2)*
          (Real.log a.minFac*(a : ℝ)⁻¹)+
        (400*(2 : ℝ)^k/v)*(a : ℝ)⁻¹) ≤
      (∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y),
        ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re := by
  have hv100 : 100 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hy0 : 0 < y := by linarith
  have hd := cofactor_data ha
  have ha0 : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero hd.1.ne_zero
  have hL0 : 0 < L := by linarith
  have hπ : Real.pi/y ≤ 1/16 := (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have ha' : v/100 ≤ v-Real.pi/y-Real.log a := by linarith [hd.2.2.2.2.1]
  have hlog : 5000 ≤ v-Real.pi/y-Real.log a := by linarith
  have hlog0 : 0 < v-Real.pi/y-Real.log a := by linarith
  let E := (2 : ℝ)^k+3*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v*Real.log a.minFac
  let B := responseConstant k*Real.log a.minFac
  have hE : 0 ≤ E := by dsimp [E]; positivity [responseConstant_pos k,Real.log_natCast_nonneg a.minFac]
  have hB : 0 ≤ B := mul_nonneg (responseConstant_pos k).le (Real.log_natCast_nonneg _)
  have hW : 0 ≤ amplitude N v := amplitude_nonneg N hv0.le
  have hC : 0 ≤ periodCost N v y (Real.log a) := by unfold periodCost; positivity
  have hpre : 2*amplitude N v/(L*a) ≤ 4*(amplitude N v/v)*(a : ℝ)⁻¹ := by
    have hh := div_le_div_of_nonneg_left (show 0 ≤ 2*amplitude N v by positivity)
      (show 0 < v/2 by positivity) (show v/2 ≤ L by linarith)
    have hm := mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr ha0.le)
    convert hm using 1 <;> first | rfl | (simp only [div_eq_mul_inv,mul_inv_rev]; ring)
  have hin : B*periodCost N v y (Real.log a)+E/(v-Real.pi/y-Real.log a) ≤
      B*(50000/v^2)+100*E/v := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (periodCost_le hv100 hNv hy hd.2.2.2.2.1) hB
    · exact (div_le_div_of_nonneg_left hE (by positivity : 0 < v/100) ha').trans_eq (by ring)
  have hpay := mul_le_mul hpre hin (by positivity : 0 ≤ B*periodCost N v y (Real.log a)+E/(v-Real.pi/y-Real.log a))
    (by positivity : 0 ≤ 4*(amplitude N v/v)*(a : ℝ)⁻¹)
  have he : 4*(amplitude N v/v)*(a : ℝ)⁻¹*(B*(50000/v^2)+100*E/v) =
      (amplitude N v/v)*
        ((200000*responseConstant k/v^2+1200*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v^2)*
          (Real.log a.minFac*(a : ℝ)⁻¹)+(400*(2 : ℝ)^k/v)*(a : ℝ)⁻¹) := by
    dsimp [B,E]
    ring
  rw [he] at hpay
  have hb := allocated_fibre_floor hk A hv100 hNv hy hL ha hlog hA hpeak hsign
  change -(2*amplitude N v/(L*a))*(B*periodCost N v y (Real.log a)+E/(v-Real.pi/y-Real.log a)) ≤ _ at hb
  have hh := neg_le_neg hpay
  rw [neg_mul] at hb
  simpa only [neg_mul] using hh.trans hb

/-- A count-dependent constant only; no growing-count uniformity is assumed. -/
def populationConstant (k : ℕ) : ℝ :=
  200000*responseConstant k*ZetaRieszCofactorMass.logMassConstant k+
    1200*((k : ℝ)+1)*responseConstant k*ZetaRieszCofactorMass.logMassConstant k+
    400*(2 : ℝ)^k*ZetaRieszCofactorMass.variationConstant k

/-- Summing the exact cofactor population preserves the signed saving.
At every fixed count the complete allocated debit is at most a constant
times `v^(-1/2)` of one radial supply unit, throughout the linear radial
range. Unaligned or clipped fibres are not silently included. -/
theorem population_floor {k N : ℕ} (hk : 2 ≤ k) (A S : Finset ℕ)
    {v y L : ℝ} (hv : 500000 ≤ v) (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y)
    (hL : (67/100 : ℝ)*v ≤ L) (hS : S ⊆ cofactors k v)
    (hA : ∀ a ∈ S, ∀ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), p ∈ A)
    (hpeak : Real.sin (y*v) = 0)
    (hsign : ∀ a ∈ S, ((-1 : ℝ)^(k+1)*(-response L v a))*Real.cos (y*v) ≤ 0) :
    -(populationConstant k*v^(-(1/2 : ℝ)))*(amplitude N v/v) ≤
      (∑ a ∈ S, ∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y),
        ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re := by
  have hv0 : 0 < v := by linarith
  have hk0 : 0 < k := by omega
  have hC := ZetaRieszCofactorMass.constants_pos hk0
  have hCl := hC.1
  have hB := responseConstant_pos k
  have hbase : 0 ≤ amplitude N v/v := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
  let F := 200000*responseConstant k/v^2+
    1200*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v^2
  let G := 400*(2 : ℝ)^k/v
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hrow := Finset.sum_le_sum (fun a (ha : a ∈ S) =>
    fibre_floor_radial hk A hv hNv hy hL (hS ha) (hA a ha) hpeak (hsign a ha))
  rw [← Complex.re_sum,← Finset.mul_sum] at hrow
  have hset : S ⊆ ZetaRieszCofactorMass.products k v := hS.trans (Finset.filter_subset _ _)
  have hmass : (∑ a ∈ S, (F*(Real.log a.minFac*(a : ℝ)⁻¹)+G*(a : ℝ)⁻¹)) ≤
      F*(ZetaRieszCofactorMass.logMassConstant k*v)+
        G*(ZetaRieszCofactorMass.variationConstant k*v^(1/2 : ℝ)) := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (ZetaRieszCofactorMass.log_mass hk0 hv0 S hset) hF)
      (mul_le_mul_of_nonneg_left (ZetaRieszCofactorMass.reciprocal_mass hk0 hv0 S hset) hG)
  have hrat : v^(1/2 : ℝ)/v = v^(-(1/2 : ℝ)) := by
    have hh := Real.rpow_sub hv0 (1/2 : ℝ) 1
    norm_num at hh
    exact hh.symm
  have hsqrt : Real.sqrt (N+1)/v ≤ v^(-(1/2 : ℝ)) := by
    have hh := div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (show (N : ℝ)+1 ≤ v by linarith)) hv0.le
    rwa [Real.sqrt_eq_rpow v,hrat] at hh
  have hinv : 1/v ≤ v^(-(1/2 : ℝ)) := by
    have hh := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ v by linarith)
      (show (-1 : ℝ) ≤ -(1/2 : ℝ) by norm_num)
    simpa only [Real.rpow_neg_one,one_div] using hh
  have he : F*(ZetaRieszCofactorMass.logMassConstant k*v)+
      G*(ZetaRieszCofactorMass.variationConstant k*v^(1/2 : ℝ)) =
      200000*responseConstant k*ZetaRieszCofactorMass.logMassConstant k*(1/v)+
        1200*((k : ℝ)+1)*responseConstant k*ZetaRieszCofactorMass.logMassConstant k*(Real.sqrt (N+1)/v)+
        400*(2 : ℝ)^k*ZetaRieszCofactorMass.variationConstant k*(v^(1/2 : ℝ)/v) := by
    dsimp [F,G]
    field_simp
  have hpay : F*(ZetaRieszCofactorMass.logMassConstant k*v)+
      G*(ZetaRieszCofactorMass.variationConstant k*v^(1/2 : ℝ)) ≤
      populationConstant k*v^(-(1/2 : ℝ)) := by
    rw [he,hrat]
    have h₁ := mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ 200000*responseConstant k*ZetaRieszCofactorMass.logMassConstant k by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hsqrt
      (show 0 ≤ 1200*((k : ℝ)+1)*responseConstant k*ZetaRieszCofactorMass.logMassConstant k by positivity)
    unfold populationConstant
    nlinarith only [h₁,h₂]
  have hh := mul_le_mul_of_nonpos_left (hmass.trans hpay) (neg_nonpos.mpr hbase)
  calc
    _ = -(amplitude N v/v)*(populationConstant k*v^(-(1/2 : ℝ))) := by ring
    _ ≤ _ := hh.trans hrow

/-- The literal signed population costs arbitrarily little of a radial
supply unit eventually, uniformly in its radial center and selected
cofactors. This does NOT claim source-scale decay or cover clipped periods. -/
theorem eventually_population_floor {k : ℕ} (hk : 2 ≤ k) {y ε : ℝ}
    (hy : 54 ≤ y) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (A S : Finset ℕ) (v L : ℝ),
      (N : ℝ)+2 ≤ v → (67/100 : ℝ)*v ≤ L → S ⊆ cofactors k v →
      (∀ a ∈ S, ∀ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), p ∈ A) →
      Real.sin (y*v) = 0 →
      (∀ a ∈ S, ((-1 : ℝ)^(k+1)*(-response L v a))*Real.cos (y*v) ≤ 0) →
      -ε*(Real.exp (-v/2)*v^N/N.factorial) ≤
        (∑ a ∈ S, ∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y),
          ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
            zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re := by
  have ht : Tendsto (fun v : ℝ => populationConstant k*v^(-(1/2 : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 1/2)).const_mul (populationConstant k)
  obtain ⟨v₀,hv₀⟩ := eventually_atTop.mp (ht.eventually_lt_const hε)
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop v₀,
    eventually_ge_atTop (500000 : ℕ)] with N hNv₀ hN A S v L hv hL hS hA hpeak hsign
  have hNR : (500000 : ℝ) ≤ N := by exact_mod_cast hN
  have hvbig : 500000 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hb := population_floor hk A S hvbig hv hy hL hS hA hpeak hsign
  have hs := (hv₀ v (by linarith)).le
  have hnon : 0 ≤ amplitude N v/v := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
  have he : amplitude N v/v = Real.exp (-v/2)*v^N/N.factorial := by
    unfold amplitude
    rw [pow_succ]
    field_simp
  have hh := mul_le_mul_of_nonneg_right (neg_le_neg hs) hnon
  rw [he] at hh hb
  exact hh.trans hb

/-- The original moving length and physical owner-prime mask are valid
throughout the full linear core, not just the old saddle band. -/
theorem eventually_core_geometry (k : ℕ) {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ,
      (39/20 : ℝ)*N ≤ v → v ≤ (203/100 : ℝ)*N →
      (67/100 : ℝ)*v ≤ SquarefreeVaughanLogSource.length u N ∧
      ∀ a ∈ cofactors k v, ∀ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y),
        p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N := by
  have hy0 : 0 < y := by linarith
  have hyabs : |y| = y := abs_of_pos hy0
  have hy' : 54 ≤ |y| := by rwa [hyabs]
  have hroom : u < Real.exp (-(137/200 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans (Real.exp_lt_exp.mpr (by norm_num)))
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)/(N : ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,pow_one,one_mul,add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hl.eventually_lt_const (by norm_num : (0 : ℝ) < 1/100),
    ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
      (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200) hroom,
    eventually_ge_atTop (1000 : ℕ)] with N hlog hL hN v hv hvu
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  refine ⟨by linarith,?_⟩
  intro a ha p hp
  have hgeo := fibre_geometry (by linarith : 100 ≤ v) hy' ha (by simpa only [hyabs] using hp)
  have hd := (cofactor_data ha).2.2.2.2.1
  have hpb := logPrimes_bounds hp
  have hpi : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  apply (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mpr
  refine ⟨hgeo.1,?_,?_⟩
  · have hlg : 2*Real.log (N : ℝ) < (N : ℝ)/50 := by
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
      have hrad := hgeo.2.2.2.2.2.1
      rw [hyabs] at hrad
      nlinarith
    have he : Real.log (((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) : ℝ) =
        SquarefreeVaughanLogSource.length u N := by
      simp only [SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hgeo.1.pos) (by positivity)).mp (he ▸ htop)

/-- Unique largest-prime ownership makes the cofactor estimate a bound for
a literal set of integer labels. No incidence multiplicity is added. -/
theorem sum_owned_subset {k : ℕ} {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ y)
    (S : Finset ℕ) (hS : S ⊆ cofactors k v) (f : ℕ → ℂ) :
    (∑ n ∈ S.biUnion (fun a =>
      (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p)), f n) =
      ∑ a ∈ S, ∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), f (p*a) := by
  have hyabs : |y| = y := abs_of_pos (by linarith)
  have hy' : 54 ≤ |y| := by rwa [hyabs]
  rw [ZetaRieszCoupledWindow.sum_owned_products _ _ f
    (fun a ha => (cofactor_data (hS ha)).1.ne_zero) (by
      intro a ha p hp
      have hg := fibre_geometry hv hy' (hS ha) (by simpa only [hyabs] using hp)
      exact ⟨hg.1,fun q hq hd => hg.2.1 q
        (hq.mem_primeFactors hd (cofactor_data (hS ha)).1.ne_zero)⟩)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.mul_comm]

/-- An independent signed floor for the actual phase-aligned population
inside any complete period in the core. The moving length, allocation and
physical prime set are the original ones. This is a relative radial-unit
payment, not a floor for all of `joinedPhysical`. -/
theorem eventually_core_aligned_floor {k : ℕ} (hk : 2 ≤ k) {u y ε : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ,
      (39/20 : ℝ)*N ≤ v-Real.pi/y → v+Real.pi/y ≤ (203/100 : ℝ)*N →
      Real.sin (y*v) = 0 →
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let S := (cofactors k v).filter
        (fun a => ((-1 : ℝ)^(k+1)*(-response L v a))*Real.cos (y*v) ≤ 0)
      let P := S.biUnion (fun a =>
        (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p));
      -ε*(Real.exp (-v/2)*v^N/N.factorial) ≤
        (∑ n ∈ P, ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hy0 : 0 < y := by linarith
  have hpi : 0 ≤ Real.pi/y := by positivity
  filter_upwards [eventually_population_floor hk hy hε,
    eventually_core_geometry k hu hU hy,eventually_ge_atTop (1000 : ℕ)] with N hN hgeo hlarge v hv hvu hpeak
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hvc : (39/20 : ℝ)*N ≤ v := by linarith
  have hvcu : v ≤ (203/100 : ℝ)*N := by linarith
  have hvg := hgeo v hvc hvcu
  dsimp only
  rw [sum_owned_subset (by linarith : 100 ≤ v) hy _ (Finset.filter_subset _ _)]
  apply hN _ _ v _ (by linarith) hvg.1 (Finset.filter_subset _ _)
  · intro a ha p hp
    exact hvg.2 a (Finset.mem_filter.mp ha).1 p hp
  · exact hpeak
  · intro a ha
    exact (Finset.mem_filter.mp ha).2

/-- The integer family in the floor theorem is a genuine subfamily of the
original core once the original order/count hypotheses are supplied. -/
theorem owned_subset_core {k : ℕ} (hk : 2 ≤ k) (j : ℕ) (hj : 32 ≤ j)
    (hcount : k+1 < ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) {u v y : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hv : 100 ≤ v)
    (hL : (5/4 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
    (hlo : (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ v-Real.pi/y)
    (hhi : v+Real.pi/y ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
    (S : Finset ℕ) (hS : S ⊆ cofactors k v) :
    S.biUnion (fun a => (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p)) ⊆
      ZetaRieszParityPacket.coreBand u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
        (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) := by
  have hyabs : |y| = y := abs_of_pos (by linarith)
  have hy' : 54 ≤ |y| := by rwa [hyabs]
  have hp := population_subset_core hk j hj hcount hu hU hy' hv hL
    (by simpa only [hyabs] using hlo) (by simpa only [hyabs] using hhi)
  apply Finset.Subset.trans _ hp
  intro n hn
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  apply Finset.mem_biUnion.mpr
  exact ⟨a,hS ha,by simpa only [hyabs] using hn⟩

end RiemannGaussian.ZetaRieszSignedPeriodFloor
