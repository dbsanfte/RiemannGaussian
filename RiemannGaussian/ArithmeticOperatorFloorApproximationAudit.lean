/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorHeatFloorAudit
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Quantitative source obstruction for arbitrary cutoff-row approximation

Density is cancelled inside each exact floor row. At an actual right-half
zeta zero, every finite complex combination still has zero Mellin value,
whereas the constant target has value `1 / rho`. Cauchy--Schwarz gives a
strictly positive critical squared-error lower bound, independently of
the coefficients, their number or how a nonlinear optimizer chooses them.

This is a scoped obstruction to obtaining approximation decay from row
identities or Gram positivity alone. It is not a refutation of classical
Nyman--Beurling approximation with genuinely new arithmetic input.
-/

namespace RiemannGaussian.ArithmeticOperatorFloorApproximationAudit
noncomputable section
open Complex Filter MeasureTheory Set
open ArithmeticOperatorFloorSourceAudit ArithmeticOperatorHeatFloorAudit
open scoped BigOperators Topology

/-- A density-balanced dilation of the unchanged literal floor. -/
def row (h t : ℝ) : ℂ :=
  (centeredFloor (t+h) : ℂ)-(Real.exp h : ℂ)*(centeredFloor t : ℂ)

/-- All cutoff discontinuities and their endpoints remain in the row. -/
theorem row_eq_floors (h t : ℝ) :
    row h t = ((⌊Real.exp (t+h)⌋ : ℤ) : ℂ)-
      (Real.exp h : ℂ)*((⌊Real.exp t⌋ : ℤ) : ℂ) := by
  unfold row centeredFloor
  rw [Real.exp_add]
  push_cast
  ring

/-- Ordinary positive integer divisor scales are actual members of this family. -/
theorem row_integer (d : ℕ) (hd : 0<d) (t : ℝ) :
    row (-Real.log d) t = ((⌊Real.exp t/(d : ℝ)⌋ : ℤ) : ℂ)-
      (d : ℂ)⁻¹*((⌊Real.exp t⌋ : ℤ) : ℂ) := by
  have hd0 : (0 : ℝ)<d := by exact_mod_cast hd
  rw [row_eq_floors,Real.exp_add,Real.exp_neg,Real.exp_log hd0]
  simp only [Complex.ofReal_inv,Complex.ofReal_natCast,div_eq_mul_inv]

theorem row_zero_of_neg {h t : ℝ} (hh : h≤0) (ht : t<0) : row h t=0 := by
  have hf (v : ℝ) (hv : v<0) : (⌊Real.exp v⌋ : ℤ)=0 :=
    Int.floor_eq_iff.mpr ⟨by simpa using (Real.exp_pos v).le,
      by simpa using Real.exp_lt_exp.mpr hv⟩
  rw [row_eq_floors,hf (t+h) (by linarith),hf t ht]
  simp

theorem measurable_row (h : ℝ) : Measurable (row h) := by
  unfold row centeredFloor
  fun_prop

theorem norm_row_le (h t : ℝ) : ‖row h t‖≤1+Real.exp h := by
  apply (norm_sub_le _ _).trans
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos h),mul_one] using
    add_le_add (centeredFloor_abs_le_one (t+h))
      (mul_le_mul_of_nonneg_left (centeredFloor_abs_le_one t) (Real.exp_pos h).le)

theorem integrable_row_transform {s : ℂ} (hs : 0<s.re) (hs1 : s.re<1)
    (h : ℝ) : Integrable (fun t : ℝ => Complex.exp (-s*t)*row h t) := by
  have hi := (integrable_shifted_floor hs hs1 h).sub
    ((integrable_floorTransform hs hs1).const_mul (Real.exp h : ℂ))
  refine hi.congr (Eventually.of_forall (fun t => ?_))
  dsimp [row]
  ring

/-- Actual row transform, before specializing to a zero. -/
theorem integral_row {s : ℂ} (hs : 0<s.re) (hs1 : s.re<1) (h : ℝ) :
    (∫ t : ℝ,Complex.exp (-s*t)*row h t)=
      (Complex.exp (s*h)-(Real.exp h : ℂ))*riemannZeta s/s := by
  have hi := integrable_floorTransform hs hs1
  have hij := integrable_shifted_floor hs hs1 h
  have he (t : ℝ) : Complex.exp (-s*t)*row h t=
      Complex.exp (-s*t)*(centeredFloor (t+h) : ℂ)-
        (Real.exp h : ℂ)*(Complex.exp (-s*t)*(centeredFloor t : ℂ)) := by
    dsimp [row]
    ring
  simp_rw [he]
  rw [integral_sub hij (hi.const_mul _),integral_shifted_floor,integral_const_mul]
  change Complex.exp (s*h)*floorTransform s-(Real.exp h : ℂ)*floorTransform s=_
  rw [floorTransform_eq_zeta_div hs hs1]
  ring

theorem integral_Ioi_row {s : ℂ} (hs : 0<s.re) (hs1 : s.re<1)
    {h : ℝ} (hh : h≤0) :
    (∫ t : ℝ in Ioi 0,Complex.exp (-s*t)*row h t)=
      (Complex.exp (s*h)-(Real.exp h : ℂ))*riemannZeta s/s := by
  rw [←integral_Ici_eq_integral_Ioi,setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_row hs hs1 h
  · intro t ht
    rw [row_zero_of_neg hh (lt_of_not_ge ht),mul_zero]

/-- Full complex error; no coefficient or floor row is discarded. -/
def error {d : ℕ} (h : Fin d → ℝ) (c : Fin d → ℂ) (t : ℝ) : ℂ :=
  1-∑ j,c j*row (h j) t

/-- Complete critical squared error, with no finite-interval tail deletion. -/
def energy {d : ℕ} (h : Fin d → ℝ) (c : Fin d → ℂ) : ℝ :=
  ∫ t : ℝ in Ioi 0,Real.exp (-t)*‖error h c t‖^2

theorem measurable_error {d : ℕ} (h : Fin d → ℝ) (c : Fin d → ℂ) :
    Measurable (error h c) := by
  unfold error
  exact measurable_const.sub (Finset.measurable_sum _
    (fun j _ => measurable_const.mul (measurable_row (h j))))

theorem norm_error_le {d : ℕ} (h : Fin d → ℝ) (c : Fin d → ℂ) (t : ℝ) :
    ‖error h c t‖≤1+∑ j,‖c j‖*(1+Real.exp (h j)) := by
  apply (norm_sub_le _ _).trans
  simpa only [norm_one] using add_le_add_right
    ((norm_sum_le Finset.univ (fun j : Fin d => c j*row (h j) t)).trans
      (Finset.sum_le_sum fun j _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_row_le (h j) t) (norm_nonneg _))) 1

theorem integrable_energy {d : ℕ} (h : Fin d → ℝ) (c : Fin d → ℂ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t)*‖error h c t‖^2) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ)<0) 0
  apply hi.mul_bdd ((measurable_error h c).norm.pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_error_le h c t) 2

theorem energy_nonneg {d : ℕ} (h : Fin d → ℝ) (c : Fin d → ℂ) :
    0≤energy h c := integral_nonneg (fun _ => by positivity)

/-- The constant target restores a nonzero source after the row annihilator. -/
theorem integral_error_at_zero {d : ℕ} {s : ℂ} (hs : 0<s.re) (hs1 : s.re<1)
    (hz : riemannZeta s=0) {h : Fin d → ℝ} (hh : ∀ j,h j≤0) (c : Fin d → ℂ) :
    (∫ t : ℝ in Ioi 0,Complex.exp (-s*t)*error h c t)=1/s := by
  have hi := integrableOn_exp_mul_complex_Ioi (by simpa using hs : (-s).re<0) 0
  have hj (j : Fin d) : IntegrableOn
      (fun t : ℝ => c j*(Complex.exp (-s*t)*row (h j) t)) (Ioi 0) :=
    ((integrable_row_transform hs hs1 (h j)).restrict).const_mul (c j)
  have he (t : ℝ) : Complex.exp (-s*t)*error h c t=
      Complex.exp (-s*t)-∑ j,c j*(Complex.exp (-s*t)*row (h j) t) := by
    dsimp [error]
    rw [mul_sub,mul_one,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_sub hi (integrable_finsetSum _ (fun j _ => hj j)),
    integral_finsetSum _ (fun j _ => hj j)]
  simp_rw [integral_const_mul,integral_Ioi_row hs hs1 (hh _),hz,mul_zero,zero_div,
    mul_zero,Finset.sum_const_zero,sub_zero]
  simpa using integral_exp_mul_complex_Ioi (by simpa using hs : (-s).re<0) 0

/-- Every coefficient choice has the same strictly positive source-sensitive
critical error lower bound. No positivity restriction on the coefficients. -/
theorem source_energy_lower {d : ℕ} {s : ℂ} (hs : 1/2<s.re) (hs1 : s.re<1)
    (hz : riemannZeta s=0) {h : Fin d → ℝ} (hh : ∀ j,h j≤0) (c : Fin d → ℂ) :
    (2*s.re-1)*‖1/s‖^2≤energy h c := by
  let f : ℝ → ℝ := fun t => Real.exp (-(1/2)*t)*‖error h c t‖
  let g : ℝ → ℝ := fun t => Real.exp (-(s.re-1/2)*t)
  have hf0 (t : ℝ) : 0≤f t := by dsimp [f]; positivity
  have hg0 (t : ℝ) : 0≤g t := (Real.exp_pos _).le
  have hfsq (t : ℝ) : f t^2=Real.exp (-t)*‖error h c t‖^2 := by
    dsimp [f]
    rw [mul_pow]
    congr 1
    rw [sq,←Real.exp_add]
    congr 1
    ring
  have hgsq (t : ℝ) : g t^2=Real.exp (-(2*s.re-1)*t) := by
    dsimp [g]
    rw [sq,←Real.exp_add]
    congr 1
    ring
  have hfi : IntegrableOn (fun t : ℝ => f t^2) (Ioi 0) := by
    simp_rw [hfsq]
    exact integrable_energy h c
  have hgi : IntegrableOn (fun t : ℝ => g t^2) (Ioi 0) := by
    simp_rw [hgsq]
    exact integrableOn_exp_mul_Ioi (by linarith : -(2*s.re-1)<0) 0
  have hfm : Measurable f := by
    dsimp [f]
    exact (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      (measurable_error h c).norm
  have hgm : Measurable g := by dsimp [g]; fun_prop
  have hf : MemLp f (ENNReal.ofReal (2 : ℝ)) (volume.restrict (Ioi 0)) := by
    simpa using (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr hfi
  have hg : MemLp g (ENNReal.ofReal (2 : ℝ)) (volume.restrict (Ioi 0)) := by
    simpa using (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr hgi
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (Real.holderConjugate_iff.mpr ⟨(by norm_num : (1 : ℝ)<2),
      (by norm_num : (2 : ℝ)⁻¹+2⁻¹=1)⟩)
    (Eventually.of_forall hf0) (Eventually.of_forall hg0) hf hg
  have hF : (∫ t : ℝ in Ioi 0,f t^2)=energy h c := by simp_rw [hfsq]; rfl
  have hG : (∫ t : ℝ in Ioi 0,g t^2)=1/(2*s.re-1) := by
    simp_rw [hgsq]
    rw [integral_exp_mul_Ioi (by linarith : -(2*s.re-1)<0)]
    simp only [mul_zero,Real.exp_zero,neg_div_neg_eq]
  have hcs : (∫ t : ℝ in Ioi 0,f t*g t)≤
      Real.sqrt (energy h c)*Real.sqrt (1/(2*s.re-1)) := by
    simpa only [Real.rpow_two,←Real.sqrt_eq_rpow,hF,hG] using hholder
  have hpoint (t : ℝ) : ‖Complex.exp (-s*t)*error h c t‖=f t*g t := by
    rw [norm_mul,Complex.norm_exp]
    simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.neg_im,
      Complex.ofReal_im,mul_zero,sub_zero]
    have he : Real.exp (-s.re*t)=Real.exp (-(1/2)*t)*Real.exp (-(s.re-1/2)*t) := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [he]
    dsimp [f,g]
    ring
  have hn : ‖1/s‖≤Real.sqrt (energy h c)*Real.sqrt (1/(2*s.re-1)) := by
    rw [←integral_error_at_zero (by linarith : 0<s.re) hs1 hz hh c]
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [hpoint]
    exact hcs
  have hd : 0<2*s.re-1 := by linarith
  have hsquare : ‖1/s‖^2≤energy h c/(2*s.re-1) := by
    calc
      _ ≤ (Real.sqrt (energy h c)*Real.sqrt (1/(2*s.re-1)))^2 :=
        pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = _ := by
        rw [mul_pow,Real.sq_sqrt (energy_nonneg h c),
          Real.sq_sqrt (by positivity : 0≤1/(2*s.re-1))]
        ring
  simpa only [mul_comm] using (le_div_iff₀ hd).mp hsquare

/-- Exact source size in ordinary zero coordinates. -/
def barrier (s : ℂ) : ℝ := (2*s.re-1)/‖s‖^2

theorem barrier_pos {s : ℂ} (hs : 1/2<s.re) : 0<barrier s := by
  have hne : s≠0 := by intro he; rw [he] at hs; norm_num at hs
  exact div_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr hne))

/-- No finite optimizer can improve past this actual-zero barrier. -/
theorem barrier_le_energy {d : ℕ} {s : ℂ} (hs : 1/2<s.re) (hs1 : s.re<1)
    (hz : riemannZeta s=0) {h : Fin d → ℝ} (hh : ∀ j,h j≤0) (c : Fin d → ℂ) :
    barrier s≤energy h c := by
  have he : (2*s.re-1)*‖(1 : ℂ)/s‖^2=barrier s := by
    rw [norm_div,norm_one,div_pow,one_pow]
    dsimp [barrier]
    ring
  rw [←he]
  exact source_energy_lower hs hs1 hz hh c

/-- Arbitrarily growing row sets and nonlinear/moving coefficient choices
retain the same positive lower bound; no asymptotic coefficient budget enters. -/
theorem not_tendsto_energy_zero {s : ℂ} (hs : 1/2<s.re) (hs1 : s.re<1)
    (hz : riemannZeta s=0) (d : ℕ → ℕ) (h : (n : ℕ) → Fin (d n) → ℝ)
    (hh : ∀ n j,h n j≤0) (c : (n : ℕ) → Fin (d n) → ℂ) :
    ¬Tendsto (fun n => energy (h n) (c n)) atTop (𝓝 0) := by
  intro ht
  have hbound : barrier s≤0 := ge_of_tendsto ht
    (Eventually.of_forall (fun n => barrier_le_energy hs hs1 hz (hh n) (c n)))
  exact (not_le_of_gt (barrier_pos hs)) hbound

/-- Genuine approximation decay would supply nonvanishing, rather than
follow from the exact row identities or the positivity of their Gram matrix. -/
theorem nonvanishing_of_energy_decay {s : ℂ} (hs : 1/2<s.re) (hs1 : s.re<1)
    (d : ℕ → ℕ) (h : (n : ℕ) → Fin (d n) → ℝ) (hh : ∀ n j,h n j≤0)
    (c : (n : ℕ) → Fin (d n) → ℂ)
    (ht : Tendsto (fun n => energy (h n) (c n)) atTop (𝓝 0)) :
    riemannZeta s≠0 := by
  intro hz
  exact not_tendsto_energy_zero hs hs1 hz d h hh c ht

end
end RiemannGaussian.ArithmeticOperatorFloorApproximationAudit
