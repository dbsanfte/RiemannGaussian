/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMarkedSaturation

/-!
# What matching the logarithmic slope does, and does not, cancel

This is an audit of an analytic shortcut, not a prime-sum estimate.
The literal factorial rectangle kills the simple-zero cofactor model.
A simple-pole cofactor, matched to its own logarithmic derivative just as
exactly, retains a positive reciprocal-order mass. Thus the Ward identity
alone cannot supply the missing bound. The actual ordered Euler product,
both Fourier frequencies and their joint integral still matter.
-/

namespace RiemannGaussian.ZetaRieszWardWindowAudit
noncomputable section
open scoped BigOperators Classical
open Complex Filter Topology
open ZetaRieszSkewAllocation ZetaRieszWideOwnerAudit

/-- A normalized synthetic pole at signed Taylor radius one. -/
def pole (s : ℂ) : ℂ := (s+1)⁻¹

/-- A normalized synthetic simple zero at the same radius. -/
def zeroMode (s : ℂ) : ℂ := s+1

theorem moment_pole (k : ℕ) : signedTaylorMoment k pole 0 = 1 := by
  change signedTaylorMoment k (fun z : ℂ => (z+1)⁻¹) 0 = 1
  simpa only [one_mul,one_pow,inv_one] using signedTaylorMoment_inv_linear k 1 1

/-- The pole is matched to its OWN slope, not to another function. -/
theorem neg_logDeriv_pole {s : ℂ} (hs : s+1 ≠ 0) :
    -logDeriv pole s = pole s := by
  have hd := ((hasDerivAt_id s).add_const 1).inv hs
  change HasDerivAt (fun z : ℂ => (z+1)⁻¹) (-1/(s+1)^2) s at hd
  rw [logDeriv_apply]
  change -(deriv (fun z : ℂ => (z+1)⁻¹) s/(s+1)⁻¹) = (s+1)⁻¹
  rw [hd.deriv]
  field_simp

theorem moment_pole_slope (k : ℕ) :
    signedTaylorMoment k (fun s => -logDeriv pole s) 0 = 1 := by
  have he : (fun s => -logDeriv pole s) =ᶠ[nhds 0] pole := by
    filter_upwards [(continuousAt_id.add_const (1 : ℂ)).eventually_ne
      (by norm_num : (0 : ℂ)+1 ≠ 0)] with s hs
    exact neg_logDeriv_pole hs
  rw [signedTaylorMoment_congr k he,moment_pole]

theorem moment_zeroMode {k : ℕ} (hk : 2 ≤ k) :
    signedTaylorMoment k zeroMode 0 = 0 := by
  change signedTaylorMoment k (fun z : ℂ => z+1) 0 = 0
  rw [signedTaylorMoment_add k (f := fun z : ℂ => z) (g := fun _ : ℂ => 1)
    analyticAt_id analyticAt_const]
  simp [signedTaylorMoment,iteratedDeriv_fun_id_zero,iteratedDeriv_const,
    show k ≠ 0 by omega,show k ≠ 1 by omega]

/-- Every retained cofactor order is genuinely at least two. This
uses the actual owner/least-order rectangle, not a limiting share box. -/
theorem rectangle_cofactor_ge_two {N j h : ℕ} (hN : 4 ≤ N)
    (hh : h ∈ rectangleOrders N j) : 2 ≤ N+1-j-h := by
  have hb := (Finset.mem_filter.mp hh).2
  have hj := hb.2.2.1
  have hh' := hb.2.2.2.2
  omega

/-- The same restricted convolution as in the matched symbol, with
an arbitrary low leg. Its signed reciprocal marked order is retained. -/
def modelRectangle (F : ℂ → ℂ) (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ rectangleOrders N j,
    (signedTaylorMoment (j-1) (fun s => -logDeriv F s) 0/(j : ℂ))*
      a h*signedTaylorMoment (N+1-j-h) F 0

/-- A pure simple-zero cofactor vanishes on the exact order window,
independently of every coefficient of the least-prime slot. -/
theorem zeroMode_rectangle (a : ℕ → ℂ) {N : ℕ} (hN : 4 ≤ N) :
    modelRectangle zeroMode a N = 0 := by
  apply Finset.sum_eq_zero
  intro j _hj
  apply Finset.sum_eq_zero
  intro h hh
  rw [moment_zeroMode (rectangle_cofactor_ge_two hN hh),mul_zero]

/-- Matching a pole to its own slope instead leaves the complete
positive selected-order mass; no Ward cancellation removes it. -/
theorem pole_rectangle (a : ℕ → ℂ) (N : ℕ) :
    modelRectangle pole a N =
      ∑ j ∈ Finset.range (N+2), ∑ h ∈ rectangleOrders N j, a h/(j : ℂ) := by
  simp only [modelRectangle,moment_pole,moment_pole_slope,mul_one]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro h _hh
  ring

/-- A concrete reciprocal low leg. This is a synthetic analytic test,
not a replacement for the actual least-prime factor. -/
def reciprocalMass (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ rectangleOrders N j,
    1/((j : ℝ)*(h+1))

theorem reciprocalMass_nonneg (N : ℕ) : 0 ≤ reciprocalMass N :=
  Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun h _ => by positivity))

theorem pole_reciprocal_rectangle (N : ℕ) :
    modelRectangle pole (fun h => 1/((h : ℂ)+1)) N = (reciprocalMass N : ℂ) := by
  rw [pole_rectangle,reciprocalMass]
  push_cast
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro h _hh
  rw [div_div, mul_comm ((h : ℂ)+1)]

theorem norm_pole_reciprocal_rectangle (N : ℕ) :
    ‖modelRectangle pole (fun h => 1/((h : ℂ)+1)) N‖ = reciprocalMass N := by
  rw [pole_reciprocal_rectangle,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (reciprocalMass_nonneg N)]

/-- A fixed positive-area rectangle lies inside the original order
mask at every order 400*t. No numerical rounding is used. -/
theorem subrectangle_mem {t j h : ℕ} (ht : 1 ≤ t)
    (hj : j ∈ Finset.Icc (210*t) (230*t))
    (hh : h ∈ Finset.Icc (4*t) (12*t-1)) :
    j ∈ Finset.range (400*t+2) ∧ h ∈ rectangleOrders (400*t) j := by
  obtain ⟨hj0,hj1⟩ := Finset.mem_Icc.mp hj
  obtain ⟨hh0,hh1⟩ := Finset.mem_Icc.mp hh
  simp only [rectangleOrders,ownerOrders,Finset.mem_filter,Finset.mem_range]
  omega

/-- The positive pole mass stays above 1/20 on a cofinal sequence.
It is not even o(1), despite exact matching of function and slope. -/
theorem reciprocalMass_lower {t : ℕ} (ht : 1 ≤ t) :
    (1/20 : ℝ) ≤ reciprocalMass (400*t) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hjsub : Finset.Icc (210*t) (230*t) ⊆ Finset.range (400*t+2) := by
    intro j hj
    have := Finset.mem_Icc.mp hj
    simp only [Finset.mem_range]
    omega
  have hsub (j : ℕ) (hj : j ∈ Finset.Icc (210*t) (230*t)) :
      Finset.Icc (4*t) (12*t-1) ⊆ rectangleOrders (400*t) j :=
    fun h hh => (subrectangle_mem ht hj hh).2
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc (210*t) (230*t))
      (h : ℕ) (hh : h ∈ Finset.Icc (4*t) (12*t-1)) :
      1/((230*(t : ℝ))*(12*t)) ≤ 1/((j : ℝ)*(h+1)) := by
    obtain ⟨hj0,hj1⟩ := Finset.mem_Icc.mp hj
    obtain ⟨hh0,hh1⟩ := Finset.mem_Icc.mp hh
    have hjp : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hjR : (j : ℝ) ≤ 230*t := by exact_mod_cast hj1
    have hhR : (h : ℝ)+1 ≤ 12*t := by exact_mod_cast (show h+1 ≤ 12*t by omega)
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (j : ℝ)*(h+1))
    exact mul_le_mul hjR hhR (by positivity) (by positivity)
  have hcj : (Finset.Icc (210*t) (230*t)).card = 20*t+1 := by
    rw [Nat.card_Icc]; omega
  have hch : (Finset.Icc (4*t) (12*t-1)).card = 8*t := by
    rw [Nat.card_Icc]; omega
  have hsmall : (1/20 : ℝ) ≤ ((20*(t : ℝ)+1)*(8*t)) /
      ((230*t)*(12*t)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (230*(t : ℝ))*(12*t))).mpr
    nlinarith [sq_pos_of_pos htR]
  calc
    _ ≤ ((20*(t : ℝ)+1)*(8*t))/((230*t)*(12*t)) := hsmall
    _ = ∑ _j ∈ Finset.Icc (210*t) (230*t), ∑ _h ∈ Finset.Icc (4*t) (12*t-1),
        1/((230*(t : ℝ))*(12*t)) := by
      simp only [Finset.sum_const,nsmul_eq_mul,hcj,hch]
      push_cast
      ring
    _ ≤ ∑ j ∈ Finset.Icc (210*t) (230*t), ∑ h ∈ Finset.Icc (4*t) (12*t-1),
        1/((j : ℝ)*(h+1)) := Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (hterm j hj))
    _ ≤ ∑ j ∈ Finset.Icc (210*t) (230*t), ∑ h ∈ rectangleOrders (400*t) j,
        1/((j : ℝ)*(h+1)) := Finset.sum_le_sum (fun j hj =>
          Finset.sum_le_sum_of_subset_of_nonneg (hsub j hj) (fun _ _ _ => by positivity))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hjsub (fun j _ _ =>
      Finset.sum_nonneg (fun h _ => by positivity))

/-- The exact order-window mass cannot tend to zero. This rules out
using the generic matched-slope law as a packet-decay theorem. -/
theorem not_tendsto_reciprocalMass :
    ¬Tendsto reciprocalMass atTop (nhds 0) := by
  intro h
  have hc : Tendsto (fun t : ℕ => 400*t) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with t ht
    omega
  have hl : (1/20 : ℝ) ≤ 0 := ge_of_tendsto (h.comp hc) (by
    filter_upwards [eventually_ge_atTop 1] with t ht
    exact reciprocalMass_lower ht)
  norm_num at hl

/-- A fully matched analytic pole and a fixed reciprocal low-leg
sequence refute a generic norm-decay conclusion for this order mask. -/
theorem not_tendsto_pole_rectangle_norm :
    ¬Tendsto (fun N => ‖modelRectangle pole (fun h => 1/((h : ℂ)+1)) N‖)
      atTop (nhds 0) := by
  simpa only [norm_pole_reciprocal_rectangle] using not_tendsto_reciprocalMass

/-- The integer gamma tail occurring in the coupled pole-model audit.
Its identification with a Fourier integral is not asserted here. -/
def poissonPrefix (m : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x)*∑ k ∈ Finset.range (m+1), x^k/(k.factorial : ℝ)

theorem poissonPrefix_nonneg (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ poissonPrefix m x := by
  unfold poissonPrefix
  positivity

/-- An exact rational tilt, without a normal or numerical approximation. -/
theorem poissonPrefix_tilt (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    poissonPrefix m x ≤ (10/9 : ℝ)^m*Real.exp (-x/10) := by
  have hk (k : ℕ) (hkm : k ∈ Finset.range (m+1)) :
      x^k/(k.factorial : ℝ) ≤ (10/9 : ℝ)^m*((9/10*x)^k/(k.factorial : ℝ)) := by
    have hp : (10/9 : ℝ)^k ≤ (10/9 : ℝ)^m :=
      pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hkm; omega)
    calc
      _ = (10/9 : ℝ)^k*((9/10*x)^k/(k.factorial : ℝ)) := by
        rw [← mul_div_assoc,← mul_pow,
          show (10/9 : ℝ)*(9/10*x) = x by ring]
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (by positivity)
  have he := Real.sum_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 9/10*x) (m+1)
  unfold poissonPrefix
  calc
    _ ≤ Real.exp (-x)*∑ k ∈ Finset.range (m+1),
        (10/9 : ℝ)^m*((9/10*x)^k/(k.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hk) (Real.exp_pos _).le
    _ = (10/9 : ℝ)^m*(Real.exp (-x)*
        ∑ k ∈ Finset.range (m+1), (9/10*x)^k/(k.factorial : ℝ)) := by
      rw [← Finset.mul_sum]; ring
    _ ≤ (10/9 : ℝ)^m*(Real.exp (-x)*Real.exp (9/10*x)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

/-- The literal largest-plus-least order bound is below the eventual
radial cutoff mean by a fixed margin. -/
theorem rectangle_joint_order {N j h : ℕ} (hh : h ∈ rectangleOrders N j) :
    200*(j+h) ≤ 123*N := by
  have hb := (Finset.mem_filter.mp hh).2
  omega

/-- The coupled time-profile's three tails all have this fixed saving.
The moving physical length supplies x=L/2>=11N/16 eventually. -/
theorem poissonPrefix_rectangle_bound (N m : ℕ) {x : ℝ}
    (hx : (11/16 : ℝ)*N ≤ x) (hm : 200*m ≤ 123*N) :
    poissonPrefix m x ≤ Real.exp (-(N : ℝ)/300) := by
  have hx0 : 0 ≤ x := (by positivity : (0 : ℝ) ≤ (11/16 : ℝ)*N).trans hx
  have hlog : Real.log (10/9 : ℝ) ≤ 53/500 := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 10/9)).mpr
    have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 53/500) 4
    norm_num [Finset.sum_range_succ] at he
    linarith
  have hmR : 200*(m : ℝ) ≤ 123*N := by exact_mod_cast hm
  have hp : (10/9 : ℝ)^m = Real.exp ((m : ℝ)*Real.log (10/9)) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  apply (poissonPrefix_tilt m hx0).trans
  rw [hp,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hl := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Keep the three integer-gamma tails joined with their exact signs.
This scalar model is not yet an identity for the literal Euler integral. -/
def joinedPoleTail (j h : ℕ) (x : ℝ) : ℝ :=
  poissonPrefix (j+h-1) x-poissonPrefix (j-1) x-poissonPrefix (h-1) x

theorem joinedPoleTail_bound {N j h : ℕ} (hh : h ∈ rectangleOrders N j)
    {x : ℝ} (hx : (11/16 : ℝ)*N ≤ x) :
    |joinedPoleTail j h x| ≤ 3*Real.exp (-(N : ℝ)/300) := by
  have hm := rectangle_joint_order hh
  have hx0 : 0 ≤ x := (by positivity : (0 : ℝ) ≤ (11/16 : ℝ)*N).trans hx
  have h1 := poissonPrefix_rectangle_bound N (j+h-1) hx (by omega)
  have h2 := poissonPrefix_rectangle_bound N (j-1) hx (by omega)
  have h3 := poissonPrefix_rectangle_bound N (h-1) hx (by omega)
  have hp1 := poissonPrefix_nonneg (j+h-1) hx0
  have hp2 := poissonPrefix_nonneg (j-1) hx0
  have hp3 := poissonPrefix_nonneg (h-1) hx0
  unfold joinedPoleTail
  apply abs_le.mpr
  constructor <;> linarith [Real.exp_pos (-(N : ℝ)/300)]

/-- The factorial-tail saving beats even the largest permitted
positive source growth. This does not supply the arithmetic transfer. -/
theorem source_times_tail_bound (N : ℕ) :
    (2*radiusCeiling)^N*Real.exp (-(N : ℝ)/300) ≤
      Real.exp (-(N : ℝ)/400) := by
  have hp : 0 < 2*radiusCeiling := by norm_num [radiusCeiling]
  have hlog := Real.log_le_sub_one_of_pos hp
  norm_num [radiusCeiling] at hlog
  have he : (2*radiusCeiling)^N = Real.exp ((N : ℝ)*Real.log (2*radiusCeiling)) := by
    rw [Real.exp_nat_mul,Real.exp_log hp]
  rw [he,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hl := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  norm_num [radiusCeiling] at hl ⊢
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- The joined scalar model keeps the entire original order rectangle
and both reciprocal leg factors. This is not the arithmetic packet. -/
def joinedRectangleTail (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ rectangleOrders N j,
    joinedPoleTail j h x/((j : ℝ)*h)

theorem joinedRectangleTail_bound (N : ℕ) {x : ℝ}
    (hx : (11/16 : ℝ)*N ≤ x) :
    |joinedRectangleTail N x| ≤ 3*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300) := by
  have hw (j h : ℕ) : (1 : ℝ)/((j : ℝ)*h) ≤ 1 := by
    by_cases hj : j = 0
    · simp [hj]
    by_cases hh : h = 0
    · simp [hh]
    have hp : (1 : ℝ) ≤ (j : ℝ)*h := by
      exact_mod_cast (show 1 ≤ j*h by exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hj hh))
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp
  have ha (j h : ℕ) (hh : h ∈ rectangleOrders N j) :
      |joinedPoleTail j h x/((j : ℝ)*h)| ≤ 3*Real.exp (-(N : ℝ)/300) := by
    rw [abs_div,abs_of_nonneg (show 0 ≤ (j : ℝ)*h by positivity),
      div_eq_mul_one_div]
    calc
      _ ≤ (3*Real.exp (-(N : ℝ)/300))*(1/((j : ℝ)*h)) :=
        mul_le_mul_of_nonneg_right (joinedPoleTail_bound hh hx) (by positivity)
      _ ≤ _ := (mul_le_mul_of_nonneg_left (hw j h) (by positivity)).trans_eq (mul_one _)
  have hc (j : ℕ) : ((rectangleOrders N j).card : ℝ) ≤ (N : ℝ)+2 := by
    have hc := Finset.card_le_card (Finset.filter_subset
      (fun h => j+h ∈ ownerOrders N ∧ 21*N ≤ 40*j ∧ 40*j ≤ 23*N ∧
        N ≤ 100*(h+1) ∧ 100*(h+1) ≤ 4*N) (Finset.range (N+1-j+1)))
    change (rectangleOrders N j).card ≤ _ at hc
    rw [Finset.card_range] at hc
    exact_mod_cast (show (rectangleOrders N j).card ≤ N+2 by omega)
  unfold joinedRectangleTail
  calc
    _ ≤ ∑ j ∈ Finset.range (N+2), ∑ h ∈ rectangleOrders N j,
        |joinedPoleTail j h x/((j : ℝ)*h)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ j ∈ Finset.range (N+2), ∑ _h ∈ rectangleOrders N j,
        3*Real.exp (-(N : ℝ)/300) :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun h hh => ha j h hh))
    _ ≤ ∑ _j ∈ Finset.range (N+2), ((N : ℝ)+2)*(3*Real.exp (-(N : ℝ)/300)) := by
      apply Finset.sum_le_sum
      intro j _hj
      simpa only [Finset.sum_const,nsmul_eq_mul] using
        mul_le_mul_of_nonneg_right (hc j) (by positivity : 0 ≤ 3*Real.exp (-(N : ℝ)/300))
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; push_cast; ring

/-- The source growth is paid for the WHOLE joined scalar model.
The Fourier identification and ordered arithmetic transfer remain open. -/
theorem source_joinedRectangleTail_bound (N : ℕ) {x : ℝ}
    (hx : (11/16 : ℝ)*N ≤ x) :
    |(2*radiusCeiling)^N*joinedRectangleTail N x| ≤
      3*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/400) := by
  have hU : 0 ≤ 2*radiusCeiling := by norm_num [radiusCeiling]
  rw [abs_mul,abs_of_nonneg (pow_nonneg hU N)]
  calc
    _ ≤ (2*radiusCeiling)^N*(3*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300)) :=
      mul_le_mul_of_nonneg_left (joinedRectangleTail_bound N hx) (pow_nonneg hU N)
    _ = (3*((N : ℝ)+2)^2)*((2*radiusCeiling)^N*Real.exp (-(N : ℝ)/300)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (source_times_tail_bound N) (by positivity)

end
end RiemannGaussian.ZetaRieszWardWindowAudit
