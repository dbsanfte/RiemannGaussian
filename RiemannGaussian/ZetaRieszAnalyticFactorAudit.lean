/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLocalXiDivisor
import RiemannGaussian.FinitePoleRegularization

/-!
# Analytic count factors need not preserve triangular inverse support

The count exponent is a logarithmic primitive of the leg generator, not
the leg generator itself. A selected negative mode and the analytic leg
1/(2-t) give an exact all-count counterexample. Its ordinary one-sided
inverse is nonzero below d=s, including at gap 3/10. This does not identify
the actual zeta remainder with the toy analytic leg.
-/

namespace RiemannGaussian.ZetaRieszAnalyticFactorAudit
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Classical
open ZetaRieszZeroParityCascade

/-- The factor produced by one positive mode outside the local source disk. -/
def toyFactor (w z : ℂ) : ℂ := (w+z+1)/(w+1)

/-- Complete nonempty count response: selected negative mode, analytic perturbation,
and the original empty-cofactor subtraction. -/
def toyResponse (w z : ℂ) : ℂ := (1-(w/(w+z))*toyFactor w z)/z^2

theorem toyResponse_eq (w z : ℂ) (hz : z ≠ 0) (hws : w+z ≠ 0) (hw : w+1 ≠ 0) :
    toyResponse w z = 1/(z*(w+z)*(w+1)) := by
  unfold toyResponse toyFactor
  field_simp
  ring

/-- The exact logarithmic count primitive: one negative mode and one
opposite-sign mode whose normalized leg is analytic out to radius two. -/
def toyIntensity (w z : ℂ) : ℂ :=
  Complex.log (w+z)-Complex.log w-(Complex.log (w+z+1)-Complex.log (w+1))

theorem toyIntensity_factor (w z : ℂ) (hw : w ≠ 0) (hws : w+z ≠ 0)
    (hw1 : w+1 ≠ 0) (hws1 : w+z+1 ≠ 0) :
    Complex.exp (-toyIntensity w z) = (w/(w+z))*toyFactor w z := by
  rw [show -toyIntensity w z =
    (Complex.log w-Complex.log (w+z))+
      (Complex.log (w+z+1)-Complex.log (w+1)) by unfold toyIntensity; ring]
  rw [Complex.exp_add, Complex.exp_sub, Complex.exp_sub,
    Complex.exp_log hw, Complex.exp_log hws, Complex.exp_log hws1, Complex.exp_log hw1]
  rfl

/-- The full convergent nonempty count exponential, with no parity class
or empty-cofactor correction silently removed. -/
theorem hasSum_toyResponse (w z : ℂ) (hw : w ≠ 0) (hws : w+z ≠ 0)
    (hw1 : w+1 ≠ 0) (hws1 : w+z+1 ≠ 0) :
    HasSum (fun k : ℕ => -(-toyIntensity w z)^(k+1)/(((k+1).factorial : ℂ)*z^2))
      (toyResponse w z) := by
  have h := ZetaRieszNegativeModeCascade.hasSum_counts ({0} : Finset ℕ)
    (fun _ => toyIntensity w z) z
  simpa only [ZetaRieszNegativeModeCascade.countTerm, Finset.sum_singleton,
    Finset.prod_singleton, toyIntensity_factor w z hw hws hw1 hws1, toyResponse] using h

/-- The perturbing leg is analytic through the full radius-4/3 disk. -/
def toyLeg (t : ℂ) : ℂ := 1/(2-t)

theorem analyticOnNhd_toyLeg : AnalyticOnNhd ℂ toyLeg (Metric.ball 0 2) := by
  intro t ht
  apply analyticAt_const.div (analyticAt_const.sub analyticAt_id)
  intro he
  change 2-t = 0 at he
  have ht2 : t = 2 := (sub_eq_zero.mp he).symm
  simp [ht2] at ht

/-- The counterexample satisfies the same requested Cauchy coefficient
envelope as the actual local analytic remainder. -/
theorem toyLeg_coefficient_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      ‖signedTaylorMoment n toyLeg 0‖ ≤ M*(3/4 : ℝ)^n := by
  apply ZetaRieszLocalXiDivisor.coefficient_bound_of_analytic
  exact analyticOnNhd_toyLeg.mono (Metric.closedBall_subset_ball (by norm_num))

/-- Correct primitive normalization: along w=1,z=-t, the count factor is
1-t/2 and its logarithmic derivative is minus the analytic leg. -/
theorem toyFactor_path (t : ℂ) : toyFactor 1 (-t) = 1-t/2 := by
  unfold toyFactor
  ring

theorem toyFactor_derivative (t : ℂ) (ht : t ≠ 2) :
    HasDerivAt (fun q => toyFactor 1 (-q)) (-toyLeg t*toyFactor 1 (-t)) t := by
  simp_rw [toyFactor_path]
  have he : -toyLeg t*(1-t/2) = -(1/2 : ℂ) := by
    unfold toyLeg
    have hn : 2-t ≠ 0 := sub_ne_zero.mpr ht.symm
    field_simp
  rw [he]
  convert! (hasDerivAt_const t (1 : ℂ)).sub ((hasDerivAt_id t).div_const 2) using 1
  simp only [zero_sub]

/-- The exact mixed contribution on the normalized one-variable path. -/
def toyPerturbation (t : ℂ) : ℂ := (1/(1-t))*(toyFactor 1 (-t)-1)

theorem toyPerturbation_eq (t : ℂ) : toyPerturbation t = -t/(2*(1-t)) := by
  rw [toyPerturbation, toyFactor_path]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem toyPerturbation_principal {t : ℂ} (ht : t ≠ 1) :
    toyPerturbation t = 1/2+(1/2)/(t-1) := by
  rw [toyPerturbation_eq]
  have h1 : 1-t ≠ 0 := sub_ne_zero.mpr ht.symm
  have ht1 : t-1 ≠ 0 := sub_ne_zero.mpr ht
  field_simp
  ring

/-- Every positive-order coefficient is exactly -1/2; no geometric decay
can be inferred from the radius-two analyticity of the perturbing leg. -/
theorem hasSum_toyPerturbation {t : ℂ} (ht : ‖t‖ < 1) :
    HasSum (fun n : ℕ => -(t^(n+1))/2) (toyPerturbation t) := by
  have h := (hasSum_geometric_of_norm_lt_one ht).mul_left (-t/2)
  have he : -t/(2*(1-t)) = -t/2*(1-t)⁻¹ := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [toyPerturbation_eq, he]
  apply h.congr_fun
  intro n
  rw [pow_succ]
  ring

/-- The exact positive-order coefficient sequence rules out every
geometric bound with rate strictly less than one. -/
theorem not_eventually_geometric (M q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ¬ ∀ᶠ n : ℕ in atTop, ‖(-1/2 : ℂ)‖ ≤ M*q^n := by
  intro h
  have ht : Tendsto (fun n : ℕ => M*q^n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
  have hs := ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  obtain ⟨n, hn, hn'⟩ := (h.and hs).exists
  norm_num at hn
  linarith

/-- An arbitrary analytic count exponent B leaves this exact simple-pole
principal part when multiplied by the selected singular count factor. -/
theorem analytic_factor_principal {Q B : ℂ → ℂ}
    (hQ : AnalyticAt ℂ Q 1) (hB : AnalyticAt ℂ B 1) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 1 ∧
      (fun t => Q t*(Complex.exp (B t)-1)/(1-t) -
        (-Q 1*(Complex.exp (B 1)-1))/(t-1)) =ᶠ[𝓝[≠] (1 : ℂ)] H := by
  let F := fun t => -Q t*(Complex.exp (B t)-1)
  have hF : AnalyticAt ℂ F 1 := hQ.neg.mul (hB.cexp.sub analyticAt_const)
  obtain ⟨H, hH, he⟩ := exists_analytic_poleTaylor_remainder hF 1
  refine ⟨H, hH, ?_⟩
  filter_upwards [he] with t ht
  simp only [poleTaylorPrincipalPart, Finset.sum_range_one, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, iteratedDeriv_zero, one_mul, pow_one] at ht
  convert ht using 1
  dsimp [F]
  rw [show 1-t = -(t-1) by ring, div_neg]
  ring

/-- A direct ordinary inverse, with the diagonal convention fixed by the
original support kernel. All one-sided and empty-cofactor terms remain. -/
def leakageKernel (s d : ℝ) : ℂ :=
  (supportKernel s d : ℂ)+Complex.exp (-(s : ℂ))*
    (Complex.exp (d : ℂ)*(1-(supportKernel s d : ℂ))-1)

theorem leakageKernel_below {s d : ℝ} (hd : d < s) :
    leakageKernel s d = Complex.exp (-(s : ℂ))*(Complex.exp (d : ℂ)-1) := by
  simp [leakageKernel, supportKernel_eq_zero hd]

/-- Leakage is positive on an open region, not just at a boundary point. -/
theorem leakageKernel_below_pos {s d : ℝ} (hd : 0 < d) (hds : d < s) :
    0 < (leakageKernel s d).re := by
  rw [leakageKernel_below hds]
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re,
    Complex.ofReal_im, Complex.sub_im, Complex.one_im, sub_self, mul_zero, sub_zero]
  exact mul_pos (Real.exp_pos _) (sub_pos.mpr (Real.one_lt_exp_iff.mpr hd))

/-- A nonzero ordinary contribution strictly beyond the literal core gap.
The cofactor share 9/20 corresponds to largest share 11/20. -/
theorem leakage_inside_core_geometry :
    (7/25 : ℝ) < 9/20-3/20 ∧
      (43/80 : ℝ) ≤ 1-9/20 ∧ 1-9/20 ≤ (9/16 : ℝ) ∧
      0 < (leakageKernel (9/20) (3/20)).re := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  exact leakageKernel_below_pos (by norm_num) (by norm_num)

private theorem exp_integrable {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun d : ℝ => Complex.exp (-(z : ℂ)*d)) (Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hz) 0

private theorem exp_integral {z : ℝ} (hz : 0 < z) :
    (∫ d : ℝ in Ioi 0, Complex.exp (-(z : ℂ)*d)) = 1/(z : ℂ) := by
  rw [integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hz)]
  simp

private theorem support_integrable (s : ℝ) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun d : ℝ => Complex.exp (-(z : ℂ)*d)*(supportKernel s d : ℂ)) (Ioi 0) := by
  have h := MeasureTheory.Integrable.indicator (exp_integrable hz)
    (s := Ici s) measurableSet_Ici
  have he : (fun d : ℝ => Complex.exp (-(z : ℂ)*d)*(supportKernel s d : ℂ)) =
      (Ici s).indicator (fun d : ℝ => Complex.exp (-(z : ℂ)*d)) := by
    funext d
    by_cases hd : s ≤ d <;> simp [supportKernel, Set.indicator, hd]
  change Integrable _ (volume.restrict (Ioi 0))
  rw [he]
  exact h

private theorem leakageKernel_inner {s z : ℝ} (hs : 0 < s) (hz : 1 < z) :
    (∫ d : ℝ in Ioi 0, Complex.exp (-(z : ℂ)*d)*leakageKernel s d) =
      (Complex.exp (-(s : ℂ))-Complex.exp (-(z : ℂ)*s))/((z : ℂ)*(z-1)) := by
  have hz0 : 0 < z := by linarith
  have hz1 : 0 < z-1 := by linarith
  have h0 := exp_integrable hz0
  have h1 := exp_integrable hz1
  have hg0 := support_integrable s hz0
  have hg1 := support_integrable s hz1
  have he (d : ℝ) : Complex.exp (-(z : ℂ)*d)*leakageKernel s d =
      (Complex.exp (-(s : ℂ))*Complex.exp (-((z-1 : ℝ) : ℂ)*d)-
        Complex.exp (-(s : ℂ))*Complex.exp (-(z : ℂ)*d))+
      (Complex.exp (-(z : ℂ)*d)*(supportKernel s d : ℂ)-
        Complex.exp (-(s : ℂ))*(Complex.exp (-((z-1 : ℝ) : ℂ)*d)*(supportKernel s d : ℂ))) := by
    have hx : Complex.exp (-(z : ℂ)*d)*Complex.exp (d : ℂ) =
        Complex.exp (-((z-1 : ℝ) : ℂ)*d) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    dsimp [leakageKernel]
    linear_combination Complex.exp (-(s : ℂ))*(1-(supportKernel s d : ℂ))*hx
  simp_rw [he]
  have hsplit := integral_add ((h1.const_mul (Complex.exp (-(s : ℂ)))).sub
        (h0.const_mul (Complex.exp (-(s : ℂ)))))
        (hg0.sub (hg1.const_mul (Complex.exp (-(s : ℂ)))))
  dsimp only [Pi.sub_apply] at hsplit
  rw [hsplit]
  have hleft := integral_sub (h1.const_mul (Complex.exp (-(s : ℂ))))
    (h0.const_mul (Complex.exp (-(s : ℂ))))
  have hright := integral_sub hg0 (hg1.const_mul (Complex.exp (-(s : ℂ))))
  rw [hleft, hright, integral_const_mul, integral_const_mul, integral_const_mul,
    exp_integral hz1, exp_integral hz0, integral_supportKernel hs hz0, integral_supportKernel hs hz1]
  have hes : Complex.exp (-(s : ℂ))*Complex.exp (-((z-1 : ℝ) : ℂ)*s) =
      Complex.exp (-(z : ℂ)*s) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← mul_div_assoc (Complex.exp (-(s : ℂ)))
    (Complex.exp (-((z-1 : ℝ) : ℂ)*s)) _, hes]
  have hzC : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz0.ne'
  have hzC1 : (z-1 : ℂ) ≠ 0 := by exact_mod_cast hz1.ne'
  push_cast
  field_simp
  ring

/-- Exact double Laplace transform of the ordinary counterexample kernel.
The open convergence domain w>0,z>1 is explicit. -/
theorem leakageKernel_transform {w z : ℝ} (hw : 0 < w) (hz : 1 < z) :
    (∫ s : ℝ in Ioi 0, Complex.exp (-(w : ℂ)*s)*
      (∫ d : ℝ in Ioi 0, Complex.exp (-(z : ℂ)*d)*leakageKernel s d)) =
      toyResponse w z := by
  have he : (fun s : ℝ => Complex.exp (-(w : ℂ)*s)*
      (∫ d : ℝ in Ioi 0, Complex.exp (-(z : ℂ)*d)*leakageKernel s d)) =ᵐ[volume.restrict (Ioi 0)]
      (fun s : ℝ => (Complex.exp (-((w+1 : ℝ) : ℂ)*s)-Complex.exp (-((w+z : ℝ) : ℂ)*s))/
        ((z : ℂ)*(z-1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [leakageKernel_inner hs hz, ← mul_div_assoc, mul_sub,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 2 <;> push_cast <;> ring
  rw [integral_congr_ae he, integral_div,
    integral_sub (exp_integrable (by linarith : 0 < w+1)) (exp_integrable (by linarith : 0 < w+z)),
    exp_integral (by linarith : 0 < w+1), exp_integral (by linarith : 0 < w+z)]
  have hzc : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith : z ≠ 0)
  have hz1 : (z-1 : ℂ) ≠ 0 := by exact_mod_cast (by linarith : z-1 ≠ 0)
  have hw1 : (w+1 : ℂ) ≠ 0 := by exact_mod_cast (by linarith : w+1 ≠ 0)
  have hwz : (w+z : ℂ) ≠ 0 := by exact_mod_cast (by linarith : w+z ≠ 0)
  rw [toyResponse_eq _ _ hzc hwz hw1]
  push_cast
  field_simp
  ring

end
end RiemannGaussian.ZetaRieszAnalyticFactorAudit
