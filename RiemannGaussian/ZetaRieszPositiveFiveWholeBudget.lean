/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCentralSharpBudget
import RiemannGaussian.ZetaRieszPositiveFiveSignedPayment

/-!
# A joint phase budget for the full positive-five interior

The extra `1/250` is added to the original `1261/10000` debit before
summing phases. The remaining `m/1200` pays the old small-prime boundary
`m/1600` and leaves `m/4800`. The fixed positive-five sector is not spent
again: it is included in the new full interior population.
-/

namespace RiemannGaussian.ZetaRieszPositiveFiveWholeBudget
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszCapacityPhaseBudget ZetaRieszCentralSharpBudget

/-- The existing certified angular constants retain a margin of 1/1200 after the sharper phase and radial costs. -/
theorem finite_interior_budget {m : ℕ} {c : ℕ → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hεu : ε ≤ 1/10000)
    (hc : (2 : ℝ)*m ≤ ∑ i ∈ Finset.range (8*m), max 0 (c i)) :
    (m : ℝ)/1200 ≤ ∑ i ∈ Finset.range (8*m),
      ((99999/100000 : ℝ)*(1309/10000)*max 0 (c i-ε)-
        (501/500 : ℝ)*(50001/50000)*(1301/10000)*(max 0 (c i)+ε)) := by
  have hp (i : ℕ) : max 0 (c i)-ε ≤ max 0 (c i-ε) := by
    by_cases hi : 0 ≤ c i
    · rw [max_eq_right hi]
      exact le_max_right _ _
    · rw [max_eq_left (le_of_not_ge hi)]
      exact (by linarith : (0 : ℝ)-ε ≤ 0).trans (le_max_left _ _)
  have hs := Finset.sum_le_sum (s := Finset.range (8*m)) (fun i _ => hp i)
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  have heps : (m : ℝ)*ε ≤ (m : ℝ)/10000 := by
    have hn : (0 : ℝ) ≤ m := by positivity
    nlinarith
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  push_cast at hs ⊢
  have hn : (0 : ℝ) ≤ m := by positivity
  nlinarith


/-- The alternative upper comparison pays the same full interior debit. -/
theorem finite_upper_interior_budget {m : ℕ} {c : ℕ → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hεu : ε ≤ 1/10000)
    (hc : (2 : ℝ)*m ≤ ∑ i ∈ Finset.range (8*m), max 0 (c i)) :
    (∑ i ∈ Finset.range (8*m),
      ((501/500 : ℝ)*(50001/50000)*(1301/10000)*(max 0 (c i)+ε)-
        (99999/100000 : ℝ)*(1309/10000)*max 0 (c i-ε))) ≤ -(m : ℝ)/1200 := by
  have hp (i : ℕ) : max 0 (c i)-ε ≤ max 0 (c i-ε) := by
    by_cases hi : 0 ≤ c i
    · rw [max_eq_right hi]
      exact le_max_right _ _
    · rw [max_eq_left (le_of_not_ge hi)]
      exact (by linarith : (0 : ℝ)-ε ≤ 0).trans (le_max_left _ _)
  have hs := Finset.sum_le_sum (s := Finset.range (8*m)) (fun i _ => hp i)
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  have heps : (m : ℝ)*ε ≤ (m : ℝ)/10000 := by
    have hn : (0 : ℝ) ≤ m := by positivity
    nlinarith
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  push_cast at hs ⊢
  have hn : (0 : ℝ) ≤ m := by positivity
  nlinarith


/-- The whole-period lower budget pays the complete additional interior debit while retaining the original radial witness. -/
theorem interior_period_budget_with_radial {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    {b y h : ℝ} (hy : 54 ≤ |y|) (hpeak : Real.cos (y*b) = -1)
    (hlo : (39/20 : ℝ)*N ≤ b-Real.pi/|y|)
    (hhi : b+Real.pi/|y| ≤ (203/100 : ℝ)*N)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hε : |y| * h ≤ 1/10000) :
    ∃ V₀ : ℝ, 0 < V₀ ∧
      Real.exp (-b/2)*b^N/N.factorial ≤ (501/500 : ℝ)*V₀ ∧ (m : ℝ)/1200*V₀*h ≤
      ∑ i ∈ Finset.range (8*m),
        let t := b+periodAngle m i/|y|
        (1309/10000 : ℝ)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*max 0 (-Real.cos (y*t)-|y| * h)*h)-
        (1301/10000 : ℝ)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*(max 0 (-Real.cos (y*t))+|y| * h)*h) := by
  obtain ⟨V₀,hV₀,hV⟩ := ZetaRieszPhaseBudget.radial_period_comparable hN hy hlo hhi
  have hy0 : 0 < |y| := by linarith
  have hyne : y ≠ 0 := by intro he; simp only [he,abs_zero] at hy; linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let T : ℕ → ℝ := fun i => b+periodAngle m i/|y|
  let c : ℕ → ℝ := fun i => Real.cos (periodAngle m i)
  let ε := |y| * h
  have hrow (i : ℕ) (hi : i ∈ Finset.range (8*m)) :
      (((99999/100000 : ℝ)*(1309/10000)*max 0 (c i-ε)-
        (501/500 : ℝ)*(50001/50000)*(1301/10000)*(max 0 (c i)+ε))*V₀*h) ≤
        (1309/10000 : ℝ)*
          ((Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*max 0 (-Real.cos (y*T i)-|y| * h)*h)-
        (1301/10000 : ℝ)*
          ((Real.exp (-T i/2)*(T i+h)^N/N.factorial)*(max 0 (-Real.cos (y*T i))+|y| * h)*h) := by
    have hai := periodAngle_bounds hm (Finset.mem_range.mp hi).le
    have hVi := hV (periodAngle m i) hai
    have htilo : (39/20 : ℝ)*N ≤ T i := by
      have hr := div_le_div_of_nonneg_right hai.1 hy0.le
      rw [neg_div] at hr
      dsimp [T]
      linarith
    have hti : 0 < T i := by nlinarith
    have hNt : (N : ℝ) ≤ T i := by nlinarith
    have hVm : (99999/100000 : ℝ)*V₀ ≤ Real.exp (-(T i+h)/2)*(T i)^N/N.factorial :=
      (mul_le_mul_of_nonneg_left hVi.1 (by norm_num)).trans (ZetaRieszCentralSharpBudget.lower_radial hti.le hhu)
    have hVp : Real.exp (-T i/2)*(T i+h)^N/N.factorial ≤
        (501/500 : ℝ)*(50001/50000)*V₀ := by
      have he := (ZetaRieszCentralSharpBudget.upper_radial hti hNt hh.le hhu).trans
        (mul_le_mul_of_nonneg_left hVi.2 (by norm_num : (0 : ℝ) ≤ 50001/50000))
      nlinarith only [he]
    have hphase : -Real.cos (y*T i) = c i :=
      ZetaRieszPhaseBudget.phase_at_negative_peak hyne hpeak (periodAngle m i)
    rw [hphase]
    have hm' := mul_le_mul_of_nonneg_right hVm
      (show 0 ≤ (1309/10000 : ℝ)*max 0 (c i-ε)*h by positivity)
    have hp' := mul_le_mul_of_nonneg_right hVp
      (show 0 ≤ (1301/10000 : ℝ)*(max 0 (c i)+ε)*h by dsimp [ε]; positivity)
    dsimp only [ε] at hm' hp' ⊢
    nlinarith only [hm',hp']
  have hsum := Finset.sum_le_sum hrow
  simp only [← Finset.sum_mul] at hsum
  have hscalar := finite_interior_budget (show 0 ≤ ε by dsimp [ε]; positivity) hε
    (sum_positive_cos_lower hm)
  have hscaled := mul_le_mul_of_nonneg_right hscalar (show 0 ≤ V₀*h by positivity)
  refine ⟨V₀,hV₀,?_,?_⟩
  · simpa only [zero_div,add_zero] using (hV 0 (by
      constructor <;> linarith [Real.pi_pos])).2
  · nlinarith only [hscaled,hsum]


/-- The whole-period upper budget pays the complete additional interior debit with the same radial witness. -/
theorem interior_upper_period_budget_with_radial {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    {b y h : ℝ} (hy : 54 ≤ |y|) (hpeak : Real.cos (y*b) = -1)
    (hlo : (39/20 : ℝ)*N ≤ b-Real.pi/|y|)
    (hhi : b+Real.pi/|y| ≤ (203/100 : ℝ)*N)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hε : |y| * h ≤ 1/10000) :
    ∃ V₀ : ℝ, 0 < V₀ ∧
      Real.exp (-b/2)*b^N/N.factorial ≤ (501/500 : ℝ)*V₀ ∧
      (∑ i ∈ Finset.range (8*m),
        let t := b+periodAngle m i/|y|
        (1301/10000 : ℝ)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*(max 0 (Real.cos (y*t))+|y| * h)*h)-
        (1309/10000 : ℝ)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*max 0 (Real.cos (y*t)-|y| * h)*h)) ≤
        -(m : ℝ)/1200*V₀*h := by
  obtain ⟨V₀,hV₀,hV⟩ := ZetaRieszPhaseBudget.radial_period_comparable hN hy hlo hhi
  have hy0 : 0 < |y| := by linarith
  have hyne : y ≠ 0 := by intro he; simp only [he,abs_zero] at hy; linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let T : ℕ → ℝ := fun i => b+periodAngle m i/|y|
  let c : ℕ → ℝ := fun i => -Real.cos (periodAngle m i)
  let ε := |y| * h
  have hrow (i : ℕ) (hi : i ∈ Finset.range (8*m)) :
      (1301/10000 : ℝ)*
          ((Real.exp (-T i/2)*(T i+h)^N/N.factorial)*(max 0 (Real.cos (y*T i))+|y| * h)*h)-
        (1309/10000 : ℝ)*
          ((Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*max 0 (Real.cos (y*T i)-|y| * h)*h) ≤
      (((501/500 : ℝ)*(50001/50000)*(1301/10000)*(max 0 (c i)+ε)-
        (99999/100000 : ℝ)*(1309/10000)*max 0 (c i-ε))*V₀*h) := by
    have hai := periodAngle_bounds hm (Finset.mem_range.mp hi).le
    have hVi := hV (periodAngle m i) hai
    have htilo : (39/20 : ℝ)*N ≤ T i := by
      have hr := div_le_div_of_nonneg_right hai.1 hy0.le
      rw [neg_div] at hr
      dsimp [T]
      linarith
    have hti : 0 < T i := by nlinarith
    have hNt : (N : ℝ) ≤ T i := by nlinarith
    have hVm : (99999/100000 : ℝ)*V₀ ≤ Real.exp (-(T i+h)/2)*(T i)^N/N.factorial :=
      (mul_le_mul_of_nonneg_left hVi.1 (by norm_num)).trans (ZetaRieszCentralSharpBudget.lower_radial hti.le hhu)
    have hVp : Real.exp (-T i/2)*(T i+h)^N/N.factorial ≤
        (501/500 : ℝ)*(50001/50000)*V₀ := by
      have he := (ZetaRieszCentralSharpBudget.upper_radial hti hNt hh.le hhu).trans
        (mul_le_mul_of_nonneg_left hVi.2 (by norm_num : (0 : ℝ) ≤ 50001/50000))
      nlinarith only [he]
    have hp := ZetaRieszPhaseBudget.phase_at_negative_peak hyne hpeak (periodAngle m i)
    have hphase : Real.cos (y*T i) = c i := by dsimp only [c,T]; linarith only [hp]
    rw [hphase]
    have hm' := mul_le_mul_of_nonneg_right hVm
      (show 0 ≤ (1309/10000 : ℝ)*max 0 (c i-ε)*h by positivity)
    have hp' := mul_le_mul_of_nonneg_right hVp
      (show 0 ≤ (1301/10000 : ℝ)*(max 0 (c i)+ε)*h by dsimp [ε]; positivity)
    dsimp only [ε] at hm' hp' ⊢
    nlinarith only [hm',hp']
  have hsum := Finset.sum_le_sum hrow
  simp only [← Finset.sum_mul] at hsum
  have hscalar := finite_upper_interior_budget (show 0 ≤ ε by dsimp [ε]; positivity) hε
    (sum_negative_cos_lower hm)
  have hscaled := mul_le_mul_of_nonneg_right hscalar (show 0 ≤ V₀*h by positivity)
  refine ⟨V₀,hV₀,?_,?_⟩
  · simpa only [zero_div,add_zero] using (hV 0 (by
      constructor <;> linarith [Real.pi_pos])).2
  · nlinarith only [hscaled,hsum]

end
end RiemannGaussian.ZetaRieszPositiveFiveWholeBudget
