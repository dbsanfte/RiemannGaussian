/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCentralReserve

/-!
# A sharper joint central budget with the original phase and radial weights

The full favorable half-period contains a triangular cosine minorant of
mass `2m`. The exact short-cell radial factors lose only `1/100000` and
`1/50000`, respectively. These gains are spent in the existing whole-sum
ledger, with no new arithmetic population or representation.
-/

namespace RiemannGaussian.ZetaRieszCentralSharpBudget
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszCapacityPhaseBudget

/-- The actual favorable short-cell radial loss is at most one hundred
thousandth, without changing its moment or endpoint. -/
theorem lower_radial {N : ℕ} {t h : ℝ} (ht : 0 ≤ t) (hhu : h ≤ 1/100000) :
    (99999/100000 : ℝ)*(Real.exp (-t/2)*t^N/N.factorial) ≤
      Real.exp (-(t+h)/2)*t^N/N.factorial := by
  have hex : (99999/100000 : ℝ) ≤ Real.exp (-h/2) := by
    have hh := Real.add_one_le_exp (-h/2)
    linarith
  have hm := mul_le_mul_of_nonneg_right hex
    (show 0 ≤ Real.exp (-t/2)*t^N/N.factorial by positivity)
  calc
    _ ≤ Real.exp (-h/2)*(Real.exp (-t/2)*t^N/N.factorial) := hm
    _ = _ := by
      rw [show -(t+h)/2 = -h/2+(-t/2) by ring,Real.exp_add]
      ring

/-- The adverse radial weight costs at most one fifty-thousandth on the
same cell; the exponential and factorial factors stay coupled. -/
theorem upper_radial {N : ℕ} {t h : ℝ} (ht : 0 < t) (hNt : (N : ℝ) ≤ t)
    (hh : 0 ≤ h) (hhu : h ≤ 1/100000) :
    Real.exp (-t/2)*(t+h)^N/N.factorial ≤
      (50001/50000 : ℝ)*(Real.exp (-t/2)*t^N/N.factorial) := by
  have hth : 0 < t+h := by linarith
  have hlog := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hth ht)) (Nat.cast_nonneg N)
  rw [Real.log_div hth.ne' ht.ne'] at hlog
  have hratio : (N : ℝ)/t ≤ 1 := (div_le_iff₀ ht).mpr (by linarith)
  have hid : (N : ℝ)*((t+h)/t-1) = h*((N : ℝ)/t) := by field_simp; ring
  rw [hid] at hlog
  have hexp : -t/2+(N : ℝ)*Real.log (t+h) ≤
      (1/100000 : ℝ)+(-t/2+(N : ℝ)*Real.log t) := by
    nlinarith [mul_le_mul_of_nonneg_left hratio hh]
  have hpow (x : ℝ) (hx : 0 < x) : x^N = Real.exp ((N : ℝ)*Real.log x) := by
    rw [Real.exp_nat_mul,Real.exp_log hx]
  rw [hpow t ht,hpow (t+h) hth,← Real.exp_add,← Real.exp_add]
  have hb : Real.exp (1/100000 : ℝ) ≤ 50001/50000 :=
    (Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1/100000)
      (by norm_num : (1/100000 : ℝ) < 1)).trans (by norm_num)
  calc
    _ ≤ Real.exp ((1/100000 : ℝ)+(-t/2+(N : ℝ)*Real.log t))/N.factorial :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = Real.exp (1/100000 : ℝ)*(Real.exp (-t/2+(N : ℝ)*Real.log t)/N.factorial) := by
      rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (by positivity)

private theorem cosine_triangle {x : ℝ} (hx : |x| ≤ Real.pi/2) :
    1-2*|x|/Real.pi ≤ Real.cos x := by
  have h := Real.mul_le_sin (x := Real.pi/2-|x|) (by linarith) (by linarith [abs_nonneg x])
  rw [Real.sin_pi_div_two_sub,Real.cos_abs] at h
  convert h using 1; field_simp

/-- The left half of the original favorable arc retains its linear
cosine minorant, including the zero-phase boundary. -/
theorem left_cosine_lower {m i : ℕ} (hm : 0 < m) (hi : i < 2*m) :
    (i : ℝ)/(2*m) ≤ max 0 (Real.cos (periodAngle m (2*m+i))) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hiR : (i : ℝ) ≤ 2*m := by exact_mod_cast hi.le
  have he : periodAngle m (2*m+i) = -Real.pi/2+(i : ℝ)*Real.pi/(4*m) := by
    unfold periodAngle
    push_cast
    field_simp
    ring
  have hdiv0 : 0 ≤ (i : ℝ)*Real.pi/(4*m) := by positivity
  have hdiv1 : (i : ℝ)*Real.pi/(4*m) ≤ Real.pi/2 :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith [Real.pi_pos])
  have hx : |periodAngle m (2*m+i)| ≤ Real.pi/2 := by
    rw [he,abs_of_nonpos (by linarith)]
    linarith
  have h := (cosine_triangle hx).trans (le_max_right 0 _)
  apply le_trans (le_of_eq ?_) h
  rw [he,abs_of_nonpos (by linarith)]
  field_simp
  ring

/-- The right half keeps the complementary linear minorant. -/
theorem right_cosine_lower {m i : ℕ} (hm : 0 < m) (hi : i < 2*m) :
    1-(i : ℝ)/(2*m) ≤ max 0 (Real.cos (periodAngle m (4*m+i))) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hiR : (i : ℝ) ≤ 2*m := by exact_mod_cast hi.le
  have he : periodAngle m (4*m+i) = (i : ℝ)*Real.pi/(4*m) := by
    unfold periodAngle
    push_cast
    field_simp
    ring
  have hdiv0 : 0 ≤ (i : ℝ)*Real.pi/(4*m) := by positivity
  have hdiv1 : (i : ℝ)*Real.pi/(4*m) ≤ Real.pi/2 :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith [Real.pi_pos])
  have hx : |periodAngle m (4*m+i)| ≤ Real.pi/2 := by
    rw [he,abs_of_nonneg hdiv0]
    exact hdiv1
  have h := (cosine_triangle hx).trans (le_max_right 0 _)
  apply le_trans (le_of_eq ?_) h
  rw [he,abs_of_nonneg hdiv0]
  field_simp
  ring

/-- Summing the full triangular minorant doubles the old certified
cosine mass. Every other phase cell remains in the sum. -/
theorem sum_positive_cos_lower {m : ℕ} (hm : 0 < m) :
    (2 : ℝ)*m ≤ ∑ i ∈ Finset.range (8*m), max 0 (Real.cos (periodAngle m i)) := by
  let f := fun i => max 0 (Real.cos (periodAngle m i))
  have hpair (i : ℕ) (hi : i ∈ Finset.range (2*m)) :
      (1 : ℝ) ≤ f (2*m+i)+f (4*m+i) := by
    have hl := left_cosine_lower hm (Finset.mem_range.mp hi)
    have hr := right_cosine_lower hm (Finset.mem_range.mp hi)
    dsimp [f]
    linarith only [hl,hr]
  have hs := Finset.sum_le_sum hpair
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,Nat.cast_mul,Nat.cast_ofNat,
    Finset.sum_add_distrib] at hs
  have hz (a : ℕ) : 0 ≤ ∑ i ∈ Finset.range (2*m), f (a+i) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  change _ ≤ ∑ i ∈ Finset.range (8*m), f i
  rw [show 8*m = 2*m+(2*m+(2*m+2*m)) by omega,Finset.sum_range_add,
    Finset.sum_range_add,Finset.sum_range_add]
  have he1 : (fun i => f (2*m+(2*m+i))) = fun i => f (4*m+i) := by funext i; congr 1; omega
  have he2 : (fun i => f (2*m+(2*m+(2*m+i)))) = fun i => f (6*m+i) := by funext i; congr 1; omega
  rw [he1,he2]
  have h0 : 0 ≤ ∑ i ∈ Finset.range (2*m), f i := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  linarith only [hs,h0,hz (6*m)]

/-- The opposite half-period has exactly the same strengthened mass. -/
theorem sum_negative_cos_lower {m : ℕ} (hm : 0 < m) :
    (2 : ℝ)*m ≤ ∑ i ∈ Finset.range (8*m), max 0 (-Real.cos (periodAngle m i)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hshift (i : ℕ) : Real.cos (periodAngle m (4*m+i)) =
      -Real.cos (periodAngle m i) := by
    have he : periodAngle m (4*m+i) = periodAngle m i+Real.pi := by
      unfold periodAngle
      push_cast
      field_simp [ne_of_gt hmR]
      ring
    rw [he,Real.cos_add_pi]
  have he : (∑ i ∈ Finset.range (8*m), max 0 (-Real.cos (periodAngle m i))) =
      ∑ i ∈ Finset.range (8*m), max 0 (Real.cos (periodAngle m i)) := by
    rw [show 8*m = 4*m+4*m by omega,Finset.sum_range_add,Finset.sum_range_add]
    simp_rw [hshift,neg_neg]
    exact add_comm _ _
  rw [he]
  exact sum_positive_cos_lower hm


/-- The existing certified angular constants retain a margin of 1/125 after the sharper phase and radial costs. -/
theorem finite_central_budget {m : ℕ} {c : ℕ → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hεu : ε ≤ 1/10000)
    (hc : (2 : ℝ)*m ≤ ∑ i ∈ Finset.range (8*m), max 0 (c i)) :
    (m : ℝ)/125 ≤ ∑ i ∈ Finset.range (8*m),
      ((99999/100000 : ℝ)*(1309/10000)*max 0 (c i-ε)-
        (501/500 : ℝ)*(50001/50000)*(1261/10000)*(max 0 (c i)+ε)) := by
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


/-- The alternative upper budget has the same strengthened margin. -/
theorem finite_upper_central_budget {m : ℕ} {c : ℕ → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hεu : ε ≤ 1/10000)
    (hc : (2 : ℝ)*m ≤ ∑ i ∈ Finset.range (8*m), max 0 (c i)) :
    (∑ i ∈ Finset.range (8*m),
      ((501/500 : ℝ)*(50001/50000)*(1261/10000)*(max 0 (c i)+ε)-
        (99999/100000 : ℝ)*(1309/10000)*max 0 (c i-ε))) ≤ -(m : ℝ)/125 := by
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


/-- The unchanged lower populations retain four times the previous period margin, with the original radial witness. -/
theorem original_central_period_budget_with_radial {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    {b y h : ℝ} (hy : 54 ≤ |y|) (hpeak : Real.cos (y*b) = -1)
    (hlo : (39/20 : ℝ)*N ≤ b-Real.pi/|y|)
    (hhi : b+Real.pi/|y| ≤ (203/100 : ℝ)*N)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hε : |y| * h ≤ 1/10000) :
    ∃ V₀ : ℝ, 0 < V₀ ∧
      Real.exp (-b/2)*b^N/N.factorial ≤ (501/500 : ℝ)*V₀ ∧ (m : ℝ)/125*V₀*h ≤
      ∑ i ∈ Finset.range (8*m),
        let t := b+periodAngle m i/|y|
        (1309/10000 : ℝ)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*max 0 (-Real.cos (y*t)-|y| * h)*h)-
        (1261/10000 : ℝ)*
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
        (501/500 : ℝ)*(50001/50000)*(1261/10000)*(max 0 (c i)+ε))*V₀*h) ≤
        (1309/10000 : ℝ)*
          ((Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*max 0 (-Real.cos (y*T i)-|y| * h)*h)-
        (1261/10000 : ℝ)*
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
      (mul_le_mul_of_nonneg_left hVi.1 (by norm_num)).trans (lower_radial hti.le hhu)
    have hVp : Real.exp (-T i/2)*(T i+h)^N/N.factorial ≤
        (501/500 : ℝ)*(50001/50000)*V₀ := by
      have he := (upper_radial hti hNt hh.le hhu).trans
        (mul_le_mul_of_nonneg_left hVi.2 (by norm_num : (0 : ℝ) ≤ 50001/50000))
      nlinarith only [he]
    have hphase : -Real.cos (y*T i) = c i :=
      ZetaRieszPhaseBudget.phase_at_negative_peak hyne hpeak (periodAngle m i)
    rw [hphase]
    have hm' := mul_le_mul_of_nonneg_right hVm
      (show 0 ≤ (1309/10000 : ℝ)*max 0 (c i-ε)*h by positivity)
    have hp' := mul_le_mul_of_nonneg_right hVp
      (show 0 ≤ (1261/10000 : ℝ)*(max 0 (c i)+ε)*h by dsimp [ε]; positivity)
    dsimp only [ε] at hm' hp' ⊢
    nlinarith only [hm',hp']
  have hsum := Finset.sum_le_sum hrow
  simp only [← Finset.sum_mul] at hsum
  have hscalar := finite_central_budget (show 0 ≤ ε by dsimp [ε]; positivity) hε
    (sum_positive_cos_lower hm)
  have hscaled := mul_le_mul_of_nonneg_right hscalar (show 0 ≤ V₀*h by positivity)
  refine ⟨V₀,hV₀,?_,?_⟩
  · simpa only [zero_div,add_zero] using (hV 0 (by
      constructor <;> linarith [Real.pi_pos])).2
  · nlinarith only [hscaled,hsum]


/-- The unchanged upper populations retain four times the previous period margin, with the original radial witness. -/
theorem original_central_upper_period_budget_with_radial {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    {b y h : ℝ} (hy : 54 ≤ |y|) (hpeak : Real.cos (y*b) = -1)
    (hlo : (39/20 : ℝ)*N ≤ b-Real.pi/|y|)
    (hhi : b+Real.pi/|y| ≤ (203/100 : ℝ)*N)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hε : |y| * h ≤ 1/10000) :
    ∃ V₀ : ℝ, 0 < V₀ ∧
      Real.exp (-b/2)*b^N/N.factorial ≤ (501/500 : ℝ)*V₀ ∧
      (∑ i ∈ Finset.range (8*m),
        let t := b+periodAngle m i/|y|
        (1261/10000 : ℝ)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*(max 0 (Real.cos (y*t))+|y| * h)*h)-
        (1309/10000 : ℝ)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*max 0 (Real.cos (y*t)-|y| * h)*h)) ≤
        -(m : ℝ)/125*V₀*h := by
  obtain ⟨V₀,hV₀,hV⟩ := ZetaRieszPhaseBudget.radial_period_comparable hN hy hlo hhi
  have hy0 : 0 < |y| := by linarith
  have hyne : y ≠ 0 := by intro he; simp only [he,abs_zero] at hy; linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let T : ℕ → ℝ := fun i => b+periodAngle m i/|y|
  let c : ℕ → ℝ := fun i => -Real.cos (periodAngle m i)
  let ε := |y| * h
  have hrow (i : ℕ) (hi : i ∈ Finset.range (8*m)) :
      (1261/10000 : ℝ)*
          ((Real.exp (-T i/2)*(T i+h)^N/N.factorial)*(max 0 (Real.cos (y*T i))+|y| * h)*h)-
        (1309/10000 : ℝ)*
          ((Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*max 0 (Real.cos (y*T i)-|y| * h)*h) ≤
      (((501/500 : ℝ)*(50001/50000)*(1261/10000)*(max 0 (c i)+ε)-
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
      (mul_le_mul_of_nonneg_left hVi.1 (by norm_num)).trans (lower_radial hti.le hhu)
    have hVp : Real.exp (-T i/2)*(T i+h)^N/N.factorial ≤
        (501/500 : ℝ)*(50001/50000)*V₀ := by
      have he := (upper_radial hti hNt hh.le hhu).trans
        (mul_le_mul_of_nonneg_left hVi.2 (by norm_num : (0 : ℝ) ≤ 50001/50000))
      nlinarith only [he]
    have hp := ZetaRieszPhaseBudget.phase_at_negative_peak hyne hpeak (periodAngle m i)
    have hphase : Real.cos (y*T i) = c i := by dsimp only [c,T]; linarith only [hp]
    rw [hphase]
    have hm' := mul_le_mul_of_nonneg_right hVm
      (show 0 ≤ (1309/10000 : ℝ)*max 0 (c i-ε)*h by positivity)
    have hp' := mul_le_mul_of_nonneg_right hVp
      (show 0 ≤ (1261/10000 : ℝ)*(max 0 (c i)+ε)*h by dsimp [ε]; positivity)
    dsimp only [ε] at hm' hp' ⊢
    nlinarith only [hm',hp']
  have hsum := Finset.sum_le_sum hrow
  simp only [← Finset.sum_mul] at hsum
  have hscalar := finite_upper_central_budget (show 0 ≤ ε by dsimp [ε]; positivity) hε
    (sum_negative_cos_lower hm)
  have hscaled := mul_le_mul_of_nonneg_right hscalar (show 0 ≤ V₀*h by positivity)
  refine ⟨V₀,hV₀,?_,?_⟩
  · simpa only [zero_div,add_zero] using (hV 0 (by
      constructor <;> linarith [Real.pi_pos])).2
  · nlinarith only [hscaled,hsum]

end
end RiemannGaussian.ZetaRieszCentralSharpBudget
