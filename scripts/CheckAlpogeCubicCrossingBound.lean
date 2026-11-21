import CheckAlpogeCubicRoughRange

/-! # Absolute cost of the moving correction

Pairing divisors around the square root controls their total on each short
quotient interval. Summing the lengths of the intervals costs a harmonic sum.
-/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real
open scoped Classical

private theorem divisors_fold {t Q : ℕ} (ht : 0 < t) (hQ : t ≤ Q^2) :
    t.divisors.card ≤ 2*((Icc 1 Q).filter (· ∣ t)).card := by
  let D := (Icc 1 Q).filter (· ∣ t)
  have hcov : t.divisors ⊆ D ∪ D.image (t/·) := by
    intro d hd
    have h := (Nat.mem_divisors.mp hd).1
    have hd0 := Nat.pos_of_dvd_of_pos h ht
    by_cases hsmall : d ≤ Q
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨hd0,hsmall⟩,h⟩)
    · let e := t/d
      have he : e*d = t := Nat.div_mul_cancel h
      have he0 : 0 < e := Nat.div_pos (Nat.le_of_dvd ht h) hd0
      have heQ : e ≤ Q := by
        by_contra! hh
        have := Nat.mul_le_mul (show Q+1 ≤ e by omega) (show Q+1 ≤ d by omega)
        nlinarith only [this,hQ,he]
      have hed : e ∣ t := ⟨d,he.symm⟩
      exact mem_union_right _ (mem_image.mpr ⟨e,mem_filter.mpr ⟨mem_Icc.mpr ⟨he0,heQ⟩,hed⟩,
        Nat.div_eq_of_eq_mul_right he0 he.symm⟩)
  exact (card_le_card hcov).trans ((card_union_le ..).trans
    ((Nat.add_le_add_left card_image_le _).trans_eq (by simp [D,two_mul])))

/-- Total divisor count on a short interval, with a square-root scale Q. -/
theorem cubicShortDivisorSum {a b Q : ℕ} (hab : a ≤ b) (hQ : b ≤ Q^2) :
    (∑ t ∈ Ioc a b, (t.divisors.card:ℝ)) ≤
      2*((Q:ℝ)+((b-a:ℕ):ℝ)*(1+log Q)) := by
  have hrow (d : ℕ) (hd : d ∈ Icc 1 Q) :
      (∑ t ∈ Ioc a b, if d ∣ t then (1:ℝ) else 0) ≤ 1 + ((b-a:ℕ):ℝ)*(d:ℝ)⁻¹ := by
    have hd0 : 0 < d := (mem_Icc.mp hd).1
    let S := (Ioc a b).filter (d ∣ ·)
    have hmap : Set.MapsTo (·/d) (↑S) (↑(Ioc (a/d) (b/d))) := by
      intro t ht
      obtain ⟨hi,hdiv⟩ := mem_filter.mp ht
      exact mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul hd0).mpr
        ((mem_Ioc.mp hi).1.trans_eq (Nat.div_mul_cancel hdiv).symm),Nat.div_le_div_right (mem_Ioc.mp hi).2⟩
    have hinj : Set.InjOn (·/d) (↑S) := by
      intro s hs t ht he
      exact (Nat.div_mul_cancel (mem_filter.mp hs).2).symm.trans
        ((congrArg (·*d) he).trans (Nat.div_mul_cancel (mem_filter.mp ht).2))
    have hc := card_le_card_of_injOn _ hmap hinj
    rw [Nat.card_Ioc] at hc
    rw [← sum_filter]
    simpa [S] using (show (S.card:ℝ) ≤ _ from
      (show (S.card:ℝ) ≤ ((b/d-a/d:ℕ):ℝ) by exact_mod_cast hc).trans (cubicQuotientInterval_count hab hd0))
  calc
    _ ≤ ∑ t ∈ Ioc a b, 2*(∑ d ∈ Icc 1 Q, if d ∣ t then (1:ℝ) else 0) := by
      apply sum_le_sum
      intro t ht
      rw [← sum_filter]
      simpa using (show (t.divisors.card:ℝ) ≤ 2*(((Icc 1 Q).filter (· ∣ t)).card:ℝ) by
        exact_mod_cast divisors_fold ((Nat.zero_le _).trans_lt (mem_Ioc.mp ht).1) ((mem_Ioc.mp ht).2.trans hQ))
    _ = 2*(∑ d ∈ Icc 1 Q, ∑ t ∈ Ioc a b, if d ∣ t then (1:ℝ) else 0) := by rw [← mul_sum,sum_comm]
    _ ≤ 2*(∑ d ∈ Icc 1 Q, (1+((b-a:ℕ):ℝ)*(d:ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hrow) (by norm_num)
    _ ≤ _ := by
      rw [sum_add_distrib,← mul_sum]
      simp only [sum_const,nsmul_eq_mul,mul_one,Nat.card_Icc,Nat.add_sub_cancel]
      gcongr
      exact primeWindow_harmonic_le le_rfl

private theorem active_weight_variation {n t : ℕ} (hn : 8 ≤ n) (ht : 0 < t) :
    |cubicMean n (fun M => activeCubicWeight M t) - activeCubicWeight (n^4) t| ≤ 1 := by
  have h (M : ℕ) : 0 ≤ activeCubicWeight M t ∧ activeCubicWeight M t ≤ 1 := by
    by_cases hm : t ≤ M
    · simpa [activeCubicWeight,hm] using weight_mem (N := M) ht
    · simp [activeCubicWeight,hm]
  have hlo := cubicMean_le_on (f := fun _ => 0) hn (fun M _ _ => (h M).1)
  have hhi := cubicMean_le_on (g := fun _ => 1) hn (fun M _ _ => (h M).2)
  rw [cubicMean_const] at hlo hhi
  exact abs_le.mpr ⟨by linarith only [hlo,(h (n^4)).2],by linarith only [hhi,(h (n^4)).1]⟩

/-- Absolute bound for the entire crossing correction. L bounds the sum of the
quotient-interval lengths. Q bounds the smaller member of every divisor pair. -/
theorem roughRangeCorrection_abs {n : ℕ} (hn : 8 ≤ n) :
    let a := cubicSampleStart n
    let b := cubicSampleEnd n
    let J : ℕ := 2*(Nat.log 2 n+1)^3
    let Q : ℕ := 2*n^2
    let L : ℝ := J + ((b-a:ℕ):ℝ)*(1+log J)
    |roughRangeCorrection n| ≤ ((1+4*(1+log Q))*L + 4*Q*J)*log b := by
  let a := cubicSampleStart n
  let b := cubicSampleEnd n
  let J := 2*(Nat.log 2 n+1)^3
  let Q := 2*n^2
  let row := fun j : ℕ => Ioc (a/j) (b/j)
  let I := Icc 1 J
  let W := fun t : ℕ => 1+2*(t.divisors.card:ℝ)
  let K := 1+4*(1+log Q)
  have hK : 0 ≤ K := by dsimp [K]; positivity [log_natCast_nonneg Q]
  have hW (t : ℕ) : 0 ≤ W t := by dsimp [W]; positivity
  have hab : a ≤ b := (Nat.sub_le _ _).trans (Nat.le_add_right _ _)
  have hQ : b ≤ Q^2 := (cubicSampleEnd_le hn).trans (by dsimp [Q]; nlinarith only [Nat.zero_le (n^4)])
  have hlog := log_natCast_nonneg b
  have hpoint {t : ℕ} (ht : t ∈ roughRangeCrossings n) :
      |roughRangeCoefficient n t| ≤ W t*log b := by
    have hi := mem_Ioc.mp (mem_filter.mp ht).1
    have ht0 := (Nat.zero_le _).trans_lt hi.1
    have hraw := (abs_cubicRoughCoefficient_le_divisors ht0 n).trans
      (mul_le_mul_of_nonneg_left (log_le_log (Nat.cast_pos.mpr ht0)
        (show (t:ℝ) ≤ b by exact_mod_cast hi.2)) (hW t))
    unfold roughRangeCoefficient cubicThreeFactorCoefficient
    split_ifs <;> first | exact hraw | simpa only [abs_zero] using mul_nonneg (hW t) hlog
  have hw (t : ℕ) (ht : t ∈ roughRangeCrossings n) :
      ∃ z ∈ I.sigma row, z.2 = t := by
    obtain ⟨j,hj,hJ,hlo,hhi⟩ := roughRangeCrossings_quotient hn ht
    exact ⟨⟨j,t⟩,mem_sigma.mpr ⟨mem_Icc.mpr ⟨hj,hJ⟩,mem_Ioc.mpr
      ⟨(Nat.div_lt_iff_lt_mul hj).mpr (by simpa [mul_comm] using hlo),
       (Nat.le_div_iff_mul_le hj).mpr (by simpa [mul_comm] using hhi)⟩⟩,rfl⟩
  choose! e he ht using hw
  have hinj : Set.InjOn e ↑(roughRangeCrossings n) := fun s hs t' ht' h =>
    (ht s hs).symm.trans ((congrArg (fun z : (Σ _ : ℕ, ℕ) => z.2) h).trans (ht t' ht'))
  have hcost : (∑ t ∈ roughRangeCrossings n, W t) ≤ ∑ j ∈ I, ∑ t ∈ row j, W t := by
    rw [sum_sigma' I row (fun _ t => W t)]
    exact sum_le_sum_of_injOn e hinj
      (by intro z hz; obtain ⟨t,ht',rfl⟩ := mem_image.mp hz; exact he t ht')
      (fun t ht' => (congrArg W (ht t ht')).ge) (fun z _ _ => hW z.2)
  have hrow (j : ℕ) : (∑ t ∈ row j, W t) ≤
      K*((b/j-a/j:ℕ):ℝ) + 4*Q := by
    have hdiv := cubicShortDivisorSum (Nat.div_le_div_right (c := j) hab) ((Nat.div_le_self b j).trans hQ)
    simp only [row,W,sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,Nat.card_Ioc,← mul_sum]
    dsimp [K]
    linarith only [hdiv]
  have hlen : (∑ j ∈ I, ((b/j-a/j:ℕ):ℝ)) ≤ J+((b-a:ℕ):ℝ)*(1+log J) := by
    refine (sum_le_sum (fun j hj => cubicQuotientInterval_count hab (mem_Icc.mp hj).1)).trans ?_
    rw [sum_add_distrib,← mul_sum]
    have hones : (∑ _j ∈ I, (1:ℝ)) = J := by simp [I,Nat.card_Icc]
    rw [hones]
    gcongr
    exact primeWindow_harmonic_le le_rfl
  have htot := hcost.trans (sum_le_sum (fun j _ => hrow j))
  have hrhs : (∑ j ∈ I, (K*((b/j-a/j:ℕ):ℝ) + 4*Q)) =
      K*(∑ j ∈ I, ((b/j-a/j:ℕ):ℝ)) + J*(4*(Q:ℝ)) := by
    rw [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul]
    simp [I,Nat.card_Icc]
  rw [hrhs] at htot
  calc
    |roughRangeCorrection n| ≤ ∑ t ∈ roughRangeCrossings n, W t*log b := by
      unfold roughRangeCorrection
      apply (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
      intro t ht'
      rw [abs_mul]
      have hv := active_weight_variation hn ((Nat.zero_le _).trans_lt (mem_Ioc.mp (mem_filter.mp ht').1).1)
      exact (mul_le_mul_of_nonneg_left hv (abs_nonneg _)).trans ((mul_one _).le.trans (hpoint ht'))
    _ = (∑ t ∈ roughRangeCrossings n, W t)*log b := (sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (by
      have hb := mul_le_mul_of_nonneg_left hlen hK
      change _ ≤ K*(J+((b-a:ℕ):ℝ)*(1+log J)) + 4*Q*J
      linarith only [htot,hb]) hlog

private theorem crossing_polynomial_bound {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    ((1+4*(1+3*y))*(2*y^3+2*y*x^3*(1+4*y)) + 4*(2*x^2)*(2*y^3))*(5*y)
      ≤ 1100*x^3*y^5 := by
  obtain ⟨v,hv,rfl⟩ := exists_nonneg_add_of_le hx
  obtain ⟨u,hu,rfl⟩ := exists_nonneg_add_of_le hy
  apply sub_nonneg.mp
  ring_nf
  positivity

/-- At the fourth-power sample scale the total moving correction is at most
n^(3+ε) for every fixed ε>0, uniformly at all sufficiently large samples. -/
theorem roughRangeCorrection_subquartic {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, |roughRangeCorrection n| ≤ (n:ℝ)^(3+ε) := by
  obtain ⟨N,hN⟩ := cubicDepth_power_eventually 5 (C := 1100) (by norm_num) hε
  refine ⟨max 8 N,fun n hn => ?_⟩
  have h8 : 8 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  let k := Nat.log 2 n+1
  have hk0 : 0 < k := Nat.succ_pos _
  have hkR : 1 ≤ (k:ℝ) := by exact_mod_cast hk0
  have hln := cubicLog_le_depth hn0
  change log (n:ℝ) ≤ k at hln
  have hlog2 : log 2 ≤ 1 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hnR0 : 0 < (n:ℝ) := Nat.cast_pos.mpr hn0
  have hkR0 : 0 < (k:ℝ) := Nat.cast_pos.mpr hk0
  have hQ : log ((2*n^2:ℕ):ℝ) ≤ 3*(k:ℝ) := by
    push_cast
    rw [log_mul (by norm_num) (by positivity),log_pow]
    norm_num1
    linarith only [hlog2,hln,hkR]
  have hJ : log ((2*k^3:ℕ):ℝ) ≤ 4*(k:ℝ) := by
    push_cast
    rw [log_mul (by norm_num) (by positivity),log_pow]
    norm_num1
    linarith only [hlog2,log_le_sub_one_of_pos hkR0,hkR]
  have hb : log (cubicSampleEnd n) ≤ 5*(k:ℝ) := by
    have hb0 : 0 < cubicSampleEnd n := (show 0 < n^4 by positivity).trans_le (Nat.le_add_right _ _)
    have hh := log_le_log (Nat.cast_pos.mpr hb0) (show (cubicSampleEnd n:ℝ) ≤ 2*(n:ℝ)^4 by
      exact_mod_cast cubicSampleEnd_le h8)
    rw [log_mul (by norm_num) (by positivity),log_pow] at hh
    norm_num1 at hh
    linarith only [hh,hlog2,hln,hkR]
  have hw : cubicSampleEnd n-cubicSampleStart n ≤ 2*k*n^3 := by
    change (n^4+k*n^3)-(n^4-k*n^3) ≤ 2*k*n^3
    rw [mul_assoc]
    omega
  have hwR : ((cubicSampleEnd n-cubicSampleStart n:ℕ):ℝ) ≤ 2*(k:ℝ)*(n:ℝ)^3 := by exact_mod_cast hw
  have h := roughRangeCorrection_abs h8
  change |roughRangeCorrection n| ≤
    ((1+4*(1+log ((2*n^2:ℕ):ℝ))) * (((2*k^3:ℕ):ℝ) +
      ((cubicSampleEnd n-cubicSampleStart n:ℕ):ℝ)*(1+log ((2*k^3:ℕ):ℝ))) +
      4*((2*n^2:ℕ):ℝ)*((2*k^3:ℕ):ℝ))*log (cubicSampleEnd n) at h
  have hL := mul_le_mul hwR (add_le_add_right hJ 1)
    (by positivity [log_natCast_nonneg (2*k^3)]) (by positivity)
  have hK : 1+4*(1+log ((2*n^2:ℕ):ℝ)) ≤ 1+4*(1+3*(k:ℝ)) := by linarith only [hQ]
  have hKL := mul_le_mul hK (add_le_add_right hL (((2*k^3:ℕ):ℝ)))
    (by positivity [log_natCast_nonneg (2*k^3)]) (by positivity)
  have hfull := mul_le_mul (add_le_add_left hKL (4*((2*n^2:ℕ):ℝ)*((2*k^3:ℕ):ℝ))) hb
    (log_natCast_nonneg _) (by positivity)
  push_cast at hfull h
  have hp := hN n (by omega)
  change 1100*(k:ℝ)^5 ≤ (n:ℝ)^ε at hp
  calc
    _ ≤ _ := h.trans hfull
    _ ≤ 1100*(n:ℝ)^3*(k:ℝ)^5 := crossing_polynomial_bound hnR hkR
    _ = (n:ℝ)^3*(1100*(k:ℝ)^5) := by ring
    _ ≤ (n:ℝ)^3*(n:ℝ)^ε := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by rw [rpow_add hnR0]; norm_num

/-- Any strictly smaller quartic margin survives evaluating the retained
coefficients at the central sample alone. -/
theorem roughRangeCentral_quartic_margin_sharp {κ : ℝ} (hκ : κ < 1/200000) :
    ∃ N : ℕ, ∀ n ≥ N, roughRangeCentralResponse n + κ*(n:ℝ)^4 ≤
      cubicWeightedResponse n (cubicThreeFactorCoefficient n) := by
  obtain ⟨A,hA⟩ := roughRangeResponse_quartic_margin_sharp
  obtain ⟨B,hB⟩ := roughRangeCorrection_subquartic (by norm_num : (0:ℝ)<1/2)
  let η := 1/200000-κ
  have hη : 0 < η := sub_pos.mpr hκ
  have hl := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).comp tendsto_natCast_atTop_atTop
  obtain ⟨D,hD⟩ := Filter.eventually_atTop.mp (hl.eventually_ge_atTop η⁻¹)
  refine ⟨max 8 (max A (max B D)),fun n hn => ?_⟩
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hh := hD n (by omega)
  change η⁻¹ ≤ (n:ℝ)^(1/2:ℝ) at hh
  have hu : 1 ≤ η*(n:ℝ)^(1/2:ℝ) := by
    simpa [hη.ne'] using mul_le_mul_of_nonneg_left hh hη.le
  have hb := mul_le_mul_of_nonneg_right hu (rpow_pos_of_pos hn0 (3+1/2)).le
  rw [one_mul,mul_assoc,← rpow_add hn0,show (1/2:ℝ)+(3+1/2) = 4 by norm_num] at hb
  rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, rpow_natCast] at hb
  norm_num1 at hb
  have hc := hB n (by omega)
  norm_num1 at hc
  have hneg := (abs_le.mp (hc.trans hb)).1
  dsimp [η] at hneg
  linarith only [roughRangeCentral_add_correction (by omega : 8 ≤ n),hA n (by omega),hneg]

theorem roughRangeCentral_quartic_margin {κ : ℝ} (hκ : κ < 3/655360) :
    ∃ N : ℕ, ∀ n ≥ N, roughRangeCentralResponse n + κ*(n:ℝ)^4 ≤
      cubicWeightedResponse n (cubicThreeFactorCoefficient n) :=
  roughRangeCentral_quartic_margin_sharp (lt_trans hκ (by norm_num))

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.cubicShortDivisorSum,
      ``RiemannGaussian.AlpogeMined.roughRangeCorrection_abs,
      ``RiemannGaussian.AlpogeMined.roughRangeCorrection_subquartic,
      ``RiemannGaussian.AlpogeMined.roughRangeCentral_quartic_margin] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
