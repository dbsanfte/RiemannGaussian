import CheckAlpogeCubicQuadrature
import CheckAlpogeIntegerBaseline
import RiemannGaussian.AlpogeZetaShortIntervals

/-! # Replacing the repeated cubic-window average by its fourth-power center -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real AlpogeZetaSamples

/-- The common affine slope cancels in a symmetric integer block. -/
private theorem blockMean_G_upper {A H : ℕ} (hA : 0 < A) :
    blockMean A (2*H+1) (fun M => G M) ≤ G (A+H : ℕ) +
      (2*(H:ℝ)+1)*log (A+2*H : ℕ)*(2*H/A) := by
  have ha : 1 ≤ (A:ℝ) := by exact_mod_cast hA
  obtain ⟨s,hs⟩ := G_affine_upper (x := (A+H:ℕ)) (b := (A+2*H:ℕ)) ha
    (by exact_mod_cast (show A ≤ A+H by omega)) (by exact_mod_cast (show A+H ≤ A+2*H by omega))
  let E := (2*(H:ℝ)+1)*log (A+2*H : ℕ)*(2*H/A)
  have hc := mean_center (N := A+H) (H := H) (by omega)
  rw [Nat.add_sub_cancel] at hc
  have hp (j : ℕ) (hj : j ∈ range (2*H+1)) :
      G (A+j : ℕ) ≤ G (A+H : ℕ)+s*((A+j:ℕ)-(A+H:ℕ):ℝ)+E := by
    have hj' := mem_range.mp hj
    have h := hs (A+j:ℕ) (by exact_mod_cast (show A ≤ A+j by omega))
      (by exact_mod_cast (show A+j ≤ A+2*H by omega))
    dsimp only [E]
    push_cast at h ⊢
    simpa only [add_sub_cancel_left] using h
  have ht := sum_le_sum hp
  simp only [sum_add_distrib,← mul_sum,sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,hc] at ht
  unfold blockMean
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (2*H+1:ℕ))).mpr
  change _ ≤ (G (A+H:ℕ)+E)*_
  push_cast at ht ⊢
  linarith only [ht]

/-- A fixed lower and upper support bound controls every individual smoothing pass. -/
theorem repeatedMean_G_upper {L U : ℕ} (hL : 0 < L) (H k A : ℕ)
    (hla : L ≤ A) (hau : A+k*(2*H) ≤ U) :
    repeatedMean (2*H+1) k (fun M => G M) A ≤ G (A+k*H : ℕ) +
      (k:ℝ)*((2*(H:ℝ)+1)*log U*(2*H/L)) := by
  let E := (2*(H:ℝ)+1)*log U*(2*H/L)
  change _ ≤ _+(k:ℝ)*E
  induction k generalizing A with
  | zero => simp [repeatedMean]
  | succ k ih =>
    rw [Nat.succ_mul] at hau
    have hw : (0:ℝ) < (2*H+1:ℕ) := by positivity
    have step (j : ℕ) (hj : j ∈ range (2*H+1)) :
        repeatedMean (2*H+1) k (fun M => G M) (A+j) ≤ G (A+k*H+j:ℕ)+(k:ℝ)*E := by
      have hj' := mem_range.mp hj
      simpa only [show A+j+k*H=A+k*H+j by omega] using ih (A+j) (by omega) (by omega)
    have he := div_le_div_of_nonneg_right (sum_le_sum step) hw.le
    rw [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,add_div,mul_div_cancel_left₀ _ hw.ne'] at he
    have ha : 0 < A+k*H := by omega
    have hh := blockMean_G_upper (H := H) ha
    have hku : A+k*H+2*H ≤ U := by rw [show k*(2*H)=2*(k*H) by ring] at hau; omega
    have hlog := log_le_log (Nat.cast_pos.mpr (show 0 < A+k*H+2*H by omega))
      (Nat.cast_le.mpr hku : ((A+k*H+2*H:ℕ):ℝ) ≤ U)
    have hden := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2*(H:ℝ)) (Nat.cast_pos.mpr hL)
      (Nat.cast_le.mpr (show L ≤ A+k*H by omega))
    have hcost : (2*(H:ℝ)+1)*log (A+k*H+2*H:ℕ)*(2*H/(A+k*H:ℕ)) ≤ E :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlog (by positivity)) hden (by positivity)
        (mul_nonneg (by positivity) (log_natCast_nonneg U))
    change blockMean A (2*H+1) (repeatedMean (2*H+1) k (fun M => G M)) ≤ _
    change blockMean A (2*H+1) _ ≤ blockMean (A+k*H) (2*H+1) (fun M => G M)+(k:ℝ)*E at he
    rw [Nat.succ_mul k H,Nat.cast_succ,← Nat.add_assoc]
    linarith only [hh,he,hcost]

open scoped ArithmeticFunction.vonMangoldt in
private theorem mean_low_prime_upper {W D : ℕ} (hw : 0 < W) (hD : 0 < D) (k A : ℕ) :
    repeatedMean W k (fun M => lowPrimeSum M D) A ≤
      Chebyshev.theta D*(1/2+((D:ℝ)/W)^k) + (log D + (log 4+4)) := by
  let S := (Ioc 0 D).filter Nat.Prime
  have htheta : Chebyshev.theta D = ∑ p ∈ S, log p := by simp [Chebyshev.theta,S]
  have hsum : (fun M => lowPrimeSum M D) = ∑ p ∈ S, (log p) • (fun M => weight M p) := by
    ext M
    simp [S,lowPrimeSum,Finset.sum_apply]
  have hM : (∑ p ∈ S, Λ p/(p:ℝ)) ≤ log D+(log 4+4) :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ =>
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))).trans
      (Formalism.LogFactorialMertensBounds.mertens_upper D hD)
  rw [hsum,map_sum,Finset.sum_apply,htheta,sum_mul]
  simp only [map_smul,Pi.smul_apply,smul_eq_mul]
  apply le_trans _ (add_le_add_right hM _)
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  obtain ⟨hi,prime⟩ := mem_filter.mp hp
  have hh := (abs_le.mp (repeated_weight_error prime.pos hw k A)).2
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (p:ℝ)/W)
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr (mem_Ioc.mp hi).2) (Nat.cast_nonneg W)) k
  have hp0 : 0 < (p:ℝ) := Nat.cast_pos.mpr prime.pos
  have hdiv : 1/(2*(p:ℝ)) ≤ 1/(p:ℝ) := one_div_le_one_div_of_le hp0 (by linarith)
  have h := mul_le_mul_of_nonneg_left
    (by linarith only [hh,hpow,hdiv] : repeatedMean W k (fun M => weight M p) A ≤
      1/2+((D:ℝ)/W)^k+1/(p:ℝ)) (log_natCast_nonneg p)
  rw [ArithmeticFunction.vonMangoldt_apply_prime prime]
  exact h.trans_eq (by ring)

private theorem repeat_tail_le_mean_G {A D : ℕ} (hD : 0 < D) (hDA : D ≤ A)
    (H k : ℕ) {B : ℝ} (hB : ∀ M, A ≤ M → M ≤ A+k*(2*H) →
      eulerMascheroniConstant*M-primeSum M ≤ G M+B) :
    eulerMascheroniConstant*((A:ℝ)+(k:ℝ)*H)-Chebyshev.theta D/2-
        repeatedMean (2*H+1) k (fun M => upperPrimeSum M D) A ≤
      repeatedMean (2*H+1) k (fun M => G M) A+B+
        Chebyshev.theta D*((D:ℝ)/(2*(H:ℝ)+1))^k+(log D+(log 4+4)) := by
  let W := 2*H+1
  have hw : 0 < W := by dsimp only [W]; omega
  have hh := @repeat_mono W k A (eulerMascheroniConstant • (fun M : ℕ => (M:ℝ)))
    ((fun M : ℕ => G M)+(fun _ => B)+(fun M => lowPrimeSum M D)+(fun M => upperPrimeSum M D)) (by
      intro M hmin hmax
      have h := hB M hmin (by simpa [W] using hmax)
      rw [split_primeSum (hDA.trans hmin)] at h
      simp only [Pi.smul_apply,smul_eq_mul,Pi.add_apply]
      linarith only [h])
  simp only [map_smul,map_add,Pi.add_apply,Pi.smul_apply,smul_eq_mul,repeat_const hw] at hh
  have hfirst := repeat_first_moment H k A
  have hlow := mean_low_prime_upper hw hD k A
  have hW : (W:ℝ) = 2*(H:ℝ)+1 := by simp [W]
  rw [hW] at hlow
  dsimp only [W] at hh hlow
  rw [hfirst] at hh
  linarith only [hh,hlow]


/-- At n⁴ the repeated prime tail and the actual centered ramp agree in both
directions within one quadratic logarithmic allowance. -/
theorem repeatedTailAt_central_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n ≥ 8,
      |repeatedTailAt (Nat.log 2 n+1) n (n^3)-G ((n:ℝ)^4)| ≤ K*(n:ℝ)^2*(1+log n)^2 := by
  obtain ⟨C,hC⟩ := integer_sample_abs_error
  refine ⟨2*|C|+130,by positivity,fun n hn => ?_⟩
  let D := n^3
  let k := Nat.log 2 n+1
  let A := n^4-k*D
  let U := 2*n^4
  let l := 1+log n
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn0
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn0
  have hd : 0 < D := pow_pos hn0 3
  have hd1 : 1 ≤ (D:ℝ) := by exact_mod_cast hd
  obtain ⟨hk,hsize⟩ := cubic_tail_parameters hn
  have hhalf : 2*(k*D) ≤ n^4 := by
    simpa only [D,k,← Nat.mul_assoc,show n^4=n*n^3 by ring] using Nat.mul_le_mul_right D hk
  have hd2 : 2*D ≤ n^4 := (Nat.mul_le_mul_right D (by omega : 2 ≤ n)).trans_eq (by dsimp [D]; ring)
  have hDA : D ≤ A := by dsimp only [A]; omega
  have ha := hd.trans_le hDA
  have hA2 : (n:ℝ)^4 ≤ 2*(A:ℝ) := by exact_mod_cast (show n^4 ≤ 2*A by dsimp [A]; omega)
  have hc : A+k*D=n^4 := by dsimp only [A]; omega
  have hu : A+k*(2*D) ≤ U := by dsimp only [U]; rw [show k*(2*D)=2*(k*D) by ring]; omega
  have hl : 1 ≤ l := by dsimp only [l]; linarith only [log_natCast_nonneg n]
  have hdepth : (k:ℝ) ≤ 2*l := cubic_depth_le_twice_log hn0
  have hlog2 : log 2 ≤ 1 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlog4 : log 4 ≤ 3 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have hlogU : log U ≤ 4*l := by
    simp only [U,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,log_mul (by norm_num : (2:ℝ) ≠ 0)
      (pow_ne_zero 4 hnR.ne'),log_pow,l]
    linarith only [hlog2]
  have hquad : (2*(D:ℝ)+1)*(2*D/A) ≤ 12*(n:ℝ)^2 := by
    rw [← mul_div_assoc,div_le_iff₀ (Nat.cast_pos.mpr ha)]
    have h := mul_le_mul_of_nonneg_right (by linarith : 2*(D:ℝ)+1 ≤ 3*D) (by positivity : 0 ≤ 2*(D:ℝ))
    dsimp only [D] at h ⊢
    push_cast at h ⊢
    nlinarith only [h,mul_le_mul_of_nonneg_left hA2 (by positivity : 0 ≤ 6*(n:ℝ)^2)]
  have hav := repeatedMean_G_upper ha D k A le_rfl hu
  rw [hc,Nat.cast_pow] at hav
  have hprod := mul_le_mul
    (mul_le_mul hdepth hlogU (log_natCast_nonneg _) (by positivity [zero_le_one.trans hl]))
    hquad (by positivity) (by positivity [zero_le_one.trans hl])
  have hcost : (k:ℝ)*((2*(D:ℝ)+1)*log U*(2*D/A)) ≤ 96*(n:ℝ)^2*l^2 := by
    nlinarith only [hprod]
  have hB (M : ℕ) (hAM : A ≤ M) (hM : M ≤ A+k*(2*D)) :
      eulerMascheroniConstant*M-primeSum M ≤ G M+2*|C| *(n:ℝ)^2 := by
    have hM' : (M:ℝ) ≤ 2*(n:ℝ)^4 := by exact_mod_cast hM.trans hu
    have hs : sqrt M ≤ 2*(n:ℝ)^2 := sqrt_le_iff.mpr ⟨by positivity,
      by nlinarith only [hM',pow_nonneg hnR.le 4]⟩
    have h := (abs_le.mp (hC M (ha.trans_le hAM))).1
    linarith only [h,mul_le_mul (le_abs_self C) hs (sqrt_nonneg _) (abs_nonneg _)]
  have ht := repeat_tail_le_mean_G hd hDA D k hB
  have hmid : (A:ℝ)+(k:ℝ)*D=(n:ℝ)^4 := by exact_mod_cast hc
  rw [hmid] at ht
  have hres : Chebyshev.theta D*((D:ℝ)/(2*(D:ℝ)+1))^k ≤ (log 4+4)*(n:ℝ)^2 := by
    simpa only [D,k,Nat.cast_pow] using repeated_endpoint_cost hsize
  have hlarge : (n:ℝ)^2 ≤ (n:ℝ)^2*l^2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hl (n := 2)) (sq_nonneg (n:ℝ))
  have hlogD : log D ≤ 3*(n:ℝ)^2 := by
    simp only [D,Nat.cast_pow,log_pow,Nat.cast_ofNat]
    nlinarith only [log_le_sub_one_of_pos hnR,sq_nonneg ((n:ℝ)-1),hn1]
  have hn2 := one_le_pow₀ hn1 (n := 2)
  have hl2 := le_self_pow₀ hl (by decide : 2 ≠ 0)
  have hdepth' : ((Nat.log 2 n:ℕ):ℝ) ≤ 2*l := by
    dsimp only [k] at hdepth
    rw [Nat.cast_add_one] at hdepth
    linarith only [hdepth]
  have hg := G_fourth_le_cubic_tail n hn
  change |_ - _| ≤ (2*|C|+130)*(n:ℝ)^2*l^2
  apply abs_le.mpr
  constructor
  · nlinarith only [hg,hlarge,mul_le_mul_of_nonneg_right hdepth' (sq_nonneg (n:ℝ)),
      mul_le_mul_of_nonneg_left hl2 (sq_nonneg (n:ℝ)),
      mul_le_mul_of_nonneg_right hlog4 (sq_nonneg (n:ℝ)),
      mul_nonneg (abs_nonneg C) (mul_nonneg (sq_nonneg (n:ℝ)) (sq_nonneg l))]
  · change eulerMascheroniConstant*(n:ℝ)^4-Chebyshev.theta D/2-
        repeatedMean (2*D+1) k (fun M => upperPrimeSum M D) A - _ ≤ _
    nlinarith only [ht,hav,hcost,hres,hlogD,hlog4,hn2,hlarge,
      mul_le_mul_of_nonneg_right hlog4 (sq_nonneg (n:ℝ)),
      mul_le_mul_of_nonneg_left hlarge (abs_nonneg C)]

/-- The signed Mangoldt statistic and the single central ramp agree up to the
allowance used in the arithmetic power-window criterion. -/
theorem cubicMangoldtTail_central_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n ≥ 8,
      |cubicMangoldtTail n-G ((n:ℝ)^4)| ≤ K*(n:ℝ)^2*(1+log n)^2 := by
  obtain ⟨C,hC,h₁⟩ := repeatedTailAt_central_error
  obtain ⟨B,hB,h₂⟩ := cubic_chebyshev_mangoldt_error
  refine ⟨C+B+32,by positivity,fun n hn => ?_⟩
  have ha := abs_le.mp (h₁ n hn)
  have hb := abs_le.mp (h₂ n hn)
  have hc := abs_le.mp (cubic_tail_sum_integral_error hn)
  have hl := one_le_pow₀ (by linarith only [log_natCast_nonneg n] : 1 ≤ 1+log n) (n := 2)
  have hscale := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (B+32)*(n:ℝ)^2)
  apply abs_le.mpr
  constructor <;> nlinarith only [ha.1,ha.2,hb.1,hb.2,hc.1,hc.2,hscale]

/-- The signed sieve comparison at the cubic cutoff can be tested at a single
fourth power, using the whole prime band above its square root. -/
theorem cubicMangoldtTail_singlePrime_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n ≥ 8, |cubicMangoldtTail n-integerPrimeDiscrepancy (n^2)| ≤
      K*(n:ℝ)^2*(1+log n)^2 := by
  obtain ⟨C,hC,h₁⟩ := cubicMangoldtTail_central_error
  obtain ⟨B,hB,h₂⟩ := singlePrime_central_error
  refine ⟨C+B,by positivity,fun n hn => ?_⟩
  have h := abs_sub_le (cubicMangoldtTail n) (G ((n:ℝ)^4)) (integerPrimeDiscrepancy (n^2))
  have hl := one_le_pow₀ (by linarith only [log_natCast_nonneg n] : 1 ≤ 1+log n) (n := 2)
  apply h.trans
  nlinarith only [h₁ n hn,h₂ n (by omega),mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ B*(n:ℝ)^2)]

/-- Increasing the allowance by K transfers excess in either direction on exactly
the same indices, before any cofinal or asymptotic argument. -/
theorem cubicMangoldt_singlePrime_window_sandwich :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ C : ℝ, ∀ {m b : ℕ}, 8 ≤ m →
      cubicMangoldtExcessOn (C+K) m b ≤ singlePrimeExcessOn C m b ∧
      singlePrimeExcessOn (C+K) m b ≤ cubicMangoldtExcessOn C m b := by
  obtain ⟨K,hK,h⟩ := cubicMangoldtTail_singlePrime_error
  refine ⟨K,hK,fun C {m b} hm => ?_⟩
  constructor <;> apply sum_le_sum <;> intro n hn <;>
    apply div_le_div_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg n) 3) <;>
    apply max_le_max_right <;>
    have hh := abs_le.mp (h n (hm.trans (mem_Icc.mp hn).1)) <;>
    linarith only [hh.1,hh.2]

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for name in [``RiemannGaussian.AlpogeMined.repeatedMean_G_upper,
      ``RiemannGaussian.AlpogeMined.cubicMangoldtTail_central_error,
      ``RiemannGaussian.AlpogeMined.cubicMangoldt_singlePrime_window_sandwich] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
