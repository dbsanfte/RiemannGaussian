import CheckAlpogeRepeatedAverage
import RiemannGaussian.AlpogeZetaPowerWindows
import RiemannGaussian.ZetaLowZeroIsolation
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MertensLogSum.PrimeLogOverPTop

/-! # The harmonic correction in the average over ordinary primes -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real AlpogeZetaSamples

/-- The excess over half the prime mass is bounded by the prime harmonic sum
and the endpoint correction for incomplete residue periods. -/
theorem mean_low_prime_upper (A W D : ℕ) (hW : 0 < W) (hD : 1 < D) :
    blockMean A W (fun M => lowPrimeSum M D) ≤
      Chebyshev.theta D/2 + log D/2 + D*Chebyshev.theta D/(8*W) := by
  let s := (Ioc 0 D).filter Nat.Prime
  have htheta : Chebyshev.theta D = ∑ p ∈ s, log p := by simp [Chebyshev.theta,s]
  have hpr (p : ℕ) (hp : p ∈ s) : p.Prime ∧ (p:ℝ) ≤ D :=
    ⟨(mem_filter.mp hp).2,by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).2⟩
  have hsum := PI.PrimeLogOverPWork.sum_log_div_prime_le D (by exact_mod_cast hD) s hpr
  have hpoint (p : ℕ) (hp : p ∈ s) :
      log p*(∑ j ∈ range W, weight (A+j) p) ≤
        log p*((W:ℝ)/2 + D/8) + (W/2)*(log p/p) := by
    obtain ⟨hprime,hpD⟩ := hpr p hp
    have hw := weight_block_identity A W hprime.pos
    have hb := (residue_bounds (A+W) hprime.pos).2
    have ha := (residue_bounds A hprime.pos).1
    have hl := Real.log_natCast_nonneg p
    have h : (∑ j ∈ range W, weight (A+j) p) ≤ W*(1/2+1/(2*(p:ℝ)))+D/8 := by linarith
    apply (mul_le_mul_of_nonneg_left h hl).trans_eq
    ring
  have hs := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum,← htheta] at hs
  have hWh : 0 ≤ (W:ℝ)/2 := by positivity
  have hw : (0:ℝ) < W := by exact_mod_cast hW
  unfold blockMean lowPrimeSum
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  apply (div_le_iff₀ hw).mpr
  apply hs.trans
  calc _ ≤ Chebyshev.theta D*((W:ℝ)/2+D/8)+(W/2)*log D :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hWh)
       _ = _ := by field_simp; ring

/-- An upper bound on the mean of the original samples transfers back to the prime
tail, with square-root, prime harmonic and residue endpoint errors shown separately. -/
theorem mean_tail_deficit_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N H D : ℕ, H < N → 1 < D → D ≤ N-H →
      Real.eulerMascheroniConstant*N - Chebyshev.theta D/2 -
        blockMean (N-H) (2*H+1) (fun M => upperPrimeSum M D) ≤
        blockMean (N-H) (2*H+1) (fun M => G M) +
        K*sqrt (N+H : ℕ) + log D/2 + D*Chebyshev.theta D/(8*(2*(H:ℝ)+1)) := by
  obtain ⟨K,hK⟩ := integer_sample_abs_error
  refine ⟨|K|,abs_nonneg _,fun N H D hH hD hcut => ?_⟩
  let A := N-H
  let W := 2*H+1
  have hW : 0 < W := by dsimp [W]; omega
  have hW' : (0:ℝ) < W := by exact_mod_cast hW
  have hw : (W:ℝ)=2*(H:ℝ)+1 := by dsimp [W]; push_cast; ring
  have hc := mean_center hH.le
  change (∑ j ∈ range W, ((A+j:ℕ):ℝ)) = _ at hc
  rw [← hw] at hc
  have hpoint (j : ℕ) (hj : j ∈ range W) :
      Real.eulerMascheroniConstant*(A+j : ℕ) ≤ G (A+j : ℕ)+lowPrimeSum (A+j) D+
        upperPrimeSum (A+j) D+|K| *sqrt (N+H : ℕ) := by
    have hmax : A+j ≤ N+H := by have hj' := mem_range.mp hj; dsimp [W,A] at *; omega
    have hmin : 1 ≤ A+j := by dsimp [A]; omega
    have hh := (abs_le.mp (hK _ hmin)).1
    rw [split_primeSum (D := D) (by dsimp [A]; omega)] at hh
    have he := mul_le_mul (le_abs_self K) (Real.sqrt_le_sqrt (by exact_mod_cast hmax :
      ((A+j : ℕ):ℝ) ≤ (N+H : ℕ))) (sqrt_nonneg _) (abs_nonneg _)
    linarith
  have hh := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum,hc,Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_add_distrib] at hh
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  have hmean : Real.eulerMascheroniConstant*N ≤ blockMean A W (fun M => G M)+
      blockMean A W (fun M => lowPrimeSum M D)+blockMean A W (fun M => upperPrimeSum M D)+
        |K| *sqrt (N+H : ℕ) := by
    unfold blockMean
    rw [← add_div,← add_div,← sub_le_iff_le_add,le_div_iff₀ hW']
    linarith only [hh]
  have hlow := mean_low_prime_upper A W D hW hD
  rw [hw] at hlow
  change _-_-blockMean A W (fun M => upperPrimeSum M D) ≤ blockMean A W (fun M => G M)+_+_+_
  linarith only [hmean,hlow]

/-- The largest integer whose square is at most n to the fifth. -/
def residueCutoff (n : ℕ) : ℕ := Nat.sqrt (n^5)

/-- The centered arithmetic deficit after replacing all the oscillating weights up to
the five-eighths power by one half of their ordinary prime mass. -/
def averagedDeficit (n : ℕ) : ℝ :=
  Real.eulerMascheroniConstant*(n:ℝ)^4-Chebyshev.theta (residueCutoff n)/2-
    blockMean (n^4-n^3) (2*n^3+1) (fun M => upperPrimeSum M (residueCutoff n))

private theorem cutoff_bounds {n : ℕ} (hn : 2 ≤ n) :
    1 < residueCutoff n ∧ residueCutoff n ≤ n^4-n^3 ∧ ((residueCutoff n:ℕ):ℝ)^2 ≤ (n:ℝ)^5 := by
  have hn1 : 1 ≤ n := by omega
  have hl : 2 ≤ Nat.sqrt (n^5) := Nat.le_sqrt.mpr (by nlinarith [Nat.pow_le_pow_left hn 5])
  have he := Nat.pow_le_pow_right hn1 (by decide : 5 ≤ 6)
  rw [show n^6 = (n^3)^2 by ring] at he
  have hu := Nat.sqrt_le_sqrt he
  rw [Nat.sqrt_eq'] at hu
  have hhalf : 2*n^3 ≤ n^4 := (Nat.mul_le_mul_right (n^3) hn).trans_eq (by ring)
  exact ⟨hl,by dsimp [residueCutoff]; omega,by exact_mod_cast Nat.sqrt_le' (n^5)⟩

/-- A square-root bound on the centered tail at all fourth powers suffices for RH. -/
theorem rh_of_averagedDeficit {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n : ℕ, 2 ≤ n → averagedDeficit n ≤ C*(n:ℝ)^2) : RiemannHypothesis := by
  apply Formalism.riemannHypothesis_of_zero_free_halfPlane
  apply zeta_ne_zero_of_fourth_G_upper (m := 2) (by decide) (B := 1/2) le_rfl (by norm_num) (C := C+(8+log 4)) (by positivity)
  intro n hn
  obtain ⟨_,hc,hs⟩ := cutoff_bounds hn
  have hh := G_fourth_le_mean_upper_primes hn hc hs
  change G _ ≤ averagedDeficit n+_ at hh
  rw [← Real.sqrt_eq_rpow, show sqrt ((n:ℝ)^4)=(n:ℝ)^2 by
    rw [show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]]
  linarith only [hh,h n hn]

/-- The zeta-only Landau implication with negative sign gives cofinal nonpositive
samples using the repository's verified critical-line zero. -/
private theorem cofinal_G_nonpositive (a : ℝ) : ∃ x ≥ a, G x ≤ 0 := by
  by_contra! h
  obtain ⟨z,_,hz,hre,_⟩ := ZetaLowZeroIsolation.isolated_critical_zero
  apply Formalism.zetaLandau (-1) (Or.inr rfl) (1/4) (by norm_num) (by norm_num) _ z (by rw [hre]; norm_num) hz
  refine ⟨0,max a 1,fun x hx => ?_⟩
  rw [zero_mul,← G_eq_archive (by linarith [le_max_right a (1:ℝ)])]
  linarith only [h x ((le_max_left _ _).trans hx)]

/-- Any all-height zero half-plane supplies its exact exponent for the centered tail
at every fourth-power sample. -/
theorem averagedDeficit_of_zero_bound {B : ℝ} (hB : 1/2 ≤ B) (hB1 : B < 1)
    (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → averagedDeficit n ≤ C*((n:ℝ)^4)^B := by
  obtain ⟨C,hC,hG⟩ := G_upper_of_cofinal_nonpositive (by linarith : 0 ≤ B) hB1 hz cofinal_G_nonpositive
  obtain ⟨K,hK,hmean⟩ := mean_tail_deficit_le
  refine ⟨2*C+2*K+2+(log 4+4),by positivity,fun n hn => ?_⟩
  obtain ⟨hd,hcut,hs⟩ := cutoff_bounds hn
  have hnR : 2 ≤ (n:ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n:ℝ) := by linarith
  have hH : n^3 < n^4 := Nat.pow_lt_pow_right (by omega) (by decide)
  have hH' : (n:ℝ)^3 ≤ (n:ℝ)^4 := by exact_mod_cast hH.le
  have hmax : ((n^4+n^3:ℕ):ℝ) ≤ 2*(n:ℝ)^4 := by push_cast; linarith
  have hN := one_le_pow₀ hn1 (n := 4)
  have hn0 : 0 < (n:ℝ) := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hN hB
  have hroot : sqrt ((n:ℝ)^4)=(n:ℝ)^2 := by
    rw [show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  rw [← Real.sqrt_eq_rpow,hroot] at hpow
  have h2 : (2:ℝ)^B ≤ 2 := (Real.rpow_le_rpow_of_exponent_le (by norm_num) hB1.le).trans_eq (Real.rpow_one _)
  have hg (j : ℕ) (hj : j ∈ range (2*n^3+1)) :
      G (n^4-n^3+j:ℕ) ≤ 2*C*((n:ℝ)^4)^B := by
    have hj' := mem_range.mp hj
    have hmin : 1 ≤ n^4-n^3+j := by omega
    have hi : n^4-n^3+j ≤ n^4+n^3 := by omega
    have hh := Real.rpow_le_rpow (Nat.cast_nonneg (α := ℝ) (n^4-n^3+j))
      ((show ((n^4-n^3+j:ℕ):ℝ) ≤ (n^4+n^3:ℕ) by exact_mod_cast hi).trans hmax) (by linarith : 0 ≤ B)
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hh
    apply (hG _ (by exact_mod_cast hmin)).trans
    have hp := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (pow_nonneg hn0.le 4) B)
    exact (mul_le_mul_of_nonneg_left (hh.trans hp) hC).trans_eq (by ring)
  have hsum := Finset.sum_le_sum hg
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  have hav : blockMean (n^4-n^3) (2*n^3+1) (fun M => G M) ≤ 2*C*((n:ℝ)^4)^B := by
    apply (div_le_iff₀ (by positivity)).mpr
    exact hsum.trans_eq (by ring)
  have hw := hmean (n^4) (n^3) _ hH hd hcut
  have hroot2 : sqrt ((n^4+n^3:ℕ):ℝ) ≤ 2*(n:ℝ)^2 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity,hmax.trans (by nlinarith [pow_nonneg hn0.le 4])⟩
  have hdR : (0:ℝ) < residueCutoff n := by exact_mod_cast (show 0 < residueCutoff n by omega)
  have hd4 : residueCutoff n ≤ n^4 := hcut.trans (Nat.sub_le _ _)
  have hlog := Real.log_le_log hdR (show (residueCutoff n:ℝ) ≤ (n:ℝ)^4 by exact_mod_cast hd4)
  rw [log_pow] at hlog
  have hl : log (residueCutoff n)/2 ≤ 2*(n:ℝ)^2 := by
    norm_num at hlog
    nlinarith only [hlog,log_le_sub_one_of_pos hn0,sq_nonneg ((n:ℝ)-1),hnR]
  push_cast at hw
  unfold averagedDeficit
  have hr := mul_le_mul_of_nonneg_left hroot2 hK
  push_cast at hr
  have he := fourth_endpoint_cost hs
  nlinarith only [hw,hav,hr,hl,he,mul_le_mul_of_nonneg_left hpow hK,hpow,
    mul_le_mul_of_nonneg_left hpow (show 0 ≤ log 4+4 by positivity)]

/-- The verified seven-eighths half-plane gives a uniform exponent for the arithmetic tail. -/
theorem averagedDeficit_seven_eighths :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → averagedDeficit n ≤ C*((n:ℝ)^4)^(7/8:ℝ) :=
  averagedDeficit_of_zero_bound (by norm_num) (by norm_num) suzukiLocalZero_re_le_seven_eighths

/-- RH is equivalent to one square-root bound on the averaged ordinary-prime deficit
with the exact half-mass of primes through the five-eighths power removed. -/
theorem rh_iff_averagedDeficit :
    RiemannHypothesis ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → averagedDeficit n ≤ C*(n:ℝ)^2 := by
  constructor
  · intro h
    obtain ⟨C,hC,hg⟩ := averagedDeficit_of_zero_bound (B := 1/2) le_rfl (by norm_num)
      (fun ρ => (h ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2).le)
    refine ⟨C,hC,fun n hn => ?_⟩
    simpa only [← Real.sqrt_eq_rpow, show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
      using hg n hn
  · rintro ⟨C,hC,h⟩
    exact rh_of_averagedDeficit hC h

private theorem repeated_low_upper {W D : ℕ} (hw : 0 < W) (hd : 1 < D) (k A : ℕ) :
    repeatedMean W k (fun M => lowPrimeSum M D) A ≤
      Chebyshev.theta D/2 + log D/2 + Chebyshev.theta D*((D:ℝ)/W)^k := by
  let s := (Ioc 0 D).filter Nat.Prime
  have htheta : Chebyshev.theta D = ∑ p ∈ s, log p := by simp [Chebyshev.theta,s]
  have he : (fun M => lowPrimeSum M D) = ∑ p ∈ s, (log p) • (fun M => weight M p) := by
    ext M
    simp [s,lowPrimeSum,Finset.sum_apply]
  have hpr (p : ℕ) (hp : p ∈ s) : p.Prime ∧ (p:ℝ) ≤ D :=
    ⟨(mem_filter.mp hp).2,by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).2⟩
  have hsum := PI.PrimeLogOverPWork.sum_log_div_prime_le D (by exact_mod_cast hd) s hpr
  have hp (p : ℕ) (h : p ∈ s) :
      log p*repeatedMean W k (fun M => weight M p) A ≤
        log p*(1/2+((D:ℝ)/W)^k)+(log p/p)/2 := by
    obtain ⟨hpp,hpD⟩ := hpr p h
    have hb := (abs_le.mp (repeated_weight_error hpp.pos hw k A)).2
    have hpow := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg W))
      (div_le_div_of_nonneg_right hpD (Nat.cast_nonneg W)) k
    have hh : repeatedMean W k (fun M => weight M p) A ≤ 1/2+((D:ℝ)/W)^k+1/(2*(p:ℝ)) := by linarith
    exact (mul_le_mul_of_nonneg_left hh (log_natCast_nonneg p)).trans_eq (by ring)
  rw [he,map_sum,Finset.sum_apply]
  simp only [map_smul,Pi.smul_apply,smul_eq_mul]
  have hh := Finset.sum_le_sum hp
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← htheta,← Finset.sum_div] at hh
  linarith only [hh,hsum]

/-- A zero half-plane controls the actual cubic-cutoff prime deficit at its exact
exponent. The reverse estimate has no factor from the number of averaging passes. -/
theorem cubic_tail_of_zero_bound {B : ℝ} (hB : 1/2 ≤ B) (hB1 : B < 1)
    (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 8 ≤ n →
      repeatedTailAt (Nat.log 2 n+1) n (n^3) ≤ C*((n:ℝ)^4)^B := by
  obtain ⟨C,hC,hG⟩ := G_upper_of_cofinal_nonpositive (by linarith : 0 ≤ B) hB1 hz cofinal_G_nonpositive
  obtain ⟨K,hK⟩ := integer_sample_abs_error
  let E := C+|K|
  have hE : 0 ≤ E := add_nonneg hC (abs_nonneg _)
  have hpoint (M : ℕ) (hm : 1 ≤ M) :
      eulerMascheroniConstant*M ≤ primeSum M+E*(M:ℝ)^B := by
    have hmR : 1 ≤ (M:ℝ) := by exact_mod_cast hm
    have hg := (abs_le.mp (hK M hm)).1
    have hroot := Real.rpow_le_rpow_of_exponent_le hmR hB
    rw [← Real.sqrt_eq_rpow] at hroot
    have hh := mul_le_mul (le_abs_self K) hroot (sqrt_nonneg _) (abs_nonneg _)
    dsimp only [E]
    linarith only [hg,hh,hG M hmR]
  refine ⟨2*E+2+(log 4+4),by positivity,fun n hn => ?_⟩
  let k := Nat.log 2 n+1
  let D := n^3
  let A := n^4-k*D
  let W := 2*D+1
  let L := repeatedMean W k
  obtain ⟨hk,hs⟩ := cubic_tail_parameters hn
  have hW : 0 < W := by dsimp [W]; omega
  have hnR : 8 ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have hN := one_le_pow₀ (show 1 ≤ (n:ℝ) by linarith) (n := 4)
  have hhalf : 2*(k*D) ≤ n^4 := by
    simpa only [D,← Nat.mul_assoc,show n^4=n*n^3 by ring] using Nat.mul_le_mul_right (n^3) hk
  have hD : 1 < D := by dsimp [D]; nlinarith [Nat.pow_le_pow_left hn 3]
  have hD2 : 2*D ≤ n^4 := (Nat.mul_le_mul_right D (by omega : 2 ≤ n)).trans_eq (by dsimp [D]; ring)
  have hcut : D ≤ A := by dsimp [A]; omega
  have hc : A+k*D=n^4 := by dsimp [A]; omega
  have hmax : A+k*(W-1) ≤ 2*n^4 := by
    dsimp [W]
    rw [show k*(2*D)=2*(k*D) by ring]
    omega
  have h2 : (2:ℝ)^B ≤ 2 := (rpow_le_rpow_of_exponent_le (by norm_num) hB1.le).trans_eq (rpow_one _)
  let U := 2*E*((n:ℝ)^4)^B
  have hh := @repeat_mono W k A (fun M => eulerMascheroniConstant*M)
    (fun M => lowPrimeSum M D+upperPrimeSum M D+U) (by
      intro M hm hr
      have hp := hpoint M (by omega)
      rw [split_primeSum (hcut.trans hm)] at hp
      have hmax' : (M:ℝ) ≤ 2*(n:ℝ)^4 := by exact_mod_cast hr.trans hmax
      have hb := Real.rpow_le_rpow (Nat.cast_nonneg M) hmax' (by linarith : 0 ≤ B)
      rw [Real.mul_rpow (by norm_num) (by positivity)] at hb
      have ht := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (pow_nonneg hn0.le 4) B)
      have he := mul_le_mul_of_nonneg_left (hb.trans ht) hE
      dsimp only [U]
      linarith only [hp,he])
  change L (eulerMascheroniConstant • (fun M : ℕ => (M:ℝ))) A ≤
    L ((fun M => lowPrimeSum M D)+(fun M => upperPrimeSum M D)+(fun _ => U)) A at hh
  simp only [map_smul,map_add,Pi.smul_apply,Pi.add_apply,smul_eq_mul] at hh
  have hlin : L (fun M : ℕ => (M:ℝ)) A=(n:ℝ)^4 :=
    (repeat_first_moment D k A).trans (by exact_mod_cast hc)
  rw [hlin,show L (fun _ => U) A=U from repeat_const hW k A U] at hh
  have hu := repeated_low_upper hW hD k A
  change L (fun M => lowPrimeSum M D) A ≤ _ at hu
  have he := repeated_endpoint_cost hs
  have he' : Chebyshev.theta D*((D:ℝ)/W)^k ≤ (log 4+4)*(n:ℝ)^2 := by
    dsimp only [D,W]
    push_cast
    simpa only [Nat.cast_pow] using he
  have hpow := Real.rpow_le_rpow_of_exponent_le hN hB
  have hroot : sqrt ((n:ℝ)^4)=(n:ℝ)^2 := by
    rw [show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  rw [← Real.sqrt_eq_rpow,hroot] at hpow
  have hlog : log D/2 ≤ 2*(n:ℝ)^2 := by
    dsimp only [D]
    rw [Nat.cast_pow,log_pow]
    norm_num
    nlinarith only [log_le_sub_one_of_pos hn0,hnR,sq_nonneg ((n:ℝ)-1)]
  change eulerMascheroniConstant*(n:ℝ)^4-Chebyshev.theta D/2-L (fun M => upperPrimeSum M D) A ≤ _
  dsimp only [U] at hh
  nlinarith only [hh,hu,he',hpow,hlog,mul_le_mul_of_nonneg_left hpow (show 0 ≤ log 4+4 by positivity)]

/-- The unconditional native exponent for the remaining ordinary-prime sum above n cubed. -/
theorem cubic_tail_seven_eighths :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 8 ≤ n →
      repeatedTailAt (Nat.log 2 n+1) n (n^3) ≤ C*((n:ℝ)^4)^(7/8:ℝ) :=
  cubic_tail_of_zero_bound (by norm_num) (by norm_num) suzukiLocalZero_re_le_seven_eighths

/-- RH is equivalent to one uniform square-root upper bound on the cubic-cutoff deficit. -/
theorem rh_iff_cubic_prime_tail : RiemannHypothesis ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 8 ≤ n →
      repeatedTailAt (Nat.log 2 n+1) n (n^3) ≤ C*(n:ℝ)^2 := by
  constructor
  · intro h
    obtain ⟨C,hC,hg⟩ := cubic_tail_of_zero_bound (B := 1/2) le_rfl (by norm_num)
      (fun ρ => (h ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2).le)
    refine ⟨C,hC,fun n hn => ?_⟩
    simpa only [← Real.sqrt_eq_rpow,show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
      using hg n hn
  · rintro ⟨C,hC,h⟩
    apply rh_of_cubic_prime_tail
    intro B hB _
    refine ⟨C,hC,fun n hn => (h n hn).trans (mul_le_mul_of_nonneg_left ?_ hC)⟩
    have h1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hp := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ h1 (n := 4)) hB.le
    simpa only [← Real.sqrt_eq_rpow,show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
      using hp

end
end RiemannGaussian.AlpogeMined


open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.mean_low_prime_upper,
      ``RiemannGaussian.AlpogeMined.mean_tail_deficit_le,
      ``RiemannGaussian.AlpogeMined.averagedDeficit_seven_eighths,
      ``RiemannGaussian.AlpogeMined.rh_iff_averagedDeficit,
      ``RiemannGaussian.AlpogeMined.cubic_tail_seven_eighths,
      ``RiemannGaussian.AlpogeMined.rh_iff_cubic_prime_tail] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
    logInfo m!"{decl} depends on {axioms}"
