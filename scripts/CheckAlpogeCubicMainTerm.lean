import CheckAlpogeCubicCrossingBound

/-! # Signed main term of the cubic arithmetic response

Keep the signs before clipping. A proportional cutoff in the quotient sum
lets the weak prime number theorem control the unscaled density.
-/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Filter Real MeasureTheory
open scoped Classical Topology ArithmeticFunction.vonMangoldt

private theorem psi_le_seven (n : ℕ) : Chebyshev.psi n ≤ 7*n := by
  have h := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α := ℝ) n)
  have h4 : log 4 ≤ 3 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith only [h4]) (Nat.cast_nonneg _))

/-- Shifting the cutoff changes only coefficients through the larger cutoff. -/
theorem mangoldtDiscrepancy_cutoff_loss {D B M : ℕ} (hD : 0 < D) (hDB : D ≤ B) (hBM : B ≤ M) :
    |weightedMangoldtDiscrepancy M D - weightedMangoldtDiscrepancy M B| ≤ 24*(B:ℝ) := by
  let f := fun p : ℕ => (1-Λ p)*weight M p
  have ha {X : ℕ} (hX : 0 < X) : |weight M X*((X:ℝ)-Chebyshev.psi X)| ≤ 8*X := by
    rw [abs_mul,abs_of_nonneg (weight_mem hX).1]
    have h := mul_le_mul_of_nonneg_right (weight_mem (N := M) hX).2 (abs_nonneg ((X:ℝ)-Chebyshev.psi X))
    have he := abs_sub (X:ℝ) (Chebyshev.psi X)
    rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) X),abs_of_nonneg (Chebyshev.psi_nonneg _)] at he
    linarith only [h,he,psi_le_seven X]
  have hsum : |∑ p ∈ Ioc D B, f p| ≤ 8*(B:ℝ) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ p ∈ Ioc D B, (1+Λ p) := by
        apply sum_le_sum
        intro p hp
        have hw := weight_mem (N := M) (hD.trans (mem_Ioc.mp hp).1)
        dsimp [f]
        rw [abs_mul,abs_of_nonneg hw.1]
        exact (mul_le_of_le_one_right (abs_nonneg _) hw.2).trans (by
          simpa only [abs_one,abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := p))]
            using abs_sub (1:ℝ) (Λ p))
      _ ≤ ∑ p ∈ Ioc 0 B, (1+Λ p) := sum_le_sum_of_subset_of_nonneg
        (Ioc_subset_Ioc_left (Nat.zero_le D)) (fun p _ _ => by positivity [ArithmeticFunction.vonMangoldt_nonneg (n := p)])
      _ ≤ _ := by
        rw [sum_add_distrib,show (∑ p ∈ Ioc 0 B, Λ p) = Chebyshev.psi B by simp [Chebyshev.psi]]
        simpa using (show (B:ℝ)+Chebyshev.psi B ≤ 8*B by linarith only [psi_le_seven B])
  have hsplit := sum_Ioc_consecutive f hDB hBM
  have hid : weightedMangoldtDiscrepancy M D - weightedMangoldtDiscrepancy M B =
      weight M D*((D:ℝ)-Chebyshev.psi D) + ∑ p ∈ Ioc D B, f p -
        weight M B*((B:ℝ)-Chebyshev.psi B) := by
    unfold weightedMangoldtDiscrepancy
    dsimp only [f] at *
    linarith only [hsplit]
  rw [hid]
  apply (abs_sub _ _).trans
  linarith only [abs_add_le (weight M D*((D:ℝ)-Chebyshev.psi D)) (∑ p ∈ Ioc D B, f p),
    ha hD,ha (hD.trans_le hDB),hsum,show (D:ℝ) ≤ B by exact_mod_cast hDB]

/-- Only the uniform relative error of the signed prefix above B enters.
The factor M/B is bounded for any fixed proportional cutoff. -/
theorem mangoldtDiscrepancy_high {M B : ℕ} (hB : 0 < B) (hBM : B ≤ M)
    {s : ℝ} (hs : 0 ≤ s)
    (hc : ∀ x ∈ Set.Icc (B:ℝ) M, |(⌊x⌋₊:ℝ)-Chebyshev.psi x| ≤ s*x) :
    |weightedMangoldtDiscrepancy M B| ≤ 2*s*((M:ℝ)/B)*M := by
  let e := fun x : ℝ => (⌊x⌋₊:ℝ)-Chebyshev.psi x
  have bpos : 0 < (B:ℝ) := Nat.cast_pos.mpr hB
  have bm : (B:ℝ) ≤ M := by exact_mod_cast hBM
  have hsum : |∑ j ∈ Icc 1 (M/B), e ((M:ℝ)/j)| ≤ ((M:ℝ)/B)*(s*M) := by
    apply (abs_sum_le_sum_abs _ _).trans
    have hrow (j : ℕ) (hj : j ∈ Icc 1 (M/B)) : |e ((M:ℝ)/j)| ≤ s*M := by
      obtain ⟨hj1,hjM⟩ := mem_Icc.mp hj
      have hjR : 1 ≤ (j:ℝ) := by exact_mod_cast hj1
      have hlo : (B:ℝ) ≤ (M:ℝ)/j := (le_div_iff₀ (zero_lt_one.trans_le hjR)).mpr
        (by exact_mod_cast (show B*j ≤ M by simpa [mul_comm] using (Nat.le_div_iff_mul_le hB).mp hjM))
      have hhi : (M:ℝ)/j ≤ M := div_le_self (Nat.cast_nonneg _) hjR
      exact (hc _ ⟨hlo,hhi⟩).trans (mul_le_mul_of_nonneg_left hhi hs)
    apply (sum_le_sum hrow).trans
    simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
    exact mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)
  have hi : |∫ x in (B:ℝ)..(M:ℝ), e x/x^2| ≤ (s/B)*(M:ℝ) := by
    have h : ‖∫ x in (B:ℝ)..(M:ℝ), e x/x^2‖ ≤ (s/B)*|(M:ℝ)-B| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Set.uIoc_of_le bm] at hx
      have hx0 := bpos.trans hx.1
      rw [Real.norm_eq_abs,abs_div,abs_of_pos (pow_pos hx0 2)]
      apply (div_le_div_of_nonneg_right (hc x ⟨hx.1.le,hx.2⟩) (sq_nonneg x)).trans
      rw [show s*x/x^2 = s/x by field_simp]
      exact div_le_div_of_nonneg_left hs bpos hx.1.le
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr bm)] at h
    exact h.trans (mul_le_mul_of_nonneg_left (sub_le_self _ (Nat.cast_nonneg _)) (by positivity))
  rw [← mangoldtDiscrepancy_quadrature hB hBM]
  change |(∑ j ∈ Icc 1 (M/B), e ((M:ℝ)/j)) - (M:ℝ)*(∫ x in (B:ℝ)..(M:ℝ), e x/x^2)| ≤ _
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) M)]
  have h := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg (α := ℝ) M)
  exact (add_le_add hsum h).trans_eq (by ring)

private theorem signedPrefix_relative {s : ℝ} (hs : 0 < s) :
    ∃ T : ℕ, ∀ x : ℝ, T ≤ x → |(⌊x⌋₊:ℝ)-Chebyshev.psi x| ≤ s*x := by
  have hfloor : Tendsto (fun x : ℝ => (⌊x⌋₊:ℝ)/x) atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one (eventually_ne_atTop (0:ℝ))).mp
      Asymptotics.isEquivalent_nat_floor
  have he := (hfloor.sub cubicPsi_div_tendsto_one).abs
  simp only [sub_self,abs_zero] at he
  obtain ⟨A,hA⟩ := eventually_atTop.mp (he.eventually (gt_mem_nhds hs))
  refine ⟨max 1 ⌈A⌉₊,fun x hx => ?_⟩
  have hx0 : 0 < x := (by exact_mod_cast (show 0 < max 1 ⌈A⌉₊ by omega) : (0:ℝ) < max 1 ⌈A⌉₊).trans_le hx
  have h := hA x ((Nat.le_ceil A).trans ((by exact_mod_cast le_max_right 1 ⌈A⌉₊ : (⌈A⌉₊:ℝ) ≤ max 1 ⌈A⌉₊).trans hx))
  change |(⌊x⌋₊:ℝ)/x-Chebyshev.psi x/x| < s at h
  rw [← sub_div,abs_div,abs_of_pos hx0] at h
  exact (div_le_iff₀ hx0).mp h.le

/-- Uniform in the cutoff D. First choose a fixed proportional boundary, then
apply the weak prime number theorem above it and charge the short prefix. -/
theorem mangoldtDiscrepancy_relative {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ M ≥ N, ∀ D, 0 < D → D ≤ M →
      |weightedMangoldtDiscrepancy M D| ≤ ε*M := by
  let K := max 2 ⌈96/ε⌉₊
  have hK : 2 ≤ K := le_max_left _ _
  have hKR : 0 < (K:ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hpay : 96 ≤ ε*(K:ℝ) := by
    have hh := (Nat.le_ceil (96/ε)).trans
      (show (⌈96/ε⌉₊:ℝ) ≤ K by exact_mod_cast le_max_right 2 ⌈96/ε⌉₊)
    linarith only [(div_le_iff₀ hε).mp hh]
  let s := ε/(4*K)
  have hs : 0 < s := by dsimp [s]; positivity
  obtain ⟨T,hT⟩ := signedPrefix_relative hs
  refine ⟨K*(T+1),fun M hM D hD hDM => ?_⟩
  have hKM : K ≤ M := (Nat.le_mul_of_pos_right _ (Nat.succ_pos T)).trans hM
  let U := M/K+1
  let B := max D U
  have hu0 : 0 < U := Nat.succ_pos _
  have hUM : U ≤ M := Nat.succ_le_of_lt (Nat.div_lt_self (by omega : 0 < M) (by omega : 1 < K))
  have hBM : B ≤ M := max_le hDM hUM
  have hB : 0 < B := hD.trans_le (le_max_left _ _)
  have hsmall : |weightedMangoldtDiscrepancy M D-weightedMangoldtDiscrepancy M B| ≤ 24*(U:ℝ) := by
    by_cases hd : D ≤ U
    · simpa [B,max_eq_right hd] using mangoldtDiscrepancy_cutoff_loss hD hd hUM
    · simp [B,max_eq_left (le_of_not_ge hd)]
  have hTU : T ≤ U := by
    have := (Nat.le_div_iff_mul_le (by omega : 0 < K)).mpr ((Nat.mul_comm (T+1) K).le.trans hM)
    dsimp [U]
    omega
  have htail := mangoldtDiscrepancy_high hB hBM hs.le (fun x hx =>
    hT x ((show (T:ℝ) ≤ B by exact_mod_cast hTU.trans (le_max_right D U)).trans hx.1))
  have hratio : (M:ℝ)/B ≤ K := (div_le_iff₀ (Nat.cast_pos.mpr hB)).mpr (by
    exact_mod_cast ((Nat.lt_mul_div_succ M (by omega : 0<K)).le.trans (Nat.mul_le_mul_left K (le_max_right D U))))
  have hlow : (U:ℝ) ≤ 2*((M:ℝ)/K) := by
    have hq := Nat.cast_div_le (m := M) (n := K) (α := ℝ)
    have h1 : 1 ≤ (M:ℝ)/K := (one_le_div hKR).mpr (by exact_mod_cast hKM)
    dsimp [U]; push_cast; linarith only [h1,hq]
  have hlow' : 24*(U:ℝ) ≤ (ε/2)*M := by
    have hh := mul_le_mul_of_nonneg_right hpay (div_nonneg (Nat.cast_nonneg (α := ℝ) M) hKR.le)
    rw [mul_assoc,show (K:ℝ)*(M/K) = M by field_simp] at hh
    linarith only [hlow,hh]
  have hup := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hs.le)) (Nat.cast_nonneg (α := ℝ) M)
  have hscale : 2*s*K = ε/2 := by dsimp [s]; field_simp; ring
  rw [hscale] at hup
  have hadd := abs_add_le (weightedMangoldtDiscrepancy M D-weightedMangoldtDiscrepancy M B)
    (weightedMangoldtDiscrepancy M B)
  rw [sub_add_cancel] at hadd
  linarith only [hadd,hsmall,hlow',htail,hup]

theorem cubicMangoldtTail_relative {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, |cubicMangoldtTail n| ≤ ε*(n:ℝ)^4 := by
  obtain ⟨N,hN⟩ := mangoldtDiscrepancy_relative hε
  refine ⟨max 8 N,fun n hn => ?_⟩
  have h8 : 8 ≤ n := by omega
  have hD : n^3 ≤ cubicSampleStart n := by
    have hk := (cubic_tail_parameters h8).1
    change n^3 ≤ n^4-(Nat.log 2 n+1)*n^3
    rw [show n^4=n*n^3 by ring,← Nat.sub_mul]
    exact Nat.le_mul_of_pos_left _ (by omega)
  let f := fun M => weightedMangoldtDiscrepancy M (n^3)
  let g : ℕ → ℝ := ε • fun M : ℕ => (M:ℝ)
  have h (M : ℕ) (hm : cubicSampleStart n ≤ M) : -g M ≤ f M ∧ f M ≤ g M :=
    abs_le.mp (hN M ((((show N ≤ n by omega).trans (Nat.le_self_pow (by decide : 3≠0) n)).trans hD).trans hm)
      _ (by positivity : 0 < n^3) (hD.trans hm))
  have hlo := cubicMean_le_on (f := -g) (g := f) h8 (fun M hm _ => (h M hm).1)
  have hhi := cubicMean_le_on (f := f) (g := g) h8 (fun M hm _ => (h M hm).2)
  have hg : cubicMean n g = ε*(n:ℝ)^4 := by
    dsimp only [g]; rw [map_smul,cubicMean_first_moment h8,smul_eq_mul]
  rw [map_neg,hg] at hlo
  rw [hg] at hhi
  exact abs_le.mpr ⟨hlo,hhi⟩

/-- The signed deficit before taking its positive part on the window. -/
def cubicArithmeticDeficit (n : ℕ) : ℝ :=
  cubicSmoothMoments n - cubicWeightedResponse n (cubicThreeFactorCoefficient n)

private theorem head_response_bounds {n : ℕ} (hn : 8 ≤ n) :
    let H := cubicMean n (fun M => weightedCoefficient M (n^3) (ZetaVaughanReduction.head n Λ))
    0 ≤ H ∧ H ≤ 7*n := by
  let H := fun M => weightedCoefficient M (n^3) (ZetaVaughanReduction.head n Λ)
  have hD : 0 < n^3 := by positivity
  have hnD := Nat.le_self_pow (by decide : 3 ≠ 0) n
  have hp : coefficientPrefix (ZetaVaughanReduction.head n Λ) (n^3:ℕ) = Chebyshev.psi n := by
    rw [coefficientPrefix,Nat.floor_natCast,Chebyshev.psi_eq_sum_Icc,Nat.floor_natCast]
    change (∑ t ∈ Icc 0 (n^3), if t ≤ n then Λ t else 0) = _
    rw [← sum_filter]
    congr 1
    ext t
    simp only [mem_filter,mem_Icc]
    omega
  have he (M : ℕ) : H M = weight M (n^3)*Chebyshev.psi n := by
    change weight M (n^3)*coefficientPrefix _ _ + _ = _
    rw [hp]
    have hz : (∑ p ∈ Ioc (n^3) M, (ZetaVaughanReduction.head n Λ) p*weight M p) = 0 :=
      sum_eq_zero (fun p h => by simp [ZetaVaughanReduction.head,not_le.mpr (hnD.trans_lt (mem_Ioc.mp h).1)])
    rw [hz,add_zero]
  have hl (M : ℕ) : 0 ≤ H M := by rw [he]; exact mul_nonneg (weight_mem hD).1 (Chebyshev.psi_nonneg _)
  have hu (M : ℕ) : H M ≤ 7*n := by
    rw [he]
    exact (mul_le_of_le_one_left (Chebyshev.psi_nonneg _) (weight_mem hD).2).trans (psi_le_seven n)
  have h := cubicMean_le_on (f := fun _ => 0) hn (fun M _ _ => hl M)
  have h' := cubicMean_le_on (g := fun _ => 7*(n:ℝ)) hn (fun M _ _ => hu M)
  rw [cubicMean_const] at h h'
  exact ⟨h,h'⟩

/-- Two-sided sample error. The small Mangoldt head is retained when
comparing the cubic sieve with the original signed Mangoldt discrepancy. -/
theorem cubicArithmeticDeficit_mangoldt_error {n : ℕ} (hn : 8 ≤ n) :
    |cubicArithmeticDeficit n - cubicMangoldtTail n| ≤
      (264*21^4+500:ℝ)*(n:ℝ)^2*((Nat.log 2 n+1:ℕ):ℝ)^2 := by
  let k := Nat.log 2 n+1
  let B := (n:ℝ)^2*(k:ℝ)^2
  have hk : 1 ≤ (k:ℝ) := by exact_mod_cast (show 1 ≤ k by dsimp [k]; omega)
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 := zero_lt_one.trans_le hn1
  have hln : log n ≤ (k:ℝ) := cubicLog_le_depth (by omega : 0<n)
  have hk0 : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hk2 : 1 ≤ (k:ℝ)^2 := one_le_pow₀ hk
  have hB : (n:ℝ)^2 ≤ B := le_mul_of_one_le_right (by positivity) hk2
  have hnk : (n:ℝ)^2*k ≤ B := mul_le_mul_of_nonneg_left
    (by nlinarith only [mul_le_mul_of_nonneg_left hk hk0] : (k:ℝ) ≤ (k:ℝ)^2) (by positivity)
  have hlog {a d : ℕ} (ha : 0 < a) : log ((a:ℝ)*(n:ℝ)^d) ≤ (a-1:ℝ) + (d:ℝ)*k := by
    rw [log_mul (by exact_mod_cast ha.ne') (pow_ne_zero _ hn0.ne'),log_pow]
    gcongr
    exact log_le_sub_one_of_pos (by exact_mod_cast ha)
  have hs : |averagedSmallDivisorLogError n| ≤ 24*B := by
    have hh := hlog (d := 4) (by decide : 0 < 2)
    norm_num1 at hh
    have hl : 1+log (2*(n:ℝ)^4) ≤ 6*k := by linarith only [hh,hk]
    have hb := mul_le_mul_of_nonneg_left hl (show 0 ≤ 4*(n:ℝ)^2 by positivity)
    linarith only [averagedSmallDivisorLogError_bound hn,hb,hnk]
  have hx : |averagedCubicCrossError n| ≤ 217*B := by
    have h4 : log 4 + 4 ≤ 7 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
    have hl : 27+3*(k:ℝ)+log n ≤ 31*k := by linarith only [hk,hln]
    have hh := mul_le_mul (mul_le_mul_of_nonneg_right h4 (sq_nonneg (n:ℝ))) hl
      (by positivity [log_natCast_nonneg n]) (by positivity)
    have hb := averagedCubicCrossError_bound hn
    change _ ≤ (log 4+4)*(n:ℝ)^2*(27+3*(k:ℝ)+log n) at hb
    linarith only [hb,hh,hnk]
  have hp : |cubicVaughanResidual n - cubicProductResidual n| ≤ 180*B := by
    have hh := hlog (d := 3) (by decide : 0 < 3)
    norm_num1 at hh
    have hpos := log_nonneg (show (1:ℝ) ≤ 3*(n:ℝ)^3 by nlinarith only [one_le_pow₀ hn1 (n := 3)])
    have hpair := mul_le_mul (by linarith only [hh,hk] : log (3*(n:ℝ)^3) ≤ 5*k)
      (by linarith only [hh,hk] : 1+log (3*(n:ℝ)^3) ≤ 6*k) (by linarith only [hpos]) (by positivity)
    have hb := mul_le_mul_of_nonneg_left hpair (show 0 ≤ 6*(n:ℝ)^2 by positivity)
    rw [cubicVaughanResidual_sub_product hn,abs_sub_comm]
    dsimp [B]
    linarith only [cubicProductResponse_error hn,hb]
  have hr : |cubicWeightedResponse n (cubicRoughCoefficient n)-cubicProductResponse n| ≤ 64*B := by
    have hh := pow_le_pow_left₀ (by positivity [log_natCast_nonneg n] : 0 ≤ 1+log n)
      (show 1+log n ≤ 2*(k:ℝ) by linarith only [hk,hln]) 2
    have hb := mul_le_mul_of_nonneg_left hh (show 0 ≤ 16*(n:ℝ)^2 by positivity)
    dsimp [B]
    linarith only [cubicRoughCoefficient_response_error hn,hb]
  have hf : |cubicWeightedResponse n (cubicRoughCoefficient n) -
      cubicWeightedResponse n (cubicThreeFactorCoefficient n)| ≤ (264*21^4:ℝ)*B := by
    have h := (div_le_iff₀ (pow_pos hn0 3)).mp (fourFactorResponse_normalized hn)
    have he : (n:ℝ)^(-(3/2):ℝ)*(n:ℝ)^3 ≤ (n:ℝ)^2 := by
      calc
        _ = (n:ℝ)^(-(3/2:ℝ)+(3:ℕ)) := by rw [rpow_add hn0,rpow_natCast]
        _ ≤ (n:ℝ)^((2:ℕ):ℝ) := rpow_le_rpow_of_exponent_le hn1 (by norm_num)
        _ = _ := rpow_natCast _ _
    linarith only [h,mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 264*21^4),hB]
  obtain ⟨hhead0,hhead⟩ := head_response_bounds hn
  have hhead' : (7:ℝ)*n ≤ 7*B := mul_le_mul_of_nonneg_left
    ((by nlinarith only [mul_le_mul_of_nonneg_right hn1 hn0.le] : (n:ℝ) ≤ (n:ℝ)^2).trans hB) (by norm_num)
  have hv := cubicMangoldtTail_signed hn
  have hu := (averagedCubicUnitError_bound hn).trans hB
  obtain ⟨s1,s2⟩ := abs_le.mp hs
  obtain ⟨x1,x2⟩ := abs_le.mp hx
  obtain ⟨p1,p2⟩ := abs_le.mp hp
  obtain ⟨r1,r2⟩ := abs_le.mp hr
  obtain ⟨f1,f2⟩ := abs_le.mp hf
  obtain ⟨u1,u2⟩ := abs_le.mp hu
  unfold cubicProductResidual at p1 p2
  unfold cubicArithmeticDeficit
  change |_ - _| ≤ (264*21^4+500:ℝ)*(n:ℝ)^2*(k:ℝ)^2
  rw [mul_assoc]
  change |_ - _| ≤ (264*21^4+500:ℝ)*B
  apply abs_le.mpr
  constructor <;> linarith only [hv,hhead0,hhead,hhead',s1,s2,x1,x2,p1,p2,r1,r2,f1,f2,u1,u2,
    show 0 ≤ B by dsimp [B]; positivity]

/-- The sieve and the Mangoldt model agree sample by sample to an error
of precisely the size of the allowance in the positive-mass criterion. -/
theorem cubicArithmeticDeficit_quadratic_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n ≥ 8, |cubicArithmeticDeficit n-cubicMangoldtTail n| ≤
      K*(n:ℝ)^2*(1+log n)^2 := by
  let A : ℝ := 264*21^4+500
  refine ⟨4*A,by dsimp [A]; positivity,fun n hn => ?_⟩
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg _) (cubic_depth_le_twice_log (by omega : 0<n)) 2
  have hd := mul_le_mul_of_nonneg_left hh (show 0 ≤ A*(n:ℝ)^2 by dsimp [A]; positivity)
  exact (cubicArithmeticDeficit_mangoldt_error hn).trans (hd.trans_eq (by ring))

private theorem depthAllowance_relative {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, C*(n:ℝ)^2*((Nat.log 2 n+1:ℕ):ℝ)^2 ≤ ε*(n:ℝ)^4 := by
  obtain ⟨N,h⟩ := cubicDepth_power_eventually 2 (C := C/ε) (by positivity) (by norm_num : (0:ℝ)<2)
  refine ⟨N,fun n hn => ?_⟩
  have he := h n hn
  rw [show (2:ℝ)=((2:ℕ):ℝ) by norm_num,rpow_natCast] at he
  let k : ℝ := ((Nat.log 2 n+1:ℕ):ℝ)
  have hx := mul_le_mul_of_nonneg_left he hε.le
  change ε*(C/ε*k^2) ≤ _ at hx
  rw [← mul_assoc,mul_div_cancel₀ _ hε.ne'] at hx
  have hh := mul_le_mul_of_nonneg_right hx (sq_nonneg (n:ℝ))
  change C*(n:ℝ)^2*k^2 ≤ _
  linarith only [hh]

/-- The raw signed deficit has zero quartic main term, uniformly in n. -/
theorem cubicArithmeticDeficit_relative {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, |cubicArithmeticDeficit n| ≤ ε*(n:ℝ)^4 := by
  obtain ⟨T,hT⟩ := cubicMangoldtTail_relative (half_pos hε)
  obtain ⟨A,hA⟩ := depthAllowance_relative (by norm_num : (0:ℝ) ≤ 264*21^4+500) (half_pos hε)
  refine ⟨max 8 (max T A),fun n hn => ?_⟩
  have hh := abs_add_le (cubicArithmeticDeficit n-cubicMangoldtTail n) (cubicMangoldtTail n)
  rw [sub_add_cancel] at hh
  linarith only [hh,(cubicArithmeticDeficit_mangoldt_error (by omega : 8 ≤ n)).trans (hA n (by omega)),hT n (by omega)]

/-- The mass obtained by replacing the exact signed payments by one constant
quartic margin and keeping the usual quadratic allowance. -/
def cubicFixedMarginMassOn (response : ℕ → ℝ) (κ C : ℝ) (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (cubicSmoothMoments n - response n - κ*(n:ℝ)^4 -
    C*(n:ℝ)^2*(1+log n)^2) 0/(n:ℝ)^3

private theorem fixedMargin_obstruction {response : ℕ → ℝ} {κ κ' C : ℝ}
    (hC : 0 ≤ C) (hκ : κ < κ')
    (h : ∃ N : ℕ, ∀ n ≥ N, response n + κ'*(n:ℝ)^4 ≤
      cubicWeightedResponse n (cubicThreeFactorCoefficient n)) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ b ≥ m, (m:ℝ)^(1/2:ℝ) < cubicFixedMarginMassOn response κ C m b := by
  let η := (κ'-κ)/3
  have hη : 0 < η := div_pos (sub_pos.mpr hκ) (by norm_num)
  obtain ⟨A,hA⟩ := h
  obtain ⟨B,hB⟩ := cubicArithmeticDeficit_relative hη
  obtain ⟨D,hD⟩ := depthAllowance_relative (mul_nonneg (by norm_num : (0:ℝ)≤4) hC) hη
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).comp tendsto_natCast_atTop_atTop
  obtain ⟨T,hT⟩ := eventually_atTop.mp (ht.eventually_gt_atTop η⁻¹)
  refine ⟨max 1 (max A (max B (max D T))),fun m hm b hb => ?_⟩
  have hm0 : 0 < m := by omega
  have hmR : 0 < (m:ℝ) := Nat.cast_pos.mpr hm0
  have hneg := (abs_le.mp (hB m (by omega))).1
  unfold cubicArithmeticDeficit at hneg
  have hbudget : C*(m:ℝ)^2*(1+log m)^2 ≤ η*(m:ℝ)^4 := by
    have hk : 1 ≤ ((Nat.log 2 m+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos (Nat.log 2 m)
    have hh := pow_le_pow_left₀ (by positivity [log_natCast_nonneg m] : 0 ≤ 1+log m)
      (by linarith only [cubicLog_le_depth hm0,hk] : 1+log m ≤ 2*((Nat.log 2 m+1:ℕ):ℝ)) 2
    have hs := mul_le_mul_of_nonneg_left hh (mul_nonneg hC (sq_nonneg (m:ℝ)))
    linarith only [hs,hD m (by omega)]
  have hrow : η*(m:ℝ)^4 ≤ cubicSmoothMoments m-response m-κ*(m:ℝ)^4-C*(m:ℝ)^2*(1+log m)^2 := by
    dsimp only [η] at hbudget hneg ⊢
    linarith only [hneg,hA m (by omega),hbudget]
  have hlow : η*(m:ℝ) ≤ cubicFixedMarginMassOn response κ C m b := by
    apply le_trans _ (single_le_sum (s := Icc m b) (f := fun n : ℕ =>
      max (cubicSmoothMoments n-response n-κ*(n:ℝ)^4-C*(n:ℝ)^2*(1+log n)^2) 0/(n:ℝ)^3)
      (fun n _ => div_nonneg (le_max_right _ _) (by positivity)) (mem_Icc.mpr ⟨le_rfl,hb⟩))
    exact (le_div_iff₀ (pow_pos hmR 3)).mpr ((by ring : η*(m:ℝ)*m^3 = η*m^4).le.trans
      (hrow.trans (le_max_left _ _)))
  have hgt := hT m (by omega)
  change η⁻¹ < (m:ℝ)^(1/2:ℝ) at hgt
  have h1 : 1 < η*(m:ℝ)^(1/2:ℝ) := by simpa [hη.ne'] using mul_lt_mul_of_pos_left hgt hη
  have h2 := mul_lt_mul_of_pos_right h1 (rpow_pos_of_pos hmR (1/2:ℝ))
  rw [one_mul,mul_assoc,← rpow_add hmR,show (1/2:ℝ)+1/2=1 by norm_num,rpow_one] at h2
  exact h2.trans_le hlow

/-- Even a singleton eventually violates the half-power bound with the
previously priced flat margin at the central sample. -/
theorem roughRangeCentral_fixedMargin_obstruction {κ C : ℝ} (hκ : κ < 1/200000) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ b ≥ m, (m:ℝ)^(1/2:ℝ) <
      cubicFixedMarginMassOn roughRangeCentralResponse κ C m b := by
  let κ' := (κ+1/200000)/2
  exact fixedMargin_obstruction hC (show κ < κ' by dsimp [κ']; linarith only [hκ])
    (roughRangeCentral_quartic_margin_sharp (by dsimp [κ']; linarith only [hκ]))

/-- The flat-margin premise of rh_of_cubicUnpairedMargin_powerWindows fails
at α=1/2, even when its separate moving semiprime surplus is retained. -/
theorem cubicUnpaired_fixedMargin_obstruction {C : ℝ} (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ b ≥ m, (m:ℝ)^(1/2:ℝ) <
      cubicFixedMarginMassOn (fun n => cubicWeightedResponse n (cubicUnpairedCoefficient n) +
        movingSemiprimeSurplus n) (3/655360) C m b := by
  apply fixedMargin_obstruction hC (by norm_num : (3/655360:ℝ) < 1/200000)
  obtain ⟨N,hN⟩ := cubicUnpairedResponse_quartic_margin_sharp
  refine ⟨max 8 N,fun n hn => ?_⟩
  linarith only [hN n (by omega),cubicCompensatedResponse_eq (by omega : 8 ≤ n)]

theorem roughRangeMassOn_as_deficit {m b : ℕ} (hm : 64 ≤ m) (C : ℝ) :
    roughRangeMassOn C m b = ∑ n ∈ Icc m b, max
      (cubicArithmeticDeficit n-C*(n:ℝ)^2*(1+log n)^2) 0/(n:ℝ)^3 := by
  rw [roughRangeMassOn_eq hm]
  apply sum_congr rfl
  intro n hn
  rw [sub_sub _ (cubicWeightedResponse n (cubicCompensatedCoefficient n)),
    cubicCompensatedResponse_eq (by have := (mem_Icc.mp hn).1; omega : 8 ≤ n)]
  rfl

/-- Enlarging the allowance by a fixed constant transfers the positive mass
in either direction on the very same window, with no additive window loss. -/
theorem roughRangeMassOn_mangoldt_sandwich :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C : ℝ) {m b : ℕ}, 64 ≤ m →
      roughRangeMassOn (C+K) m b ≤ cubicMangoldtExcessOn C m b ∧
      cubicMangoldtExcessOn (C+K) m b ≤ roughRangeMassOn C m b := by
  obtain ⟨K,hK,h⟩ := cubicArithmeticDeficit_quadratic_error
  refine ⟨K,hK,fun C {m b} hm => ?_⟩
  rw [roughRangeMassOn_as_deficit hm,roughRangeMassOn_as_deficit hm]
  constructor <;> apply sum_le_sum <;> intro n hn <;> apply div_le_div_of_nonneg_right _ (by positivity) <;>
    apply max_le_max_right <;> have hw := abs_le.mp (h n (by have := (mem_Icc.mp hn).1; omega)) <;>
    linarith only [hw.1,hw.2]

private theorem subpowerWindows_mono_late {F H : ℕ → ℕ → ℝ}
    (he : ∀ {m b : ℕ}, 64 ≤ m → F m b ≤ H m b)
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, H m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, F m (powerWindowEnd δ m) ≤ (m:ℝ)^α := by
  intro α hα
  obtain ⟨δ,hδ,h1,hw⟩ := h α hα
  refine ⟨δ,hδ,h1,fun A => ?_⟩
  obtain ⟨m,hm,hb⟩ := hw (max 64 A)
  exact ⟨m,by omega,(he (by omega : 64 ≤ m)).trans hb⟩

/-- The exact open sieve condition and the direct signed Mangoldt condition
are equivalent after existentially quantifying the quadratic allowance. -/
theorem roughRange_powerWindows_iff_mangoldt :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, roughRangeMassOn C m (powerWindowEnd δ m) ≤ (m:ℝ)^α) ↔
    (∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, cubicMangoldtExcessOn C m (powerWindowEnd δ m) ≤ (m:ℝ)^α) := by
  obtain ⟨K,hK,h⟩ := roughRangeMassOn_mangoldt_sandwich
  constructor <;> rintro ⟨C,hC,hw⟩ <;> refine ⟨C+K,add_nonneg hC hK,subpowerWindows_mono_late ?_ hw⟩
  · exact fun hm => (h C hm).2
  · exact fun hm => (h C hm).1

theorem cubicUnpaired_flatMargin_powerWindows_false {C : ℝ} (hC : 0 ≤ C) :
    ¬ (∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ A : ℕ, ∃ m ≥ A,
      (∑ n ∈ Icc m (powerWindowEnd δ m), max
        (cubicSmoothMoments n - cubicWeightedResponse n (cubicUnpairedCoefficient n) -
          (3/655360:ℝ)*(n:ℝ)^4 - movingSemiprimeSurplus n - C*(n:ℝ)^2*(1+log n)^2) 0/(n:ℝ)^3)
        ≤ (m:ℝ)^α) := by
  intro h
  obtain ⟨N,hN⟩ := cubicUnpaired_fixedMargin_obstruction hC
  obtain ⟨δ,hδ,hδ1,hw⟩ := h (1/2) (by norm_num)
  obtain ⟨m,hm,hb⟩ := hw (max 1 N)
  have hg := hN m (by omega) _ (powerWindowEnd_bounds (by omega : 1 ≤ m) hδ.le hδ1).1
  apply (not_le.mpr hg)
  apply le_trans (le_of_eq ?_) hb
  unfold cubicFixedMarginMassOn
  apply sum_congr rfl
  intro n _
  ring_nf

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.mangoldtDiscrepancy_cutoff_loss,
      ``RiemannGaussian.AlpogeMined.mangoldtDiscrepancy_high,
      ``RiemannGaussian.AlpogeMined.mangoldtDiscrepancy_relative,
      ``RiemannGaussian.AlpogeMined.cubicMangoldtTail_relative,
      ``RiemannGaussian.AlpogeMined.cubicArithmeticDeficit_quadratic_error,
      ``RiemannGaussian.AlpogeMined.cubicArithmeticDeficit_relative,
      ``RiemannGaussian.AlpogeMined.roughRangeCentral_fixedMargin_obstruction,
      ``RiemannGaussian.AlpogeMined.cubicUnpaired_flatMargin_powerWindows_false,
      ``RiemannGaussian.AlpogeMined.roughRangeMassOn_mangoldt_sandwich,
      ``RiemannGaussian.AlpogeMined.roughRange_powerWindows_iff_mangoldt,
      ``RiemannGaussian.AlpogeMined.rh_of_cubicMangoldtExcessOn_powerWindows] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
