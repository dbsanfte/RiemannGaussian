/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSquarefreeSeparatedMean

/-!
# Linear cutoff cost for the retained signed prime sum

The signed Gram decay of sharp Möbius prefixes is integrated with the exact
positive finite-Abel weights of the Riesz hinge difference. Their logarithmic
row mass is uniformly bounded, giving a linear displacement cost for every
squarefree cofactor population. Both signed inequalities retain arbitrary
correlated weights, and the terminal theorem applies to the original finite
prime fibre. Its weight energy remains explicit; no whole source floor or
ceiling is inferred.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ArithmeticFunction.Moebius Classical
namespace RiemannGaussian.ZetaRieszLinearCutoffMean

/-- The upper half of the logarithmic separation row has a numerical integral bound. -/
theorem upper_logarithmic_row (K M : ℕ) (hK : 0 < K) (hKM : K ≤ M) :
    (∑ n ∈ Finset.Icc K M, 1/((n : ℝ)*(4+Real.log ((n : ℝ)/K))^2)) ≤ 2 := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKM' : (K : ℝ) ≤ M := by exact_mod_cast hKM
  let H := fun t : ℝ => 4+Real.log t-Real.log K
  let f := fun t : ℝ => t⁻¹*(H t^2)⁻¹
  let F := fun t : ℝ => -(H t)⁻¹
  have hH t (ht : t ∈ Set.Icc (K : ℝ) M) : 4 ≤ H t := by
    have hl := Real.log_le_log hK0 ht.1
    dsimp [H]
    linarith
  have hder t (ht : t ∈ Set.Icc (K : ℝ) M) :
      HasDerivAt f (-(H t+2)/(t^2*H t^3)) t := by
    have ht0 : 0 < t := hK0.trans_le ht.1
    have hHt : 0 < H t := by linarith [hH t ht]
    have hh : HasDerivAt H t⁻¹ t := by
      simpa only [H,zero_add,sub_zero] using!
        ((hasDerivAt_const t 4).add (Real.hasDerivAt_log ht0.ne')).sub_const (Real.log K)
    have hd := ((hasDerivAt_id t).inv ht0.ne').mul ((hh.pow 2).inv (pow_ne_zero 2 hHt.ne'))
    apply hd.congr_deriv
    dsimp only [Pi.inv_apply,Pi.pow_apply,id_eq]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
    change -1/t^2*(H t^2)⁻¹+t⁻¹*(-(2*H t*t⁻¹)/(H t^2)^2) = _
    field_simp [ht0.ne',hHt.ne']
    ring
  have hc : ContinuousOn f (Set.Icc (K : ℝ) M) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hanti : AntitoneOn f (Set.Icc (K : ℝ) M) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hc
    · intro t ht
      exact (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hder t (interior_subset ht)).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hH t (interior_subset ht)])
        (mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith [hH t (interior_subset ht)]) _))
  have hprim t (ht : t ∈ Set.Icc (K : ℝ) M) : HasDerivAt F (f t) t := by
    have ht0 : 0 < t := hK0.trans_le ht.1
    have hHt : 0 < H t := by linarith [hH t ht]
    have hh : HasDerivAt H t⁻¹ t := by
      simpa only [H,zero_add,sub_zero] using!
        ((hasDerivAt_const t 4).add (Real.hasDerivAt_log ht0.ne')).sub_const (Real.log K)
    have hd := (hh.inv hHt.ne').neg
    apply hd.congr_deriv
    dsimp only [f,Pi.inv_apply,Pi.pow_apply]
    field_simp [ht0.ne',hHt.ne']
  have hint : IntervalIntegrable f volume K M := hc.intervalIntegrable_of_Icc hKM'
  have hi : (∫ t in (K : ℝ)..M, f t) = F M-F K :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hprim t
      (by simpa only [Set.uIcc_of_le hKM'] using ht)) hint
  have hFM : F M ≤ 0 := by
    dsimp [F]
    have hp : 0 ≤ (H M)⁻¹ := inv_nonneg.mpr (by linarith [hH M ⟨hKM',le_rfl⟩])
    linarith
  have hFK : F K = -(1/4 : ℝ) := by norm_num [F,H]
  have hfK : f K ≤ 1 := by
    dsimp only [f,H]
    have hk : (K : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hK0).mpr hK1
    norm_num
    nlinarith
  have hsum := AntitoneOn.sum_le_integral_Ico (f := f) (a := K) (b := M) hKM hanti
  rw [Finset.sum_Ico_add' (fun n : ℕ => f n) K M 1] at hsum
  have hset : Finset.Ico (K+1) (M+1) = Finset.Icc (K+1) M := by
    ext n
    simp only [Finset.mem_Ico,Finset.mem_Icc]
    omega
  rw [hset] at hsum
  have he : Finset.Icc K M = insert K (Finset.Icc (K+1) M) := by
    ext n
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hs : (∑ n ∈ Finset.Icc K M, f n) ≤ 2 := by
    rw [he,Finset.sum_insert (by simp)]
    linarith only [hsum,hi,hFM,hFK,hfK]
  convert hs using 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (0 : ℝ) < n := hK0.trans_le (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
  dsimp [f,H]
  rw [Real.log_div hn0.ne' hK0.ne',show 4+(Real.log n-Real.log K) =
    4+Real.log n-Real.log K by ring]
  simp only [one_div,mul_inv_rev]
  ring

/-- Both halves of the logarithmic separation row have total cost at most four. -/
theorem logarithmic_row (K M : ℕ) (hK : 0 < K) :
    (∑ n ∈ Finset.Icc 1 M,
      1/((n : ℝ)*(4+|Real.log K-Real.log n|)^2)) ≤ 4 := by
  let f := fun n : ℕ => 1/((n : ℝ)*(4+|Real.log K-Real.log n|)^2)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hlo (T : ℕ) (hTK : T ≤ K) : (∑ n ∈ Finset.Icc 1 T, f n) ≤ 2 := by
    have hs := ZetaRieszCrossCutoff.logarithmic_square_row_sum_le_two T hK0
      (by exact_mod_cast hTK)
    convert hs using 1
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnK : (n : ℝ) ≤ K := by exact_mod_cast (Finset.mem_Icc.mp hn).2.trans hTK
    dsimp [f]
    rw [Real.log_div hK0.ne' hn0.ne',abs_of_nonneg (sub_nonneg.mpr
      (Real.log_le_log hn0 hnK))]
  by_cases hKM : K ≤ M
  · have hhi : (∑ n ∈ Finset.Icc K M, f n) ≤ 2 := by
      have hs := upper_logarithmic_row K M hK hKM
      convert hs using 1
      apply Finset.sum_congr rfl
      intro n hn
      have hnK : (K : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hn0 := hK0.trans_le hnK
      dsimp [f]
      rw [Real.log_div hn0.ne' hK0.ne',abs_of_nonpos (sub_nonpos.mpr
        (Real.log_le_log hK0 hnK))]
      congr 3
      ring
    have hset : (Finset.Icc 1 M).filter (fun n => n ≤ K) = Finset.Icc 1 K := by
      ext n
      simp only [Finset.mem_filter,Finset.mem_Icc]
      omega
    have hsub : (Finset.Icc 1 M).filter (fun n => ¬n ≤ K) ⊆ Finset.Icc K M := by
      intro n hn
      simp only [Finset.mem_filter,Finset.mem_Icc] at hn ⊢
      omega
    have hpart := Finset.sum_filter_add_sum_filter_not (s := Finset.Icc 1 M)
      (p := fun n => n ≤ K) (f := f)
    rw [hset] at hpart
    have hbound := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n hn _ => by dsimp [f]; positivity : ∀ n ∈ Finset.Icc K M,
        n ∉ (Finset.Icc 1 M).filter (fun n => ¬n ≤ K) → 0 ≤ f n)
    change (∑ n ∈ Finset.Icc 1 M, f n) ≤ 4
    linarith only [hpart,hbound,hlo K le_rfl,hhi]
  · exact (hlo M (by omega)).trans (by norm_num)

/-- Positive logarithmic weights exploit the entire signed Gram row before
estimating its size. The numerical row cost is independent of the cutoff. -/
theorem positive_weighted_gram_mean (I T : Finset ℕ) (R : ℕ)
    (b : ℕ → ℝ) (f : ℕ → ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hI : I ⊆ Finset.Icc 1 R)
    (hb : ∀ k ∈ I, 0 ≤ b k) (hbhi : ∀ k ∈ I, b k ≤ 1/(k : ℝ))
    (hpair : ∀ i ∈ I, ∀ j ∈ I,
      |∑ n ∈ T, f i n*f j n| ≤ C/(4+|Real.log i-Real.log j|)^2) :
    (∑ n ∈ T, (∑ i ∈ I, b i*f i n)^2) ≤ 4*C*(∑ i ∈ I, b i) := by
  let G := fun i j => ∑ n ∈ T, f i n*f j n
  have hrows i (hi : i ∈ I) :
      (∑ j ∈ I, b j/(4+|Real.log i-Real.log j|)^2) ≤ 4 := by
    calc
      _ ≤ ∑ j ∈ I, 1/((j : ℝ)*(4+|Real.log i-Real.log j|)^2) := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          _ ≤ (1/(j : ℝ))/(4+|Real.log i-Real.log j|)^2 :=
            div_le_div_of_nonneg_right (hbhi j hj) (sq_nonneg _)
          _ = _ := by rw [div_div]
      _ ≤ ∑ j ∈ Finset.Icc 1 R,
          1/((j : ℝ)*(4+|Real.log i-Real.log j|)^2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hI (fun j _ _ => by positivity)
      _ ≤ 4 := logarithmic_row i R (Finset.mem_Icc.mp (hI hi)).1
  have he : (∑ n ∈ T, (∑ i ∈ I, b i*f i n)^2) =
      ∑ i ∈ I, ∑ j ∈ I, b i*b j*G i j := by
    calc
      _ = ∑ n ∈ T, ∑ i ∈ I, ∑ j ∈ I, (b i*f i n)*(b j*f j n) := by
        simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        rw [Finset.sum_comm]
      _ = ∑ i ∈ I, ∑ j ∈ I, ∑ n ∈ T, (b i*f i n)*(b j*f j n) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        simp only [G,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro n _
        ring
  rw [he]
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ I, b i*b j*(C/(4+|Real.log i-Real.log j|)^2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left ((le_abs_self (G i j)).trans (hpair i hi j hj))
        (mul_nonneg (hb i hi) (hb j hj))
    _ = ∑ i ∈ I, b i*C*(∑ j ∈ I, b j/(4+|Real.log i-Real.log j|)^2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ i ∈ I, b i*C*4 :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hrows i hi)
        (mul_nonneg (hb i hi) hC))
    _ = _ := by rw [← Finset.sum_mul,← Finset.sum_mul]; ring

/-- A logarithmically Lipschitz mixture of all sharp cutoffs pays linear
mixture mass, uniformly beyond and below the square-root transition. -/
theorem exists_log_weighted_mean :
    ∃ E : ℝ, 0 < E ∧ ∀ (X R : ℕ) (S : Finset ℕ) (b : ℕ → ℝ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∀ i ∈ Finset.Icc 1 R, 0 ≤ b i) →
      (∀ i ∈ Finset.Icc 1 R, b i ≤ 1/(i : ℝ)) →
      (∑ n ∈ S,
        (∑ i ∈ Finset.Icc 1 R, b i*(∑ d ∈ Finset.Icc 1 i,
          if d ∣ n then (μ d : ℝ) else 0))^2) ≤
      E*X*(∑ i ∈ Finset.Icc 1 R, b i) := by
  obtain ⟨C,hC,hsmall⟩ := ZetaRieszSquarefreeSeparatedMean.exists_small_gram_bound
  obtain ⟨D,hD,hlarge⟩ := ZetaRieszSquarefreeSeparatedMean.exists_large_gram_bound
  refine ⟨8*(C+D),by linarith,fun X R S b hS hSF hb hbhi => ?_⟩
  let I := Finset.Icc 1 R
  let U := I.filter (fun i => i^2 ≤ X)
  let V := I.filter (fun i => ¬i^2 ≤ X)
  have hU : U ⊆ I := Finset.filter_subset _ _
  have hV : V ⊆ I := Finset.filter_subset _ _
  have hSI : S ⊆ Finset.Icc 1 X := by
    intro n hn
    have h := Finset.mem_Ioc.mp (hS hn)
    exact Finset.mem_Icc.mpr ⟨by omega,h.2⟩
  have hEU : (∑ i ∈ U, b i) ≤ ∑ i ∈ I, b i :=
    Finset.sum_le_sum_of_subset_of_nonneg hU (fun i hi _ => hb i hi)
  have hEV : (∑ i ∈ V, b i) ≤ ∑ i ∈ I, b i :=
    Finset.sum_le_sum_of_subset_of_nonneg hV (fun i hi _ => hb i hi)
  have hs := positive_weighted_gram_mean U (Finset.Icc 1 X) R b
    (fun i n => ∑ d ∈ Finset.Icc 1 i, if d ∣ n then (μ d : ℝ) else 0)
    (C := C*X) (by positivity) hU (fun i hi => hb i (hU hi))
    (fun i hi => hbhi i (hU hi))
    (fun i hi j hj => hsmall X i j (Finset.mem_Icc.mp (hU hi)).1
      (Finset.mem_Icc.mp (hU hj)).1 (Finset.mem_filter.mp hi).2
      (Finset.mem_filter.mp hj).2)
  have hl := positive_weighted_gram_mean V (Finset.Icc 1 X) R b
    (fun i n => ∑ d ∈ Finset.Icc 1 ((n-1)/i), if d ∣ n then (μ d : ℝ) else 0)
    (C := D*X) (by positivity) hV (fun i hi => hb i (hV hi))
    (fun i hi => hbhi i (hV hi))
    (fun i hi j hj => hlarge X i j (Finset.mem_Icc.mp (hV hi)).1
      (Finset.mem_Icc.mp (hV hj)).1
      (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hi).2))
      (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hj).2)))
  simp only [← mul_assoc] at hs hl
  have hsmallS : (∑ n ∈ S,
      (∑ i ∈ U, b i*(∑ d ∈ Finset.Icc 1 i, if d ∣ n then (μ d : ℝ) else 0))^2) ≤
      4*C*X*(∑ i ∈ I, b i) :=
    ((Finset.sum_le_sum_of_subset_of_nonneg hSI (fun _ _ _ => sq_nonneg _)).trans hs).trans
      (mul_le_mul_of_nonneg_left hEU (by positivity))
  have href n (hn : n ∈ S) :
      (∑ i ∈ V, b i*(∑ d ∈ Finset.Icc 1 i, if d ∣ n then (μ d : ℝ) else 0))^2 =
      (∑ i ∈ V, b i*(∑ d ∈ Finset.Icc 1 ((n-1)/i), if d ∣ n then (μ d : ℝ) else 0))^2 := by
    have he : (∑ i ∈ V, b i*(∑ d ∈ Finset.Icc 1 i, if d ∣ n then (μ d : ℝ) else 0)) =
        -(μ n : ℝ)*(∑ i ∈ V, b i*(∑ d ∈ Finset.Icc 1 ((n-1)/i), if d ∣ n then (μ d : ℝ) else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [ZetaRieszSquarefreeDualMean.sharp_reflection (hSF n hn)
        (by have := (Finset.mem_Ioc.mp (hS hn)).1; omega) ((Finset.mem_Icc.mp (hV hi)).1)]
      ring
    have hm : (μ n : ℝ)^2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hSF n hn)
    rw [he,mul_pow,neg_sq,hm,one_mul]
  have hlargeS : (∑ n ∈ S,
      (∑ i ∈ V, b i*(∑ d ∈ Finset.Icc 1 i, if d ∣ n then (μ d : ℝ) else 0))^2) ≤
      4*D*X*(∑ i ∈ I, b i) := by
    rw [Finset.sum_congr rfl href]
    exact ((Finset.sum_le_sum_of_subset_of_nonneg hSI (fun _ _ _ => sq_nonneg _)).trans hl).trans
      (mul_le_mul_of_nonneg_left hEV (by positivity))
  have hp n :
      (∑ i ∈ I, b i*(∑ d ∈ Finset.Icc 1 i, if d ∣ n then (μ d : ℝ) else 0))^2 ≤
      2*(∑ i ∈ U, b i*(∑ d ∈ Finset.Icc 1 i, if d ∣ n then (μ d : ℝ) else 0))^2+
      2*(∑ i ∈ V, b i*(∑ d ∈ Finset.Icc 1 i, if d ∣ n then (μ d : ℝ) else 0))^2 := by
    have he := Finset.sum_filter_add_sum_filter_not I (fun i => i^2 ≤ X)
      (fun i => b i*(∑ d ∈ Finset.Icc 1 i, if d ∣ n then (μ d : ℝ) else 0))
    change (∑ i ∈ U, _)+(∑ i ∈ V, _) = _ at he
    rw [← he]
    nlinarith only [sq_nonneg ((∑ i ∈ U, b i*(∑ d ∈ Finset.Icc 1 i, if d ∣ n then (μ d : ℝ) else 0))-
      (∑ i ∈ V, b i*(∑ d ∈ Finset.Icc 1 i, if d ∣ n then (μ d : ℝ) else 0)))]
  have ht := Finset.sum_le_sum (fun n (_ : n ∈ S) => hp n)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at ht
  nlinarith only [ht,hsmallS,hlargeS]

/-- Finite Abel summation transfers the improved all-cutoff Gram estimate
without replacing the signed divisor sum by its absolute values. -/
theorem exists_monotone_log_weight_mean :
    ∃ E : ℝ, 0 < E ∧ ∀ (X R : ℕ) (S : Finset ℕ) (f : ℕ → ℝ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) → 0 < R → f (R+1)=0 →
      (∀ k ∈ Finset.Icc 1 R, f (k+1) ≤ f k) →
      (∀ k ∈ Finset.Icc 1 R, f k-f (k+1) ≤ 1/(k : ℝ)) →
      (∑ n ∈ S, (∑ d ∈ Finset.Icc 1 R,
        f d*(if d ∣ n then (μ d : ℝ) else 0))^2) ≤ E*X*f 1 := by
  obtain ⟨E,hE,hmean⟩ := exists_log_weighted_mean
  refine ⟨E,hE,fun X R S f hS hSF hR hend hmono hstep => ?_⟩
  let z := fun n d => if d ∣ n then (μ d : ℝ) else 0
  let b := fun k => f k-f (k+1)
  have hb k (hk : k ∈ Finset.Icc 1 R) : 0 ≤ b k := sub_nonneg.mpr (hmono k hk)
  have htail d (hd : d ≤ R+1) : (∑ k ∈ Finset.Icc d R, b k) = f d := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    calc
      _ = -(∑ k ∈ Finset.Ico d (R+1), (f (k+1)-f k)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro k _
        dsimp [b]
        ring
      _ = f d := by rw [Finset.sum_Ico_sub f hd,hend]; ring
  have htotal : (∑ k ∈ Finset.Icc 1 R, b k) = f 1 := htail 1 (by omega)
  have he n : (∑ d ∈ Finset.Icc 1 R, f d*z n d) =
      ∑ k ∈ Finset.Icc 1 R, b k*(∑ d ∈ Finset.Icc 1 k, z n d) := by
    calc
      _ = ∑ d ∈ Finset.Icc 1 R, ∑ k ∈ Finset.Icc d R, b k*z n d := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [← Finset.sum_mul,htail d (by have := (Finset.mem_Icc.mp hd).2; omega)]
      _ = _ := by
        have h := Finset.sum_Ico_Ico_comm 1 (R+1) (fun d k => b k*z n d)
        simp only [Finset.Ico_add_one_right_eq_Icc,← Finset.mul_sum] at h
        exact h

  have hm := hmean X R S b hS hSF hb hstep
  rw [htotal] at hm
  simpa only [he,z] using hm

private theorem hinge_difference_eq_min {A B t : ℝ} (hAB : A ≤ B) :
    max 0 (B-t)-max 0 (A-t) = min (B-A) (max 0 (B-t)) := by
  simp only [min_def,max_def]
  split_ifs <;> linarith

/-- The exact Riesz cutoff-difference mean is linear in the displacement,
with one constant for every cutoff and every squarefree prime count. -/
theorem exists_linear_riesz_difference_mean_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ (X : ℕ) (S : Finset ℕ) (A B : ℝ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) → A ≤ B →
      (∑ n ∈ S, (VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n)^2) ≤
        E*X*(B-A) := by
  obtain ⟨E,hE,hmean⟩ := exists_monotone_log_weight_mean
  refine ⟨E,hE,fun X S A B hS hSF hAB => ?_⟩
  obtain ⟨R,hR⟩ := exists_nat_gt (max 1 (Real.exp B))
  have hR0 : 0 < R := by
    have h := (le_max_left (1 : ℝ) (Real.exp B)).trans_lt hR
    exact_mod_cast (by linarith : (0 : ℝ) < R)
  have hhi : Real.exp B < R+1 := by
    have h := (le_max_right (1 : ℝ) (Real.exp B)).trans_lt hR
    linarith
  let f := fun d : ℕ => max 0 (B-Real.log d)-max 0 (A-Real.log d)
  have hend : f (R+1) = 0 := by
    have hlog : B < Real.log (R+1 : ℕ) := by
      simpa only [Real.log_exp,Nat.cast_add,Nat.cast_one] using
        Real.log_lt_log (Real.exp_pos B) hhi
    dsimp [f]
    rw [max_eq_left (by linarith : B-Real.log (R+1 : ℕ) ≤ 0),
      max_eq_left (by linarith : A-Real.log (R+1 : ℕ) ≤ 0)]
    ring
  have hmono k (hk : k ∈ Finset.Icc 1 R) : f (k+1) ≤ f k := by
    dsimp only [f]
    rw [hinge_difference_eq_min hAB,hinge_difference_eq_min hAB]
    apply min_le_min_left
    apply max_le_max_left
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    exact sub_le_sub_left (Real.log_le_log hk0 (by norm_cast; omega)) B
  have hstep k (hk : k ∈ Finset.Icc 1 R) : f k-f (k+1) ≤ 1/(k : ℝ) := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hk1 : (0 : ℝ) < (k+1 : ℕ) := by positivity
    have hlogs : Real.log (k : ℝ) ≤ Real.log (k+1 : ℕ) :=
      Real.log_le_log hk0 (by norm_cast; omega)
    have hf : f k-f (k+1) ≤ Real.log (k+1 : ℕ)-Real.log k := by
      dsimp only [f]
      simp only [max_def]
      split_ifs <;> linarith
    have hl := Real.log_le_sub_one_of_pos (div_pos hk1 hk0)
    rw [Real.log_div hk1.ne' hk0.ne'] at hl
    have he : ((k+1 : ℕ) : ℝ)/(k : ℝ)-1 = 1/(k : ℝ) := by
      push_cast
      field_simp
      ring
    rw [he] at hl
    exact hf.trans hl
  have hm := hmean X R S f hS hSF hR0 hend hmono hstep
  have he n (hn : n ∈ S) :
      VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n =
        ∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (μ d : ℝ) else 0) :=
    ZetaRieszCutoffMean.riesz_difference_eq_prefix R hAB hhi
      (by have := (Finset.mem_Ioc.mp (hS hn)).1; omega)
  have hf : f 1 ≤ B-A := by
    dsimp only [f]
    rw [hinge_difference_eq_min hAB]
    exact min_le_left _ _
  calc
    _ = ∑ n ∈ S, (∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (μ d : ℝ) else 0))^2 :=
      Finset.sum_congr rfl (fun n hn => by rw [he n hn])
    _ ≤ E*X*f 1 := hm
    _ ≤ _ := mul_le_mul_of_nonneg_left hf (by positivity)

/-- The smaller quadratic/linear cutoff budget applies to every squarefree
subset; neither the physical cutoff nor the prime count enters the constant. -/
theorem exists_min_riesz_difference_mean_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ (X : ℕ) (S : Finset ℕ) (A B : ℝ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) → A ≤ B →
      (∑ n ∈ S, (VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n)^2) ≤
        E*X*min ((B-A)^2) (B-A) := by
  obtain ⟨C,hC,hfirst⟩ := exists_linear_riesz_difference_mean_bound
  obtain ⟨D,hD,hsecond⟩ := ZetaRieszSquarefreeUniformMean.exists_riesz_difference_mean_bound
  refine ⟨C+D,by linarith,fun X S A B hS hSF hAB => ?_⟩
  have hx : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hdelta : 0 ≤ B-A := sub_nonneg.mpr hAB
  have hlin := hfirst X S A B hS hSF hAB
  have hquad := hsecond X S A B hS hSF hAB
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ (C+D)*(X : ℝ))]
  apply le_min
  · nlinarith only [hquad,mul_nonneg (mul_nonneg hC.le hx) (sq_nonneg (B-A))]
  · nlinarith only [hlin,mul_nonneg (mul_nonneg hD.le hx) hdelta]

/-- Both sides of the retained signed sum inherit the smaller cutoff cost;
the common weight remains completely correlated with each literal label. -/
theorem exists_joint_difference_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) (A B : ℝ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) → A ≤ B →
      let J := ∑ n ∈ S, w n*(VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n);
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*(E*X*min ((B-A)^2) (B-A)));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_min_riesz_difference_mean_bound
  refine ⟨E,hE,fun X S w A B hS hSF hAB => ?_⟩
  dsimp only
  have hw : 0 ≤ ∑ n ∈ S, (w n)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hd : 0 ≤ B-A := sub_nonneg.mpr hAB
  have hs := (Finset.sum_mul_sq_le_sq_mul_sq S w
    (fun n => VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n)).trans
      (mul_le_mul_of_nonneg_left (hmean X S A B hS hSF hAB) hw)
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs,Real.sq_sqrt (by positivity)]
  exact hs

/-- The improved logarithmic cost is applied to the original finite
prime fibre with all original factorial, phase, allocation and support weights. -/
theorem exists_literal_prime_fibre_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X N p : ℕ) (A S : Finset ℕ) (L y : ℝ),
      S ⊆ Finset.Ioc 1 X →
      (∀ a ∈ S, Squarefree a ∧ 2 ≤ a.primeFactors.card) →
      p.Prime → (∀ a ∈ S, ¬p ∣ a) →
      let K := Real.sqrt ((∑ a ∈ S,
        (ZetaRieszGlobalPrimePeriod.signedPrimeWeight A L N y a p/a)^2)*
        (E*X*min ((Real.log p)^2) (Real.log p)));
      let J := (∑ a ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re;
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_joint_difference_bounds
  refine ⟨E,hE,fun X N p A S L y hS hSF hp hpd => ?_⟩
  let g := fun a => ZetaRieszGlobalPrimePeriod.signedPrimeWeight A L N y a p/a
  let w := fun a => -(μ a : ℝ)*g a
  have he a (ha : a ∈ S) :
      (ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re =
      w a*(VaughanLogAverage.riesz L a-VaughanLogAverage.riesz (L-Real.log p) a) := by
    rw [ZetaRieszGlobalPrimePeriod.re_residual_atom
      (hSF a ha).1 (hSF a ha).2 hp (hpd a ha) A L y N,
      ZetaRieszSquarefreeDualMean.response_reflection L (Real.log p) (hSF a ha).1
        (by have := (Finset.mem_Ioc.mp (hS ha)).1; omega)
        (by intro h; have hc := (hSF a ha).2; rw [h.primeFactors] at hc; simp at hc)]
    dsimp [w,g]
    ring
  have hw : (∑ a ∈ S, (w a)^2) = ∑ a ∈ S, (g a)^2 := by
    apply Finset.sum_congr rfl
    intro a ha
    have hm : (μ a : ℝ)^2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hSF a ha).1
    dsimp [w]
    rw [mul_pow,neg_sq,hm,one_mul]
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hb := hbound X S w (L-Real.log p) L hS
    (fun a ha => (hSF a ha).1) (by linarith)
  dsimp only at hb ⊢
  rw [hw,show L-(L-Real.log p) = Real.log p by ring] at hb
  rw [Complex.re_sum,Finset.sum_congr rfl he]
  exact hb

end RiemannGaussian.ZetaRieszLinearCutoffMean
