/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeTailEnergy
import RiemannGaussian.FiniteAbelVariation

/-!
# Actual varying prime amplitudes in the joint Riesz energy

The amplitude is retained inside each signed prime tail. Complete-period
cancellation and its partial tails pay its variation together with the
original two Riesz hinges, before the squarefree mean is applied.
-/

noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszWeightedPrimeTail
open ZetaRieszPrimeTailEnergy

private theorem real_abel (f z : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range (N+1), f i*z i) =
      f N*(∑ i ∈ Finset.range (N+1), z i)+
        ∑ i ∈ Finset.range N, (f i-f (i+1))*(∑ k ∈ Finset.range (i+1), z k) := by
  have h := FiniteAbelVariation.weighted_sum_eq (fun i => (f i : ℂ))
    (fun i => (z i : ℂ)) N
  exact_mod_cast h

/-- The complete moment and partial tails pay distinct numerical costs.
This retains the full-period cancellation for a nonconstant amplitude. -/
theorem weighted_bound (f z : ℕ → ℝ) (N : ℕ) {W V B C : ℝ}
    (hW : |f N| ≤ W) (hV : (∑ i ∈ Finset.range N, |f i-f (i+1)|) ≤ V)
    (hB : ∀ k < N, |∑ i ∈ Finset.range (k+1), z i| ≤ B)
    (hC : |∑ i ∈ Finset.range (N+1), z i| ≤ C) (hB0 : 0 ≤ B) :
    |∑ i ∈ Finset.range (N+1), f i*z i| ≤ W*C+V*B := by
  rw [real_abel]
  apply (abs_add_le _ _).trans
  apply (add_le_add (show |f N*(∑ i ∈ Finset.range (N+1), z i)| ≤ W*C from ?_)
    (show |∑ i ∈ Finset.range N, (f i-f (i+1))*(∑ k ∈ Finset.range (i+1), z k)| ≤ V*B from ?_))
  · rw [abs_mul]
    exact mul_le_mul hW hC (abs_nonneg _) ((abs_nonneg _).trans hW)
  · calc
      _ ≤ ∑ i ∈ Finset.range N, |(f i-f (i+1))*(∑ k ∈ Finset.range (i+1), z k)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range N, |f i-f (i+1)| *B := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hB i (Finset.mem_range.mp hi)) (abs_nonneg _)
      _ ≤ V*B := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hV hB0

private theorem prefix_eq (a b : ℝ) (c : ℕ → ℝ) {M : ℕ} (hM : M ≤ ⌊Real.exp b⌋₊) :
    (∑ n ∈ Finset.range (M+1),
      if n ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).filter Nat.Prime then c n else 0) =
      ∑ n ∈ (Finset.Ioc ⌊Real.exp a⌋₊ M).filter Nat.Prime, c n := by
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ioc]
  constructor
  · rintro ⟨hn,⟨⟨ha,_⟩,hp⟩⟩
    exact ⟨⟨ha,by omega⟩,hp⟩
  · rintro ⟨⟨ha,hn⟩,hp⟩
    exact ⟨by omega,⟨⟨ha,hn.trans hM⟩,hp⟩⟩

private theorem prefix_cosine_bound {a b y : ℝ} (ha : 5000 ≤ a)
    (hy : 54 ≤ |y|) (hlen : b-a ≤ 2*Real.pi/|y|) (c : ℝ)
    {M : ℕ} (hM : M ≤ ⌊Real.exp b⌋₊) :
    |∑ n ∈ (Finset.Ioc ⌊Real.exp a⌋₊ M).filter Nat.Prime,
      Real.cos (y*(Real.log n+c))/(n : ℝ)| ≤ 2/(|y| *a)+4/a^2 := by
  have ha0 : 0 < a := by linarith
  have hy0 : 0 < |y| := by linarith
  by_cases hMa : M ≤ ⌊Real.exp a⌋₊
  · rw [Finset.Ioc_eq_empty_of_le hMa,Finset.filter_empty,Finset.sum_empty,abs_zero]
    positivity
  · have hMa' : ⌊Real.exp a⌋₊ < M := lt_of_not_ge hMa
    have hM0 : (0 : ℝ) < M := (Real.exp_pos a).trans (Nat.lt_of_floor_lt hMa')
    have haM : a ≤ Real.log M := (Real.lt_log_iff_exp_lt hM0).mpr (Nat.lt_of_floor_lt hMa') |>.le
    have hMb : Real.log M ≤ b := (Real.log_le_iff_le_exp hM0).mpr
      ((by exact_mod_cast hM : (M : ℝ) ≤ ⌊Real.exp b⌋₊).trans (Nat.floor_le (Real.exp_pos b).le))
    have he : ⌊Real.exp (Real.log M)⌋₊ = M := by rw [Real.exp_log hM0]; exact Nat.floor_natCast M
    have h := clipped_cosine_bound ha haM hy (by linarith : Real.log M-a ≤ 2*Real.pi/|y|) c
    simpa only [he] using h

private theorem clamped_log_mem {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {k : ℕ} (hk : k ≤ ⌊Real.exp b⌋₊) : max a (Real.log k) ∈ Set.Icc a b := by
  refine ⟨le_max_left _ _,max_le hab ?_⟩
  by_cases h : k=0
  · subst k; simpa using ha.trans hab
  · have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero h
    apply (Real.log_le_iff_le_exp hk0).mpr
    exact (by exact_mod_cast hk : (k : ℝ) ≤ ⌊Real.exp b⌋₊).trans (Nat.floor_le (Real.exp_pos b).le)

private theorem clamped_log_succ (a : ℝ) (k : ℕ) :
    max a (Real.log k) ≤ max a (Real.log (k+1 : ℕ)) := by
  apply max_le_max_left
  by_cases h : k=0
  · subst k; simp
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h) (by norm_cast; omega)

private theorem clamped_variation (G : ℝ → ℝ) {a b D : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hD : 0 ≤ D)
    (hG : ∀ x ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b, |G x-G z| ≤ D*|x-z|) :
    (∑ k ∈ Finset.range ⌊Real.exp b⌋₊,
      |G (max a (Real.log k))-G (max a (Real.log (k+1 : ℕ)))|) ≤ D*(b-a) := by
  let f := fun k : ℕ => max a (Real.log k)
  have hp k (hk : k ∈ Finset.range ⌊Real.exp b⌋₊) :
      |G (f k)-G (f (k+1))| ≤ D*(f (k+1)-f k) := by
    have hkN := Finset.mem_range.mp hk
    have h := hG (f k) (clamped_log_mem ha hab (by omega))
      (f (k+1)) (clamped_log_mem ha hab (by omega))
    rwa [abs_of_nonpos (sub_nonpos.mpr (clamped_log_succ a k)),neg_sub] at h
  calc
    _ ≤ ∑ k ∈ Finset.range ⌊Real.exp b⌋₊, D*(f (k+1)-f k) := Finset.sum_le_sum hp
    _ = D*(f ⌊Real.exp b⌋₊-f 0) := by rw [← Finset.mul_sum,Finset.sum_range_sub]
    _ ≤ D*(b-a) := by
      have hmem := clamped_log_mem ha hab (le_refl ⌊Real.exp b⌋₊)
      have he : f 0=a := by dsimp [f]; simp only [Nat.cast_zero,Real.log_zero,max_eq_left ha]
      rw [he]
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right hmem.2 a) hD

private theorem weighted_cosine_of_full {a b y W D C : ℝ} (ha : 5000 ≤ a)
    (hab : a ≤ b) (hy : 54 ≤ |y|) (hlen : b-a ≤ 2*Real.pi/|y|)
    (G : ℝ → ℝ) (c : ℝ) (hD : 0 ≤ D)
    (hG : ∀ t ∈ Set.Icc a b, |G t| ≤ W)
    (hLip : ∀ t ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b, |G t-G z| ≤ D*|t-z|)
    (hC : |∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).filter Nat.Prime,
      Real.cos (y*(Real.log p+c))/(p : ℝ)| ≤ C) :
    |∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).filter Nat.Prime,
      G (Real.log p)*Real.cos (y*(Real.log p+c))/(p : ℝ)| ≤
      W*C+D*(b-a)*(2/(|y| *a)+4/a^2) := by
  have ha0 : 0 < a := by linarith
  have hy0 : 0 < |y| := by linarith
  let P := (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).filter Nat.Prime
  let f := fun n : ℕ => G (max a (Real.log n))
  let z := fun n : ℕ => if n ∈ P then Real.cos (y*(Real.log n+c))/(n : ℝ) else 0
  have hprefix k (hk : k ≤ ⌊Real.exp b⌋₊) :
      |∑ i ∈ Finset.range (k+1), z i| ≤ 2/(|y| *a)+4/a^2 := by
    dsimp only [z,P]
    rw [prefix_eq a b _ hk]
    exact prefix_cosine_bound ha hy hlen c hk
  have hlast : |∑ i ∈ Finset.range (⌊Real.exp b⌋₊+1), z i| ≤ C := by
    dsimp only [z,P]
    rw [prefix_eq a b _ le_rfl]
    exact hC
  have he : (∑ n ∈ Finset.range (⌊Real.exp b⌋₊+1), f n*z n) =
      ∑ p ∈ P, G (Real.log p)*Real.cos (y*(Real.log p+c))/(p : ℝ) := by
    simp only [z,mul_ite,mul_zero]
    rw [prefix_eq a b _ le_rfl]
    apply Finset.sum_congr rfl
    intro p hp
    have hpa := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    have hl : a ≤ Real.log p := (Real.lt_log_iff_exp_lt
      (by exact_mod_cast (Finset.mem_filter.mp hp).2.pos)).mpr (Nat.lt_of_floor_lt hpa) |>.le
    simp only [f,max_eq_right hl,mul_div_assoc]
  have h := weighted_bound f z ⌊Real.exp b⌋₊
    (hG _ (clamped_log_mem ha0.le hab le_rfl))
    (clamped_variation G ha0.le hab hD hLip)
    (fun k hk => hprefix k hk.le) hlast (by positivity)
  rw [he] at h
  exact h

/-- Nonconstant ordinary-prime amplitudes pay their true variation while
the complete moment keeps the sharper inverse-square cancellation. -/
theorem weighted_cosine_period {a y W D : ℝ} (ha : 5000 ≤ a) (hy : 54 ≤ |y|)
    (G : ℝ → ℝ) (c : ℝ) (hD : 0 ≤ D)
    (hG : ∀ t ∈ Set.Icc a (a+2*Real.pi/|y|), |G t| ≤ W)
    (hLip : ∀ t ∈ Set.Icc a (a+2*Real.pi/|y|), ∀ z ∈ Set.Icc a (a+2*Real.pi/|y|),
      |G t-G z| ≤ D*|t-z|) :
    |∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/|y|)⌋₊).filter Nat.Prime,
      G (Real.log p)*Real.cos (y*(Real.log p+c))/(p : ℝ)| ≤
      W*(4/a^2)+D*(2*Real.pi/|y|)*(2/(|y| *a)+4/a^2) := by
  have hlen : 0 ≤ 2*Real.pi/|y| := by positivity
  simpa only [add_sub_cancel_left] using weighted_cosine_of_full ha (by linarith) hy
    (by linarith) G c hD hG hLip (ZetaRieszQuantitativePrimePeriod.cosine_period_bound ha hy c)

/-- A literal clipped prime interval pays the same varying amplitude with
its full clipped-tail budget. No prime endpoint is completed. -/
theorem weighted_cosine_interval {a b y W D : ℝ} (ha : 5000 ≤ a) (hab : a ≤ b)
    (hy : 54 ≤ |y|) (hlen : b-a ≤ 2*Real.pi/|y|) (G : ℝ → ℝ) (c : ℝ) (hD : 0 ≤ D)
    (hG : ∀ t ∈ Set.Icc a b, |G t| ≤ W)
    (hLip : ∀ t ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b, |G t-G z| ≤ D*|t-z|) :
    |∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).filter Nat.Prime,
      G (Real.log p)*Real.cos (y*(Real.log p+c))/(p : ℝ)| ≤
      (W+D*(b-a))*(2/(|y| *a)+4/a^2) := by
  have h := weighted_cosine_of_full ha hab hy hlen G c hD hG hLip
    (clipped_cosine_bound ha hab hy hlen c)
  nlinarith only [h]

/-- The joint energy cost retains both the complete weighted moment and
every clipped weighted tail. It is independent of the Riesz length. -/
def amplitudeEnergy (a y W D : ℝ) : ℝ :=
  a*(W*(4/a^2)+D*(2*Real.pi/|y|)*(2/(|y| *a)+4/a^2))^2+
    (2*Real.pi/|y|)*((W+D*(2*Real.pi/|y|))*(2/(|y| *a)+4/a^2))^2

/-- The actual varying prime amplitude pays every Riesz crossing with an
explicit numerical energy. Only its amplitude and Lipschitz bounds enter. -/
theorem weighted_profile_energy {a y W D : ℝ} (ha : 5000 ≤ a) (hy : 54 ≤ |y|)
    (G : ℝ → ℝ) (c L : ℝ) (hW : 0 ≤ W) (hD : 0 ≤ D)
    (hG : ∀ t ∈ Set.Icc a (a+2*Real.pi/|y|), |G t| ≤ W)
    (hLip : ∀ t ∈ Set.Icc a (a+2*Real.pi/|y|), ∀ z ∈ Set.Icc a (a+2*Real.pi/|y|),
      |G t-G z| ≤ D*|t-z|) (R : ℕ) :
    let P := (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/|y|)⌋₊).filter Nat.Prime;
    let f := profile P (fun p => G (Real.log p)*Real.cos (y*(Real.log p+c))/(p : ℝ))
      (fun p => Real.log p) L;
    (∑ k ∈ Finset.Icc 1 R, (k : ℝ)*(f k-f (k+1))^2) ≤ amplitudeEnergy a y W D := by
  have ha0 : 0 < a := by linarith
  have hy0 : 0 < |y| := by linarith
  let h := 2*Real.pi/|y|
  have hh : 0 ≤ h := by dsimp [h]; positivity
  let B := (W+D*h)*(2/(|y| *a)+4/a^2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let P := (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+h)⌋₊).filter Nat.Prime
  let w := fun p : ℕ => G (Real.log p)*Real.cos (y*(Real.log p+c))/(p : ℝ)
  have ht (t : ℝ) (ht : t ∈ Set.Ioc (L-(a+h)) (L-a)) :
      |tail P w (fun p => Real.log p) L t| ≤ B := by
    let v := L-t
    have hav : a ≤ v := by dsimp [v]; linarith [ht.2]
    have hvb : v ≤ a+h := by dsimp [v]; linarith [ht.1]
    have hv0 : 0 < v := ha0.trans_le hav
    have he : t=L-v := by dsimp [v]; ring
    rw [he,tail_eq_prime_interval hav hv0.le]
    have hsub : Set.Icc v (a+h) ⊆ Set.Icc a (a+h) := fun _ hx => ⟨hav.trans hx.1,hx.2⟩
    have hb := weighted_cosine_interval (ha.trans hav) hvb hy (by dsimp [h] at hvb ⊢; linarith)
      G c hD (fun x hx => hG x (hsub hx))
      (fun x hx z hz => hLip x (hsub hx) z (hsub hz))
    apply hb.trans
    apply mul_le_mul
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (by linarith : a+h-v ≤ h) hD)
    · apply add_le_add
      · exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_left hav hy0.le)
      · exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (pow_le_pow_left₀ ha0.le hav 2)
    · positivity
    · positivity
  have hb := profile_energy_bound P w (fun p => Real.log p) L ha0.le
    (by linarith : a ≤ a+h) hB
    (fun p hp => ⟨(prime_interval_logs hp).1.le,(prime_interval_logs hp).2⟩) ht R
  have hm := weighted_cosine_period ha hy G c hD hG hLip
  have hs := pow_le_pow_left₀ (abs_nonneg _) hm 2
  rw [sq_abs] at hs
  dsimp only
  apply hb.trans
  dsimp only [amplitudeEnergy,B,h]
  rw [show a+2*Real.pi/|y|-a = 2*Real.pi/|y| by ring]
  exact add_le_add (mul_le_mul_of_nonneg_left hs ha0.le) le_rfl

/-- The literal single-prime factorial amplitude, without the reciprocal
prime or its phase. All derivative orders, including zero, are retained. -/
def factorialAmplitude (j : ℕ) (t : ℝ) : ℝ := Real.exp (-t/2)*t^j

/-- Exact saddle score of one factorial-order leg. -/
theorem factorialAmplitude_deriv (j : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (factorialAmplitude j)
      ((j/t-1/2)*factorialAmplitude j t) t := by
  have h := (((hasDerivAt_id t).neg.div_const 2).exp).mul ((hasDerivAt_id t).pow j)
  apply h.congr_deriv
  change Real.exp (-t/2)*(-1/2)*t^j+Real.exp (-t/2)*((j : ℝ)*t^(j-1)*1) =
    (j/t-1/2)*(Real.exp (-t/2)*t^j)
  cases j with
  | zero => norm_num; ring
  | succ j => simp only [Nat.succ_sub_one,Nat.cast_add,Nat.cast_one,pow_succ]; field_simp; ring

/-- The exact variation cost uses distance from the factorial saddle,
not the worst derivative order. It is suitable for binomial averaging. -/
def factorialScore (a h : ℝ) (j : ℕ) : ℝ := |j/a-1/2|+j*h/a^2

/-- Numerical amplitude and saddle-score bounds hold uniformly on a
prime-log interval and include both endpoints. -/
theorem factorialAmplitude_bounds (j : ℕ) {a h t : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (ht : t ∈ Set.Icc a (a+h)) :
    |factorialAmplitude j t| ≤ Real.exp (-a/2)*(a+h)^j ∧
    |(j/t-1/2)*factorialAmplitude j t| ≤
      (Real.exp (-a/2)*(a+h)^j)*factorialScore a h j := by
  have ht0 : 0 < t := ha.trans_le ht.1
  have hval : 0 ≤ factorialAmplitude j t := by dsimp [factorialAmplitude]; positivity
  have hamp : |factorialAmplitude j t| ≤ Real.exp (-a/2)*(a+h)^j := by
    rw [abs_of_nonneg hval]
    exact mul_le_mul (Real.exp_le_exp.mpr (by linarith [ht.1]))
      (pow_le_pow_left₀ ht0.le ht.2 j) (pow_nonneg ht0.le j) (Real.exp_pos _).le
  have hdiv : 0 ≤ (j : ℝ)/a-j/t :=
    sub_nonneg.mpr (div_le_div_of_nonneg_left (Nat.cast_nonneg j) ha ht.1)
  have hd : (j : ℝ)/a-j/t ≤ j*h/a^2 := by
    have he : (j : ℝ)/a-j/t = j*(t-a)/(a*t) := by field_simp
    rw [he]
    apply (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith [ht.2] : t-a ≤ h) (Nat.cast_nonneg j))
        (by positivity : 0 ≤ a*t)).trans
    exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ha)
      (by nlinarith [mul_le_mul_of_nonneg_left ht.1 ha.le])
  have hscore : |(j : ℝ)/t-1/2| ≤ factorialScore a h j := by
    have hs := abs_sub_le ((j : ℝ)/t) (j/a) (1/2)
    rw [abs_sub_comm ((j : ℝ)/t) (j/a),abs_of_nonneg hdiv] at hs
    dsimp [factorialScore]
    linarith only [hs,hd]
  refine ⟨hamp,?_⟩
  rw [abs_mul,mul_comm]
  exact mul_le_mul hamp hscore (abs_nonneg _) (by positivity)

/-- Every individual factorial prime leg has its explicit saddle-score
Lipschitz budget; no low-order allocation is removed. -/
theorem factorialAmplitude_lipschitz (j : ℕ) {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    {x z : ℝ} (hx : x ∈ Set.Icc a (a+h)) (hz : z ∈ Set.Icc a (a+h)) :
    |factorialAmplitude j x-factorialAmplitude j z| ≤
      (Real.exp (-a/2)*(a+h)^j)*factorialScore a h j*|x-z| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (ht : t ∈ Set.Icc a (a+h)) => (factorialAmplitude_deriv j (ha.trans_le ht.1)).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using (factorialAmplitude_bounds j ha hh ht).2)
    (convex_Icc a (a+h)) hz hx
  simpa only [Real.norm_eq_abs] using h

/-- A factorial leg's entire joint cutoff energy has a numerical bound.
The derivative cost retains its distance from the radial saddle. -/
theorem factorial_profile_energy {a y : ℝ} (ha : 5000 ≤ a) (hy : 54 ≤ |y|)
    (j : ℕ) (c L : ℝ) (R : ℕ) :
    let h := 2*Real.pi/|y|;
    let W := Real.exp (-a/2)*(a+h)^j;
    let P := (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+h)⌋₊).filter Nat.Prime;
    let f := profile P (fun p => factorialAmplitude j (Real.log p)*
      Real.cos (y*(Real.log p+c))/(p : ℝ)) (fun p => Real.log p) L;
    (∑ k ∈ Finset.Icc 1 R, (k : ℝ)*(f k-f (k+1))^2) ≤
      amplitudeEnergy a y W (W*factorialScore a h j) := by
  have ha0 : 0 < a := by linarith
  have hh : 0 ≤ 2*Real.pi/|y| := by positivity
  apply weighted_profile_energy ha hy (factorialAmplitude j) c L (by positivity)
    (by dsimp [factorialScore]; positivity)
    (fun t ht => (factorialAmplitude_bounds j ha0 hh ht).1)
    (fun x hx z hz => factorialAmplitude_lipschitz j ha0 hh hx hz) R

/-- The original two-Riesz-cutoff prime sum with its varying amplitude. -/
def weightedResponse (G : ℝ → ℝ) (a y L c : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/|y|)⌋₊).filter Nat.Prime,
    G (Real.log p)*Real.cos (y*(Real.log p+c))/(p : ℝ)*
      (VaughanLogAverage.riesz L n-VaughanLogAverage.riesz (L-Real.log p) n)

/-- Exact finite divisor profile for a weighted prime period, including
every cutoff endpoint. This identity also permits joint period summation. -/
theorem weighted_response_profile (G : ℝ → ℝ) (a y L c : ℝ) (R : ℕ)
    (hR : Real.exp L < R+1) {n : ℕ} (hn : 0 < n) :
    weightedResponse G a y L c n =
      ∑ d ∈ Finset.Icc 1 R,
        profile ((Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/|y|)⌋₊).filter Nat.Prime)
          (fun p => G (Real.log p)*Real.cos (y*(Real.log p+c))/(p : ℝ)) (fun p => Real.log p) L d*
            (if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0) := by
  unfold weightedResponse
  have he (p : ℕ) := ZetaRieszCutoffMean.riesz_difference_eq_prefix R
    (sub_le_self L (Real.log_natCast_nonneg p)) hR hn
  simp_rw [he,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simp only [profile,Finset.sum_mul,mul_assoc]

/-- Retain an arbitrary cofactor phase by an exact two-component rotation,
before combining prime periods or taking any quadratic mean. -/
theorem weighted_phase (G : ℝ → ℝ) (a y L : ℝ) (hy : y ≠ 0) (v : ℝ) (n : ℕ) :
    weightedResponse G a y L v n =
      Real.cos (y*v)*weightedResponse G a y L 0 n+
      Real.sin (y*v)*weightedResponse G a y L (Real.pi/(2*y)) n := by
  have he p : Real.cos (y*(Real.log p+Real.pi/(2*y))) = -Real.sin (y*Real.log p) := by
    rw [show y*(Real.log p+Real.pi/(2*y)) = y*Real.log p+Real.pi/2 by field_simp,
      Real.cos_add_pi_div_two]
  unfold weightedResponse
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [he]
  simp only [add_zero,mul_add,Real.cos_add]
  ring

private theorem weighted_phase_square (G : ℝ → ℝ) (a y L : ℝ) (hy : y ≠ 0) (v : ℝ) (n : ℕ) :
    (weightedResponse G a y L v n)^2 ≤ (weightedResponse G a y L 0 n)^2+
      (weightedResponse G a y L (Real.pi/(2*y)) n)^2 := by
  rw [weighted_phase G a y L hy v n]
  let C := weightedResponse G a y L 0 n
  let D := weightedResponse G a y L (Real.pi/(2*y)) n
  have ht := Real.sin_sq_add_cos_sq (y*v)
  have he : (Real.cos (y*v)*C+Real.sin (y*v)*D)^2+
      (Real.sin (y*v)*C-Real.cos (y*v)*D)^2 = C^2+D^2 := by
    calc
      _ = (Real.sin (y*v)^2+Real.cos (y*v)^2)*(C^2+D^2) := by ring
      _ = _ := by rw [ht,one_mul]
  nlinarith only [he,sq_nonneg (Real.sin (y*v)*C-Real.cos (y*v)*D)]

/-- The numerical joint energy gives an all-count arithmetic mean for
varying prime amplitudes and the full correlated cofactor phase. -/
theorem exists_weighted_mean :
    ∃ E : ℝ, 0 < E ∧ ∀ (a y L W D : ℝ) (G : ℝ → ℝ) (c : ℕ → ℝ) (X : ℕ) (S : Finset ℕ),
      5000 ≤ a → 54 ≤ |y| → 0 ≤ W → 0 ≤ D →
      (∀ t ∈ Set.Icc a (a+2*Real.pi/|y|), |G t| ≤ W) →
      (∀ t ∈ Set.Icc a (a+2*Real.pi/|y|), ∀ z ∈ Set.Icc a (a+2*Real.pi/|y|),
        |G t-G z| ≤ D*|t-z|) →
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, (weightedResponse G a y L (c n) n)^2) ≤ E*X*amplitudeEnergy a y W D := by
  obtain ⟨E,hE,hmean⟩ := ZetaRieszSignedCutoffEnergy.exists_divisor_profile_mean
  refine ⟨2*E,by positivity,fun a y L W D G c X S ha hy hW hD hG hLip hS hSF => ?_⟩
  let R := ⌊Real.exp L⌋₊
  have hR : Real.exp L < R+1 := Nat.lt_floor_add_one (Real.exp L)
  let P := (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/|y|)⌋₊).filter Nat.Prime
  have hconst v : (∑ n ∈ S, (weightedResponse G a y L v n)^2) ≤ E*X*amplitudeEnergy a y W D := by
    let f := profile P (fun p => G (Real.log p)*Real.cos (y*(Real.log p+v))/(p : ℝ))
      (fun p => Real.log p) L
    have hf : f (R+1)=0 := profile_endpoint P _ _ L R hR (fun p _ => Real.log_natCast_nonneg p)
    have he n (hn : n ∈ S) : weightedResponse G a y L v n =
        ∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0) :=
      weighted_response_profile G a y L v R hR (by have := (Finset.mem_Ioc.mp (hS hn)).1; omega)
    rw [Finset.sum_congr rfl (fun n hn => congrArg (fun x : ℝ => x^2) (he n hn))]
    exact (hmean X R S f hS hSF hf).trans
      (mul_le_mul_of_nonneg_left (weighted_profile_energy ha hy G v L hW hD hG hLip R) (by positivity))
  have hyne : y ≠ 0 := abs_pos.mp (by linarith : 0 < |y|)
  have hs := Finset.sum_le_sum (fun n (_ : n ∈ S) => weighted_phase_square G a y L hyne (c n) n)
  rw [Finset.sum_add_distrib] at hs
  nlinarith only [hs,hconst 0,hconst (Real.pi/(2*y))]

/-- A factorial leg's squarefree mean is now unconditional, with its exact
prime phase, every order including zero, and its numerical saddle cost. -/
theorem exists_factorial_mean :
    ∃ E : ℝ, 0 < E ∧ ∀ (a y L : ℝ) (j : ℕ) (c : ℕ → ℝ) (X : ℕ) (S : Finset ℕ),
      5000 ≤ a → 54 ≤ |y| → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      let h := 2*Real.pi/|y|;
      let W := Real.exp (-a/2)*(a+h)^j;
      (∑ n ∈ S, (weightedResponse (factorialAmplitude j) a y L (c n) n)^2) ≤
        E*X*amplitudeEnergy a y W (W*factorialScore a h j) := by
  obtain ⟨E,hE,hmean⟩ := exists_weighted_mean
  refine ⟨E,hE,fun a y L j c X S ha hy hS hSF => ?_⟩
  have ha0 : 0 < a := by linarith
  have hh : 0 ≤ 2*Real.pi/|y| := by positivity
  exact hmean a y L _ _ (factorialAmplitude j) c X S ha hy (by positivity)
    (by dsimp [factorialScore]; positivity)
    (fun t ht => (factorialAmplitude_bounds j ha0 hh ht).1)
    (fun x hx z hz => factorialAmplitude_lipschitz j ha0 hh hx hz) hS hSF

/-- Every factorial leg has both signed cofactor-shell bounds with the
reciprocal cofactor energy completely paid. One constant works for all j. -/
theorem exists_factorial_shell_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (a y L V : ℝ) (j : ℕ) (c w : ℕ → ℝ) (M : ℕ) (S : Finset ℕ),
      5000 ≤ a → 54 ≤ |y| → 0 ≤ V → 1 ≤ M → S ⊆ Finset.Ioc M (2*M) →
      (∀ n ∈ S, Squarefree n) → (∀ n ∈ S, |w n| ≤ V/n) →
      let h := 2*Real.pi/|y|;
      let W := Real.exp (-a/2)*(a+h)^j;
      let J := ∑ n ∈ S, w n*weightedResponse (factorialAmplitude j) a y L (c n) n;
      let K := Real.sqrt E*V*Real.sqrt (amplitudeEnergy a y W (W*factorialScore a h j));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_factorial_mean
  refine ⟨2*E,by positivity,fun a y L V j c w M S ha hy hV hM hS hSF hw => ?_⟩
  dsimp only
  have ha0 : 0 < a := by linarith
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hSI : S ⊆ Finset.Ioc 1 (2*M) := by
    intro n hn
    have h := Finset.mem_Ioc.mp (hS hn)
    exact Finset.mem_Ioc.mpr ⟨by omega,h.2⟩
  have hcard : (S.card : ℝ) ≤ M := by
    have h := Finset.card_le_card hS
    rw [Nat.card_Ioc,show 2*M-M=M by omega] at h
    exact_mod_cast h
  have hwE : (∑ n ∈ S, (w n)^2) ≤ V^2/M := by
    have hp n (hn : n ∈ S) : (w n)^2 ≤ (V/M)^2 := by
      have hnM : (M : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp (hS hn)).1.le
      have h := (hw n hn).trans (div_le_div_of_nonneg_left hV hM0 hnM)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
    calc
      _ ≤ ∑ _n ∈ S, (V/M)^2 := Finset.sum_le_sum hp
      _ = S.card*(V/M)^2 := by simp
      _ ≤ M*(V/M)^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = V^2/M := by field_simp
  let W := Real.exp (-a/2)*(a+2*Real.pi/|y|)^j
  let Q := amplitudeEnergy a y W (W*factorialScore a (2*Real.pi/|y|) j)
  have hQ : 0 ≤ Q := by dsimp [Q,amplitudeEnergy]; positivity
  have hmean' := hmean a y L j c (2*M) S ha hy hSI hSF
  change _ ≤ E*(2*M : ℕ)*Q at hmean'
  have hs := (Finset.sum_mul_sq_le_sq_mul_sq S w
    (fun n => weightedResponse (factorialAmplitude j) a y L (c n) n)).trans
      (mul_le_mul hwE hmean' (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity))
  have he : V^2/M*(E*(2*M)*Q) = 2*E*V^2*Q := by field_simp
  push_cast at hs
  rw [he] at hs
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs,mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hQ]
  nlinarith only [hs]

end RiemannGaussian.ZetaRieszWeightedPrimeTail
