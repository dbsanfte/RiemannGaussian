/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLinearCutoffMean

/-!
# Joint signed cutoff energy

The complete signed cutoff profile is summed before its energy is taken.
The estimate retains cancellation between prime moments and cutoff crossings;
there is no separate absolute crossing price. Every finite cutoff is allowed,
including cutoffs on either side of the square-root transition.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszSignedCutoffEnergy

/-- A logarithmic Schur estimate for arbitrary signed coefficients. Unlike
the positive-mixture bound, the cost is the squared energy of the already
combined profile, not the sum of absolute prime or divisor contributions. -/
theorem signed_gram_mean (I T : Finset ℕ) (R : ℕ)
    (b : ℕ → ℝ) (f : ℕ → ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hI : I ⊆ Finset.Icc 1 R)
    (hpair : ∀ i ∈ I, ∀ j ∈ I,
      |∑ n ∈ T, f i n*f j n| ≤ C/(4+|Real.log i-Real.log j|)^2) :
    (∑ n ∈ T, (∑ i ∈ I, b i*f i n)^2) ≤
      4*C*(∑ i ∈ I, (i : ℝ)*(b i)^2) := by
  let G := fun i j => ∑ n ∈ T, f i n*f j n
  let K := fun i j : ℕ => (4+|Real.log i-Real.log j|)^2
  let Q := fun i j : ℕ => (i : ℝ)*(b i)^2/((j : ℝ)*K i j)
  have hK i j : 0 < K i j := by dsimp [K]; positivity
  have hsym i j : K i j = K j i := by dsimp [K]; rw [abs_sub_comm]
  have hrows i (hi : i ∈ I) : (∑ j ∈ I, 1/((j : ℝ)*K i j)) ≤ 4 := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg hI (fun j _ _ => by
      exact div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg j) (hK i j).le))).trans
    exact ZetaRieszLinearCutoffMean.logarithmic_row i R (Finset.mem_Icc.mp (hI hi)).1
  have hp i (hi : i ∈ I) j (hj : j ∈ I) :
      b i*b j*G i j ≤ (C/2)*(Q i j+Q j i) := by
    have hi0 : (0 : ℝ) < i := by exact_mod_cast (Finset.mem_Icc.mp (hI hi)).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp (hI hj)).1
    have hb : |b i*b j| ≤ ((i : ℝ)^2*(b i)^2+(j : ℝ)^2*(b j)^2)/(2*i*j) := by
      apply (le_div_iff₀ (by positivity)).mpr
      rw [abs_mul]
      nlinarith only [sq_nonneg ((i : ℝ)*|b i|-(j : ℝ)*|b j|),
        sq_abs (b i),sq_abs (b j)]
    calc
      _ ≤ |b i*b j| *|G i j| := by simpa only [abs_mul] using le_abs_self (b i*b j*G i j)
      _ ≤ (((i : ℝ)^2*(b i)^2+(j : ℝ)^2*(b j)^2)/(2*i*j))*(C/K i j) :=
        mul_le_mul hb (hpair i hi j hj) (abs_nonneg _) (by positivity)
      _ = _ := by dsimp only [Q]; rw [hsym j i]; field_simp
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
  have hswap : (∑ i ∈ I, ∑ j ∈ I, Q j i) = ∑ i ∈ I, ∑ j ∈ I, Q i j :=
    Finset.sum_comm
  have hQ : (∑ i ∈ I, ∑ j ∈ I, Q i j) ≤ 4*(∑ i ∈ I, (i : ℝ)*(b i)^2) := by
    calc
      _ = ∑ i ∈ I, (i : ℝ)*(b i)^2*(∑ j ∈ I, 1/((j : ℝ)*K i j)) := by
        simp only [Finset.mul_sum,Q]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ ∑ i ∈ I, (i : ℝ)*(b i)^2*4 := Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (hrows i hi) (mul_nonneg (Nat.cast_nonneg i) (sq_nonneg _)))
      _ = _ := by rw [← Finset.sum_mul]; ring
  rw [he]
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ I, (C/2)*(Q i j+Q j i) :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hp i hi j hj))
    _ = C*(∑ i ∈ I, ∑ j ∈ I, Q i j) := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum]
      rw [hswap]
      ring
    _ ≤ C*(4*(∑ i ∈ I, (i : ℝ)*(b i)^2)) := mul_le_mul_of_nonneg_left hQ hC
    _ = _ := by ring

/-- Every signed cutoff profile has a uniform all-count mean controlled by
its logarithmic squared energy. All finite counting errors are paid. The
profile is common across the squarefree cofactor population. -/
theorem exists_signed_profile_mean :
    ∃ E : ℝ, 0 < E ∧ ∀ (X R : ℕ) (S : Finset ℕ) (b : ℕ → ℝ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S,
        (∑ i ∈ Finset.Icc 1 R, b i*(∑ d ∈ Finset.Icc 1 i,
          if d ∣ n then (μ d : ℝ) else 0))^2) ≤
      E*X*(∑ i ∈ Finset.Icc 1 R, (i : ℝ)*(b i)^2) := by
  obtain ⟨C,hC,hsmall⟩ := ZetaRieszSquarefreeSeparatedMean.exists_small_gram_bound
  obtain ⟨D,hD,hlarge⟩ := ZetaRieszSquarefreeSeparatedMean.exists_large_gram_bound
  refine ⟨8*(C+D),by linarith,fun X R S b hS hSF => ?_⟩
  let I := Finset.Icc 1 R
  let U := I.filter (fun i => i^2 ≤ X)
  let V := I.filter (fun i => ¬i^2 ≤ X)
  have hU : U ⊆ I := Finset.filter_subset _ _
  have hV : V ⊆ I := Finset.filter_subset _ _
  have hSI : S ⊆ Finset.Icc 1 X := by
    intro n hn
    have h := Finset.mem_Ioc.mp (hS hn)
    exact Finset.mem_Icc.mpr ⟨by omega,h.2⟩
  have hEU : (∑ i ∈ U, (i : ℝ)*(b i)^2) ≤ ∑ i ∈ I, (i : ℝ)*(b i)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hU (fun i _ _ => mul_nonneg (Nat.cast_nonneg i) (sq_nonneg _))
  have hEV : (∑ i ∈ V, (i : ℝ)*(b i)^2) ≤ ∑ i ∈ I, (i : ℝ)*(b i)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hV (fun i _ _ => mul_nonneg (Nat.cast_nonneg i) (sq_nonneg _))
  have hs := signed_gram_mean U (Finset.Icc 1 X) R b
    (fun i n => ∑ d ∈ Finset.Icc 1 i, if d ∣ n then (μ d : ℝ) else 0)
    (C := C*X) (by positivity) hU
    (fun i hi j hj => hsmall X i j (Finset.mem_Icc.mp (hU hi)).1
      (Finset.mem_Icc.mp (hU hj)).1 (Finset.mem_filter.mp hi).2
      (Finset.mem_filter.mp hj).2)
  have hl := signed_gram_mean V (Finset.Icc 1 X) R b
    (fun i n => ∑ d ∈ Finset.Icc 1 ((n-1)/i), if d ∣ n then (μ d : ℝ) else 0)
    (C := D*X) (by positivity) hV
    (fun i hi j hj => hlarge X i j (Finset.mem_Icc.mp (hV hi)).1
      (Finset.mem_Icc.mp (hV hj)).1
      (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hi).2))
      (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hj).2)))
  simp only [← mul_assoc] at hs hl
  have hsmallS : (∑ n ∈ S,
      (∑ i ∈ U, b i*(∑ d ∈ Finset.Icc 1 i, if d ∣ n then (μ d : ℝ) else 0))^2) ≤
      4*C*X*(∑ i ∈ I, (i : ℝ)*(b i)^2) :=
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
      4*D*X*(∑ i ∈ I, (i : ℝ)*(b i)^2) := by
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



/-- Finite summation by parts, with its endpoint discharged explicitly. -/
theorem abel_profile (R : ℕ) (f z : ℕ → ℝ) (hend : f (R+1)=0) :
    (∑ d ∈ Finset.Icc 1 R, f d*z d) =
      ∑ k ∈ Finset.Icc 1 R, (f k-f (k+1))*(∑ d ∈ Finset.Icc 1 k, z d) := by
  have htail d (hd : d ≤ R+1) :
      (∑ k ∈ Finset.Icc d R, (f k-f (k+1))) = f d := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    calc
      _ = -(∑ k ∈ Finset.Ico d (R+1), (f (k+1)-f k)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = f d := by rw [Finset.sum_Ico_sub f hd,hend]; ring
  calc
    _ = ∑ d ∈ Finset.Icc 1 R, ∑ k ∈ Finset.Icc d R, (f k-f (k+1))*z d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_mul,htail d (by have := (Finset.mem_Icc.mp hd).2; omega)]
    _ = _ := by
      have h := Finset.sum_Ico_Ico_comm 1 (R+1) (fun d k => (f k-f (k+1))*z d)
      simp only [Finset.Ico_add_one_right_eq_Icc,← Finset.mul_sum] at h
      exact h

/-- The mean of any signed divisor profile is bounded by its exact finite
logarithmic difference energy. No monotonicity or sign restriction is used. -/
theorem exists_divisor_profile_mean :
    ∃ E : ℝ, 0 < E ∧ ∀ (X R : ℕ) (S : Finset ℕ) (f : ℕ → ℝ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) → f (R+1)=0 →
      (∑ n ∈ S, (∑ d ∈ Finset.Icc 1 R,
        f d*(if d ∣ n then (μ d : ℝ) else 0))^2) ≤
      E*X*(∑ k ∈ Finset.Icc 1 R, (k : ℝ)*(f k-f (k+1))^2) := by
  obtain ⟨E,hE,hmean⟩ := exists_signed_profile_mean
  refine ⟨E,hE,fun X R S f hS hSF hend => ?_⟩
  simp_rw [abel_profile R f _ hend]
  exact hmean X R S (fun k => f k-f (k+1)) hS hSF

/-- The whole signed profile, including all cutoff crossings, has simultaneous
upper and lower bounds with its prime sums still inside the squared energy. -/
theorem exists_joint_profile_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X R : ℕ) (S : Finset ℕ) (f w : ℕ → ℝ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) → f (R+1)=0 →
      let J := ∑ n ∈ S, w n*(∑ d ∈ Finset.Icc 1 R,
        f d*(if d ∣ n then (μ d : ℝ) else 0));
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*E*X*
        (∑ k ∈ Finset.Icc 1 R, (k : ℝ)*(f k-f (k+1))^2));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_divisor_profile_mean
  refine ⟨E,hE,fun X R S f w hS hSF hend => ?_⟩
  dsimp only
  have hs := (Finset.sum_mul_sq_le_sq_mul_sq S w
    (fun n => ∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (μ d : ℝ) else 0))).trans
      (mul_le_mul_of_nonneg_left (hmean X R S f hS hSF hend)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs,Real.sq_sqrt (by positivity)]
  nlinarith only [hs]

private theorem prefix_bound {E : ℝ} (hE : 0 < E)
    (hmean : ∀ (X R : ℕ) (S : Finset ℕ) (b : ℕ → ℝ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, (∑ i ∈ Finset.Icc 1 R, b i*(∑ d ∈ Finset.Icc 1 i,
        if d ∣ n then (μ d : ℝ) else 0))^2) ≤
      E*X*(∑ i ∈ Finset.Icc 1 R, (i : ℝ)*(b i)^2))
    (X R : ℕ) (S : Finset ℕ) (b : ℕ → ℝ)
    (hS : S ⊆ Finset.Ioc 1 X) (hSF : ∀ n ∈ S, Squarefree n) :
    |∑ n ∈ S, ∑ i ∈ Finset.Icc 1 R, b i*(∑ d ∈ Finset.Icc 1 i,
      if d ∣ n then (μ d : ℝ) else 0)| ≤
      Real.sqrt E*X*Real.sqrt (∑ i ∈ Finset.Icc 1 R, (i : ℝ)*(b i)^2) := by
  let Q := ∑ i ∈ Finset.Icc 1 R, (i : ℝ)*(b i)^2
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg i) (sq_nonneg _))
  have hcard : (S.card : ℝ) ≤ X := by
    have h := Finset.card_le_card hS
    simp only [Nat.card_Ioc] at h
    exact_mod_cast h.trans (Nat.sub_le X 1)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ))
    (fun n => ∑ i ∈ Finset.Icc 1 R, b i*(∑ d ∈ Finset.Icc 1 i,
      if d ∣ n then (μ d : ℝ) else 0))
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hcs
  have hb := mul_le_mul_of_nonneg_left (hmean X R S b hS hSF) (Nat.cast_nonneg S.card)
  have hc := mul_le_mul_of_nonneg_right hcard (show 0 ≤ E*X*Q by positivity)
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs,mul_pow,mul_pow,Real.sq_sqrt hE.le,Real.sq_sqrt hQ]
  nlinarith only [hcs,hb,hc]

/-- Cofactor-dependent profiles retain their exact signed finite differences.
This pays every moving mask boundary explicitly and never separates the
constant moment, first moment and signed cutoff correction. -/
theorem exists_varying_profile_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X R : ℕ) (S : Finset ℕ) (b : ℕ → ℕ → ℝ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∀ i, b (X+1) i=0) →
      let J := ∑ n ∈ S, ∑ i ∈ Finset.Icc 1 R, b n i*(∑ d ∈ Finset.Icc 1 i,
        if d ∣ n then (μ d : ℝ) else 0);
      let K := Real.sqrt E*(∑ q ∈ Finset.Icc 1 X, (q : ℝ)*
        Real.sqrt (∑ i ∈ Finset.Icc 1 R, (i : ℝ)*(b q i-b (q+1) i)^2));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_signed_profile_mean
  refine ⟨E,hE,fun X R S b hS hSF hend => ?_⟩
  dsimp only
  let z := fun n i => if n ∈ S then
    (∑ d ∈ Finset.Icc 1 i, if d ∣ n then (μ d : ℝ) else 0) else 0
  have hSI : S ⊆ Finset.Icc 1 X := fun n hn =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp (hS hn)).1.le,(Finset.mem_Ioc.mp (hS hn)).2⟩
  have hs i : (∑ n ∈ S, b n i*(∑ d ∈ Finset.Icc 1 i,
      if d ∣ n then (μ d : ℝ) else 0)) = ∑ n ∈ Finset.Icc 1 X, b n i*z n i := by
    have he : (Finset.Icc 1 X).filter (fun n => n ∈ S) = S := Finset.filter_mem_eq_inter.trans
      (Finset.inter_eq_right.mpr hSI)
    simp only [z,mul_ite,mul_zero]
    rw [← Finset.sum_filter,he]
  have hprefix q i : (∑ n ∈ Finset.Icc 1 q, z n i) =
      ∑ n ∈ S.filter (fun n => n ≤ q), ∑ d ∈ Finset.Icc 1 i,
        if d ∣ n then (μ d : ℝ) else 0 := by
    have he : (Finset.Icc 1 q).filter (fun n => n ∈ S) = S.filter (fun n => n ≤ q) := by
      ext n
      simp only [Finset.mem_filter,Finset.mem_Icc]
      constructor
      · rintro ⟨⟨_,hnq⟩,hn⟩; exact ⟨hn,hnq⟩
      · rintro ⟨hn,hnq⟩; exact ⟨⟨(Finset.mem_Ioc.mp (hS hn)).1.le,hnq⟩,hn⟩
    simp only [z]
    rw [← Finset.sum_filter,he]
  have he : (∑ n ∈ S, ∑ i ∈ Finset.Icc 1 R, b n i*(∑ d ∈ Finset.Icc 1 i,
      if d ∣ n then (μ d : ℝ) else 0)) =
      ∑ q ∈ Finset.Icc 1 X, ∑ n ∈ S.filter (fun n => n ≤ q),
        ∑ i ∈ Finset.Icc 1 R, (b q i-b (q+1) i)*(∑ d ∈ Finset.Icc 1 i,
          if d ∣ n then (μ d : ℝ) else 0) := by
    rw [Finset.sum_comm]
    simp_rw [hs,abel_profile X (fun n => b n _) (fun n => z n _) (hend _),hprefix]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  apply abs_le.mp
  rw [he]
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 X, |∑ n ∈ S.filter (fun n => n ≤ q),
        ∑ i ∈ Finset.Icc 1 R, (b q i-b (q+1) i)*(∑ d ∈ Finset.Icc 1 i,
          if d ∣ n then (μ d : ℝ) else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 X, Real.sqrt E*q*
        Real.sqrt (∑ i ∈ Finset.Icc 1 R, (i : ℝ)*(b q i-b (q+1) i)^2) := by
      apply Finset.sum_le_sum
      intro q _
      exact prefix_bound hE hmean q R (S.filter (fun n => n ≤ q))
        (fun i => b q i-b (q+1) i) (fun n hn => Finset.mem_Ioc.mpr
          ⟨(Finset.mem_Ioc.mp (hS (Finset.mem_filter.mp hn).1)).1,(Finset.mem_filter.mp hn).2⟩)
        (fun n hn => hSF n (Finset.mem_filter.mp hn).1)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring


/-- The same estimate directly bounds the original divisor profile with
cofactor dependence. Its mixed finite difference pays every exterior and
interior boundary, including noncontiguous masks. -/
theorem exists_varying_divisor_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X R : ℕ) (S : Finset ℕ) (f : ℕ → ℕ → ℝ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∀ i, f (X+1) i=0) → (∀ n, f n (R+1)=0) →
      let b := fun n i => f n i-f n (i+1);
      let J := ∑ n ∈ S, ∑ d ∈ Finset.Icc 1 R,
        f n d*(if d ∣ n then (μ d : ℝ) else 0);
      let K := Real.sqrt E*(∑ q ∈ Finset.Icc 1 X, (q : ℝ)*
        Real.sqrt (∑ i ∈ Finset.Icc 1 R, (i : ℝ)*(b q i-b (q+1) i)^2));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_varying_profile_bounds
  refine ⟨E,hE,fun X R S f hS hSF hx hr => ?_⟩
  dsimp only
  simp_rw [abel_profile R (f _) _ (hr _)]
  exact hbound X R S (fun n i => f n i-f n (i+1)) hS hSF (by simp [hx])

/-- The literal signed prime sums are combined into their divisor-cutoff
profile BEFORE any norm. This keeps the allocation, factorial kernel, full
phase, both reflected cutoffs and every selected prime/cofactor mask. -/
def primeProfile (A : Finset ℕ) (X : ℕ) (P : ℕ → Finset ℕ) (L : ℝ)
    (N : ℕ) (y : ℝ) (a d : ℕ) : ℝ :=
  if a ≤ X then -((-1 : ℝ)^a.primeFactors.card)/(a : ℝ)*(∑ p ∈ P a,
    ZetaRieszGlobalPrimePeriod.signedPrimeWeight A L N y a p*
      (max 0 (L-Real.log d)-max 0 (L-Real.log p-Real.log d))) else 0

private theorem prime_profile_endpoint (A : Finset ℕ) (X : ℕ) (P : ℕ → Finset ℕ)
    (L : ℝ) (N : ℕ) (y : ℝ) (R : ℕ) (hR : Real.exp L < R+1)
    (a : ℕ) :
    primeProfile A X P L N y a (R+1) = 0 := by
  by_cases ha : a ≤ X
  · have hl : L < Real.log (R+1 : ℕ) := by
      simpa only [Real.log_exp,Nat.cast_add,Nat.cast_one] using
        Real.log_lt_log (Real.exp_pos L) hR
    rw [primeProfile,if_pos ha]
    have hz : (∑ p ∈ P a, ZetaRieszGlobalPrimePeriod.signedPrimeWeight A L N y a p*
        (max 0 (L-Real.log (R+1 : ℕ))-max 0 (L-Real.log p-Real.log (R+1 : ℕ)))) = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      have hp0 := Real.log_natCast_nonneg p
      rw [max_eq_left (by linarith : L-Real.log (R+1 : ℕ) ≤ 0),
        max_eq_left (by linarith : L-Real.log p-Real.log (R+1 : ℕ) ≤ 0)]
      ring
    rw [hz,mul_zero]
  · simp only [primeProfile,if_neg ha]

private theorem literal_profile_eq (A S : Finset ℕ) (X : ℕ) (P : ℕ → Finset ℕ)
    (L : ℝ) (N : ℕ) (y : ℝ) (R : ℕ) (hR : Real.exp L < R+1)
    (hS : S ⊆ Finset.Ioc 1 X)
    (hSF : ∀ a ∈ S, Squarefree a ∧ 2 ≤ a.primeFactors.card)
    (hP : ∀ a ∈ S, ∀ p ∈ P a, p.Prime ∧ ¬p ∣ a) :
    (∑ a ∈ S, ∑ p ∈ P a, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re =
      ∑ a ∈ S, ∑ d ∈ Finset.Icc 1 R, primeProfile A X P L N y a d*
        (if d ∣ a then (μ d : ℝ) else 0) := by
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have haX : a ≤ X := (Finset.mem_Ioc.mp (hS ha)).2
  have hmu : (μ a : ℝ) = (-1 : ℝ)^a.primeFactors.card := by
    exact_mod_cast ZetaRieszReflectedLinear.moebius_eq_primeCount (hSF a ha).1
  have ha1 : a ≠ 1 := by intro he; simpa [he] using (hSF a ha).2
  have hap : ¬a.Prime := by
    intro hp
    have h := (hSF a ha).2
    rw [hp.primeFactors,Finset.card_singleton] at h
    omega
  have he p (hp : p ∈ P a) :
      (ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re =
      -(μ a : ℝ)/(a : ℝ)*ZetaRieszGlobalPrimePeriod.signedPrimeWeight A L N y a p*
        (VaughanLogAverage.riesz L a-VaughanLogAverage.riesz (L-Real.log p) a) := by
    rw [ZetaRieszGlobalPrimePeriod.re_residual_atom (hSF a ha).1 (hSF a ha).2
      (hP a ha p hp).1 (hP a ha p hp).2,
      ZetaRieszSquarefreeDualMean.response_reflection L (Real.log p) (hSF a ha).1 ha1 hap]
    ring
  rw [Complex.re_sum]
  calc
    _ = ∑ p ∈ P a, -(μ a : ℝ)/(a : ℝ)*
        ZetaRieszGlobalPrimePeriod.signedPrimeWeight A L N y a p*
          (VaughanLogAverage.riesz L a-VaughanLogAverage.riesz (L-Real.log p) a) :=
      Finset.sum_congr rfl he
    _ = ∑ p ∈ P a, -(μ a : ℝ)/(a : ℝ)*
        ZetaRieszGlobalPrimePeriod.signedPrimeWeight A L N y a p*
          (∑ d ∈ Finset.Icc 1 R,
            (max 0 (L-Real.log d)-max 0 (L-Real.log p-Real.log d))*
              (if d ∣ a then (μ d : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [ZetaRieszCutoffMean.riesz_difference_eq_prefix R
        (by linarith [Real.log_natCast_nonneg p] : L-Real.log p ≤ L) hR
        (Nat.pos_of_ne_zero (hSF a ha).1.ne_zero)]
    _ = _ := by
      rw [hmu]
      simp only [primeProfile,if_pos haX,Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro p _
      ring

/-- A simultaneous bound for the whole original finite prime sum. The exact
signed prime/profile energy includes all moments, crossings and mask jumps;
no absolute crossing sum, fixed count ceiling, or prime-density assumption
appears. Its eventual source-scale size remains to be estimated. -/
theorem exists_literal_joint_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X R N : ℕ) (A S : Finset ℕ) (P : ℕ → Finset ℕ) (L y : ℝ),
      S ⊆ Finset.Ioc 1 X → (∀ a ∈ S, Squarefree a ∧ 2 ≤ a.primeFactors.card) →
      (∀ a ∈ S, ∀ p ∈ P a, p.Prime ∧ ¬p ∣ a) → Real.exp L < R+1 →
      let f := primeProfile A X P L N y;
      let b := fun a i => f a i-f a (i+1);
      let K := Real.sqrt E*(∑ q ∈ Finset.Icc 1 X, (q : ℝ)*
        Real.sqrt (∑ i ∈ Finset.Icc 1 R, (i : ℝ)*(b q i-b (q+1) i)^2));
      let J := (∑ a ∈ S, ∑ p ∈ P a,
        ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re;
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_varying_divisor_bounds
  refine ⟨E,hE,fun X R N A S P L y hS hSF hP hR => ?_⟩
  have hb := hbound X R S (primeProfile A X P L N y) hS
    (fun a ha => (hSF a ha).1) (by simp [primeProfile])
    (prime_profile_endpoint A X P L N y R hR)
  dsimp only at hb ⊢
  rw [literal_profile_eq A S X P L N y R hR hS hSF hP]
  exact hb

end RiemannGaussian.ZetaRieszSignedCutoffEnergy
