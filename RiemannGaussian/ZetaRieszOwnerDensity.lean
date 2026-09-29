/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnerUniformMean

/-!
# Correlated decreasing weights in the joint owner estimate

A positive decreasing factor may vary with the cofactor. Selecting its
largest original signed prefix retains the established joint maximal price.
The reciprocal prime-log factor keeps each cofactor's own positive lower
bound in the weight energy. No replacement of actual primes by a density
and no source-scale estimate for the remaining energy is asserted.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszOwnerDensity
open ZetaRieszOwnerMaximal

private theorem shifted_sum (f : ℕ → ℝ) (o m : ℕ) :
    (∑ j ∈ Finset.range m, f (o+j)) = ∑ i ∈ Finset.Ico o (o+m), f i := by
  simpa only [Nat.Ico_zero_eq_range,Nat.zero_add,Nat.add_zero,Nat.add_comm] using
    Finset.sum_Ico_add f 0 m o

/-- A positive decreasing density costs only its first value, after
the original signed prefixes have been combined. -/
theorem decreasing_interval_bound (f v : ℕ → ℝ) {lo hi : ℕ} {B D : ℝ}
    (hlo : lo ≤ hi) (hD : 0 ≤ D)
    (hv : ∀ i ∈ Finset.Ico lo hi, 0 ≤ v i ∧ v i ≤ D)
    (hdec : ∀ i ∈ Finset.Ico lo hi, ∀ j ∈ Finset.Ico lo hi, i ≤ j → v j ≤ v i)
    (hB : ∀ j ∈ Finset.Icc lo hi, |∑ i ∈ Finset.Ico lo j, f i| ≤ B) :
    |∑ i ∈ Finset.Ico lo hi, v i*f i| ≤ D*B := by
  have hB0 : 0 ≤ B := by simpa using hB lo (Finset.mem_Icc.mpr ⟨le_rfl,hlo⟩)
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hlo
  cases m with
  | zero => simp only [Nat.add_zero,Finset.Ico_self,Finset.sum_empty,abs_zero]; positivity
  | succ m =>
    have hm i (hi : i ≤ m) : lo+i ∈ Finset.Ico lo (lo+(m+1)) :=
      Finset.mem_Ico.mpr ⟨by omega,by omega⟩
    have ht := FiniteAbelVariation.decreasing_bound (fun i => v (lo+i))
      (fun i => (f (lo+i) : ℂ)) m (fun i hi => (hv _ (hm i hi)).1)
      (by
        intro i hi j hj hij
        exact hdec _ (hm i hi.2) _ (hm j hj.2) (by omega))
      (by
        intro j hj
        rw [← Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,shifted_sum]
        exact hB _ (Finset.mem_Icc.mpr ⟨by omega,by omega⟩))
    simp_rw [← Complex.ofReal_mul,← Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs] at ht
    rw [shifted_sum (fun i => v i*f i)] at ht
    exact ht.trans (by simpa only [Nat.add_zero,mul_comm] using
      mul_le_mul_of_nonneg_left (hv lo (by simp)).2 hB0)

/-- A cofactor-dependent monotone density retains the same joint owner
mean, multiplied only by its squared maximum. There is no added period
or maximal-depth loss. -/
theorem exists_density_mean_bound {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (b N X : ℕ) (S : Finset ℕ) (R : ℕ → ℕ)
      (a : ℕ → ℝ) (x v : ℕ → ℕ → ℝ) (lo hi : ℕ → ℕ) (D : ℝ),
      32 ≤ N → 0 ≤ D → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∀ i < 2^b, 0 < R i) →
      (∀ (i : ℕ), i < 2^b → ∀ (j : ℕ), j < 2^b →
        h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n), x n i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ n ∈ S, ∀ i, lo n ≤ i → i+1 < hi n → x n (i+1) ≤ x n i) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n), 0 ≤ v n i ∧ v n i ≤ D) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n),
        ∀ j ∈ Finset.Ico (lo n) (hi n), i ≤ j → v n j ≤ v n i) →
      (∑ n ∈ S, (∑ i ∈ Finset.Ico (lo n) (hi n),
        v n i*(ownerWeight N (x n i)*a i*
          (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0)))^2) ≤
        D^2*(36*(((b+1 : ℕ) : ℝ)^2)*(E*X)*(∑ i ∈ Finset.range (2^b), (a i)^2)) := by
  obtain ⟨E,hE,hmean⟩ := ZetaRieszOwnerUniformMean.exists_owner_interval_mean_bound hh
  refine ⟨E,hE,fun b N X S R a x v lo hi D hN hD hS hSF hR hsep hr hx hd hv hvd => ?_⟩
  let f := fun n i => ownerWeight N (x n i)*a i*
    (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0)
  have hm : ∀ n ∈ S, ∃ j ∈ Finset.Icc (lo n) (hi n),
      ∀ k ∈ Finset.Icc (lo n) (hi n),
        |∑ i ∈ Finset.Ico (lo n) k, f n i| ≤ |∑ i ∈ Finset.Ico (lo n) j, f n i| := by
    intro n hn
    exact Finset.exists_max_image _ _ ⟨lo n,Finset.mem_Icc.mpr ⟨le_rfl,(hr n hn).1⟩⟩
  choose j hj hjmax using hm
  let endpoint := fun n => if hn : n ∈ S then j n hn else 0
  have he n (hn : n ∈ S) : endpoint n = j n hn := dif_pos hn
  have hr' n (hn : n ∈ S) : lo n ≤ endpoint n ∧ endpoint n ≤ 2^b := by
    rw [he n hn]
    exact ⟨(Finset.mem_Icc.mp (hj n hn)).1,
      (Finset.mem_Icc.mp (hj n hn)).2.trans (hr n hn).2⟩
  have hsub n (hn : n ∈ S) : Finset.Ico (lo n) (endpoint n) ⊆ Finset.Ico (lo n) (hi n) := by
    intro i hi'
    rw [he n hn] at hi'
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hi').1,
      ((Finset.mem_Ico.mp hi').2).trans_le (Finset.mem_Icc.mp (hj n hn)).2⟩
  have hc n (hn : n ∈ S) :
      (∑ i ∈ Finset.Ico (lo n) (hi n), v n i*f n i)^2 ≤
        D^2*(∑ i ∈ Finset.Ico (lo n) (endpoint n), f n i)^2 := by
    have ht := decreasing_interval_bound (f n) (v n)
      (B := |∑ i ∈ Finset.Ico (lo n) (endpoint n), f n i|) (hr n hn).1 hD (hv n hn)
      (hvd n hn) (by rw [he n hn]; exact hjmax n hn)
    have hs := pow_le_pow_left₀ (abs_nonneg _) ht 2
    simpa only [mul_pow,sq_abs] using hs
  have hm' := hmean b N X S R a x lo endpoint hN hS hSF hR hsep hr'
    (fun n hn i hi' => hx n hn i (hsub n hn hi'))
    (fun n hn i hli hij => hd n hn i hli (by
      rw [he n hn] at hij
      exact hij.trans_le (Finset.mem_Icc.mp (hj n hn)).2))
  exact (Finset.sum_le_sum hc).trans (by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hm' (sq_nonneg D))

/-- The reciprocal prime logarithm can depend on the cofactor without
another period-count price. The literal owner and sharp Riesz slopes
are retained. This is not a replacement of primes by their density. -/
theorem exists_reciprocal_slope_bounds {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (b N X : ℕ) (S : Finset ℕ) (R : ℕ → ℕ)
      (D a w : ℕ → ℝ) (T : ℕ → ℕ → ℝ) (lo hi : ℕ → ℕ) (δ : ℕ → ℝ),
      32 ≤ N → (∀ n ∈ S, 0 < δ n) → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∀ i < 2^b, 0 < R i) →
      (∀ i < 2^b, (R i : ℝ) < Real.exp (D i) ∧ Real.exp (D i) ≤ R i+1) →
      (∀ (i : ℕ), i < 2^b → ∀ (j : ℕ), j < 2^b →
        h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n), δ n ≤ T n i-Real.log n) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n),
        ∀ j ∈ Finset.Ico (lo n) (hi n), i ≤ j → T n i ≤ T n j) →
      let J := ∑ n ∈ S, w n*(∑ i ∈ Finset.Ico (lo n) (hi n),
        (ownerWeight N (Real.log n/T n i)*a i*
          ZetaRieszGlobalCurvature.cutoffSlope (D i) n)/(T n i-Real.log n));
      let K := Real.sqrt ((∑ n ∈ S, (w n/δ n)^2)*36*(((b+1 : ℕ) : ℝ)^2)*
        (E*X)*(∑ i ∈ Finset.range (2^b), (a i)^2));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_density_mean_bound hh
  refine ⟨E,hE,fun b N X S R D a w T lo hi δ hN hδ hS hSF hR hD hsep hr hgap hmono => ?_⟩
  let x : ℕ → ℕ → ℝ := fun n i => Real.log n/T n i
  let v : ℕ → ℕ → ℝ := fun n i => δ n/(T n i-Real.log n)
  have hT n (hn : n ∈ S) i (hi' : i ∈ Finset.Ico (lo n) (hi n)) : 0 < T n i := by
    have := hgap n hn i hi'
    linarith [Real.log_natCast_nonneg n,hδ n hn]
  have hx n (hn : n ∈ S) i (hi' : i ∈ Finset.Ico (lo n) (hi n)) :
      x n i ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (Real.log_natCast_nonneg n) (hT n hn i hi').le,?_⟩
    exact (div_le_one (hT n hn i hi')).mpr (by linarith [hgap n hn i hi',hδ n hn])
  have hd n (hn : n ∈ S) i (hli : lo n ≤ i) (hih : i+1 < hi n) : x n (i+1) ≤ x n i :=
    div_le_div_of_nonneg_left (Real.log_natCast_nonneg n)
      (hT n hn i (Finset.mem_Ico.mpr ⟨hli,by omega⟩))
      (hmono n hn i (Finset.mem_Ico.mpr ⟨hli,by omega⟩)
        (i+1) (Finset.mem_Ico.mpr ⟨by omega,hih⟩) (by omega))
  have hv n (hn : n ∈ S) i (hi' : i ∈ Finset.Ico (lo n) (hi n)) :
      0 ≤ v n i ∧ v n i ≤ 1 :=
    ⟨div_nonneg (hδ n hn).le ((hδ n hn).le.trans (hgap n hn i hi')),
      (div_le_one ((hδ n hn).trans_le (hgap n hn i hi'))).mpr (hgap n hn i hi')⟩
  have hvd n (hn : n ∈ S) i (hi' : i ∈ Finset.Ico (lo n) (hi n))
      j (hj' : j ∈ Finset.Ico (lo n) (hi n)) (hij : i ≤ j) : v n j ≤ v n i :=
    div_le_div_of_nonneg_left (hδ n hn).le ((hδ n hn).trans_le (hgap n hn i hi'))
      (sub_le_sub_right (hmono n hn i hi' j hj' hij) _)
  have hm := hmean b N X S R a x v lo hi 1 hN (by norm_num)
    hS hSF hR hsep hr hx hd hv hvd
  let F := fun n => ∑ i ∈ Finset.Ico (lo n) (hi n),
    v n i*(ownerWeight N (x n i)*a i*
      (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0))
  have hs := (Finset.sum_mul_sq_le_sq_mul_sq S (fun n => w n/δ n) F).trans
    (mul_le_mul_of_nonneg_left hm (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have he : (∑ n ∈ S, w n*(∑ i ∈ Finset.Ico (lo n) (hi n),
      (ownerWeight N (Real.log n/T n i)*a i*
        ZetaRieszGlobalCurvature.cutoffSlope (D i) n)/(T n i-Real.log n))) =
      ∑ n ∈ S, (w n/δ n)*F n := by
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [F]
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi'
    have hiB : i < 2^b := ((Finset.mem_Ico.mp hi').2).trans_le (hr n hn).2
    rw [ZetaRieszCrossCutoff.cutoffSlope_eq_prefix (R i) (D i) (hD i hiB).1 (hD i hiB).2
      (by have := (Finset.mem_Ioc.mp (hS hn)).1; omega)]
    dsimp only [x,v]
    field_simp [(hδ n hn).ne']
  dsimp only
  rw [he]
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs,Real.sq_sqrt (by positivity)]
  simpa only [mul_assoc,one_pow,one_mul] using hs

end RiemannGaussian.ZetaRieszOwnerDensity
