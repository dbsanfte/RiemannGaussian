/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSquarefreeSeparatedMean
import RiemannGaussian.ZetaRieszOwnerMaximal

/-!
# A linear joint mean with the literal varying owner allocation

The original owner and cofactor-dependent interval endpoints are retained.
The new separated squarefree mean pays every binary-block counting error.
Only the proved logarithmic-depth maximal price and explicit coefficient
and weight energies remain; no source-normalized smallness is assumed.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszOwnerUniformMean
open ZetaRieszOwnerMaximal

private theorem dyadic_mean_le (S : Finset ℕ) (M : ℕ)
    (F : ℕ → ℕ → ℕ → ℝ) (a : ℕ → ℝ) (E : ℝ)
    (hb : ∀ o m : ℕ, o+m ≤ M →
      (∑ n ∈ S, F n o m) ≤ E*(∑ i ∈ Finset.Ico o (o+m), a i))
    (b o : ℕ) (hbo : o+2^b ≤ M) :
    (∑ n ∈ S, dyadicCost (F n) b o) ≤
      ((b+1 : ℕ) : ℝ)*E*(∑ i ∈ Finset.Ico o (o+2^b), a i) := by
  induction b generalizing o with
  | zero => simpa [dyadicCost] using hb o 1 (by simpa using hbo)
  | succ b ih =>
    have hp : 2^(b+1) = 2^b+2^b := by rw [pow_succ]; omega
    have hend : o+2^b+2^b = o+2^(b+1) := by rw [hp]; omega
    have hhalf : 2^b ≤ 2^(b+1) := by rw [hp]; exact Nat.le_add_right _ _
    have hl := ih o ((Nat.add_le_add_left hhalf o).trans hbo)
    have hr := ih (o+2^b) (by rw [hend]; exact hbo)
    rw [hend] at hr
    have hroot := hb o (2^(b+1)) hbo
    have hsplit := Finset.sum_Ico_consecutive a (Nat.le_add_right o (2^b))
      (Nat.add_le_add_left hhalf o)
    simp only [dyadicCost,Finset.sum_add_distrib]
    rw [← hsplit] at hroot ⊢
    push_cast at hl hr ⊢
    nlinarith only [hl,hr,hroot]

/-- The varying owner and both moving interval endpoints now have a
joint linear squarefree mean. There is NO unpaid block-floor term.
The remaining price is 36*(b+1)^2 for 2^b periods. -/
theorem exists_owner_interval_mean_bound {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (b N X : ℕ) (S : Finset ℕ) (R : ℕ → ℕ)
      (a : ℕ → ℝ) (x : ℕ → ℕ → ℝ) (lo hi : ℕ → ℕ),
      32 ≤ N → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∀ i < 2^b, 0 < R i) →
      (∀ (i : ℕ), i < 2^b → ∀ (j : ℕ), j < 2^b →
        h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n), x n i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ n ∈ S, ∀ i, lo n ≤ i → i+1 < hi n → x n (i+1) ≤ x n i) →
      (∑ n ∈ S, (∑ i ∈ Finset.Ico (lo n) (hi n),
        ownerWeight N (x n i)*a i*
          (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0))^2) ≤
        36*(((b+1 : ℕ) : ℝ)^2)*(E*X)*(∑ i ∈ Finset.range (2^b), (a i)^2) := by
  obtain ⟨E,hE,hmean⟩ := ZetaRieszSquarefreeSeparatedMean.exists_separated_mean_bound hh
  refine ⟨E,hE,fun b N X S R a x lo hi hN hS hSF hR hsep hr hx hdec => ?_⟩
  let f := fun n i => a i*(∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0)
  let F := fun n o m => (∑ i ∈ Finset.Ico o (o+m), f n i)^2
  have hs : (∑ n ∈ S, (∑ i ∈ Finset.Ico (lo n) (hi n), ownerWeight N (x n i)*f n i)^2) ≤
      36*((b+1 : ℕ) : ℝ)*(∑ n ∈ S, dyadicCost (F n) b 0) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun n hn => owner_interval_sq_le_dyadicCost hN b (lo n) (hi n)
      (f n) (x n) (hr n hn).1 (hr n hn).2 (hx n hn) (hdec n hn))
  have hb o m (hom : o+m ≤ 2^b) : (∑ n ∈ S, F n o m) ≤
      (E*X)*(∑ i ∈ Finset.Ico o (o+m), (a i)^2) := by
    have hI i (hi : i ∈ Finset.Ico o (o+m)) : i < 2^b := by
      have := (Finset.mem_Ico.mp hi).2
      omega
    exact hmean (Finset.Ico o (o+m)) R a X S hS hSF
      (fun i hi => hR i (hI i hi)) (fun i hi j hj => hsep i (hI i hi) j (hI j hj))
  have hd := dyadic_mean_le S (2^b) F (fun i => (a i)^2) (E*X) hb b 0 (by omega)
  simp only [Nat.zero_add,Nat.Ico_zero_eq_range] at hd
  have ht := hs.trans (mul_le_mul_of_nonneg_left hd (by positivity))
  simpa only [f,pow_two,mul_assoc] using ht

/-- The improved owner estimate gives both signed sides of the joint
sum, keeping the exact cofactor dependence covered by the maximal theorem. -/
theorem exists_owner_interval_signed_bounds {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (b N X : ℕ) (S : Finset ℕ) (R : ℕ → ℕ)
      (a w : ℕ → ℝ) (x : ℕ → ℕ → ℝ) (lo hi : ℕ → ℕ),
      32 ≤ N → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∀ i < 2^b, 0 < R i) →
      (∀ (i : ℕ), i < 2^b → ∀ (j : ℕ), j < 2^b →
        h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n), x n i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ n ∈ S, ∀ i, lo n ≤ i → i+1 < hi n → x n (i+1) ≤ x n i) →
      let J := ∑ n ∈ S, w n*(∑ i ∈ Finset.Ico (lo n) (hi n),
        ownerWeight N (x n i)*a i*
          (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0));
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*36*(((b+1 : ℕ) : ℝ)^2)*
        (E*X)*(∑ i ∈ Finset.range (2^b), (a i)^2));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_owner_interval_mean_bound hh
  refine ⟨E,hE,fun b N X S R a w x lo hi hN hS hSF hR hsep hr hx hd => ?_⟩
  dsimp only
  let F := fun n => ∑ i ∈ Finset.Ico (lo n) (hi n), ownerWeight N (x n i)*a i*
    (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0)
  have hm := hmean b N X S R a x lo hi hN hS hSF hR hsep hr hx hd
  have hs := (Finset.sum_mul_sq_le_sq_mul_sq S w F).trans
    (mul_le_mul_of_nonneg_left hm (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs,Real.sq_sqrt (by positivity)]
  simpa only [F,mul_assoc] using hs

/-- The original strict Riesz slopes retain literal logarithmic owner
shares and moving radial lengths, with the linear joint arithmetic budget. -/
theorem exists_owner_slope_bounds {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (b N X : ℕ) (S : Finset ℕ) (R : ℕ → ℕ)
      (D a w : ℕ → ℝ) (T : ℕ → ℕ → ℝ) (lo hi : ℕ → ℕ),
      32 ≤ N → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∀ i < 2^b, 0 < R i) →
      (∀ i < 2^b, (R i : ℝ) < Real.exp (D i) ∧ Real.exp (D i) ≤ R i+1) →
      (∀ (i : ℕ), i < 2^b → ∀ (j : ℕ), j < 2^b →
        h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n), 0 < T n i ∧ Real.log n ≤ T n i) →
      (∀ n ∈ S, ∀ i, lo n ≤ i → i+1 < hi n → T n i ≤ T n (i+1)) →
      let J := ∑ n ∈ S, w n*(∑ i ∈ Finset.Ico (lo n) (hi n),
        ownerWeight N (Real.log n/T n i)*a i*ZetaRieszGlobalCurvature.cutoffSlope (D i) n);
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*36*(((b+1 : ℕ) : ℝ)^2)*
        (E*X)*(∑ i ∈ Finset.range (2^b), (a i)^2));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_owner_interval_signed_bounds hh
  refine ⟨E,hE,fun b N X S R D a w T lo hi hN hS hSF hR hD hsep hr hT hmono => ?_⟩
  let x : ℕ → ℕ → ℝ := fun n i => Real.log n/T n i
  have hx n (hn : n ∈ S) i (hi : i ∈ Finset.Ico (lo n) (hi n)) :
      x n i ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (Real.log_natCast_nonneg n) (hT n hn i hi).1.le,
      (div_le_one (hT n hn i hi).1).mpr (hT n hn i hi).2⟩
  have hd n (hn : n ∈ S) i (hli : lo n ≤ i) (hih : i+1 < hi n) : x n (i+1) ≤ x n i :=
    div_le_div_of_nonneg_left (Real.log_natCast_nonneg n)
      (hT n hn i (Finset.mem_Ico.mpr ⟨hli,by omega⟩)).1 (hmono n hn i hli hih)
  have ht := hbound b N X S R a w x lo hi hN hS hSF hR hsep hr hx hd
  dsimp only at ht ⊢
  have he : (∑ n ∈ S, w n*(∑ i ∈ Finset.Ico (lo n) (hi n),
      ownerWeight N (Real.log n/T n i)*a i*ZetaRieszGlobalCurvature.cutoffSlope (D i) n)) =
      ∑ n ∈ S, w n*(∑ i ∈ Finset.Ico (lo n) (hi n), ownerWeight N (x n i)*a i*
        (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    apply Finset.sum_congr rfl
    intro i hi'
    have hiB : i < 2^b := ((Finset.mem_Ico.mp hi').2).trans_le (hr n hn).2
    rw [ZetaRieszCrossCutoff.cutoffSlope_eq_prefix (R i) (D i) (hD i hiB).1 (hD i hiB).2
      (by have := (Finset.mem_Ioc.mp (hS hn)).1; omega)]
  rw [he]
  exact ht

end RiemannGaussian.ZetaRieszOwnerUniformMean
