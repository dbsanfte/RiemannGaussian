/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryPhaseQuadrature
import RiemannGaussian.SuzukiCarryPhaseHolomorphy

/-!
# Exact signed phase lags

The diagonal cancels before any integration. All positive lags and both
ordered incidences are retained. This is the finite algebraic bridge for
the all-jet source gate, not a signed prime-sum estimate.
-/

namespace RiemannGaussian.SuzukiCarryPhaseLag
noncomputable section
open Complex MeasureTheory Set Filter
open SuzukiCarryMellinLimit SuzukiCarryPhaseQuadrature
open scoped BigOperators Topology ComplexConjugate

/-- Finite modulated profile with its literal real weights and locations. -/
def finiteProfile (K : ℕ) (w v : ℕ → ℝ) (tau : ℝ) : ℂ :=
  ∑ n ∈ Finset.range K, (w n : ℂ)*Complex.exp (I*tau*v n)

private theorem product_re (w z v a tau : ℝ) :
    (((w : ℂ)*Complex.exp (I*tau*v))*
      conj ((z : ℂ)*Complex.exp (I*tau*a))).re = w*z*Real.cos (tau*(v-a)) := by
  have he : ((w : ℂ)*Complex.exp (I*tau*v))*
      conj ((z : ℂ)*Complex.exp (I*tau*a)) =
      ((w*z : ℝ) : ℂ)*Complex.exp (((tau*(v-a) : ℝ) : ℂ)*I) := by
    simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
      Complex.conj_I]
    rw [show (w : ℂ)*Complex.exp (I*tau*v)*
      ((z : ℂ)*Complex.exp (-I*tau*a)) =
      ((w*z : ℝ) : ℂ)*(Complex.exp (I*tau*v)*Complex.exp (-I*tau*a)) by
        push_cast; ring,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_ofReal_mul_I_re]

theorem finiteProfile_norm_sq (K : ℕ) (w v : ℕ → ℝ) (tau : ℝ) :
    ‖finiteProfile K w v tau‖^2 =
      ∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K,
        w i*w j*Real.cos (tau*(v i-v j)) := by
  have he : ‖finiteProfile K w v tau‖^2 =
      (finiteProfile K w v tau*conj (finiteProfile K w v tau)).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [he]
  unfold finiteProfile
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hr (f : ℕ → ℂ) : (∑ n ∈ Finset.range K, f n).re =
      ∑ n ∈ Finset.range K, (f n).re := map_sum Complex.reAddGroupHom f _
  simp_rw [hr]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact product_re _ _ _ _ _

/-- A symmetric zero-diagonal array is exactly twice its strict upper
triangle. No pointwise signed contribution is discarded. -/
theorem symmetric_sum (K : ℕ) (g : ℕ → ℕ → ℝ)
    (hs : ∀ i j, g i j = g j i) (hd : ∀ i, g i i = 0) :
    (∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K, g i j) =
      2*(∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K, if i < j then g i j else 0) := by
  have he (i j : ℕ) : g i j =
      (if i < j then g i j else 0)+(if j < i then g i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · rw [ite_eq_left h, ite_eq_right (by omega), add_zero]
    · subst j; simp [hd]
    · rw [ite_eq_right (by omega), ite_eq_left h, zero_add]
  have hy : (∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K, g i j) =
      ∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K,
        ((if i < j then g i j else 0)+(if j < i then g i j else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_congr rfl (fun j _ => he i j)
  rw [hy]
  simp only [Finset.sum_add_distrib]
  have hx : (∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K,
      if j < i then g i j else 0) =
      ∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K,
        if i < j then g i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  rw [hx]
  ring

/-- Strict upper-triangular incidences of a finite profile. -/
def upperPairs (K : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range K).product (Finset.range K)).filter (fun p => p.1 < p.2)

/-- The same incidences indexed by positive lag and starting location. -/
def lagPairs (K : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range K).product (Finset.range K)).filter (fun p => p.2+p.1+1 < K)

/-- Exact incidence reindexing by positive lag. -/
theorem upperPairs_eq_lags (K : ℕ) (g : ℕ → ℕ → ℝ) :
    (∑ p ∈ upperPairs K, g p.1 p.2) =
      ∑ p ∈ lagPairs K, g p.2 (p.2+p.1+1) := by
  apply Finset.sum_bij (fun p _ => (p.2-p.1-1,p.1))
  · intro p hp
    simp only [upperPairs, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_range] at hp
    simp only [lagPairs, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega,hp.1.1⟩,by omega⟩
  · intro p hp q hq he
    simp only [upperPairs, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_range] at hp hq
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    dsimp at h1 h2
    apply Prod.ext <;> omega
  · intro q hq
    simp only [lagPairs, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_range] at hq
    refine ⟨(q.2,q.2+q.1+1),?_,?_⟩
    · simp only [upperPairs, Finset.mem_filter, Finset.product_eq_sprod,
        Finset.mem_product, Finset.mem_range]
      exact ⟨⟨hq.1.2,hq.2⟩,by omega⟩
    · apply Prod.ext <;> omega
  · intro p hp
    simp only [upperPairs, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_range] at hp
    have he : p.1+(p.2-p.1-1)+1 = p.2 := by omega
    change g p.1 p.2 = g p.1 (p.1+(p.2-p.1-1)+1)
    rw [he]

/-- Exact finite contrast; the full phase correlation appears only
through the positive lag, with its original signed product. -/
theorem finiteProfile_contrast_eq_lags (K : ℕ) (w v : ℕ → ℝ) (tau : ℝ) :
    ‖finiteProfile K w v tau‖^2-‖finiteProfile K w v 0‖^2 =
      2*(∑ p ∈ lagPairs K,
        w p.2*w (p.2+p.1+1)*
          (Real.cos (tau*(v p.2-v (p.2+p.1+1)))-1)) := by
  rw [finiteProfile_norm_sq, finiteProfile_norm_sq]
  simp only [zero_mul, Real.cos_zero, mul_one]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib,
    show ∀ i j : ℕ, w i*w j*Real.cos (tau*(v i-v j))-w i*w j =
      w i*w j*(Real.cos (tau*(v i-v j))-1) by intro i j; ring]
  rw [symmetric_sum K (fun i j => w i*w j*(Real.cos (tau*(v i-v j))-1))
    (fun i j => by rw [show tau*(v j-v i) = -(tau*(v i-v j)) by ring,
      Real.cos_neg]; ring) (fun i => by simp)]
  have he : (∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K,
      if i < j then w i*w j*(Real.cos (tau*(v i-v j))-1) else 0) =
      ∑ p ∈ upperPairs K, w p.1*w p.2*(Real.cos (tau*(v p.1-v p.2))-1) := by
    rw [upperPairs, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  rw [he]
  congr 1
  exact upperPairs_eq_lags K (fun i j => w i*w j*(Real.cos (tau*(v i-v j))-1))

/-- Signed tent weight at the original carry grid point. -/
def gridWeight (x : ℝ) (n : ℕ) : ℝ := (-1 : ℝ)^n*tent ((n : ℝ)*x/2)

/-- Physical location of the original carry grid point. -/
def gridLocation (x : ℝ) (n : ℕ) : ℝ := (n : ℝ)*x/2

theorem profile_eq_grid (tau x : ℝ) :
    profile tau x = -finiteProfile (jumpCount x+1) (gridWeight x) (gridLocation x) tau := by
  unfold finiteProfile
  rw [Finset.sum_range_succ']
  simp only [gridWeight, gridLocation, Nat.cast_zero, zero_mul, zero_div,
    tent_eq_zero_of_le (by norm_num : (0 : ℝ) ≤ 1), mul_zero,
    Complex.ofReal_zero, zero_mul, add_zero]
  rw [← Finset.sum_neg_distrib]
  unfold profile amplitude
  apply Finset.sum_congr rfl
  intro k _
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one, pow_succ]
  ring

private theorem grid_zero {x : ℝ} (hx : 0 < x) {n : ℕ}
    (hn : jumpCount x ≤ n) : tent ((n : ℝ)*x/2) = 0 := by
  have hc := (Nat.le_ceil (6/x)).trans (show (jumpCount x : ℝ) ≤ n by exact_mod_cast hn)
  have hh := (div_le_iff₀ hx).mp hc
  exact tent_eq_zero_of_ge (by linarith)

private theorem overlap_grid_eq {x : ℝ} (hx : 0 < x) (v : ℝ) :
    (∑ n ∈ Finset.range (jumpCount x+1),
      tent ((n : ℝ)*x/2)*tent ((n : ℝ)*x/2+v)) = overlapSum v (x/2) := by
  have hx2 : 0 < x/2 := by positivity
  have he : 3/(x/2) = 6/x := by field_simp; ring
  have hs : Finset.range (⌊3/(x/2)⌋₊+1) ⊆ Finset.range (jumpCount x+1) := by
    apply Finset.range_mono
    unfold jumpCount
    rw [he]
    exact Nat.add_le_add_right (Nat.floor_le_ceil _) 1
  unfold overlapSum
  simp only [mul_div_assoc]
  apply (Finset.sum_subset hs ?_).symm
  intro n _ hn
  have hn' : ⌊3/(x/2)⌋₊+1 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
  have hf := (Nat.lt_floor_add_one (3/(x/2))).trans_le
    (show (⌊3/(x/2)⌋₊ : ℝ)+1 ≤ n by exact_mod_cast hn')
  have hp := (div_lt_iff₀ hx2).mp hf
  rw [tent_eq_zero_of_ge (by linarith : 3 ≤ (n : ℝ)*(x/2)), zero_mul]

/-- Signed contribution of lag h+1 to the literal phase contrast. -/
def literalLag (tau x : ℝ) (h : ℕ) : ℝ :=
  (-1 : ℝ)^(h+1)*(Real.cos (tau*((h+1 : ℕ) : ℝ)*x/2)-1)*
    overlapSum (((h+1 : ℕ) : ℝ)*x/2) (x/2)

private theorem grid_pair {x : ℝ} (n h : ℕ) (tau : ℝ) :
    gridWeight x n*gridWeight x (n+h+1)*
      (Real.cos (tau*(gridLocation x n-gridLocation x (n+h+1)))-1) =
      (-1 : ℝ)^(h+1)*(Real.cos (tau*((h+1 : ℕ) : ℝ)*x/2)-1)*
        (tent ((n : ℝ)*x/2)*tent ((n : ℝ)*x/2+((h+1 : ℕ) : ℝ)*x/2)) := by
  have he : (-1 : ℝ)^n*(-1 : ℝ)^(n+h+1) = (-1 : ℝ)^(h+1) := by
    rw [← pow_add, show n+(n+h+1) = 2*n+(h+1) by omega, pow_add, pow_mul]
    norm_num
  have hl : gridLocation x n-gridLocation x (n+h+1) = -(((h+1 : ℕ) : ℝ)*x/2) := by
    unfold gridLocation; push_cast; ring
  have ht : ((n+h+1 : ℕ) : ℝ)*x/2 = (n : ℝ)*x/2+((h+1 : ℕ) : ℝ)*x/2 := by
    push_cast; ring
  rw [hl, mul_neg, Real.cos_neg]
  unfold gridWeight
  rw [ht]
  calc
    _ = ((-1 : ℝ)^n*(-1 : ℝ)^(n+h+1))*
        (Real.cos (tau*(((h+1 : ℕ) : ℝ)*x/2))-1)*
        (tent ((n : ℝ)*x/2)*tent ((n : ℝ)*x/2+((h+1 : ℕ) : ℝ)*x/2)) := by ring
    _ = _ := by rw [he]; congr 2; congr 1; congr 1; ring

/-- The complete literal phase contrast is an exactly signed lag sum.
The infinite notation is pointwise finite, with every carry jump retained. -/
theorem profile_contrast_eq_lags {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    ‖profile tau x‖^2-‖profile 0 x‖^2 = 2*(∑' h : ℕ, literalLag tau x h) := by
  rw [profile_eq_grid, profile_eq_grid, norm_neg, norm_neg,
    finiteProfile_contrast_eq_lags]
  have he : (∑ p ∈ lagPairs (jumpCount x+1),
      gridWeight x p.2*gridWeight x (p.2+p.1+1)*
        (Real.cos (tau*(gridLocation x p.2-gridLocation x (p.2+p.1+1)))-1)) =
      ∑ h ∈ Finset.range (jumpCount x+1), literalLag tau x h := by
    rw [lagPairs, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro h _
    have hr : (∑ n ∈ Finset.range (jumpCount x+1),
        if n+h+1 < jumpCount x+1 then
          gridWeight x n*gridWeight x (n+h+1)*
            (Real.cos (tau*(gridLocation x n-gridLocation x (n+h+1)))-1) else 0) =
        ∑ n ∈ Finset.range (jumpCount x+1),
          gridWeight x n*gridWeight x (n+h+1)*
            (Real.cos (tau*(gridLocation x n-gridLocation x (n+h+1)))-1) := by
      apply Finset.sum_congr rfl
      intro n _
      split_ifs with hn
      · rfl
      · have hz := grid_zero hx (n := n+h+1) (by omega)
        have hw : gridWeight x (n+h+1) = 0 := by
          unfold gridWeight; rw [hz, mul_zero]
        rw [hw, mul_zero, zero_mul]
    rw [hr]
    simp_rw [grid_pair]
    rw [← Finset.mul_sum, overlap_grid_eq hx]
    rfl
  rw [he]
  congr 1
  symm
  apply tsum_eq_sum
  intro h hh
  have hh' : jumpCount x+1 ≤ h := by simpa only [Finset.mem_range, not_lt] using hh
  have hn : jumpCount x ≤ h+1 := by omega
  have hc := (Nat.le_ceil (6/x)).trans
    (show (jumpCount x : ℝ) ≤ ((h+1 : ℕ) : ℝ) by exact_mod_cast hn)
  have hp := (div_le_iff₀ hx).mp hc
  rw [literalLag, overlapSum_eq_zero (by linarith), mul_zero]

end
end RiemannGaussian.SuzukiCarryPhaseLag
