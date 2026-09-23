/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovNarrowResonance
import RiemannGaussian.VinogradovDampedSaving

/-!
# Actual Dirichlet cancellation with fixed numerical coefficients

The improved homogeneous moments enter the original polynomial product,
Taylor remainder, shift average, every partial block and literal damped
zeta coefficient. The full original block has bound
5*M^(4-1/(8192*k^2)), for k>=12 and M>=(7k+1)k on the stated height
rectangle. No moment hypothesis or unevaluated degree coefficient remains.
Global scale coverage and the VK zero detector remain separate obligations.
-/

namespace RiemannGaussian.VinogradovNarrowDirichlet
noncomputable section
open scoped BigOperators
open VinogradovNarrowResonance VinogradovRectanglePowerSaving
open VinogradovKorobovBlock VinogradovKorobovDamping VinogradovDampedSaving

/-- The literal shifted imaginary-power product has the evaluated coefficient,
with the entire Taylor remainder paid. -/
theorem product_bound (k : ℕ) (hk : 12 ≤ k)
    (M : ℕ) (hM : 1 ≤ M) (hrM : (7 * k + 1) * k ≤ M)
    (t z : ℝ) (htlo : (M : ℝ) ^ (2 * k - 2) ≤ t) (hthi : t ≤ (M : ℝ) ^ (2 * k))
    (hzlo : (M : ℝ) ^ 4 ≤ z) (hzhi : z ≤ 4 * (M : ℝ) ^ 4)
    (B : Finset ℕ) (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) :
    ‖∑ b : Fin M, ∑ c ∈ B, dirichletTerm t z ((b.val + 1) * c)‖ ≤
      ((3 : ℝ)) * (M : ℝ) ^ (2 - 1 / (8192 * (k : ℝ) ^ 2)) := by
  let alpha := 2 - 1 / (8192 * (k : ℝ) ^ 2)
  have hden : 1 ≤ 8192 * (k : ℝ) ^ 2 := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hs := one_le_pow₀ (n := 2) hk1
    nlinarith only [hs]
  have halpha : 0 ≤ alpha := by
    have hdiv : 1 / (8192 * (k : ℝ) ^ 2) ≤ 1 := (div_le_one (zero_lt_one.trans_le hden)).mpr hden
    dsimp only [alpha]
    linarith only [hdiv]
  let C := (2 : ℝ)
  have hM1 : 1 ≤ M := hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  let T := t
  let Z := z
  have hZ : 0 < Z := (pow_pos hMpos 4).trans_le hzlo
  have he : (∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBlock.dirichletTerm T Z ((b.val + 1) * c)) =
      VinogradovKorobovBlock.basePhase T Z *
        ∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBilinearPhase.logarithmicPhase T Z ((b.val + 1 : ℕ) : ℝ) c := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    simpa only [zero_add, Nat.cast_zero, add_zero] using
      VinogradovKorobovBlock.dirichletTerm_shift hZ T 0 (b.val + 1) c
  change ‖∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBlock.dirichletTerm T Z ((b.val + 1) * c)‖ ≤ _
  rw [he, norm_mul, VinogradovKorobovBlock.norm_basePhase, one_mul]
  have hpoly := polynomial_bound k hk M hM hrM t z htlo hthi hzlo hzhi B hB
  have herr := rectangle_logarithmic_error_le k (by omega : 0 < M) B hB
    ((pow_pos hMpos _).trans_le htlo).le hthi hzlo
  let L := ∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBilinearPhase.logarithmicPhase T Z ((b.val + 1 : ℕ) : ℝ) c
  let P := ∑ b : Fin M, ∑ c ∈ B, VinogradovKorobovBilinearPhase.polynomialPhase k T Z ((b.val + 1 : ℕ) : ℝ) c
  have hnorm : ‖L‖ ≤ ‖P‖ + ‖L - P‖ := by
    calc
      _ = ‖P + (L - P)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have hpow : 1 ≤ (M : ℝ) ^ alpha := Real.one_le_rpow (by exact_mod_cast hM1) halpha
  have herror : 1 / ((k : ℝ) + 1) ≤ (M : ℝ) ^ alpha := by
    apply le_trans _ hpow
    apply (div_le_one (by positivity)).mpr
    linarith only [Nat.cast_nonneg (α := ℝ) k]
  have htotal := hnorm.trans (add_le_add hpoly herr)
  calc
    _ ≤ C * (M : ℝ) ^ alpha + 1 / ((k : ℝ) + 1) := htotal
    _ ≤ (C + 1) * (M : ℝ) ^ alpha := by nlinarith only [herror]
    _ = _ := by norm_num [C, alpha]

/-- Every original partial block retains the explicit cancellation coefficient
and the full normalized shift-boundary cost. -/
theorem partial_block_bound (k : ℕ) (hk : 12 ≤ k)
    (M : ℕ) (hM : 1 ≤ M) (hrM : (7 * k + 1) * k ≤ M)
    (t z : ℝ) (htlo : (M : ℝ) ^ (2 * k - 2) ≤ t) (hthi : t ≤ (M : ℝ) ^ (2 * k))
    (hzlo : (M : ℝ) ^ 4 ≤ z) (hzhi : z ≤ 2 * (M : ℝ) ^ 4)
    (L : ℕ) (hL : L ≤ 2 * M ^ 4) :
    ‖block (dirichletTerm t z) L‖ ≤
      ((3 : ℝ)) * L * (M : ℝ) ^ (-(1 / (8192 * (k : ℝ) ^ 2))) + 2 * (M : ℝ) ^ 2 := by
  let C := (3 : ℝ)
  have hM1 : 1 ≤ M := hM
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM1
  have hz : 0 < z := (pow_pos hMr 4).trans_le hzlo
  let delta := 1 / (8192 * (k : ℝ) ^ 2)
  have hp := VinogradovDirichletSaving.block_bound_of_product_bound (by omega : 0 < M) hz t
    (C * (M : ℝ) ^ (2 - delta)) (by
      intro n hn
      apply product_bound k hk M hM hrM t (z + n) htlo hthi
        (hzlo.trans (le_add_of_nonneg_right (Nat.cast_nonneg n)))
      · have hn' : (n : ℝ) ≤ 2 * (M : ℝ) ^ 4 := by
          exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hn)).trans hL
        linarith only [hzhi, hn']
      · intro b hb
        exact Finset.mem_Icc.mp hb)
  apply hp.trans_eq
  congr 1
  rw [show 2 - delta = 2 + (-delta) by ring, Real.rpow_add hMr,
    Real.rpow_two]
  field_simp
  rfl

/-- The original full block has coefficient five, an explicit inverse-square
saving and a polynomial starting condition on its degree. -/
theorem block_bound (k : ℕ) (hk : 12 ≤ k)
    (M : ℕ) (hM : 1 ≤ M) (hrM : (7 * k + 1) * k ≤ M)
    (t z : ℝ) (htlo : (M : ℝ) ^ (2 * k - 2) ≤ t) (hthi : t ≤ (M : ℝ) ^ (2 * k))
    (hzlo : (M : ℝ) ^ 4 ≤ z) (hzhi : z ≤ 2 * (M : ℝ) ^ 4) :
    ‖block (dirichletTerm t z) (M ^ 4)‖ ≤
      ((5 : ℝ)) * (M : ℝ) ^ (4 - 1 / (8192 * (k : ℝ) ^ 2)) := by
  let C := (3 : ℝ)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMr := zero_lt_one.trans_le hM1
  have hb := partial_block_bound k hk M hM hrM t z htlo hthi hzlo hzhi (M ^ 4) (by omega)
  let delta := 1 / (8192 * (k : ℝ) ^ 2)
  have hden : 1 ≤ 8192 * (k : ℝ) ^ 2 := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hs := one_le_pow₀ (n := 2) hk1
    nlinarith only [hs]
  have hd : delta ≤ 1 := (div_le_one (zero_lt_one.trans_le hden)).mpr hden
  have hpow : (M : ℝ) ^ 2 ≤ (M : ℝ) ^ (4 - delta) := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hM1 (by linarith only [hd])
  have he : C * ((M ^ 4 : ℕ) : ℝ) * (M : ℝ) ^ (-delta) =
      C * (M : ℝ) ^ (4 - delta) := by
    push_cast
    rw [mul_assoc, ← Real.rpow_natCast (M : ℝ) 4, ← Real.rpow_add hMr]
    congr 2
  change _ ≤ C * ((M ^ 4 : ℕ) : ℝ) * (M : ℝ) ^ (-delta) + 2 * (M : ℝ) ^ 2 at hb
  rw [he] at hb
  calc
    _ ≤ C * (M : ℝ) ^ (4 - delta) + 2 * (M : ℝ) ^ 2 := hb
    _ ≤ ((5 : ℝ)) * (M : ℝ) ^ (4 - delta) := by
      dsimp only [C]
      nlinarith only [hpow]

/-- Every nonnegative decreasing amplitude retains the explicit degree cost,
its actual total mass and only its initial weight in the boundary payment. -/
theorem weighted_block_bound (k : ℕ) (hk : 12 ≤ k)
    (M : ℕ) (hM : 1 ≤ M) (hrM : (7 * k + 1) * k ≤ M)
    (t z : ℝ) (htlo : (M : ℝ) ^ (2 * k - 2) ≤ t) (hthi : t ≤ (M : ℝ) ^ (2 * k))
    (hzlo : (M : ℝ) ^ 4 ≤ z) (hzhi : z ≤ 2 * (M : ℝ) ^ 4)
    (N : ℕ) (hN : N + 1 ≤ 2 * M ^ 4) (w : ℕ → ℝ)
    (hw : ∀ n ≤ N, 0 ≤ w n) (hm : AntitoneOn w (Set.Icc 0 N)) :
    ‖∑ n ∈ Finset.range (N + 1), (w n : ℂ) * dirichletTerm t z n‖ ≤
      (((3 : ℝ)) * (M : ℝ) ^ (-(1 / (8192 * (k : ℝ) ^ 2)))) *
        (∑ n ∈ Finset.range (N + 1), w n) + 2 * (M : ℝ) ^ 2 * w 0 := by
  rw [weighted_identity]
  apply abelTransform_norm_affine_le w _ N hw hm
  intro n hn
  have hp := partial_block_bound k hk M hM hrM t z htlo hthi hzlo hzhi (n + 1) (by omega)
  convert hp using 1
  ring

/-- The actual damped zeta coefficients inherit a fully specified coefficient
at every admissible degree, height and block, without a moment hypothesis. -/
theorem feature_block_bound (k : ℕ) (hk : 12 ≤ k)
    (M : ℕ) (hM : 1 ≤ M) (hrM : (7 * k + 1) * k ≤ M) (s : ℂ) (hσ : 0 ≤ s.re)
    (htlo : (M : ℝ) ^ (2 * k - 2) ≤ s.im) (hthi : s.im ≤ (M : ℝ) ^ (2 * k))
    (a : ℕ) (halo : (M : ℝ) ^ 4 ≤ a) (hahi : (a : ℝ) ≤ 2 * (M : ℝ) ^ 4)
    (N : ℕ) (hN : N + 1 ≤ 2 * M ^ 4) :
    ‖∑ n ∈ Finset.range (N + 1), zetaPrimeFeature s (a + n)‖ ≤
      (((3 : ℝ)) * (M : ℝ) ^ (-(1 / (8192 * (k : ℝ) ^ 2)))) *
        (∑ n ∈ Finset.range (N + 1), zetaPrimeExpWeight s.re (a + n)) +
        2 * (M : ℝ) ^ 2 * zetaPrimeExpWeight s.re a := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have haR : (0 : ℝ) < a := (pow_pos hMr 4).trans_le halo
  have ha : 0 < a := by exact_mod_cast haR
  have hw (n : ℕ) (_hn : n ≤ N) : 0 ≤ zetaPrimeExpWeight s.re (a + n) :=
    (Real.exp_pos _).le
  have hm : AntitoneOn (fun n : ℕ => zetaPrimeExpWeight s.re (a + n)) (Set.Icc 0 N) := by
    intro i _ j _ hij
    apply DirichletSecondDerivativeBound.damping_antitoneOn hσ
    · change (0 : ℝ) < (a + i : ℕ)
      exact_mod_cast (show 0 < a + i by omega)
    · change (0 : ℝ) < (a + j : ℕ)
      exact_mod_cast (show 0 < a + j by omega)
    · exact_mod_cast (show a + i ≤ a + j by omega)
  simpa only [← feature_eq_damped s ha, Nat.add_zero] using
    weighted_block_bound k hk M hM hrM s.im a htlo hthi halo hahi N hN
      (fun n => zetaPrimeExpWeight s.re (a + n)) hw hm

end
end RiemannGaussian.VinogradovNarrowDirichlet
