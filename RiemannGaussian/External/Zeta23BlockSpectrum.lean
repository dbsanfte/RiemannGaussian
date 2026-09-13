/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.External.Zeta23InverseSamplingZeroSide

/-!
# Arbitrary block sizes for the retained simple-zero spectrum

The convex spectral remainder pays a full unit-capped off-diagonal energy
for a block of any finite size. Principal-block pinching is likewise
independent of block size. These statements retain every pair inside a
chosen block and support consecutive-window numerical certificates.
-/

namespace RiemannGaussian.Zeta23InverseSampling.ZeroBlockData
noncomputable section
open Matrix RHLinalg Zeta23.ZeroSide.RankTraceMult
open scoped BigOperators ComplexOrder MatrixOrder

/-- Every ordered off-diagonal pair, without a three-column restriction. -/
def offDiagEnergy {α : Type*} [Fintype α] [DecidableEq α]
    (K : Matrix α α ℂ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, ‖K i j‖ ^ 2

/-- The same ordered-pair energy with a zero diagonal on the full index
square; this form supports entrywise approximation estimates. -/
theorem offDiagEnergy_eq_sum_ite {α : Type*} [Fintype α] [DecidableEq α]
    (K : Matrix α α ℂ) :
    offDiagEnergy K = ∑ i, ∑ j, if i = j then 0 else ‖K i j‖ ^ 2 := by
  unfold offDiagEnergy
  apply Finset.sum_congr rfl
  intro i _
  have hset : Finset.univ.erase i =
      Finset.univ.filter (fun j => i ≠ j) := by
    ext j
    simp [ne_comm]
  rw [hset, Finset.sum_filter]
  simp only [ne_eq, ite_not]

/-- The diagonal and off-diagonal squared norms partition the Frobenius energy. -/
theorem frobSq_eq_diag_add_offDiag {α : Type*} [Fintype α] [DecidableEq α]
    (K : Matrix α α ℂ) :
    frobSq K = (∑ i, ‖K i i‖ ^ 2) + offDiagEnergy K := by
  rw [frobSq_eq_sum_norm_sq_local]
  unfold offDiagEnergy
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    (Finset.add_sum_erase Finset.univ (fun j => ‖K i j‖ ^ 2)
      (Finset.mem_univ i)).symm

/-- Off-diagonal energy is bounded by total squared spectral displacement
from one, with no assumption on the individual diagonal entries. -/
theorem offDiagEnergy_le_spectral_displacement {α : Type*}
    [Fintype α] [DecidableEq α] {K : Matrix α α ℂ} (hK : K.IsHermitian) :
    offDiagEnergy K ≤ ∑ i, (hK.eigenvalues i - 1) ^ 2 := by
  have hspec : (∑ i, (hK.eigenvalues i - 1) ^ 2) =
      frobSq K - 2 * rtrace K + Fintype.card α := by
    rw [rtrace_eq_sum_eigenvalues hK, frobSq_hermitian_eq_sum_sq_eigenvalues hK]
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_pow, mul_one]
  have hdiag : ∑ i, (2 * (K i i).re - 1) ≤ ∑ i, ‖K i i‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (‖K i i‖ - 1), Complex.re_le_norm (K i i)]
  have htrace : (∑ i, (K i i).re) = rtrace K := by
    simp [rtrace, trace]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, htrace] at hdiag
  rw [hspec]
  linarith [frobSq_eq_diag_add_offDiag K]

/-- The unit-capped energy estimate holds for every finite block. -/
theorem min_offDiagEnergy_one_le_simpleDefect {α : Type*}
    [Fintype α] [DecidableEq α] {K : Matrix α α ℂ} (hK : K.IsHermitian) :
    min (offDiagEnergy K) 1 ≤ ∑ i, simpleDefect (hK.eigenvalues i) := by
  by_cases hle : ∀ i, hK.eigenvalues i ≤ 2
  · have heq : (∑ i, simpleDefect (hK.eigenvalues i)) =
        ∑ i, (hK.eigenvalues i - 1) ^ 2 :=
      Finset.sum_congr rfl fun i _ => simpleDefect_eq_sq_sub_one (hle i)
    rw [heq]
    exact (min_le_left _ _).trans (offDiagEnergy_le_spectral_displacement hK)
  · push Not at hle
    obtain ⟨i, hi⟩ := hle
    have hone : 1 ≤ simpleDefect (hK.eigenvalues i) := by
      rw [simpleDefect_eq_two_mul_sub_three hi.le]
      linarith
    exact (min_le_right _ _).trans (hone.trans
      (Finset.single_le_sum (fun j _ => simpleDefect_nonneg _)
        (Finset.mem_univ i)))

/-- Convex spectral pinching for every finite principal-block size. -/
theorem sumGc_blocks_le_sumGc_eigenvalues
    {α : Type*} [Fintype α] [DecidableEq α]
    {β : Type*} [Fintype β] [DecidableEq β]
    {K : Matrix (α × β) (α × β) ℂ} (hK : K.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) :
    (∑ b, ∑ i, gc c
      ((hK.1.submatrix (fun j : α => (j, b))).eigenvalues i)) ≤
        ∑ p, gc c (hK.1.eigenvalues p) := by
  let H : β → Matrix (α) (α) ℂ :=
    fun b => K.submatrix (fun j : α => (j, b)) (fun j : α => (j, b))
  let hH : ∀ b, (H b).IsHermitian := fun b => hK.1.submatrix _
  let Ub : β → Matrix (α) (α) ℂ :=
    fun b => (hH b).eigenvectorUnitary
  let Umat : Matrix (α × β) (α × β) ℂ := Matrix.blockDiagonal Ub
  have hUstarU : Umatᴴ * Umat = 1 := by
    unfold Umat
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul,
      ← Matrix.blockDiagonal_one]
    congr 1
    funext b
    exact Unitary.coe_star_mul_self (hH b).eigenvectorUnitary
  let U : Matrix.unitaryGroup (α × β) ℂ :=
    ⟨Umat, Matrix.mem_unitaryGroup_iff'.2 (by
      simpa [Matrix.star_eq_conjTranspose] using hUstarU)⟩
  have hdiag : ∀ b i,
      RCLike.re (((U : Matrix (α × β) (α × β) ℂ)ᴴ * K *
          (U : Matrix (α × β) (α × β) ℂ)) (i, b) (i, b)) =
        (hH b).eigenvalues i := by
    intro b i
    have hblock :
        (((U : Matrix (α × β) (α × β) ℂ)ᴴ * K *
            (U : Matrix (α × β) (α × β) ℂ)) (i, b) (i, b)) =
          ((Ub b)ᴴ * H b * Ub b) i i := by
      simp only [U, Umat, Matrix.mul_apply, Matrix.blockDiagonal_apply,
        Matrix.conjTranspose_apply, RCLike.star_def]
      simp only [Fintype.sum_prod_type]
      simp [H, Matrix.submatrix]
      have hinner : ∀ x : α,
          (∑ x₁ : α, ∑ x₂ : β,
              starRingEnd ℂ (if x₂ = b then Ub x₂ x₁ i else 0) *
                K (x₁, x₂) (x, b)) =
            ∑ x₁ : α, starRingEnd ℂ (Ub b x₁ i) * K (x₁, b) (x, b) := by
        intro x
        refine Finset.sum_congr rfl fun x₁ _ => ?_
        rw [Finset.sum_eq_single b]
        · simp
        · intro b' _ hb'
          rw [if_neg hb']
          simp
        · simp
      simp_rw [hinner]
    have hspectral := (hH b).conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at hspectral
    have hii := congrFun (congrFun hspectral i) i
    simp only [Matrix.diagonal_apply_eq, Function.comp_apply] at hii
    have heq : ((Ub b)ᴴ * H b * Ub b) i i =
        ((hH b).eigenvalues i : ℂ) := by
      simpa [Ub, Matrix.star_eq_conjTranspose] using hii
    rw [hblock, heq]
    exact RCLike.ofReal_re _
  have hSchur := sumGc_diag_unitaryConj_le_sumGc_eigenvalues hK U hc
  calc
    (∑ b, ∑ i, gc c
        ((hK.1.submatrix (fun j : α => (j, b))).eigenvalues i)) =
        ∑ p : α × β, gc c
          ((hK.1.submatrix (fun j : α => (j, p.2))).eigenvalues p.1) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ p, gc c (RCLike.re
        (((U : Matrix (α × β) (α × β) ℂ)ᴴ * K *
          (U : Matrix (α × β) (α × β) ℂ)) p p)) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hdiag p.2 p.1]
    _ ≤ ∑ p, gc c (hK.1.eigenvalues p) := hSchur

/-- The constant part of the convex defect is preserved by every complete
principal-block partition. -/
theorem sumSimpleDefect_blocks_le_sumSimpleDefect_eigenvalues
    {α : Type*} [Fintype α] [DecidableEq α]
    {β : Type*} [Fintype β] [DecidableEq β]
    {K : Matrix (α × β) (α × β) ℂ} (hK : K.PosSemidef) :
    (∑ b, ∑ i, simpleDefect
      ((hK.1.submatrix (fun j : α => (j, b))).eigenvalues i)) ≤
        ∑ p, simpleDefect (hK.1.eigenvalues p) := by
  have hgc := sumGc_blocks_le_sumGc_eigenvalues hK (c := 2) (by norm_num)
  unfold simpleDefect
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Fintype.card_prod, Nat.cast_mul]
  linarith

/-- Every disjoint block contributes its full unit-capped off-diagonal
energy to the original spectral defect. -/
theorem sum_min_offDiagEnergy_le_sum_simpleDefect
    {α : Type*} [Fintype α] [DecidableEq α]
    {β : Type*} [Fintype β] [DecidableEq β]
    {K : Matrix (α × β) (α × β) ℂ} (hK : K.PosSemidef) :
    (∑ b, min (offDiagEnergy
      (K.submatrix (fun j : α => (j, b)) (fun j : α => (j, b)))) 1) ≤
        ∑ p, simpleDefect (hK.1.eigenvalues p) := by
  calc
    _ ≤ ∑ b, ∑ i, simpleDefect
        ((hK.1.submatrix (fun j : α => (j, b))).eigenvalues i) := by
      exact Finset.sum_le_sum fun b _ =>
        min_offDiagEnergy_one_le_simpleDefect (hK.1.submatrix _)
    _ ≤ _ := sumSimpleDefect_blocks_le_sumSimpleDefect_eigenvalues hK

/-- An arbitrary finite block arrangement with explicitly zero padding. -/
def paddedBlockFamily {α κ β γ n : Type*}
    (e : γ × β ≃ Sum α κ) (v : α → n → ℂ) : γ × β → n → ℂ :=
  fun p => Sum.elim v (fun _ _ => 0) (e p)

/-- Zero padding has exactly its dimension as spectral-defect cost,
independently of the selected block size. -/
theorem sumSimpleDefect_paddedBlockFamily_eq
    {α κ β γ n : Type*}
    [Fintype α] [DecidableEq α] [Fintype κ]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    [Fintype n] [DecidableEq n]
    (v : α → n → ℂ) (e : γ × β ≃ Sum α κ) :
    let vp := paddedBlockFamily e v
    (∑ p, simpleDefect ((columnGram_posSemidef vp).1.eigenvalues p)) =
      (∑ i, simpleDefect ((columnGram_posSemidef v).1.eigenvalues i)) +
        Fintype.card κ := by
  let vp := paddedBlockFamily e v
  let W₀ := Wmat (fun _ : α => (1 : ℝ)) v
  let Wp := Wmat (fun _ : γ × β => (1 : ℝ)) vp
  have hP : Wp * Wpᴴ = W₀ * W₀ᴴ := by
    change Pmat (fun _ : γ × β => (1 : ℝ)) vp =
      Pmat (fun _ : α => (1 : ℝ)) v
    ext a b
    rw [Pmat_apply (fun _ => zero_le_one), Pmat_apply (fun _ => zero_le_one)]
    norm_num
    let g : Sum α κ → ℂ := fun s =>
      Sum.elim v (fun _ _ => 0) s a * starRingEnd ℂ (Sum.elim v (fun _ _ => 0) s b)
    change (∑ x, g (e x)) = ∑ x, v x a * starRingEnd ℂ (v x b)
    rw [e.sum_comp]
    simp [g, Fintype.sum_sum_type]
  have hgc :
      (∑ p, gc 2 ((columnGram_posSemidef vp).1.eigenvalues p)) =
        ∑ i, gc 2 ((columnGram_posSemidef v).1.eigenvalues i) := by
    calc
      _ = ∑ j, gc 2
          ((Matrix.posSemidef_self_mul_conjTranspose Wp).1.eigenvalues j) :=
        (sum_eigenvalues_comm Wp (gc 2) (by norm_num)).symm
      _ = ∑ j, gc 2
          ((Matrix.posSemidef_self_mul_conjTranspose W₀).1.eigenvalues j) :=
        sumEigenvalues_congr_matrix
          (Matrix.posSemidef_self_mul_conjTranspose Wp).1
          (Matrix.posSemidef_self_mul_conjTranspose W₀).1 hP (gc 2)
      _ = _ := sum_eigenvalues_comm W₀ (gc 2) (by norm_num)
  have hcard : (Fintype.card (γ × β) : ℝ) =
      Fintype.card α + Fintype.card κ := by
    exact_mod_cast (Fintype.card_congr e).trans Fintype.card_sum
  unfold simpleDefect
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  rw [hgc, hcard]
  ring

/-- The complete spectral budget for arbitrary disjoint blocks, retaining
every pair and the exact number of zero padding columns. -/
theorem packedBlockEnergy_le_originalDefect_add_padding
    {α κ β γ n : Type*}
    [Fintype α] [DecidableEq α] [Fintype κ]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    [Fintype n] [DecidableEq n]
    (v : α → n → ℂ) (e : γ × β ≃ Sum α κ) :
    let vp := paddedBlockFamily e v
    (∑ b, min (offDiagEnergy
      ((columnGram vp).submatrix (fun j : γ => (j, b))
        (fun j : γ => (j, b)))) 1) ≤
      (∑ i, simpleDefect ((columnGram_posSemidef v).1.eigenvalues i)) +
        Fintype.card κ := by
  exact (sum_min_offDiagEnergy_le_sum_simpleDefect
    (columnGram_posSemidef (paddedBlockFamily e v))).trans_eq
      (sumSimpleDefect_paddedBlockFamily_eq v e)

end
end RiemannGaussian.Zeta23InverseSampling.ZeroBlockData
