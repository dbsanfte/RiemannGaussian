import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.CauchyIntegral
import RiemannGaussian.GaussianZetaGeometry

/-!
# Counting zeta zeros with the pole-cleared xi function

The entire function `completedRiemannZeta₀` is convenient analytically, but
its zero set is not the nontrivial zero set of zeta.  This file instead uses

`riemannXi s = s * (1 - s) * completedRiemannZeta₀ s - 1`.

Away from `0` and `1` this is exactly
`s * (1 - s) * completedRiemannZeta s`.  Consequently its zeros are exactly
the nontrivial zeta zeros, with their analytic multiplicities.  We then state
the one quantitative estimate needed by Jensen's inequality as a separate
predicate.  Proving that estimate from Mathlib's theta-kernel Mellin
representation is the remaining zero-counting task.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeromorphicOn Metric Set Topology

/-- An entire pole-cleared xi function.  This normalization differs from the
classical xi function only by a nonzero constant factor. -/
def riemannXi (s : ℂ) : ℂ :=
  s * (1 - s) * completedRiemannZeta₀ s - 1

@[simp]
theorem riemannXi_zero : riemannXi 0 = -1 := by
  simp [riemannXi]

@[simp]
theorem riemannXi_one : riemannXi 1 = -1 := by
  simp [riemannXi]

/-- The pole-cleared xi function is entire. -/
theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  unfold riemannXi
  apply Differentiable.sub
  · apply Differentiable.mul
    · apply Differentiable.mul
      · exact differentiable_id
      · exact (differentiable_const (c := (1 : ℂ))).sub differentiable_id
    · exact differentiable_completedZeta₀
  · exact differentiable_const (c := (1 : ℂ))

theorem analyticOnNhd_riemannXi :
    AnalyticOnNhd ℂ riemannXi Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr
    differentiable_riemannXi

theorem analyticAt_riemannXi (s : ℂ) :
    AnalyticAt ℂ riemannXi s :=
  differentiable_riemannXi.analyticAt s

/-- Away from the two removed poles, `riemannXi` is the polynomial factor
`s(1-s)` times completed zeta. -/
theorem riemannXi_eq_mul_completedRiemannZeta
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (1 - s) * completedRiemannZeta s := by
  rw [riemannXi, completedRiemannZeta_eq]
  field_simp [hs0, sub_ne_zero.mpr hs1]
  ring

/-- Every zero of `riemannXi` is a nontrivial zeta zero. -/
theorem isNontrivialZetaZero_of_riemannXi_eq_zero
    {s : ℂ} (hxi : riemannXi s = 0) :
    IsNontrivialZetaZero s := by
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hxi
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hxi
  have hcompleted : completedRiemannZeta s = 0 := by
    rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
      mul_eq_zero] at hxi
    rcases hxi with hfactor | hcompleted
    · rcases mul_eq_zero.mp hfactor with hs | hs
      · exact (hs0 hs).elim
      · exact (hs1 (sub_eq_zero.mp hs).symm).elim
    · exact hcompleted
  have hzeta : riemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, hcompleted, zero_div]
  refine ⟨hzeta, ?_, hs1⟩
  rintro ⟨n, rfl⟩
  let w : ℂ := 1 - (-2 * ((n : ℂ) + 1))
  have hw0 : w ≠ 0 := by
    dsimp [w]
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hpos : (0 : ℝ) < 1 + 2 * ((n : ℝ) + 1) := by positivity
    linarith
  have hwre : 1 ≤ w.re := by
    dsimp [w]
    norm_num
    positivity
  have hwcompleted : completedRiemannZeta w = 0 := by
    dsimp [w]
    rw [completedRiemannZeta_one_sub]
    exact hcompleted
  have hwzeta : riemannZeta w = 0 := by
    rw [riemannZeta_def_of_ne_zero hw0, hwcompleted, zero_div]
  exact riemannZeta_ne_zero_of_one_le_re hwre hwzeta

/-- Every nontrivial zeta zero is a zero of `riemannXi`. -/
theorem riemannXi_eq_zero_of_isNontrivialZetaZero
    {s : ℂ} (hs : IsNontrivialZetaZero s) :
    riemannXi s = 0 := by
  let ρ : NontrivialZetaZero := ⟨s, hs⟩
  rw [riemannXi_eq_mul_completedRiemannZeta
    (NontrivialZetaZero.coe_ne_zero ρ) hs.2.2,
    NontrivialZetaZero.completedRiemannZeta_eq_zero, mul_zero]

/-- Exact zero-set identification for the entire xi function. -/
theorem riemannXi_eq_zero_iff_isNontrivialZetaZero (s : ℂ) :
    riemannXi s = 0 ↔ IsNontrivialZetaZero s :=
  ⟨isNontrivialZetaZero_of_riemannXi_eq_zero,
    riemannXi_eq_zero_of_isNontrivialZetaZero⟩

/-- At a nontrivial zero, `riemannXi` and zeta have the same analytic order. -/
theorem analyticOrderAt_riemannXi_eq_riemannZeta
    (ρ : NontrivialZetaZero) :
    analyticOrderAt riemannXi ρ.1 =
      analyticOrderAt riemannZeta ρ.1 := by
  let factor : ℂ → ℂ := fun z => z * (1 - z)
  have hfactorAnalytic : AnalyticAt ℂ factor ρ.1 := by
    dsimp [factor]
    fun_prop
  have hfactorNe : factor ρ.1 ≠ 0 := by
    dsimp [factor]
    exact mul_ne_zero (NontrivialZetaZero.coe_ne_zero ρ)
      (sub_ne_zero.mpr ρ.2.2.2.symm)
  have hfactorOrder : analyticOrderAt factor ρ.1 = 0 :=
    hfactorAnalytic.analyticOrderAt_eq_zero.mpr hfactorNe
  have heq :
      riemannXi =ᶠ[nhds ρ.1]
        fun z => factor z * completedRiemannZeta z := by
    filter_upwards
      [eventually_ne_nhds (NontrivialZetaZero.coe_ne_zero ρ),
        eventually_ne_nhds ρ.2.2.2] with z hz0 hz1
    exact riemannXi_eq_mul_completedRiemannZeta hz0 hz1
  calc
    analyticOrderAt riemannXi ρ.1 =
        analyticOrderAt
          (fun z => factor z * completedRiemannZeta z) ρ.1 :=
      analyticOrderAt_congr heq
    _ = analyticOrderAt factor ρ.1 +
        analyticOrderAt completedRiemannZeta ρ.1 :=
      analyticOrderAt_mul hfactorAnalytic
        (analyticAt_completedRiemannZeta_nontrivialZero ρ)
    _ = analyticOrderAt completedRiemannZeta ρ.1 := by
      rw [hfactorOrder, zero_add]
    _ = analyticOrderAt riemannZeta ρ.1 :=
      (analyticOrderAt_riemannZeta_eq_completedRiemannZeta ρ).symm

/-- The xi divisor records the genuine zeta-zero multiplicity. -/
theorem analyticOrderNatAt_riemannXi_eq_analyticZetaZeroMultiplicity
    (ρ : NontrivialZetaZero) :
    analyticOrderNatAt riemannXi ρ.1 =
      analyticZetaZeroMultiplicity ρ := by
  simp only [analyticOrderNatAt, analyticZetaZeroMultiplicity,
    analyticOrderAt_riemannXi_eq_riemannZeta]

/-- On a ball containing a finite collection of distinct nontrivial zeros,
the xi divisor dominates the sum of their genuine multiplicities. -/
theorem sum_analyticZetaZeroMultiplicity_le_riemannXi_divisor
    {R : ℝ} (S : Finset NontrivialZetaZero)
    (hS : ∀ ρ ∈ S, ‖(ρ.1 : ℂ)‖ ≤ R) :
    ∑ ρ ∈ S, (analyticZetaZeroMultiplicity ρ : ℝ) ≤
      ((∑ᶠ u, divisor riemannXi (closedBall 0 R) u : ℤ) : ℝ) := by
  classical
  let D := divisor riemannXi (closedBall (0 : ℂ) R)
  have hxiAnalytic :
      AnalyticOnNhd ℂ riemannXi (closedBall (0 : ℂ) R) :=
    analyticOnNhd_riemannXi.mono (subset_univ _)
  have hD (ρ : NontrivialZetaZero) (hρ : ρ ∈ S) :
      D ρ.1 = (analyticZetaZeroMultiplicity ρ : ℤ) := by
    have hmem : (ρ.1 : ℂ) ∈ closedBall (0 : ℂ) R := by
      simpa [mem_closedBall] using hS ρ hρ
    rw [show D ρ.1 = divisor riemannXi (closedBall (0 : ℂ) R) ρ.1 by rfl,
      hxiAnalytic.divisor_apply hmem,
      analyticOrderAt_riemannXi_eq_riemannZeta]
    have hfinite := analyticOrderAt_riemannZeta_nontrivialZero_ne_top ρ
    rw [← Nat.cast_analyticOrderNatAt hfinite]
    simp [analyticZetaZeroMultiplicity]
  let T : Finset ℂ :=
    (D.finiteSupport (isCompact_closedBall (0 : ℂ) R)).toFinset
  have himage : S.image (fun ρ : NontrivialZetaZero => (ρ.1 : ℂ)) ⊆ T := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨ρ, hρS, rfl⟩
    rw [Set.Finite.mem_toFinset]
    change D ρ.1 ≠ 0
    rw [hD ρ hρS]
    exact Int.ofNat_ne_zero.mpr
      (Nat.ne_of_gt (analyticZetaZeroMultiplicity_positive ρ))
  calc
    ∑ ρ ∈ S, (analyticZetaZeroMultiplicity ρ : ℝ) =
        ∑ z ∈ S.image (fun ρ : NontrivialZetaZero => (ρ.1 : ℂ)),
          (D z : ℝ) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro ρ hρ
        rw [hD ρ hρ]
        norm_cast
      · intro ρ _ σ _ hρσ
        exact Subtype.ext hρσ
    _ ≤ ∑ z ∈ T, (D z : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro z _ _
      exact_mod_cast hxiAnalytic.divisor_nonneg z
    _ = ∑ᶠ z, (D z : ℝ) := by
      rw [finsum_eq_sum_of_support_subset]
      intro z hz
      change z ∈
        (D.finiteSupport (isCompact_closedBall (0 : ℂ) R)).toFinset
      apply (D.finiteSupport
        (isCompact_closedBall (0 : ℂ) R)).mem_toFinset.mpr
      change D z ≠ 0
      intro hDz
      apply hz
      simp [hDz]
    _ = ((∑ᶠ z, D z : ℤ) : ℝ) := by
      exact (map_finsum (Int.castRingHom ℝ)
        (D.finiteSupport (isCompact_closedBall (0 : ℂ) R))).symm

/-- A deliberately coarse entire-function growth estimate.  Any witness is
enough for Jensen to give a polynomial zero-count and hence Gaussian
summability of zero ordinates. -/
def RiemannXiQuadraticGrowth : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧ ∀ z : ℂ,
    ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2)

/-- Jensen's inequality specialized to the pole-cleared xi function.  A
quadratic exponential norm bound gives an explicit quadratic bound for the
xi divisor in every centered closed ball. -/
theorem jensen_riemannXi_divisor_le
    {A r : ℝ} (hA : 1 ≤ A) (hr : 0 < r)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2)) :
    ∑ᶠ u, divisor riemannXi (closedBall 0 r) u ≤
      A * (2 * r + 1) ^ 2 / Real.log 2 := by
  have hRpos : 0 < 2 * r := mul_pos (by norm_num) hr
  have hM : 1 ≤ Real.exp (A * (2 * r + 1) ^ 2) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg (le_trans (by norm_num) hA) (sq_nonneg _)
  have hJensen := AnalyticOnNhd.sum_divisor_le
    (f := riemannXi) (c := (0 : ℂ)) (r := r) (R := 2 * r)
    (M := Real.exp (A * (2 * r + 1) ^ 2))
    (by simpa [abs_of_pos hr] using hr)
    (by simp only [abs_of_pos hr, abs_of_pos hRpos]; linarith)
    hM
    (analyticOnNhd_riemannXi.mono (subset_univ _))
    (by norm_num)
    (by
      intro z hz
      have hnorm : ‖z‖ = 2 * r := by
        simpa [mem_sphere, abs_of_pos hRpos] using hz
      simpa [hnorm] using hbound z)
  have hratio : (2 * r) / r = 2 := by
    field_simp [hr.ne']
  rw [abs_of_pos hr] at hJensen
  simpa [riemannXi_zero, hratio, Real.log_exp] using hJensen

/-- The isolated growth condition supplies one uniform quadratic zero-count
constant. -/
theorem RiemannXiQuadraticGrowth.exists_divisor_bound
    (hGrowth : RiemannXiQuadraticGrowth) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ r : ℝ, 0 < r →
      ∑ᶠ u, divisor riemannXi (closedBall 0 r) u ≤
        A * (2 * r + 1) ^ 2 / Real.log 2 := by
  rcases hGrowth with ⟨A, hA, hbound⟩
  exact ⟨A, hA, fun r hr =>
    jensen_riemannXi_divisor_le hA hr hbound⟩

/-! ## From a quadratic zero count to Gaussian ordinate summability -/

/-- Integer shell containing the absolute ordinate of a nontrivial zero. -/
def zetaZeroOrdinateShellIndex (ρ : NontrivialZetaZero) : ℕ :=
  ⌊|(zetaSpectralCoordinate ρ.1).re|⌋₊

theorem zetaZeroOrdinateShellIndex_le_abs
    (ρ : NontrivialZetaZero) :
    (zetaZeroOrdinateShellIndex ρ : ℝ) ≤
      |(zetaSpectralCoordinate ρ.1).re| := by
  exact Nat.floor_le (abs_nonneg _)

theorem abs_lt_zetaZeroOrdinateShellIndex_add_one
    (ρ : NontrivialZetaZero) :
    |(zetaSpectralCoordinate ρ.1).re| <
      (zetaZeroOrdinateShellIndex ρ : ℝ) + 1 := by
  exact Nat.lt_floor_add_one _

/-- The critical-strip bound makes a zero's complex norm at most a fixed
additive constant larger than its ordinate shell. -/
theorem norm_lt_zetaZeroOrdinateShellIndex_add_two
    (ρ : NontrivialZetaZero) :
    ‖(ρ.1 : ℂ)‖ < (zetaZeroOrdinateShellIndex ρ : ℝ) + 2 := by
  have hre : |ρ.1.re| < 1 := by
    rw [abs_of_pos (NontrivialZetaZero.zero_lt_re ρ)]
    exact NontrivialZetaZero.re_lt_one ρ
  have him : |ρ.1.im| <
      (zetaZeroOrdinateShellIndex ρ : ℝ) + 1 := by
    simpa using abs_lt_zetaZeroOrdinateShellIndex_add_one ρ
  calc
    ‖(ρ.1 : ℂ)‖ ≤ |ρ.1.re| + |ρ.1.im| :=
      Complex.norm_le_abs_re_add_abs_im ρ.1
    _ < 1 + ((zetaZeroOrdinateShellIndex ρ : ℝ) + 1) :=
      add_lt_add hre him
    _ = (zetaZeroOrdinateShellIndex ρ : ℝ) + 2 := by ring

/-- Each ordinate shell contains only finitely many distinct nontrivial
zeros.  This uses only local finiteness, not a global zero count. -/
theorem zetaZeroOrdinateShell_finite (n : ℕ) :
    {ρ : NontrivialZetaZero | zetaZeroOrdinateShellIndex ρ = n}.Finite := by
  let B : Set ℂ :=
    closedBall (0 : ℂ) ((n : ℝ) + 2) ∩ nontrivialZetaZeroSet
  have hB : B.Finite := by
    dsimp [B]
    exact IsCompact.inter_nontrivialZetaZeroSet_finite
      (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 2))
  have hpre :
      ((fun ρ : NontrivialZetaZero => (ρ.1 : ℂ)) ⁻¹' B).Finite :=
    hB.preimage Subtype.val_injective.injOn
  apply hpre.subset
  intro ρ hρ
  change (ρ.1 : ℂ) ∈ B
  refine ⟨?_, ρ.2⟩
  have hnorm := norm_lt_zetaZeroOrdinateShellIndex_add_two ρ
  rw [hρ] at hnorm
  simpa [mem_closedBall] using hnorm.le

/-- The quadratic Jensen bound multiplied by an exponential ordinate tail
is summable over integer shells. -/
theorem summable_riemannXi_shell_majorant
    (A : ℝ) {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℕ =>
      (A * (2 * ((n : ℝ) + 2) + 1) ^ 2 / Real.log 2) *
        Real.exp (-c * (n : ℝ)) := by
  have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 hc
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 hc
  have h2 := Real.summable_pow_mul_exp_neg_nat_mul 2 hc
  have hpoly : Summable fun n : ℕ =>
      (2 * ((n : ℝ) + 2) + 1) ^ 2 *
        Real.exp (-c * (n : ℝ)) := by
    refine ((h2.mul_left 4).add
      ((h1.mul_left 20).add (h0.mul_left 25))).congr fun n => ?_
    norm_num
    ring
  refine (hpoly.mul_left (A / Real.log 2)).congr fun n => ?_
  ring

/-- Quantitative bound for one ordinate shell, counted with analytic
multiplicity. -/
theorem tsum_zetaZeroOrdinateShell_le
    {A c : ℝ} (hA : 1 ≤ A) (hc : 0 < c)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2))
    (n : ℕ) :
    ∑' ρ : {ρ : NontrivialZetaZero |
        zetaZeroOrdinateShellIndex ρ = n},
      (analyticZetaZeroMultiplicity ρ.1 : ℝ) *
        Real.exp
          (-c * (zetaSpectralCoordinate ρ.1.1).re ^ 2) ≤
      (A * (2 * ((n : ℝ) + 2) + 1) ^ 2 / Real.log 2) *
        Real.exp (-c * (n : ℝ) ^ 2) := by
  classical
  let shell : Set NontrivialZetaZero :=
    {ρ | zetaZeroOrdinateShellIndex ρ = n}
  let : Fintype shell := (zetaZeroOrdinateShell_finite n).fintype
  let S : Finset NontrivialZetaZero :=
    Finset.univ.image (fun ρ : shell => ρ.1)
  have hSinBall : ∀ ρ ∈ S, ‖(ρ.1 : ℂ)‖ ≤ (n : ℝ) + 2 := by
    intro ρ hρ
    rcases Finset.mem_image.mp hρ with ⟨σ, -, rfl⟩
    have hnorm := norm_lt_zetaZeroOrdinateShellIndex_add_two σ.1
    rw [σ.2] at hnorm
    exact hnorm.le
  have hsumEq :
      ∑ ρ ∈ S, (analyticZetaZeroMultiplicity ρ : ℝ) =
        ∑ ρ : shell,
          (analyticZetaZeroMultiplicity ρ.1 : ℝ) := by
    dsimp [S]
    rw [Finset.sum_image]
    simp
  have hcount :
      ∑ ρ : shell, (analyticZetaZeroMultiplicity ρ.1 : ℝ) ≤
        A * (2 * ((n : ℝ) + 2) + 1) ^ 2 / Real.log 2 := by
    rw [← hsumEq]
    exact (sum_analyticZetaZeroMultiplicity_le_riemannXi_divisor
      S hSinBall).trans
        (jensen_riemannXi_divisor_le hA (by positivity) hbound)
  rw [tsum_fintype]
  calc
    ∑ ρ : shell,
        (analyticZetaZeroMultiplicity ρ.1 : ℝ) *
          Real.exp (-c * (zetaSpectralCoordinate ρ.1.1).re ^ 2) ≤
        ∑ ρ : shell,
          (analyticZetaZeroMultiplicity ρ.1 : ℝ) *
            Real.exp (-c * (n : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro ρ _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Real.exp_le_exp.mpr
      have hlower := zetaZeroOrdinateShellIndex_le_abs ρ.1
      rw [ρ.2] at hlower
      have hsquare : (n : ℝ) ^ 2 ≤
          (zetaSpectralCoordinate ρ.1.1).re ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity)]
          using hlower
      nlinarith
    _ = (∑ ρ : shell,
          (analyticZetaZeroMultiplicity ρ.1 : ℝ)) *
        Real.exp (-c * (n : ℝ) ^ 2) := by
      rw [Finset.sum_mul]
    _ ≤ (A * (2 * ((n : ℝ) + 2) + 1) ^ 2 / Real.log 2) *
        Real.exp (-c * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hcount (Real.exp_nonneg _)

/-- A quadratic xi growth bound makes the multiplicity-weighted Gaussian
series over distinct nontrivial zeros summable. -/
theorem summable_distinct_zetaZeroGaussianOrdinate_of_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2))
    {c : ℝ} (hc : 0 < c) :
    Summable fun ρ : NontrivialZetaZero =>
      (analyticZetaZeroMultiplicity ρ : ℝ) *
        Real.exp
          (-c * (zetaSpectralCoordinate ρ.1).re ^ 2) := by
  let shell : ℕ → Set NontrivialZetaZero := fun n =>
    {ρ | zetaZeroOrdinateShellIndex ρ = n}
  apply (summable_partition
    (f := fun ρ : NontrivialZetaZero =>
      (analyticZetaZeroMultiplicity ρ : ℝ) *
        Real.exp (-c * (zetaSpectralCoordinate ρ.1).re ^ 2))
    (fun ρ => mul_nonneg (Nat.cast_nonneg _)
      (Real.exp_nonneg _))
    (s := shell) (by
      intro ρ
      refine ⟨zetaZeroOrdinateShellIndex ρ, rfl, ?_⟩
      intro n hn
      exact hn.symm)).2
  constructor
  · intro n
    let : Fintype (shell n) := (zetaZeroOrdinateShell_finite n).fintype
    exact Summable.of_finite
  · apply (summable_riemannXi_shell_majorant A hc).of_nonneg_of_le
      (fun n => tsum_nonneg fun ρ =>
        mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _))
    intro n
    calc
      ∑' ρ : shell n,
          (analyticZetaZeroMultiplicity ρ.1 : ℝ) *
            Real.exp
              (-c * (zetaSpectralCoordinate ρ.1.1).re ^ 2) ≤
          (A * (2 * ((n : ℝ) + 2) + 1) ^ 2 / Real.log 2) *
            Real.exp (-c * (n : ℝ) ^ 2) := by
        exact tsum_zetaZeroOrdinateShell_le hA hc hbound n
      _ ≤ (A * (2 * ((n : ℝ) + 2) + 1) ^ 2 / Real.log 2) *
          Real.exp (-c * (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
        · apply Real.exp_le_exp.mpr
          have hnSquare : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
            cases n with
            | zero => norm_num
            | succ n =>
                have hn : (1 : ℝ) ≤ (Nat.succ n : ℝ) := by norm_num
                nlinarith
          nlinarith
        · exact div_nonneg
            (mul_nonneg (le_trans (by norm_num) hA) (sq_nonneg _))
            (Real.log_pos (by norm_num)).le

/-- The quadratic xi growth bound implies the exact occurrence-slot
ordinate-tail condition used to construct the canonical Gaussian zero sum. -/
theorem zetaZeroGaussianOrdinateSummable_of_riemannXiQuadraticGrowth
    (hGrowth : RiemannXiQuadraticGrowth) :
    ZetaZeroGaussianOrdinateSummable := by
  rcases hGrowth with ⟨A, hA, hbound⟩
  intro c hc
  have hdistinct :=
    summable_distinct_zetaZeroGaussianOrdinate_of_growth
      hA hbound hc
  apply (summable_sigma_of_nonneg
    (f := fun occurrence :
        NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity =>
      Real.exp
        (-c * (zetaSpectralCoordinate occurrence.1.1).re ^ 2))
    (fun _ => Real.exp_nonneg _)).2
  constructor
  · intro ρ
    exact Summable.of_finite
  · refine hdistinct.congr fun ρ => ?_
    rw [tsum_fintype]
    simp [Finset.sum_const, nsmul_eq_mul]

/-- Under the isolated xi growth estimate, the canonical translated zero
sum has the required convergent `HasSum` representation. -/
theorem representsCanonicalZetaGaussianZeroSum_of_riemannXiQuadraticGrowth
    (hGrowth : RiemannXiQuadraticGrowth) :
    RepresentsZetaGaussianZeroSum analyticZetaZeroMultiplicity
      canonicalZetaGaussianZeroSum :=
  representsCanonicalZetaGaussianZeroSum
    (zetaZeroGaussianOrdinateSummable_of_riemannXiQuadraticGrowth hGrowth)

/-- Thus, conditional only on the quantitative xi growth estimate,
nonnegativity of the canonical symmetric Gaussian zero sum is equivalent to
the Riemann hypothesis. -/
theorem canonicalZetaSymmetricGaussianZeroSum_nonnegative_iff_riemannHypothesis_of_growth
    (hGrowth : RiemannXiQuadraticGrowth) :
    ZetaSymmetricGaussianZeroSumNonnegative
        canonicalZetaSymmetricGaussianZeroSum ↔
      RiemannHypothesis :=
  canonicalZetaSymmetricGaussianZeroSum_nonnegative_iff_riemannHypothesis
    (zetaZeroGaussianOrdinateSummable_of_riemannXiQuadraticGrowth hGrowth)

end

end RiemannGaussian
