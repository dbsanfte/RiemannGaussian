/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszShiftedCenter
import RiemannGaussian.ZetaRieszHalfPlaneModes
import RiemannGaussian.ZetaRieszMinimumCollisionAudit

/-!
# Height-penalized selection and a tilted source half-plane

A small positive height penalty has an attained, generically unique
maximum on the genuine upper zeta divisor. Moving the safe evaluation
ordinate slightly downwards turns that supporting line into a half-plane
through the selected source denominator. This concerns genuine zero modes;
it neither removes the zeta pole nor transfers a masked prime sum through
an analytic remainder. The original arithmetic carrier is not redefined.
-/

namespace RiemannGaussian.ZetaTiltedZeroSelection
noncomputable section
open scoped BigOperators Classical ComplexConjugate

/-- A linear height penalty on the upper nontrivial divisor. -/
def score (a : ℝ) (rho : NontrivialZetaZero) : ℝ := rho.1.re-a*rho.1.im

/-- Only the evaluation height is shifted; the safe real line is unchanged. -/
def center (a : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  3/2+Complex.I*(rho.1.im-a*(3/2-rho.1.re))

/-- The selected complex denominator, rather than a horizontal radius. -/
def source (a : ℝ) (rho : NontrivialZetaZero) : ℂ := center a rho-rho.1

theorem source_ne_zero (a : ℝ) (rho : NontrivialZetaZero) : source a rho ≠ 0 := by
  apply Complex.ne_zero_of_re_pos
  have hr := NontrivialZetaZero.re_lt_one rho
  norm_num [source,center]
  linarith

/-- The supporting score is exactly the projection along the source.
No zero approximation or reflected local mode enters this identity. -/
theorem projection_identity (a : ℝ) (rho tau : NontrivialZetaZero) :
    (conj (source a rho)*(center a rho-tau.1)).re =
      ‖source a rho‖^2+(3/2-rho.1.re)*(score a rho-score a tau) := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]
  norm_num [source,center,score,Complex.normSq_apply]
  ring

/-- Distinct scores in a finite window can be ensured by avoiding only
finitely many slopes. Zeros at equal height cause no exception. -/
theorem exists_injective_score (S : Finset NontrivialZetaZero) {a b : ℝ}
    (hab : a < b) :
    ∃ t ∈ Set.Ioo a b, Set.InjOn (score t) (S : Set NontrivialZetaZero) := by
  let bad : Finset ℝ := (S ×ˢ S).image
    (fun p => (p.1.1.re-p.2.1.re)/(p.1.1.im-p.2.1.im))
  have hex : ∃ t ∈ Set.Ioo a b, t ∉ bad := by
    by_contra! h
    exact (Set.Ioo_infinite hab) (bad.finite_toSet.subset (fun t ht => h t ht))
  obtain ⟨t,ht,hbad⟩ := hex
  refine ⟨t,ht,?_⟩
  intro rho hrho tau htau he
  by_cases hi : rho.1.im = tau.1.im
  · apply Subtype.ext
    apply Complex.ext
    · dsimp [score] at he
      rw [hi] at he
      linarith
    · exact hi
  · exfalso
    apply hbad
    apply Finset.mem_image.mpr
    refine ⟨(rho,tau),Finset.mem_product.mpr ⟨hrho,htau⟩,?_⟩
    apply (div_eq_iff (sub_ne_zero.mpr hi)).mpr
    dsimp [score] at he
    linarith

/-- A genuine upper zero above a target supplies a unique global
height-penalized maximizer in any admissible interval of positive slopes.
The finiteness of a height window, rather than a rightward chain, gives
attainment. No globally rightmost zero is assumed. -/
theorem exists_unique_upper_max (rho0 : NontrivialZetaZero)
    {target a b : ℝ} (htarget : 0 ≤ target) (ha : 0 < a) (hab : a < b)
    (hupper : 0 ≤ rho0.1.im) (hmargin : b*rho0.1.im < rho0.1.re-target) :
    ∃ t ∈ Set.Ioo a b, ∃ rho : NontrivialZetaZero,
      0 ≤ rho.1.im ∧ target < score t rho ∧
        ∀ tau : NontrivialZetaZero, 0 ≤ tau.1.im → tau ≠ rho →
          score t tau < score t rho := by
  let S := (spectralZetaZeroWindow (1/a)).filter (fun rho => 0 ≤ rho.1.im)
  have hwindow (rho : NontrivialZetaZero) :
      rho ∈ S ↔ |rho.1.im| ≤ 1/a ∧ 0 ≤ rho.1.im := by
    dsimp only [S]
    rw [Finset.mem_filter,mem_spectralZetaZeroWindow (by positivity : (0 : ℝ) ≤ 1/a)]
    simp only [zetaSpectralCoordinate_re]
  have h0 : rho0 ∈ S := by
    rw [hwindow,abs_of_nonneg hupper]
    refine ⟨(le_div_iff₀ ha).mpr ?_,hupper⟩
    have hr := NontrivialZetaZero.re_lt_one rho0
    nlinarith [mul_nonneg (sub_nonneg.mpr hab.le) hupper]
  obtain ⟨t,ht,hinj⟩ := exists_injective_score S hab
  obtain ⟨rho,hrho,hmax⟩ := S.exists_max_image (score t) ⟨rho0,h0⟩
  have hscore : target < score t rho := by
    have hh := hmax rho0 h0
    dsimp [score] at hh ⊢
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2.le) hupper]
  refine ⟨t,ht,rho,(hwindow rho).mp hrho |>.2,hscore,?_⟩
  intro tau htau hne
  by_cases hm : tau ∈ S
  · apply lt_of_le_of_ne (hmax tau hm)
    intro he
    exact hne (hinj hm hrho he)
  · have hh : 1/a < tau.1.im := by
      by_contra! hn
      apply hm
      rw [hwindow,abs_of_nonneg htau]
      exact ⟨hn,htau⟩
    have hmul : 1 < tau.1.im*a := (div_lt_iff₀ ha).mp hh
    have hr := NontrivialZetaZero.re_lt_one tau
    dsimp [score] at hscore ⊢
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.1.le) htau]

/-- The entire convex mixture retains its signed score gap. This
identity is stated before a norm is taken. -/
theorem convex_projection_identity {ι : Type*} (S : Finset ι) (q : ι → ℝ)
    (tau : ι → NontrivialZetaZero) (rho : NontrivialZetaZero) (a : ℝ)
    (hq : ∑ j ∈ S, q j = 1) :
    (conj (source a rho)*(∑ j ∈ S, (q j : ℂ)*(center a rho-(tau j).1))).re =
      ‖source a rho‖^2+(3/2-rho.1.re)*
        ∑ j ∈ S, q j*(score a rho-score a (tau j)) := by
  have he (j : ι) :
      (conj (source a rho)*((q j : ℂ)*(center a rho-(tau j).1))).re =
        q j*(conj (source a rho)*(center a rho-(tau j).1)).re := by
    rw [← mul_assoc,mul_comm (conj (source a rho)) (q j : ℂ),mul_assoc]
    simp
  rw [Finset.mul_sum,Complex.re_sum]
  simp_rw [he,projection_identity,mul_add]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,hq,one_mul,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Quantitative separation for the coupled denominator. No estimate
of its individual prime legs has been used. -/
theorem convex_norm_gap {ι : Type*} (S : Finset ι) (q : ι → ℝ)
    (tau : ι → NontrivialZetaZero) (rho : NontrivialZetaZero) (a : ℝ)
    (hq : ∑ j ∈ S, q j = 1) :
    ‖source a rho‖+(3/2-rho.1.re)*
      (∑ j ∈ S, q j*(score a rho-score a (tau j)))/‖source a rho‖ ≤
        ‖∑ j ∈ S, (q j : ℂ)*(center a rho-(tau j).1)‖ := by
  have hr : 0 < ‖source a rho‖ := norm_pos_iff.mpr (source_ne_zero a rho)
  have hh := Complex.re_le_norm
    (conj (source a rho)*(∑ j ∈ S, (q j : ℂ)*(center a rho-(tau j).1)))
  rw [norm_mul,RCLike.norm_conj,convex_projection_identity S q tau rho a hq] at hh
  rw [add_div_eq_mul_add_div _ _ (ne_of_gt hr)]
  apply (div_le_iff₀ hr).mpr
  nlinarith

/-- A supporting score controls a genuinely coupled upper-mode mixture.
The premise is supplied by `exists_unique_upper_max`, rather than by an
assumed globally rightmost zero. -/
theorem convex_norm_ge_of_score {ι : Type*} (S : Finset ι) (q : ι → ℝ)
    (tau : ι → NontrivialZetaZero) (rho : NontrivialZetaZero) (a : ℝ)
    (hq : ∀ j ∈ S, 0 ≤ q j) (hs : ∑ j ∈ S, q j = 1)
    (hscore : ∀ j ∈ S, score a (tau j) ≤ score a rho) :
    ‖source a rho‖ ≤ ‖∑ j ∈ S, (q j : ℂ)*(center a rho-(tau j).1)‖ := by
  have hsum : 0 ≤ ∑ j ∈ S, q j*(score a rho-score a (tau j)) :=
    Finset.sum_nonneg (fun j hj => mul_nonneg (hq j hj) (sub_nonneg.mpr (hscore j hj)))
  have hu : 0 < 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  exact (le_add_of_nonneg_right (div_nonneg (mul_nonneg hu.le hsum)
    (norm_nonneg _))).trans (convex_norm_gap S q tau rho a hs)

/-- If any positively weighted mode has strictly smaller score, the
coupled denominator is strictly outside the source disk. This is a finite
geometric separation, not a transfer through the least-prime projection. -/
theorem convex_norm_gt_of_score {ι : Type*} (S : Finset ι) (q : ι → ℝ)
    (tau : ι → NontrivialZetaZero) (rho : NontrivialZetaZero) (a : ℝ)
    (hq : ∀ j ∈ S, 0 ≤ q j) (hs : ∑ j ∈ S, q j = 1)
    (hscore : ∀ j ∈ S, score a (tau j) ≤ score a rho)
    (hstrict : ∃ j ∈ S, 0 < q j ∧ score a (tau j) < score a rho) :
    ‖source a rho‖ < ‖∑ j ∈ S, (q j : ℂ)*(center a rho-(tau j).1)‖ := by
  obtain ⟨j,hj,hqj,hsj⟩ := hstrict
  have hsum : 0 < ∑ j ∈ S, q j*(score a rho-score a (tau j)) :=
    Finset.sum_pos' (fun j hj => mul_nonneg (hq j hj) (sub_nonneg.mpr (hscore j hj)))
      ⟨j,hj,mul_pos hqj (sub_pos.mpr hsj)⟩
  have hu : 0 < 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  exact (lt_add_of_pos_right _ (div_pos (mul_pos hu hsum)
    (norm_pos_iff.mpr (source_ne_zero a rho)))).trans_le
      (convex_norm_gap S q tau rho a hs)

/-- A remote symmetric model can defeat a conclusion about *all* modes.
The two upper competitors both lose the tilted score, while their
opposite-height partners remain available. No synthetic point in this
statement is asserted to be a zeta zero. -/
theorem remote_upper_scores {beta gamma a delta G y : ℝ}
    (ha : 0 ≤ a) (hy : 0 ≤ y) (hgain : delta < a*(G-gamma)) :
    (beta+delta)-a*G < beta-a*gamma ∧
      (beta+delta)-a*(G+2*y) < beta-a*gamma := by
  constructor
  · linarith
  · nlinarith [mul_nonneg ha hy]

/-- The remote pair at ordinates -G and G+2y has cancelling offsets
at evaluation height y. Increasing G improves local analyticity without
changing their average real denominator. -/
theorem remote_pair_denominators (beta delta G y : ℝ) :
    (3/2+Complex.I*(y : ℂ))-((beta+delta : ℝ)+Complex.I*(-G : ℝ)) =
      ZetaRieszMinimumCollisionAudit.node (3/2-beta-delta) (G+y) ∧
    (3/2+Complex.I*(y : ℂ))-((beta+delta : ℝ)+Complex.I*(G+2*y : ℝ)) =
      ZetaRieszMinimumCollisionAudit.node (3/2-beta-delta) (-(G+y)) := by
  constructor <;> unfold ZetaRieszMinimumCollisionAudit.node <;> push_cast <;> ring

/-- A positive horizontal gain makes the exact remote minimum moment
grow at source scale, however distant its ordinates. This does not assert
growth of the joined Riesz/count sum, nor the existence of such zeta zeros. -/
theorem remote_minimum_tendsto {beta delta : ℝ} (hd : 0 < delta)
    (hdu : delta < 3/2-beta) (G y : ℝ) :
    Filter.Tendsto (fun h : ℕ =>
      (((2*(3/2-beta) : ℝ) : ℂ)^h*
        ZetaRieszMinimumCollisionAudit.minimumMoment h (3/2-beta-delta) (G+y)).re)
      Filter.atTop Filter.atTop := by
  exact ZetaRieszMinimumCollisionAudit.normalized_minimumMoment_tendsto_of_gain
    (by linarith) (by linarith) _

end
end RiemannGaussian.ZetaTiltedZeroSelection
