/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianXiInverseSquareSummability
import RiemannGaussian.ZetaRieszLargeSmoothDeletion
import RiemannGaussian.ZetaZeroModeFilter
import RiemannGaussian.ZetaReciprocalGeometry
import RiemannGaussian.ZetaCenteredEulerZeroFree
import RiemannGaussian.ZetaRieszCompositeBoundaryWindow
import Mathlib.Analysis.PSeries

/-!
# Exposed right-half zeros without a rightmost-zero hypothesis

Any hypothetical right-half zero leads to one at least as far right whose
horizontal source disk contains no competing zero, including its boundary.
The actual inverse-square divisor summability rules out infinite competing
chains. Local finiteness supplies a strictly larger isolating radius.
The RH-floor reduction retains an explicit, unproved arithmetic premise.
-/

namespace RiemannGaussian.ZetaExposedZero
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- A distinct zero in the selected horizontal source disk must
move strictly rightwards. Its squared vertical displacement is paid by
twice its real-coordinate improvement. -/
theorem competing_disk_step {rho tau : NontrivialZetaZero}
    (hrho : 1 / 2 < rho.1.re) (hne : tau ≠ rho)
    (hd : ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖ ≤ 3 / 2 - rho.1.re) :
    rho.1.re < tau.1.re ∧ (tau.1.im - rho.1.im) ^ 2 ≤ 2 * (tau.1.re - rho.1.re) := by
  have hr1 := NontrivialZetaZero.re_lt_one rho
  have ht1 := NontrivialZetaZero.re_lt_one tau
  have hnorm0 := norm_nonneg ((3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1)
  have hn : ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖ ^ 2 ≤ (3 / 2 - rho.1.re) ^ 2 := by
    nlinarith
  have he := Complex.sq_norm_sub_sq_im ((3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1)
  norm_num at he
  have hre : rho.1.re ≤ tau.1.re := by
    nlinarith [sq_nonneg (rho.1.im - tau.1.im)]
  have hlt : rho.1.re < tau.1.re := by
    by_contra h
    have heq : rho.1.re = tau.1.re := le_antisymm hre (le_of_not_gt h)
    have him : rho.1.im = tau.1.im := by
      rw [heq] at hn
      nlinarith [sq_nonneg (rho.1.im - tau.1.im)]
    apply hne
    apply Subtype.ext
    exact Complex.ext heq.symm him.symm
  refine ⟨hlt, ?_⟩
  nlinarith [sq_nonneg (tau.1.re - rho.1.re),
    mul_nonneg (sub_nonneg.mpr hrho.le) (sub_nonneg.mpr hre)]

/-- Along a sequence of competing source disks, the complete
vertical displacement has only linear squared growth. -/
theorem chain_im_sq_le (z : ℕ → NontrivialZetaZero)
    (hstep : ∀ n, ((z (n + 1)).1.im - (z n).1.im) ^ 2 ≤
      2 * ((z (n + 1)).1.re - (z n).1.re)) (n : ℕ) :
    ((z n).1.im - (z 0).1.im) ^ 2 ≤ 2 * n := by
  have hsum : (∑ k ∈ Finset.range n, ((z (k + 1)).1.im - (z k).1.im) ^ 2) ≤
      2 * ((z n).1.re - (z 0).1.re) := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, 2 * ((z (k + 1)).1.re - (z k).1.re) :=
        Finset.sum_le_sum (fun k _ => hstep k)
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub (fun k => (z k).1.re)]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n)
    (fun _ => (1 : ℝ)) (fun k => (z (k + 1)).1.im - (z k).1.im)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one] at hCS
  rw [Finset.sum_range_sub (fun k => (z k).1.im)] at hCS
  have hb : (z n).1.re - (z 0).1.re ≤ 1 := by
    linarith [NontrivialZetaZero.re_lt_one (z n), NontrivialZetaZero.zero_lt_re (z 0)]
  calc
    _ ≤ (n : ℝ) * ∑ k ∈ Finset.range n, ((z (k + 1)).1.im - (z k).1.im) ^ 2 := hCS
    _ ≤ (n : ℝ) * (2 * ((z n).1.re - (z 0).1.re)) := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ ≤ 2 * n := by nlinarith [mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n)]

/-- A competing-disk chain has a uniform linear bound for its
inverse-square denominator, in terms of its initial ordinate. -/
theorem chain_norm_sq_le (z : ℕ → NontrivialZetaZero)
    (hstep : ∀ n, ((z (n + 1)).1.im - (z n).1.im) ^ 2 ≤
      2 * ((z (n + 1)).1.re - (z n).1.re)) (n : ℕ) :
    1 + ‖(z n).1‖ ^ 2 ≤ (4 + 2 * (z 0).1.im ^ 2) * ((n : ℝ) + 1) := by
  have hsq := chain_im_sq_le z hstep n
  have he := Complex.sq_norm_sub_sq_im (z n).1
  have hre0 := NontrivialZetaZero.zero_lt_re (z n)
  have hre1 := NontrivialZetaZero.re_lt_one (z n)
  have hre : (z n).1.re ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg ((z n).1.im - 2 * (z 0).1.im),
    mul_nonneg (sq_nonneg (z 0).1.im) (Nat.cast_nonneg n)]

/-- The actual inverse-square summability of the zeta divisor
rules out an infinite injective competing-disk chain. No zero-free
strip improvement or rightmost-zero assumption is used. -/
theorem no_infinite_competing_chain (z : ℕ → NontrivialZetaZero) (hinj : Function.Injective z)
    (hstep : ∀ n, ((z (n + 1)).1.im - (z n).1.im) ^ 2 ≤
      2 * ((z (n + 1)).1.re - (z n).1.re)) : False := by
  let C : ℝ := 4 + 2 * (z 0).1.im ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hs := summable_distinct_zetaZeroInverseSquareNorm.comp_injective hinj
  have hh : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    apply (hs.mul_left C).of_nonneg_of_le (fun n => by positivity)
    intro n
    have hD : 0 < 1 + ‖(z n).1‖ ^ 2 := by positivity
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity (z n) := by
      exact_mod_cast analyticZetaZeroMultiplicity_positive (z n)
    have hrec : 1 / ((n : ℝ) + 1) ≤ C / (1 + ‖(z n).1‖ ^ 2) := by
      apply (div_le_div_iff₀ hn hD).mpr
      simpa only [one_mul, C] using chain_norm_sq_le z hstep n
    calc
      _ ≤ C / (1 + ‖(z n).1‖ ^ 2) := hrec
      _ = C * (1 / (1 + ‖(z n).1‖ ^ 2)) := by ring
      _ ≤ C * ((analyticZetaZeroMultiplicity (z n) : ℝ) / (1 + ‖(z n).1‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hm hD.le) hC.le
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using hh

/-- From any hypothetical right-half zero one can select a zero
at least as far right whose horizontal source disk contains no competing
zero, even on its boundary. Infinite rightward escape is ruled out by
the proved inverse-square summability of the actual divisor. -/
theorem exists_exposed_right_half_zero (rho0 : NontrivialZetaZero)
    (hrho0 : 1 / 2 < rho0.1.re) :
    ∃ rho : NontrivialZetaZero, rho0.1.re ≤ rho.1.re ∧
      ∀ tau : NontrivialZetaZero, tau ≠ rho →
        3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖ := by
  by_contra! h
  let S := {rho : NontrivialZetaZero // rho0.1.re ≤ rho.1.re}
  have hn (rho : S) : ∃ tau : S,
      rho.1.1.re < tau.1.1.re ∧
        (tau.1.1.im - rho.1.1.im) ^ 2 ≤ 2 * (tau.1.1.re - rho.1.1.re) := by
    obtain ⟨tau, hne, hd⟩ := h rho.1 rho.2
    have hs := competing_disk_step (hrho0.trans_le rho.2) hne hd
    exact ⟨⟨tau, rho.2.trans hs.1.le⟩, hs⟩
  choose next hnext using hn
  let z : ℕ → S := Nat.rec ⟨rho0, le_rfl⟩ (fun _ old => next old)
  have hstrict : StrictMono (fun n => (z n).1.1.re) :=
    strictMono_nat_of_lt_succ (fun n => (hnext (z n)).1)
  apply no_infinite_competing_chain (fun n => (z n).1)
  · intro m n he
    apply hstrict.injective
    exact congrArg (fun rho : NontrivialZetaZero => rho.1.re) he
  · intro n
    exact (hnext (z n)).2

/-- It suffices to prove independent signed floors only at exposed
right-half zeros. The actual adaptive arithmetic carrier, normalization
and cofinal margin are unchanged. The required floors remain premises. -/
theorem rh_of_exposed_adaptiveSmooth_floors
    (hfloor : ∀ (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re),
      (∀ tau : NontrivialZetaZero, tau ≠ rho →
        3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) →
      ∃ c : ℝ, c < 1 ∧ ∃ᶠ N in atTop,
        -c ≤ (ZetaRieszLargeSmoothDeletion.normalizedAdaptiveSmooth rho hrho N).re) :
    RiemannHypothesis := by
  have hright (rho : NontrivialZetaZero) : rho.1.re ≤ 1 / 2 := by
    apply le_of_not_gt
    intro hrho
    obtain ⟨sigma, hright, hexposed⟩ := exists_exposed_right_half_zero rho hrho
    have hsigma : 1 / 2 < sigma.1.re := hrho.trans_le hright
    obtain ⟨c, hc, hf⟩ := hfloor sigma hsigma hexposed
    exact ZetaRieszLargeSmoothDeletion.false_of_adaptiveSmooth_cofinal_floor sigma hsigma hc hf
  intro s hs htriv hone
  let rho : NontrivialZetaZero := ⟨s, hs, htriv, hone⟩
  have hupper := hright rho
  have hlower := hright (NontrivialZetaZero.functionalPartner rho)
  simp only [NontrivialZetaZero.functionalPartner_coe, Complex.sub_re, Complex.one_re] at hlower
  change s.re ≤ 1 / 2 at hupper
  change 1 - s.re ≤ 1 / 2 at hlower
  linarith

/-- Local finiteness upgrades the strict exposed disk to a larger
source disk with a genuine gap to every competing nontrivial zero. -/
theorem exists_exposed_source_radius {rho : NontrivialZetaZero}
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    ∃ R : ℝ, 3 / 2 - rho.1.re < R ∧ R < 1 ∧
      ∀ tau : NontrivialZetaZero, tau ≠ rho →
        R < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖ := by
  let c : ℂ := 3 / 2 + Complex.I * (rho.1.im : ℂ)
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : u < 1 := by dsimp [u]; linarith
  let T : Set NontrivialZetaZero := {tau | ‖c - tau.1‖ ≤ 1 ∧ tau ≠ rho}
  have hT : T.Finite := by
    have hf : ((fun tau : NontrivialZetaZero => tau.1) ⁻¹'
        (Metric.closedBall c 1 ∩ nontrivialZetaZeroSet)).Finite :=
      (IsCompact.inter_nontrivialZetaZeroSet_finite (isCompact_closedBall c 1)).preimage
        Subtype.val_injective.injOn
    apply hf.subset
    intro tau ht
    refine ⟨?_, tau.2⟩
    simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using ht.1
  let W : Finset ℝ := insert 1 (hT.toFinset.image (fun tau => ‖c - tau.1‖))
  have hW : W.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let v := W.min' hW
  have hv : v ≤ 1 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have huv : u < v := by
    change u < W.min' hW
    have hm := Finset.min'_mem W hW
    rcases Finset.mem_insert.mp hm with he | hm
    · simpa only [he] using hu
    · obtain ⟨tau, ht, he⟩ := Finset.mem_image.mp hm
      rw [← he]
      exact hexposed tau (hT.mem_toFinset.mp ht).2
  refine ⟨(u + v) / 2, by dsimp [u] at huv ⊢; linarith, by linarith, ?_⟩
  intro tau hne
  by_cases ht : ‖c - tau.1‖ ≤ 1
  · have hm : ‖c - tau.1‖ ∈ W := Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨tau, hT.mem_toFinset.mpr ⟨ht, hne⟩, rfl⟩)
    have hvd := Finset.min'_le W _ hm
    change (u + v) / 2 < ‖c - tau.1‖
    change v ≤ ‖c - tau.1‖ at hvd
    linarith
  · have hd : 1 < ‖c - tau.1‖ := lt_of_not_ge ht
    change (u + v) / 2 < ‖c - tau.1‖
    linarith

/-- Every canonical divisor point at an exposed ordinate lies at
least the source distance from the expansion center. This transports the
global nontrivial-zero separation into the actual finite local divisor. -/
theorem canonical_support_norm_ge_exposed {rho : NontrivialZetaZero}
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (r : Set.Ico (3 / 4 : ℝ) 1) {i : ℂ} (hi : i ∈ adaptiveZetaZeroSupport r rho.1.im) :
    3 / 2 - rho.1.re ≤ ‖i‖ := by
  have hdiv := (mem_adaptiveZetaZeroSupport r rho.1.im i).mp hi
  have himem := (MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
    (Metric.ball 0 (adaptiveZetaCanonicalRadius r rho.1.im))).supportWithinDomain hdiv
  have hiR : ‖i‖ < adaptiveZetaCanonicalRadius r rho.1.im := by
    simpa only [Metric.mem_ball, dist_zero_right] using himem
  have hi1 : ‖i‖ < 1 := hiR.trans (adaptiveZetaCanonicalRadius_spec r rho.1.im).2.1
  let s : ℂ := 3 / 2 + Complex.I * (rho.1.im : ℂ) + i
  have hspos : 0 < s.re := by
    simp only [s, Complex.add_re, Complex.mul_re, Complex.div_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    norm_num
    linarith [(abs_le.mp (Complex.abs_re_le_norm i)).1]
  have hs0 : riemannZeta₁ s = 0 := adaptiveZetaPoleRemoved_eq_zero_of_divisor_ne_zero r rho.1.im hdiv
  let tau : NontrivialZetaZero := ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hs0⟩
  by_cases hsame : tau = rho
  · have he := congrArg (fun tau : NontrivialZetaZero => tau.1.re) hsame
    change s.re = rho.1.re at he
    norm_num [s] at he
    linarith [(abs_le.mp (Complex.abs_re_le_norm i)).1]
  · have he : (3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1 = -i := by
      change (3 / 2 + Complex.I * (rho.1.im : ℂ)) - s = -i
      dsimp [s]
      ring
    have h := hexposed tau hsame
    rw [he, norm_neg] at h
    exact h.le

end
end RiemannGaussian.ZetaExposedZero
