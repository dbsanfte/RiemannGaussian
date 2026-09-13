/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianPrimeBlocks
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Anchored prime correlations with the real phase retained

An anchored Schur inequality applies to every nonnegative summable phase
spectrum and every finite weighted configuration. Mirroring the whole
configuration removes the sine energy exactly: the remaining cosine
energy is the average of its ratio-phase and product-phase energies.

For the complete Gaussian prime measure this yields an unconditional
necessary correlation inequality in the original finite-zero budget.
An independent upper gap for this real pair energy would give a linear
arithmetic floor. That gap remains a hypothesis of the conditional floor
criterion; no new zero-free region or RH proof is obtained here.
-/

open RiemannGaussian
open scoped Classical

namespace RiemannGaussian.ZetaGaussianPrimeCorrelation
noncomputable section

/-- Finite phase work with an anchor at zero. -/
def work {ι : Type*} [Fintype ι] (a ω : ℕ → ℝ) (u w : ι → ℝ) : ℝ :=
  ∑ i, w i * zetaPhaseKernel a ω (u i)

/-- The full ratio energy of a finite phase configuration. -/
def energy {ι : Type*} [Fintype ι] (a ω : ℕ → ℝ) (u w : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, w i * w j * zetaPhaseKernel a ω (u j - u i)

/-- An anchored mixed phase energy keeps the linear response exactly. -/
theorem anchored_energy {ι : Type*} [Fintype ι] (a ω : ℕ → ℝ)
    (u w : ι → ℝ) (z : ℝ) :
    energy a ω (fun i : Option ι => i.elim 0 u) (fun i => i.elim z w) =
      (∑' n, a n) * z ^ 2 + 2 * work a ω u w * z + energy a ω u w := by
  simp only [energy, work, Fintype.sum_option, Option.elim_none, Option.elim_some,
    sub_zero, zero_sub, zetaPhaseKernel_zero, zetaPhaseKernel_neg,
    Finset.sum_add_distrib]
  simp_rw [mul_assoc (z : ℝ), ← Finset.mul_sum]
  simp_rw [mul_right_comm (w _ : ℝ) z, ← Finset.sum_mul]
  ring

/-- Schur's anchored inequality retains the signed work and every ratio. -/
theorem anchored_schur {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (r : ℕ) (hr : ω r = 0) {ι : Type*} [Fintype ι] (u w : ι → ℝ) :
    (work a ω u w - a r * (∑ i, w i)) ^ 2 ≤
      ((∑' n, a n) - a r) * (energy a ω u w - a r * (∑ i, w i) ^ 2) := by
  have hquad (z : ℝ) :
      0 ≤ ((∑' n, a n) - a r) * (z * z) +
        (2 * (work a ω u w - a r * (∑ i, w i))) * z +
        (energy a ω u w - a r * (∑ i, w i) ^ 2) := by
    have h := zetaPhase_gramEnergy_zeroFrequency_le ha hs r hr
      (fun i : Option ι => i.elim 0 u) (fun i => i.elim z w)
    change a r * (∑ i : Option ι, i.elim z w) ^ 2 ≤
      energy a ω (fun i : Option ι => i.elim 0 u) (fun i => i.elim z w) at h
    rw [anchored_energy, Fintype.sum_option] at h
    simp only [Option.elim_none, Option.elim_some] at h
    nlinarith only [h]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith only [hd]

/-- The product-phase energy supplies the absolute phase missing from ratios. -/
def productEnergy {ι : Type*} [Fintype ι] (a ω : ℕ → ℝ) (u w : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, w i * w j * zetaPhaseKernel a ω (u j + u i)

/-- Mirroring the whole configuration retains its signed work. -/
theorem mirrored_work {ι : Type*} [Fintype ι] (a ω : ℕ → ℝ) (u w : ι → ℝ) :
    work a ω (fun i : Bool × ι => if i.1 then u i.2 else -u i.2)
      (fun i => w i.2 / 2) = work a ω u w := by
  simp only [work, Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true,
    if_false, if_true, zetaPhaseKernel_neg]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  ring

/-- Mirroring cancels the sine channel before taking any energy bound. -/
theorem mirrored_energy {ι : Type*} [Fintype ι] (a ω : ℕ → ℝ) (u w : ι → ℝ) :
    energy a ω (fun i : Bool × ι => if i.1 then u i.2 else -u i.2)
      (fun i => w i.2 / 2) = (energy a ω u w + productEnergy a ω u w) / 2 := by
  have hneg (v z : ℝ) : zetaPhaseKernel a ω (-v - z) = zetaPhaseKernel a ω (v + z) := by
    rw [show -v - z = -(v + z) by ring, zetaPhaseKernel_neg]
  simp only [energy, productEnergy, Fintype.sum_prod_type, Fintype.sum_bool,
    Bool.false_eq_true, if_false, if_true, sub_neg_eq_add, hneg,
    Finset.sum_add_distrib]
  ring_nf
  simp_rw [← Finset.sum_mul]
  ring

/-- The sharper anchored Schur bound uses cosine energy only, while retaining
both the ratio and product phases in its exact arithmetic expression. -/
theorem cosine_schur {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (r : ℕ) (hr : ω r = 0) {ι : Type*} [Fintype ι] (u w : ι → ℝ) :
    (work a ω u w - a r * (∑ i, w i)) ^ 2 ≤
      ((∑' n, a n) - a r) *
        ((energy a ω u w + productEnergy a ω u w) / 2 - a r * (∑ i, w i) ^ 2) := by
  have h := anchored_schur ha hs r hr
    (fun i : Bool × ι => if i.1 then u i.2 else -u i.2) (fun i => w i.2 / 2)
  rw [mirrored_work, mirrored_energy] at h
  simpa only [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_div,
    add_self_div_two] using h

/-- The ratio-product average is the exact convergent cosine-channel energy. -/
theorem hasSum_cosineEnergy {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {ι : Type*} [Fintype ι] (u w : ι → ℝ) :
    HasSum (fun n => a n * (∑ i, w i * Real.cos (ω n * u i)) ^ 2)
      ((energy a ω u w + productEnergy a ω u w) / 2) := by
  have h := hasSum_zetaPhase_gramEnergy (ω := ω) ha hs
    (fun i : Bool × ι => if i.1 then u i.2 else -u i.2) (fun i => w i.2 / 2)
  change HasSum _ (energy a ω (fun i : Bool × ι => if i.1 then u i.2 else -u i.2)
    (fun i => w i.2 / 2)) at h
  rw [mirrored_energy] at h
  apply h.congr_fun
  intro n
  rw [finiteCosinePhaseEnergy_eq_squares]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true,
    if_false, if_true, mul_neg, Real.cos_neg, Real.sin_neg]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_neg_distrib]
  ring_nf
  simp_rw [← Finset.sum_mul]
  ring

/-- Discarding the sine channel can only reduce the required energy allowance. -/
theorem cosineEnergy_le_energy {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {ι : Type*} [Fintype ι] (u w : ι → ℝ) :
    (energy a ω u w + productEnergy a ω u w) / 2 ≤ energy a ω u w := by
  have hc := hasSum_cosineEnergy (ω := ω) ha hs u w
  have h := hasSum_zetaPhase_gramEnergy (ω := ω) ha hs u w
  rw [← hc.tsum_eq]
  change _ ≤ energy a ω u w
  change HasSum _ (energy a ω u w) at h
  rw [← h.tsum_eq]
  apply hc.summable.tsum_le_tsum _ h.summable
  intro n
  rw [finiteCosinePhaseEnergy_eq_squares]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) (ha n)
/-- A small signed response forces a large joint phase energy. -/
theorem forced_correlation {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (r : ℕ) (hr : ω r = 0) {ι : Type*} [Fintype ι] (u w : ι → ℝ) :
    a r * (∑' n, a n) * (∑ i, w i) ^ 2 ≤
      ((∑' n, a n) - a r) * ((energy a ω u w + productEnergy a ω u w) / 2) +
        2 * a r * (∑ i, w i) * work a ω u w := by
  have h := cosine_schur ha hs r hr u w
  nlinarith only [h, sq_nonneg (work a ω u w)]

/-- The entire pair sum retains logarithmic prime ratios and all mixed phases. -/
def ratioEnergy (a ω W : ℕ → ℝ) (t : ℝ) (S : Finset ℕ) : ℝ :=
  ∑ p ∈ S, ∑ q ∈ S, W p * W q *
    zetaPhaseKernel a ω (t * (Real.log q - Real.log p))

/-- The explicit ratio sum is exactly the finite phase energy. -/
theorem ratioEnergy_eq_energy (a ω W : ℕ → ℝ) (t : ℝ) (S : Finset ℕ) :
    ratioEnergy a ω W t S =
      energy a ω (fun p : S => t * Real.log p.val) (fun p : S => W p.val) := by
  unfold ratioEnergy energy
  rw [Finset.sum_coe_sort S (fun p => ∑ q : S, W p * W q.val *
    zetaPhaseKernel a ω (t * Real.log q.val - t * Real.log p))]
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [mul_sub]
  exact (Finset.sum_coe_sort S (fun q => W p * W q *
    zetaPhaseKernel a ω (t * Real.log q - t * Real.log p))).symm

/-- On positive support the retained difference is the logarithm of the actual ratio. -/
theorem ratioEnergy_eq_log_div (a ω W : ℕ → ℝ) (t : ℝ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, 0 < p) :
    ratioEnergy a ω W t S =
      ∑ p ∈ S, ∑ q ∈ S, W p * W q *
        zetaPhaseKernel a ω (t * Real.log ((q : ℝ) / p)) := by
  unfold ratioEnergy
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [Real.log_div (by exact_mod_cast (hS q hq).ne')
    (by exact_mod_cast (hS p hp).ne')]

/-- Both sine and cosine channels occur in the exact convergent ratio energy. -/
theorem hasSum_ratioEnergy {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (W : ℕ → ℝ) (t : ℝ) (S : Finset ℕ) :
    HasSum (fun n => a n *
      ((∑ p ∈ S, W p * Real.cos (ω n * (t * Real.log p))) ^ 2 +
       (∑ p ∈ S, W p * Real.sin (ω n * (t * Real.log p))) ^ 2))
      (ratioEnergy a ω W t S) := by
  have h := hasSum_zetaPhase_gramEnergy (ω := ω) ha hs
    (fun p : S => t * Real.log p.val) (fun p : S => W p.val)
  change HasSum _ (energy a ω (fun p : S => t * Real.log p.val)
    (fun p : S => W p.val)) at h
  rw [← ratioEnergy_eq_energy] at h
  apply h.congr_fun
  intro n
  rw [finiteCosinePhaseEnergy_eq_squares]
  rw [Finset.sum_coe_sort S (fun p => W p * Real.cos (ω n * (t * Real.log p))),
    Finset.sum_coe_sort S (fun p => W p * Real.sin (ω n * (t * Real.log p)))]

/-- The real prime energy keeps the ratio and product phases together. -/
def realPrimeEnergy (a ω W : ℕ → ℝ) (t : ℝ) (S : Finset ℕ) : ℝ :=
  (ratioEnergy a ω W t S + ∑ p ∈ S, ∑ q ∈ S, W p * W q *
    zetaPhaseKernel a ω (t * (Real.log q + Real.log p))) / 2

/-- The real prime energy is exactly the cosine projection of its full Gram. -/
theorem realPrimeEnergy_eq_cosineEnergy (a ω W : ℕ → ℝ) (t : ℝ) (S : Finset ℕ) :
    realPrimeEnergy a ω W t S =
      (energy a ω (fun p : S => t * Real.log p.val) (fun p : S => W p.val) +
        productEnergy a ω (fun p : S => t * Real.log p.val) (fun p : S => W p.val)) / 2 := by
  rw [realPrimeEnergy, ratioEnergy_eq_energy]
  congr 2
  unfold productEnergy
  rw [Finset.sum_coe_sort S (fun p => ∑ q : S, W p * W q.val *
    zetaPhaseKernel a ω (t * Real.log q.val + t * Real.log p))]
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [mul_add]
  exact (Finset.sum_coe_sort S (fun q => W p * W q *
    zetaPhaseKernel a ω (t * Real.log q + t * Real.log p))).symm

/-- Prime ratios and products give the exact anchored arithmetic coordinates. -/
theorem realPrimeEnergy_eq_log_products (a ω W : ℕ → ℝ) (t : ℝ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, 0 < p) :
    realPrimeEnergy a ω W t S =
      (∑ p ∈ S, ∑ q ∈ S, W p * W q *
        (zetaPhaseKernel a ω (t * Real.log ((q : ℝ) / p)) +
         zetaPhaseKernel a ω (t * Real.log ((q : ℝ) * p)))) / 2 := by
  rw [realPrimeEnergy, ratioEnergy_eq_log_div a ω W t S hS]
  simp_rw [mul_add, Finset.sum_add_distrib]
  congr 2
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [Real.log_mul (by exact_mod_cast (hS q hq).ne')
    (by exact_mod_cast (hS p hp).ne'), mul_add]

/-- The anchored arithmetic energy has an exact convergent cosine-square expansion. -/
theorem hasSum_realPrimeEnergy {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (W : ℕ → ℝ) (t : ℝ) (S : Finset ℕ) :
    HasSum (fun n => a n *
      (∑ p ∈ S, W p * Real.cos (ω n * (t * Real.log p))) ^ 2)
      (realPrimeEnergy a ω W t S) := by
  have h := hasSum_cosineEnergy (ω := ω) ha hs
    (fun p : S => t * Real.log p.val) (fun p : S => W p.val)
  rw [← realPrimeEnergy_eq_cosineEnergy] at h
  apply h.congr_fun
  intro n
  rw [Finset.sum_coe_sort S (fun p => W p * Real.cos (ω n * (t * Real.log p)))]

/-- The exact excess in the ratio-only energy is the convergent sine energy. -/
theorem hasSum_sineDefect {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (W : ℕ → ℝ) (t : ℝ) (S : Finset ℕ) :
    HasSum (fun n => a n *
      (∑ p ∈ S, W p * Real.sin (ω n * (t * Real.log p))) ^ 2)
      (ratioEnergy a ω W t S - realPrimeEnergy a ω W t S) := by
  have h := (hasSum_ratioEnergy (ω := ω) ha hs W t S).sub
    (hasSum_realPrimeEnergy (ω := ω) ha hs W t S)
  apply h.congr_fun
  intro n
  ring

/-- The real energy is no larger than the ratio-only energy; the removed
allowance is precisely a nonnegative sine-channel energy. -/
theorem realPrimeEnergy_le_ratioEnergy {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (W : ℕ → ℝ) (t : ℝ) (S : Finset ℕ) :
    realPrimeEnergy a ω W t S ≤ ratioEnergy a ω W t S := by
  have h := hasSum_sineDefect (ω := ω) ha hs W t S
  have hn : 0 ≤ ratioEnergy a ω W t S - realPrimeEnergy a ω W t S := by
    rw [← h.tsum_eq]
    exact tsum_nonneg fun n => mul_nonneg (ha n) (sq_nonneg _)
  linarith

/-- Low actual Gaussian prime work requires collective ratio correlation.
The full three-response amplitude and all finite mixed terms are retained. -/
theorem gaussian_forced_correlation {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hP : ∀ u, 0 ≤ zetaPhaseKernel a ω u) (r : ℕ) (hr : ω r = 0)
    (k : ℕ) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (t : ℝ) (S : Finset ℕ) :
    a r * (∑' n, a n) * (∑ p ∈ S, ZetaGaussianPrimeBlocks.amplitude k B x p) ^ 2 ≤
      ((∑' n, a n) - a r) *
        realPrimeEnergy a ω (ZetaGaussianPrimeBlocks.amplitude k B x) t S +
      2 * a r * (∑ p ∈ S, ZetaGaussianPrimeBlocks.amplitude k B x p) *
        ZetaGaussianStripPhaseFamily.mixedWork k B x t a ω := by
  have h := forced_correlation ha hs r hr
    (fun p : S => t * Real.log p.val)
    (fun p : S => ZetaGaussianPrimeBlocks.amplitude k B x p.val)
  rw [← realPrimeEnergy_eq_cosineEnergy] at h
  simp only [work, Finset.sum_coe_sort] at h
  rw [Finset.sum_coe_sort S (fun p => ZetaGaussianPrimeBlocks.amplitude k B x p *
    zetaPhaseKernel a ω (t * Real.log p))] at h
  have hb := ZetaGaussianPrimeBlocks.finite_work_le ha hs hP k hB hx t S
  have hM : 0 ≤ ∑ p ∈ S, ZetaGaussianPrimeBlocks.amplitude k B x p :=
    Finset.sum_nonneg fun p _ => ZetaGaussianPrimeBlocks.amplitude_nonneg k hB.le hx p
  have hscale : 0 ≤ 2 * a r * (∑ p ∈ S, ZetaGaussianPrimeBlocks.amplitude k B x p) :=
    mul_nonneg (mul_nonneg (by norm_num) (ha r)) hM
  have hc := mul_le_mul_of_nonneg_left hb hscale
  exact h.trans (add_le_add_right hc _)

/-- A quantitative gap in the full ratio energy gives a linear floor for
actual Gaussian prime work. The energy gap is an explicit remaining premise. -/
theorem gaussian_work_of_energy_gap {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hP : ∀ u, 0 ≤ zetaPhaseKernel a ω u) (r : ℕ) (hr : ω r = 0) (har : 0 < a r)
    (k : ℕ) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (t : ℝ) (S : Finset ℕ)
    (hM : 0 < ∑ p ∈ S, ZetaGaussianPrimeBlocks.amplitude k B x p) (δ : ℝ)
    (hgap : ((∑' n, a n) - a r) *
        realPrimeEnergy a ω (ZetaGaussianPrimeBlocks.amplitude k B x) t S ≤
      a r * ((∑' n, a n) - 2 * δ) *
        (∑ p ∈ S, ZetaGaussianPrimeBlocks.amplitude k B x p) ^ 2) :
    δ * (∑ p ∈ S, ZetaGaussianPrimeBlocks.amplitude k B x p) ≤
      ZetaGaussianStripPhaseFamily.mixedWork k B x t a ω := by
  have h := gaussian_forced_correlation ha hs hP r hr k hB hx t S
  by_contra hcontra
  have hm := mul_lt_mul_of_pos_left (lt_of_not_ge hcontra)
    (by positivity : 0 < 2 * a r * (∑ p ∈ S, ZetaGaussianPrimeBlocks.amplitude k B x p))
  nlinarith only [h, hgap, hm]

/-- The actual finite zero group forces the full squared real-correlation constraint.
Both product and ratio phases, and the signed boundary mean, remain in the original budget. -/
theorem finite_source_correlation_constraint {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hP : ∀ u, 0 ≤ zetaPhaseKernel a ω u)
    (hω0 : ω 0 = 0) (hω1 : ω 1 = 1) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => ZetaAngularPhaseAllowance.tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 2 ≤ k) {B x M : ℝ} (hB : 0 < B) (hx : 0 < x)
    (hx' : x ≤ DerivativeOrderComparison.delta k / 4) (hM : 0 ≤ M)
    (t : ℝ) (Z : Finset NontrivialZetaZero) (hscale : 1 ≤ ZetaNearOneBudgetLimit.scale t)
    (S : Finset ℕ) :
    (max 0 (a 0 * (∑ p ∈ S, ZetaGaussianPrimeBlocks.amplitude k B x p) +
        (a 1 * ∑ ρ ∈ Z, ZetaGaussianNearCancellation.compensated B
          (ZetaStripEulerConstraint.halfWidth k x) (ZetaNearOneLocalDisc.center x t) ρ) -
        ZetaGaussianStripPhaseFamily.exactBudget k B M x t a ω)) ^ 2 ≤
      ((∑' n, a n) - a 0) *
        (realPrimeEnergy a ω (ZetaGaussianPrimeBlocks.amplitude k B x) t S -
          a 0 * (∑ p ∈ S, ZetaGaussianPrimeBlocks.amplitude k B x p) ^ 2) := by
  have h := cosine_schur ha hs 0 hω0
    (fun p : S => t * Real.log p.val)
    (fun p : S => ZetaGaussianPrimeBlocks.amplitude k B x p.val)
  rw [← realPrimeEnergy_eq_cosineEnergy] at h
  simp only [work, Finset.sum_coe_sort] at h
  rw [Finset.sum_coe_sort S (fun p => ZetaGaussianPrimeBlocks.amplitude k B x p *
    zetaPhaseKernel a ω (t * Real.log p))] at h
  have hb := ZetaGaussianPrimeBlocks.finite_work_le ha hs hP k hB hx t S
  have hz := ZetaGaussianStripPhaseFamily.finite_source_add_mixedWork_le_exactBudget
    ha hs hω0 hω1 hω hlog k hk hB hx hx' hM t Z hscale
  let b := ∑ p ∈ S, ZetaGaussianPrimeBlocks.amplitude k B x p *
    zetaPhaseKernel a ω (t * Real.log p)
  let c := a 0 * (∑ p ∈ S, ZetaGaussianPrimeBlocks.amplitude k B x p)
  let F := a 1 * ∑ ρ ∈ Z, ZetaGaussianNearCancellation.compensated B
    (ZetaStripEulerConstraint.halfWidth k x) (ZetaNearOneLocalDisc.center x t) ρ
  let D := ZetaGaussianStripPhaseFamily.exactBudget k B M x t a ω
  have hbc : c + F - D ≤ -(b - c) := by
    dsimp [b, c, F, D]
    linarith only [hb, hz]
  have hmax : max 0 (c + F - D) ≤ |b - c| :=
    max_le (abs_nonneg _) (hbc.trans (neg_le_abs _))
  have hsq := mul_self_le_mul_self (le_max_left 0 (c + F - D)) hmax
  have habs := sq_abs (b - c)
  change (b - c) ^ 2 ≤ _ at h
  change (max 0 (c + F - D)) ^ 2 ≤ _
  nlinarith only [h, hsq, habs]


/-- Product and ratio logarithms diagonalize the actual Gaussian prime-pair
weight and retain the exact logarithmic separation factor. -/
theorem gaussian_pair_coordinates (σ B : ℝ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ZetaGaussianPhaseArithmetic.amplitude σ B p *
        ZetaGaussianPhaseArithmetic.amplitude σ B q =
      ((Real.log q + Real.log p) ^ 2 - (Real.log q - Real.log p) ^ 2) / 4 *
        Real.exp (-σ * (Real.log q + Real.log p)) *
        Real.exp (-(B / 2) * (Real.log q + Real.log p) ^ 2) *
        Real.exp (-(B / 2) * (Real.log q - Real.log p) ^ 2) := by
  simp only [ZetaGaussianPhaseArithmetic.amplitude, zetaPhasePrimeWeight,
    ArithmeticFunction.vonMangoldt_apply_prime hp, ArithmeticFunction.vonMangoldt_apply_prime hq,
    GaussianFermiZeroPair.window]
  have he : Real.exp (-σ * Real.log p) * Real.exp (-B * Real.log p ^ 2) *
        Real.exp (-σ * Real.log q) * Real.exp (-B * Real.log q ^ 2) =
      Real.exp (-σ * (Real.log q + Real.log p)) *
        Real.exp (-(B / 2) * (Real.log q + Real.log p) ^ 2) *
        Real.exp (-(B / 2) * (Real.log q - Real.log p) ^ 2) := by
    simp only [← Real.exp_add]
    congr 1
    ring
  calc
    _ = Real.log p * Real.log q *
        (Real.exp (-σ * Real.log p) * Real.exp (-B * Real.log p ^ 2) *
          Real.exp (-σ * Real.log q) * Real.exp (-B * Real.log q ^ 2)) := by ring
    _ = _ := by rw [he]; ring

end
end RiemannGaussian.ZetaGaussianPrimeCorrelation
