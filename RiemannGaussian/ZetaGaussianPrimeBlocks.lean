/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianStripPhaseFamily
import RiemannGaussian.ZetaGaussianScaledBandBudget
import RiemannGaussian.ZetaPhaseWeightedRecurrence
import Mathlib.Data.Nat.Prime.Int

/-!
# The common prime measure and disjoint weighted phase blocks

All three original Gaussian-strip prime responses use the same phase
kernel. Their complete arithmetic amplitudes can therefore be combined
before keeping disjoint prime-power blocks. The weighted Gram recurrence
retains every triangular return multiplicity. No independent bound on the
centered signed prime carrier is assumed or proved by this transport.
-/

namespace RiemannGaussian.ZetaGaussianPrimeBlocks
noncomputable section
open Complex
open ZetaGaussianStripPhaseFamily ZetaNearOneLocalDisc ZetaNearOneBudgetLimit
open ZetaStripEulerConstraint ZetaAngularPhaseAllowance
open scoped Classical

/-- The full common amplitude of the Gaussian, Euler and averaged
logarithmic prime responses, with their original multipliers. -/
def amplitude (k : ℕ) (B x : ℝ) (m : ℕ) : ℝ :=
  ZetaGaussianPhaseArithmetic.amplitude (1 + x) B m +
    factor k B x * zetaPhasePrimeWeight (rightLine k x) m +
    ZetaSechPrimeBoundary.amplitude (rightLine k x) (verticalScale k x) m /
      (2 * halfWidth k x)

/-- Each term of the common prime measure is nonnegative. -/
theorem amplitude_nonneg (k : ℕ) {B x : ℝ} (hB : 0 ≤ B) (hx : 0 < x) (m : ℕ) :
    0 ≤ amplitude k B x m := by
  have hη := halfWidth_pos k hx
  unfold amplitude factor
  exact add_nonneg (add_nonneg (ZetaGaussianPhaseArithmetic.amplitude_nonneg _ _ _)
    (mul_nonneg (by positivity) (zetaPhasePrimeWeight_nonneg _ _)))
    (div_nonneg (ZetaSechPrimeBoundary.amplitude_nonneg _ _ _) (by positivity))

/-- The complete common arithmetic mass is summable. -/
theorem summable_amplitude (k : ℕ) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) :
    Summable (amplitude k B x) := by
  exact ((ZetaGaussianPhaseArithmetic.summable_amplitude (by linarith) hB).add
    ((hasSum_zetaPhasePrimeWeight (rightLine_gt_one k hx)).summable.mul_left (factor k B x))).add
      ((ZetaSechPrimeBoundary.summable_amplitude (rightLine_gt_one k hx) _).div_const _)

/-- The three actual prime responses are one convergent sum against
their common phase kernel; no frequency or prime term is discarded. -/
theorem hasSum_mixedWork {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (k : ℕ) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (t : ℝ) :
    HasSum (fun m => amplitude k B x m * zetaPhaseKernel a ω (t * Real.log m))
      (mixedWork k B x t a ω) := by
  have hg := ZetaGaussianPhaseArithmetic.hasSum_arithmetic (ω := ω) ha hs
    (by linarith : 2 / 3 < 1 + x) hB t
  have he := (hasSum_zetaPhase_arithmetic (ω := ω) ha hs (rightLine_gt_one k hx) t).summable.hasSum
  have hb := ZetaSechPhaseFamily.hasSum_arithmetic (ω := ω) ha hs (rightLine_gt_one k hx)
    t (verticalScale k x)
  convert (hg.add (he.mul_left (factor k B x))).add (hb.div_const (2 * halfWidth k x)) using 1
  · funext m
    unfold amplitude
    ring
  · rfl

/-- The original constant work is precisely the mass of the same measure. -/
theorem constantWork_eq_sum (k : ℕ) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) :
    constantWork k B x = ∑' m, amplitude k B x m := by
  have hg := (ZetaGaussianPhaseArithmetic.summable_amplitude
    (by linarith : 2 / 3 < 1 + x) hB).hasSum
  have he := hasSum_zetaPhasePrimeWeight (rightLine_gt_one k hx)
  have hb := (ZetaSechPrimeBoundary.summable_amplitude (rightLine_gt_one k hx)
    (verticalScale k x)).hasSum
  have h := ((hg.add (he.mul_left (factor k B x))).add (hb.div_const (2 * halfWidth k x))).tsum_eq
  simpa only [amplitude, constantWork, ZetaGaussianPhaseArithmetic.ordinarySum_zero,
    ZetaSechPrimeBoundary.mean_zero_eq (rightLine_gt_one k hx)] using h.symm

/-- Every finite set retains its full actual contribution below the
combined arithmetic work, rather than below three separate totals. -/
theorem finite_work_le {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hP : ∀ u, 0 ≤ zetaPhaseKernel a ω u) (k : ℕ) {B x : ℝ}
    (hB : 0 < B) (hx : 0 < x) (t : ℝ) (S : Finset ℕ) :
    (∑ m ∈ S, amplitude k B x m * zetaPhaseKernel a ω (t * Real.log m)) ≤
      mixedWork k B x t a ω := by
  have h := hasSum_mixedWork (ω := ω) ha hs k hB hx t
  rw [← h.tsum_eq]
  exact h.summable.sum_le_tsum S
    (fun m _ => mul_nonneg (amplitude_nonneg k hB.le hx m) (hP _))

/-- The nonnegative reserve forced by a whole triangular phase block. -/
def reserve (a₀ A : ℝ) (H : ℕ) : ℝ :=
  max 0 (((H : ℝ) + 1) * (((H : ℝ) + 1) * a₀ - A) / 2)

/-- A block's weighted Gram reserve is paid by that block's own
arithmetic sum. This avoids reusing the complete prime sum for each block. -/
theorem block_lower {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hP : ∀ u, 0 ≤ zetaPhaseKernel a ω u) (r : ℕ) (hr : ω r = 0)
    (W : ℕ → ℝ) (hW : ∀ m, 0 ≤ W m) (p H : ℕ)
    {c : ℝ} (hc : 0 ≤ c)
    (hcost : ∀ j, 1 ≤ j → j ≤ H → ((H + 1 - j : ℕ) : ℝ) * c ≤ W (p ^ j)) (t : ℝ) :
    c * reserve (a r) (∑' n, a n) H ≤
      ∑ j ∈ Finset.range H, W (p ^ (j + 1)) *
        zetaPhaseKernel a ω (t * Real.log (p ^ (j + 1) : ℕ)) := by
  have hg := mul_le_mul_of_nonneg_left
    (zetaPhase_weighted_returns_le ha hs r hr H (t * Real.log p)) hc
  have hw : c * (∑ j ∈ Finset.range H, ((H - j : ℕ) : ℝ) *
      zetaPhaseKernel a ω (((j + 1 : ℕ) : ℝ) * (t * Real.log p))) ≤
      ∑ j ∈ Finset.range H, W (p ^ (j + 1)) *
        zetaPhaseKernel a ω (t * Real.log (p ^ (j + 1) : ℕ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjH := Finset.mem_range.mp hj
    have h := hcost (j + 1) (by omega) (by omega)
    rw [show H + 1 - (j + 1) = H - j by omega] at h
    have he : t * Real.log (p ^ (j + 1) : ℕ) =
        ((j + 1 : ℕ) : ℝ) * (t * Real.log p) := by
      rw [Nat.cast_pow, Real.log_pow]
      ring
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_right h (hP (((j + 1 : ℕ) : ℝ) * (t * Real.log p)))]
  rw [reserve, mul_max_of_nonneg _ _ hc, mul_zero]
  apply max_le
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (hW _) (hP _))
  · nlinarith only [hg, hw]

/-- Distinct prime bases have disjoint positive-power blocks, even
when their lengths are chosen separately. -/
theorem blocks_disjoint (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (H : ℕ → ℕ) :
    Set.PairwiseDisjoint (↑S) (fun p => (Finset.range (H p)).image (fun j => p ^ (j + 1))) := by
  intro p hp q hq hpq
  apply Finset.disjoint_left.mpr
  intro m hm hn
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hn
  exact hpq ((hS p hp).pow_inj (hS q hq) he.symm).1

/-- Every collection of disjoint prime-power blocks gives one valid
lower bound on the original full Gaussian-strip arithmetic work. -/
theorem blocks_lower {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hP : ∀ u, 0 ≤ zetaPhaseKernel a ω u) (r : ℕ) (hr : ω r = 0)
    (k : ℕ) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (t : ℝ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (H : ℕ → ℕ) (c : ℕ → ℝ)
    (hc : ∀ p ∈ S, 0 ≤ c p)
    (hcost : ∀ p ∈ S, ∀ j, 1 ≤ j → j ≤ H p →
      ((H p + 1 - j : ℕ) : ℝ) * c p ≤ amplitude k B x (p ^ j)) :
    (∑ p ∈ S, c p * reserve (a r) (∑' n, a n) (H p)) ≤ mixedWork k B x t a ω := by
  let T (p : ℕ) := (Finset.range (H p)).image (fun j => p ^ (j + 1))
  have hf := finite_work_le ha hs hP k hB hx t (S.biUnion T)
  rw [Finset.sum_biUnion (blocks_disjoint S hS H)] at hf
  apply le_trans _ hf
  apply Finset.sum_le_sum
  intro p hp
  rw [Finset.sum_image (fun i _ j _ hij =>
    Nat.add_right_cancel (Nat.pow_right_injective (hS p hp).two_le hij))]
  exact block_lower ha hs hP r hr _ (amplitude_nonneg k hB.le hx) p
    (H p) (hc p hp) (hcost p hp) t

/-- The last Gaussian prime-power amplitude pays for a full triangular
block, with its logarithmic prime weight and Gaussian factor explicit. -/
def gaussianCoefficient (B x : ℝ) (p H : ℕ) : ℝ :=
  zetaPhasePrimeBlockWeight (1 + x) p H *
    GaussianFermiZeroPair.window B ((H : ℝ) * Real.log p)

/-- Every such actual Gaussian block coefficient is positive. -/
theorem gaussianCoefficient_pos (B x : ℝ) {p : ℕ} (hp : p.Prime) (H : ℕ) :
    0 < gaussianCoefficient B x p H :=
  mul_pos (zetaPhasePrimeBlockWeight_pos _ hp _) (Real.exp_pos _)

/-- The complete common amplitude dominates its original Gaussian part. -/
theorem gaussian_le_amplitude (k : ℕ) {B x : ℝ} (hB : 0 ≤ B) (hx : 0 < x) (m : ℕ) :
    ZetaGaussianPhaseArithmetic.amplitude (1 + x) B m ≤ amplitude k B x m := by
  have hη := halfWidth_pos k hx
  unfold amplitude factor
  have h₁ : 0 ≤ 24 * B / halfWidth k x ^ 2 * zetaPhasePrimeWeight (rightLine k x) m :=
    mul_nonneg (by positivity) (zetaPhasePrimeWeight_nonneg _ _)
  have h₂ : 0 ≤ ZetaSechPrimeBoundary.amplitude (rightLine k x) (verticalScale k x) m /
      (2 * halfWidth k x) := div_nonneg (ZetaSechPrimeBoundary.amplitude_nonneg _ _ _) (by positivity)
  linarith

/-- Actual Gaussian amplitudes pay every triangular return multiplicity.
The Gaussian damping improves in the same direction as the Euler weights. -/
theorem gaussianCoefficient_triangle_le (k : ℕ) {B x : ℝ} (hB : 0 ≤ B) (hx : 0 < x)
    {p : ℕ} (hp : p.Prime) {H j : ℕ} (hj : 1 ≤ j) (hjH : j ≤ H) :
    ((H + 1 - j : ℕ) : ℝ) * gaussianCoefficient B x p H ≤ amplitude k B x (p ^ j) := by
  have ht := zetaPhasePrimeBlockWeight_triangle_le (by linarith : 1 ≤ 1 + x) hp hj hjH
  have hg : GaussianFermiZeroPair.window B ((H : ℝ) * Real.log p) ≤
      GaussianFermiZeroPair.window B (Real.log (p ^ j : ℕ)) := by
    rw [Nat.cast_pow, Real.log_pow]
    unfold GaussianFermiZeroPair.window
    apply Real.exp_le_exp.mpr
    have hjr : (j : ℝ) ≤ H := by exact_mod_cast hjH
    have hlog := Real.log_natCast_nonneg p
    have hsq : ((j : ℝ) * Real.log p) ^ 2 ≤ ((H : ℝ) * Real.log p) ^ 2 := by
      gcongr
    nlinarith only [mul_le_mul_of_nonneg_left hsq hB]
  have h := mul_le_mul ht hg (Real.exp_pos _).le (zetaPhasePrimeWeight_nonneg _ _)
  change _ ≤ zetaPhasePrimeWeight (1 + x) (p ^ j) *
    GaussianFermiZeroPair.window B (Real.log (p ^ j : ℕ)) at h
  apply le_trans _ (gaussian_le_amplitude k hB hx (p ^ j))
  simpa only [gaussianCoefficient, ZetaGaussianPhaseArithmetic.amplitude, mul_assoc] using h

/-- A fully discharged arithmetic floor for arbitrary distinct-prime
collections and individually chosen block lengths, at every detector height. -/
theorem gaussian_blocks_lower {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hP : ∀ u, 0 ≤ zetaPhaseKernel a ω u) (r : ℕ) (hr : ω r = 0)
    (k : ℕ) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (t : ℝ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (H : ℕ → ℕ) :
    (∑ p ∈ S, gaussianCoefficient B x p (H p) * reserve (a r) (∑' n, a n) (H p)) ≤
      mixedWork k B x t a ω :=
  blocks_lower ha hs hP r hr k hB hx t S hS H
    (fun p => gaussianCoefficient B x p (H p))
    (fun p hp => (gaussianCoefficient_pos B x (hS p hp) _).le)
    (fun p hp j hj hjH => gaussianCoefficient_triangle_le (j := j) k hB.le hx (hS p hp) hj hjH)

private theorem half_le_log_prime {p : ℕ} (hp : p.Prime) : 1 / 2 ≤ Real.log p := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h
  exact h.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le))

/-- The full common amplitude on a proper prime power has a uniform
majorant throughout the original Gaussian dilation family. -/
theorem scaled_amplitude_prime_power_le {q : ℝ} (hq : 1 ≤ q)
    {p H : ℕ} (hp : p.Prime) (hH : 2 ≤ H) :
    amplitude 9 (ZetaGaussianScaledBandBudget.gaussianScale q)
      (ZetaGaussianScaledBandBudget.shift q) (p ^ H) ≤
        96 * zetaPhasePrimeBlockWeight 1 p H := by
  let B := ZetaGaussianScaledBandBudget.gaussianScale q
  let x := ZetaGaussianScaledBandBudget.shift q
  have hB : 0 < B := (ZetaGaussianScaledBandBudget.gaussianScale_bounds hq).1
  have hx : 0 < x := (ZetaGaussianScaledBandBudget.shift_bounds hq).1
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hweight {σ : ℝ} (hσ : 1 ≤ σ) :
      zetaPhasePrimeWeight σ (p ^ H) ≤ zetaPhasePrimeBlockWeight 1 p H := by
    rw [zetaPhasePrimeWeight, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow]
    unfold zetaPhasePrimeBlockWeight
    apply mul_le_mul_of_nonneg_left _ hlog.le
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hσ (mul_nonneg hHpos.le hlog.le)]
  have hg : ZetaGaussianPhaseArithmetic.amplitude (1 + x) B (p ^ H) ≤
      zetaPhasePrimeBlockWeight 1 p H := by
    have hw : GaussianFermiZeroPair.window B (Real.log (p ^ H : ℕ)) ≤ 1 := by
      unfold GaussianFermiZeroPair.window
      exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (Real.log (p ^ H : ℕ))])
    exact (mul_le_of_le_one_right (zetaPhasePrimeWeight_nonneg _ _) hw).trans
      (hweight (by linarith))
  have he := mul_le_mul (ZetaGaussianScaledBandBudget.factor_bounds hq).2
    (hweight (rightLine_gt_one 9 hx).le) (zetaPhasePrimeWeight_nonneg _ _) (by norm_num : (0 : ℝ) ≤ 1 / 50000)
  have hcoeff : ZetaLogPrimeSeries.coefficient (p ^ H) ≤ Real.log p := by
    rw [ZetaLogPrimeSeries.coefficient, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow]
    have hd : Real.log p / ((H : ℝ) * Real.log p) = 1 / H := by field_simp
    rw [hd]
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (by exact_mod_cast hH)).trans (half_le_log_prime hp)
  have hs : ZetaSechPrimeBoundary.amplitude (rightLine 9 x) (verticalScale 9 x) (p ^ H) ≤
      zetaPhasePrimeBlockWeight 1 p H := by
    apply (ZetaSechPrimeBoundary.amplitude_le _ _ _).trans
    unfold ZetaLogPrimeSeries.weight zetaPhasePrimeBlockWeight
    rw [Nat.cast_pow, Real.log_pow]
    apply mul_le_mul hcoeff _ (Real.exp_pos _).le hlog.le
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right (rightLine_gt_one 9 hx).le
      (mul_nonneg hHpos.le hlog.le)]
  have hη := halfWidth_pos 9 hx
  have hb := mul_le_mul hs (ZetaGaussianScaledBandBudget.geometry hq).2.2.1
    (by positivity : (0 : ℝ) ≤ 1 / (2 * halfWidth 9 x))
    (zetaPhasePrimeBlockWeight_pos 1 hp H).le
  rw [mul_one_div] at hb
  change amplitude 9 B x (p ^ H) ≤ _
  unfold amplitude
  change factor 9 B x * zetaPhasePrimeWeight (rightLine 9 x) (p ^ H) ≤ _ at he
  nlinarith only [hg, he, hb, (zetaPhasePrimeBlockWeight_pos 1 hp H).le]

/-- Quadratic triangular multiplicities cannot offset prime-power
damping: the bound is uniform in every prime and every block length. -/
theorem weighted_damping_le {p H : ℕ} (hp : p.Prime) (hH : 2 ≤ H) :
    ((H : ℝ) + 1) ^ 2 * zetaPhasePrimeBlockWeight 1 p H ≤
      9 * zetaPhasePrimeWeight 2 p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hpoly (n : ℕ) : ((n : ℝ) + 3) ^ 2 ≤ 9 * (p : ℝ) ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hs : ((n : ℝ) + 4) ^ 2 ≤ (p : ℝ) * ((n : ℝ) + 3) ^ 2 := by
        nlinarith only [hn, sq_nonneg (n : ℝ), mul_le_mul_of_nonneg_right hp2 (sq_nonneg ((n : ℝ) + 3))]
      have hh := hs.trans (mul_le_mul_of_nonneg_left ih hp0.le)
      simpa only [Nat.cast_add, Nat.cast_one, pow_succ, add_assoc, show (1 : ℝ) + 3 = 4 by norm_num,
        mul_assoc, mul_left_comm, mul_comm] using hh
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hH
  have he : (p : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log p) := by
    rw [Real.exp_nat_mul, Real.exp_log hp0]
  have hm := mul_le_mul_of_nonneg_right (hpoly n)
    (Real.exp_pos (-((n : ℝ) + 2) * Real.log p)).le
  rw [he, mul_assoc, ← Real.exp_add] at hm
  have hex : (n : ℝ) * Real.log p + -((n : ℝ) + 2) * Real.log p = -2 * Real.log p := by ring
  rw [hex] at hm
  have h := mul_le_mul_of_nonneg_left hm (Real.log_natCast_nonneg p)
  unfold zetaPhasePrimeBlockWeight zetaPhasePrimeWeight
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  push_cast
  simpa only [show (2 : ℝ) + (n : ℝ) = (n : ℝ) + 2 by ring, add_assoc,
    show (2 : ℝ) + 1 = 3 by norm_num, neg_one_mul, mul_assoc, mul_left_comm, mul_comm] using h

/-- A positive weighted reserve needs at least two returns when the
total coefficient mass is at least twice its constant channel. -/
theorem reserve_eq_zero_of_le_one {a₀ A : ℝ} (ha₀ : 0 ≤ a₀) (hA : 2 * a₀ ≤ A)
    {H : ℕ} (hH : H ≤ 1) : reserve a₀ A H = 0 := by
  interval_cases H <;> unfold reserve <;> apply max_eq_left <;> norm_num <;> linarith

/-- The complete weighted reserve has its exact quadratic coefficient
ceiling, before any prime-power damping is applied. -/
theorem reserve_le {a₀ A : ℝ} (ha₀ : 0 ≤ a₀) (hA : 0 ≤ A) (H : ℕ) :
    reserve a₀ A H ≤ ((H : ℝ) + 1) ^ 2 * a₀ / 2 := by
  unfold reserve
  apply max_le
  · positivity
  · nlinarith only [mul_nonneg (show 0 ≤ (H : ℝ) + 1 by positivity) hA]

/-- No triangular block minorant of the actual combined amplitudes
can pay more than this fixed square-prime mass, regardless of block length. -/
theorem scaled_block_ceiling {q : ℝ} (hq : 1 ≤ q) {p H : ℕ} (hp : p.Prime)
    {a₀ A c : ℝ} (ha₀ : 0 ≤ a₀) (hA : 2 * a₀ ≤ A)
    (hcost : ∀ j, 1 ≤ j → j ≤ H → ((H + 1 - j : ℕ) : ℝ) * c ≤
      amplitude 9 (ZetaGaussianScaledBandBudget.gaussianScale q)
        (ZetaGaussianScaledBandBudget.shift q) (p ^ j)) :
    c * reserve a₀ A H ≤ 432 * a₀ * zetaPhasePrimeWeight 2 p := by
  by_cases hH : H ≤ 1
  · rw [reserve_eq_zero_of_le_one ha₀ hA hH, mul_zero]
    exact mul_nonneg (by positivity) (zetaPhasePrimeWeight_nonneg _ _)
  · have hH2 : 2 ≤ H := by omega
    have hlast := hcost H (by omega) le_rfl
    simp only [Nat.add_sub_cancel_left, Nat.cast_one, one_mul] at hlast
    have hc' := hlast.trans (scaled_amplitude_prime_power_le hq hp hH2)
    have hr := reserve_le (A := A) ha₀ (by linarith) H
    have h := mul_le_mul hc' hr (le_max_left 0 _)
      (mul_nonneg (by norm_num) (zetaPhasePrimeBlockWeight_pos 1 hp H).le)
    have hd := mul_le_mul_of_nonneg_left (weighted_damping_le hp hH2) ha₀
    nlinarith only [h, hd]

/-- Arbitrarily many distinct primes and independently chosen weighted
blocks still have a bounded total guaranteed reserve. The ceiling is
independent of height, dilation, prime cutoff and all block lengths. -/
theorem scaled_blocks_ceiling {q : ℝ} (hq : 1 ≤ q) {a₀ A : ℝ}
    (ha₀ : 0 ≤ a₀) (hA : 2 * a₀ ≤ A) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (H : ℕ → ℕ) (c : ℕ → ℝ)
    (hcost : ∀ p ∈ S, ∀ j, 1 ≤ j → j ≤ H p → ((H p + 1 - j : ℕ) : ℝ) * c p ≤
      amplitude 9 (ZetaGaussianScaledBandBudget.gaussianScale q)
        (ZetaGaussianScaledBandBudget.shift q) (p ^ j)) :
    (∑ p ∈ S, c p * reserve a₀ A (H p)) ≤
      432 * a₀ * (-logDeriv riemannZeta (2 : ℂ)).re := by
  have h := Finset.sum_le_sum (fun p hp =>
    scaled_block_ceiling hq (hS p hp) ha₀ hA (hcost p hp))
  rw [← Finset.mul_sum] at h
  have he := hasSum_zetaPhasePrimeWeight (by norm_num : (1 : ℝ) < 2)
  have hm := he.summable.sum_le_tsum S (fun p _ => zetaPhasePrimeWeight_nonneg 2 p)
  rw [he.tsum_eq] at hm
  exact h.trans (mul_le_mul_of_nonneg_left hm (by positivity))

/-- The current first-channel enclosure pays for twice the constant
mass, using the actual complete coefficient sum. -/
theorem two_constant_le_mass {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (h01 : a 0 ≤ a 1) : 2 * a 0 ≤ ∑' n, a n := by
  have h : a 0 + a 1 ≤ ∑' n, a n := by
    simpa using hs.sum_le_tsum ({0, 1} : Finset ℕ) (fun n _ => ha n)
  linarith

/-- The all-block ceiling applies to every coefficient family in the
current Gaussian enclosure, with its entire mass premise discharged. -/
theorem eligible_blocks_ceiling {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (ha0 : a 0 ≤ 37 / 200) (ha1 : 79 / 250 ≤ a 1) {q : ℝ} (hq : 1 ≤ q)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (H : ℕ → ℕ) (c : ℕ → ℝ)
    (hcost : ∀ p ∈ S, ∀ j, 1 ≤ j → j ≤ H p → ((H p + 1 - j : ℕ) : ℝ) * c p ≤
      amplitude 9 (ZetaGaussianScaledBandBudget.gaussianScale q)
        (ZetaGaussianScaledBandBudget.shift q) (p ^ j)) :
    (∑ p ∈ S, c p * reserve (a 0) (∑' n, a n) (H p)) ≤
      (1998 / 25 : ℝ) * (-logDeriv riemannZeta (2 : ℂ)).re := by
  have hmass := two_constant_le_mass ha hs (by linarith)
  have h := scaled_blocks_ceiling hq (ha 0) hmass S hS H c hcost
  have hE : 0 ≤ (-logDeriv riemannZeta (2 : ℂ)).re := by
    have he := (hasSum_zetaPhasePrimeWeight (by norm_num : (1 : ℝ) < 2)).tsum_eq
    norm_num only [Complex.ofReal_ofNat] at he
    rw [← he]
    exact tsum_nonneg (zetaPhasePrimeWeight_nonneg 2)
  have hm := mul_le_mul_of_nonneg_right ha0 hE
  nlinarith only [h, hm]

/-- The actual coupled arithmetic work is strictly positive whenever
the constant phase has positive mass. The witness uses a real finite
prime-power block and retains all triangular returns. -/
theorem mixedWork_pos {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hP : ∀ u, 0 ≤ zetaPhaseKernel a ω u) (hω0 : ω 0 = 0) (ha0 : 0 < a 0)
    (k : ℕ) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (t : ℝ) :
    0 < mixedWork k B x t a ω := by
  obtain ⟨H, hH⟩ := exists_nat_gt ((∑' n, a n) / a 0)
  have hgap : 0 < ((H : ℝ) + 1) * a 0 - (∑' n, a n) := by
    have h := (div_lt_iff₀ ha0).mp hH
    linarith
  have hreserve : 0 < reserve (a 0) (∑' n, a n) H := by
    apply lt_of_lt_of_le _ (le_max_right 0 _)
    exact div_pos (mul_pos (by positivity) hgap) (by norm_num)
  have h := gaussian_blocks_lower ha hs hP 0 hω0 k hB hx t {2}
    (by simpa using Nat.prime_two) (fun _ => H)
  simp only [Finset.sum_singleton] at h
  exact (mul_pos (gaussianCoefficient_pos B x Nat.prime_two H) hreserve).trans_le h

/-- The disjoint-block floor reaches the actual finite-divisor
Gaussian inequality, with every selected zero, all three prime responses
and the signed boundary budget inherited from the original chain. -/
theorem finite_source_add_blocks_le_budget {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hP : ∀ u, 0 ≤ zetaPhaseKernel a ω u)
    (hω0 : ω 0 = 0) (hω1 : ω 1 = 1) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 2 ≤ k) {B x M : ℝ} (hB : 0 < B) (hx : 0 < x)
    (hx' : x ≤ DerivativeOrderComparison.delta k / 4) (hM : 0 ≤ M)
    (t : ℝ) (Z : Finset NontrivialZetaZero) (hscale : 1 ≤ scale t)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (H : ℕ → ℕ) :
    a 1 * (∑ ρ ∈ Z, ZetaGaussianNearCancellation.compensated B (halfWidth k x) (center x t) ρ) +
      (∑ p ∈ S, gaussianCoefficient B x p (H p) * reserve (a 0) (∑' n, a n) (H p)) ≤
        exactBudget k B M x t a ω := by
  have h := finite_source_add_mixedWork_le_exactBudget ha hs hω0 hω1 hω hlog
    k hk hB hx hx' hM t Z hscale
  have hblocks := gaussian_blocks_lower ha hs hP 0 hω0 k hB hx t S hS H
  linarith

/-- Even moving coefficient families, growing prime sets and separately
chosen block lengths have a vanishing guaranteed reserve after division
by the unbounded Gaussian dilation. This bounds only the block minorant,
not the actual mixed arithmetic work, whose cross-prime information remains. -/
theorem tendsto_normalized_block_reserves
    (a : ℕ → ℕ → ℝ) (ha : ∀ N n, 0 ≤ a N n) (hs : ∀ N, Summable (a N))
    (ha0 : ∀ N, a N 0 ≤ 37 / 200) (ha1 : ∀ N, 79 / 250 ≤ a N 1)
    (q : ℕ → ℝ) (hq : ∀ N, 1 ≤ q N) (hqt : Filter.Tendsto q Filter.atTop Filter.atTop)
    (S : ℕ → Finset ℕ) (hS : ∀ N p, p ∈ S N → p.Prime)
    (H : ℕ → ℕ → ℕ) (c : ℕ → ℕ → ℝ) (hc : ∀ N p, p ∈ S N → 0 ≤ c N p)
    (hcost : ∀ N p, p ∈ S N → ∀ j, 1 ≤ j → j ≤ H N p →
      ((H N p + 1 - j : ℕ) : ℝ) * c N p ≤
        amplitude 9 (ZetaGaussianScaledBandBudget.gaussianScale (q N))
          (ZetaGaussianScaledBandBudget.shift (q N)) (p ^ j)) :
    Filter.Tendsto
      (fun N => (∑ p ∈ S N, c N p * reserve (a N 0) (∑' n, a N n) (H N p)) / q N)
      Filter.atTop (nhds 0) := by
  have hlim : Filter.Tendsto
      (fun N => ((1998 / 25 : ℝ) * (-logDeriv riemannZeta (2 : ℂ)).re) / q N)
      Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hqt).const_mul
        ((1998 / 25 : ℝ) * (-logDeriv riemannZeta (2 : ℂ)).re)
  apply squeeze_zero _ _ hlim
  · intro N
    exact div_nonneg (Finset.sum_nonneg (fun p hp =>
      mul_nonneg (hc N p hp) (le_max_left 0 _))) (by linarith [hq N])
  · intro N
    exact div_le_div_of_nonneg_right
      (eligible_blocks_ceiling (ha N) (hs N) (ha0 N) (ha1 N) (hq N) (S N) (hS N)
        (H N) (c N) (hcost N)) (by linarith [hq N])

end
end RiemannGaussian.ZetaGaussianPrimeBlocks
