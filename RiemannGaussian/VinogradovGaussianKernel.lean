/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovMomentReduction
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Gaussian smoothing with the phase differences retained

Poisson summation turns the complete Gaussian Fourier series into a
positive, periodized Gaussian. Its finite weighted Gram identity keeps
the original complex coefficients and all phase differences. The kernel
identity itself does not assert a spacing or Vinogradov moment saving.
-/

namespace RiemannGaussian.VinogradovGaussianKernel
noncomputable section
open Filter Asymptotics
open scoped BigOperators ComplexConjugate

/-- Gaussian damping of an integer Fourier frequency. -/
def weight (a : ℝ) (n : ℤ) : ℝ := Real.exp (-Real.pi * a * (n : ℝ) ^ 2)

/-- A literal unit Fourier phase at a real sampling point. -/
def phase (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * n * x)

/-- The full periodized Gaussian, with every integer translate retained. -/
def kernel (a x : ℝ) : ℝ :=
  (1 / a ^ (1 / 2 : ℝ)) *
    ∑' m : ℤ, Real.exp (-Real.pi / a * ((m : ℝ) - x) ^ 2)

/-- Every real exponential of a negative quadratic is genuinely summable
on the complete integer lattice, including linear and constant shifts. -/
theorem summable_real_quadratic {A : ℝ} (hA : A < 0) (B C : ℝ) :
    Summable (fun n : ℤ => Real.exp (A * (n : ℝ) ^ 2 + B * n + C)) := by
  have h := (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact
    (a := (A : ℂ)) (by simpa using hA) (B : ℂ) (-2)).isBigO
  have hs := summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    (h.comp_tendsto Int.tendsto_coe_cofinite)
  have hm := hs.mul_right (Complex.exp C)
  apply Complex.summable_ofReal.mp
  apply hm.congr
  intro n
  dsimp only [Function.comp_apply]
  rw [← Complex.exp_add, Complex.ofReal_exp]
  push_cast
  rfl

/-- The Fourier Gaussian weights are genuinely summable at every positive
scale, by quadratic decay along both integer directions. -/
theorem summable_weight {a : ℝ} (ha : 0 < a) : Summable (weight a) := by
  change Summable (fun n : ℤ => Real.exp (-Real.pi * a * (n : ℝ) ^ 2))
  simpa only [zero_mul, add_zero] using
    summable_real_quadratic (mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) ha) 0 0

/-- The spatial kernel's translated Gaussian series is genuinely
summable at every positive scale and every real phase difference. -/
theorem summable_kernel_translates {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Summable (fun m : ℤ => Real.exp (-Real.pi / a * ((m : ℝ) - x) ^ 2)) := by
  have h := summable_real_quadratic
    (div_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) ha)
    (2 * Real.pi / a * x) (-Real.pi / a * x ^ 2)
  convert h using 1
  ext m
  congr 1
  ring

/-- Each Fourier atom has exactly unit modulus. -/
theorem norm_phase (n : ℤ) (x : ℝ) : ‖phase n x‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- The phase difference is retained exactly in a Gram cross term. -/
theorem phase_mul_conj (n : ℤ) (x y : ℝ) :
    phase n x * conj (phase n y) = phase n (x - y) := by
  simp only [phase, ← Complex.exp_conj, map_mul, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I, map_intCast]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Gaussian Fourier summation is exactly a positive near-resonance
kernel. No integer translate or phase difference is discarded. -/
theorem poisson {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∑' n : ℤ, (weight a n : ℂ) * phase n x) = (kernel a x : ℂ) := by
  have h := Complex.tsum_exp_neg_quadratic
    (a := (a : ℂ)) (by simpa using ha) (Complex.I * x)
  have he (n : ℤ) : (weight a n : ℂ) * phase n x =
      Complex.exp (-Real.pi * (a : ℂ) * n ^ 2 +
        2 * Real.pi * (Complex.I * x) * n) := by
    rw [weight, phase, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he]
  rw [h]
  have hi : Complex.I * (Complex.I * (x : ℂ)) = -x := by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  simp only [hi, ← sub_eq_add_neg]
  simp only [kernel, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_cpow ha.le, Complex.ofReal_tsum, Complex.ofReal_exp,
    Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_intCast,
    Complex.ofReal_ofNat]

/-- The spatial kernel is strictly positive; actual summability justifies
retaining any one of its positive integer translates. -/
theorem kernel_pos {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 < kernel a x := by
  have h := (summable_kernel_translates ha x).sum_le_tsum {0}
    (fun m _ => (Real.exp_pos _).le)
  simp only [Finset.sum_singleton] at h
  unfold kernel
  exact mul_pos (by positivity) ((Real.exp_pos _).trans_le h)

/-- The real-space kernel is nonnegative at every phase difference. -/
theorem kernel_nonneg {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 ≤ kernel a x :=
  (kernel_pos ha x).le

/-- Independent absolutely summable coordinate factors give an absolutely
summable function on the complete integer lattice. -/
theorem summable_lattice_product {k : ℕ} (f : Fin k → ℤ → ℂ)
    (hf : ∀ j, Summable (f j)) :
    Summable (fun n : Fin k → ℤ => ∏ j, f j (n j)) := by
  induction k with
  | zero => exact summable_of_hasFiniteSupport (Set.toFinite _)
  | succ k ih =>
    have ht := ih (fun j => f j.succ) (fun j => hf j.succ)
    have hp := summable_mul_of_summable_norm (hf 0).norm ht.norm
    have he := hp.comp_injective (Fin.consEquiv (fun _ : Fin (k + 1) => ℤ)).symm.injective
    simpa only [Fin.consEquiv, Equiv.coe_fn_symm_mk, Function.comp_def,
      Fin.prod_univ_succ, Fin.tail] using he

/-- The full lattice Fourier sum factors coordinatewise, with genuine
absolute convergence rather than a formal exchange of infinite sums. -/
theorem tsum_lattice_product {k : ℕ} (f : Fin k → ℤ → ℂ)
    (hf : ∀ j, Summable (f j)) :
    (∑' n : Fin k → ℤ, ∏ j, f j (n j)) = ∏ j, ∑' n : ℤ, f j n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ht := summable_lattice_product (fun j => f j.succ) (fun j => hf j.succ)
    have he := (Fin.consEquiv (fun _ : Fin (k + 1) => ℤ)).symm.tsum_eq
      (fun p : ℤ × (Fin k → ℤ) => f 0 p.1 * ∏ j, f j.succ (p.2 j))
    simp only [Fin.consEquiv, Equiv.coe_fn_symm_mk, Fin.tail] at he
    simp_rw [Fin.prod_univ_succ]
    rw [he, ← tsum_mul_tsum_of_summable_norm (hf 0).norm ht.norm,
      ih (fun j => f j.succ) (fun j => hf j.succ)]

/-- The complete product Gaussian on integer frequency vectors. -/
def latticeWeight {k : ℕ} (a : Fin k → ℝ) (n : Fin k → ℤ) : ℝ :=
  ∏ j, weight (a j) (n j)

/-- The literal phase pairing keeps every real coordinate. -/
def latticePhase {k : ℕ} (n : Fin k → ℤ) (x : Fin k → ℝ) : ℂ :=
  ∏ j, phase (n j) (x j)

/-- The complete Gaussian near-resonance kernel in all coordinates. -/
def latticeKernel {k : ℕ} (a x : Fin k → ℝ) : ℝ := ∏ j, kernel (a j) (x j)

/-- The product Gaussian frequency weights are genuinely summable. -/
theorem summable_latticeWeight {k : ℕ} {a : Fin k → ℝ} (ha : ∀ j, 0 < a j) :
    Summable (latticeWeight a) := by
  apply Complex.summable_ofReal.mp
  simpa only [latticeWeight, Complex.ofReal_prod] using
    summable_lattice_product (fun j n => (weight (a j) n : ℂ))
      (fun j => Complex.summable_ofReal.mpr (summable_weight (ha j)))

/-- The full multivariate phase has unit modulus. -/
theorem norm_latticePhase {k : ℕ} (n : Fin k → ℤ) (x : Fin k → ℝ) :
    ‖latticePhase n x‖ = 1 := by
  simp only [latticePhase, norm_prod, norm_phase, Finset.prod_const_one]

/-- All phase coordinates remain coupled in a Gram cross term. -/
theorem latticePhase_mul_conj {k : ℕ} (n : Fin k → ℤ) (x y : Fin k → ℝ) :
    latticePhase n x * conj (latticePhase n y) = latticePhase n (x - y) := by
  simp only [latticePhase, map_prod, ← Finset.prod_mul_distrib,
    phase_mul_conj, Pi.sub_apply]

/-- The all-coordinate Poisson identity retains every lattice translate.
This is the positive kernel for the actual joint frequency space. -/
theorem lattice_poisson {k : ℕ} {a : Fin k → ℝ} (ha : ∀ j, 0 < a j)
    (x : Fin k → ℝ) :
    (∑' n : Fin k → ℤ, (latticeWeight a n : ℂ) * latticePhase n x) =
      (latticeKernel a x : ℂ) := by
  have hs (j : Fin k) : Summable (fun n : ℤ => (weight (a j) n : ℂ) * phase n (x j)) := by
    apply (summable_weight (ha j)).of_norm_bounded
    intro n
    rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
      weight, abs_of_pos (Real.exp_pos _)]
  simp only [latticeWeight, latticePhase, Complex.ofReal_prod,
    ← Finset.prod_mul_distrib]
  rw [tsum_lattice_product _ hs]
  simp only [poisson, latticeKernel, Complex.ofReal_prod, ha]

/-- The Gaussian weight is nonnegative on every full frequency vector. -/
theorem latticeWeight_nonneg {k : ℕ} (a : Fin k → ℝ) (n : Fin k → ℤ) :
    0 ≤ latticeWeight a n :=
  Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le)

/-- Multiplying the summable Gaussian by any full phase retains absolute
convergence, at every real sampling vector. -/
theorem summable_latticeFourier {k : ℕ} {a : Fin k → ℝ} (ha : ∀ j, 0 < a j)
    (x : Fin k → ℝ) :
    Summable (fun n : Fin k → ℤ => (latticeWeight a n : ℂ) * latticePhase n x) := by
  apply (summable_latticeWeight ha).of_norm_bounded
  intro n
  rw [norm_mul, norm_latticePhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (latticeWeight_nonneg a n)]

/-- The real-coordinate pairing is exactly the existing torus monomial. -/
theorem latticePhase_eq_mFourier {k : ℕ} (n : Fin k → ℤ) (x : Fin k → ℝ) :
    latticePhase n x = UnitAddTorus.mFourier n (fun j => (x j : UnitAddCircle)) := by
  simp only [latticePhase, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    fourier_coe_apply, Complex.ofReal_one, div_one, phase]

/-- The Gaussian-weighted square of every finite complex Fourier family
is genuinely summable. No spacing or bounded-weight premise is needed. -/
theorem summable_energy {k : ℕ} {ι : Type*} [Fintype ι]
    {a : Fin k → ℝ} (ha : ∀ j, 0 < a j) (x : ι → Fin k → ℝ) (w : ι → ℂ) :
    Summable (fun n : Fin k → ℤ =>
      latticeWeight a n * ‖∑ b, w b * latticePhase n (x b)‖ ^ 2) := by
  have hb (n : Fin k → ℤ) : ‖∑ b, w b * latticePhase n (x b)‖ ≤ ∑ b, ‖w b‖ := by
    apply (norm_sum_le _ _).trans_eq
    simp only [norm_mul, norm_latticePhase, mul_one]
  apply ((summable_latticeWeight ha).mul_right ((∑ b, ‖w b‖) ^ 2)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (latticeWeight_nonneg a n) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb n) 2)
    (latticeWeight_nonneg a n)

/-- Exact Gaussian Gram identity for all original complex weights and
joint phase differences. The signed cross terms are not replaced by their
absolute values, despite the positive spatial kernel. -/
theorem energy_eq_gram {k : ℕ} {ι : Type*} [Fintype ι]
    {a : Fin k → ℝ} (ha : ∀ j, 0 < a j) (x : ι → Fin k → ℝ) (w : ι → ℂ) :
    ((∑' n : Fin k → ℤ, latticeWeight a n *
        ‖∑ b, w b * latticePhase n (x b)‖ ^ 2 : ℝ) : ℂ) =
      ∑ b, ∑ c, (w b * conj (w c)) * (latticeKernel a (x b - x c) : ℂ) := by
  classical
  have hi (b c : ι) := (summable_latticeFourier ha (x b - x c)).mul_left
    (w b * conj (w c))
  have he (n : Fin k → ℤ) :
      ((latticeWeight a n * ‖∑ b, w b * latticePhase n (x b)‖ ^ 2 : ℝ) : ℂ) =
        ∑ b, ∑ c, (w b * conj (w c)) *
          ((latticeWeight a n : ℂ) * latticePhase n (x b - x c)) := by
    rw [Complex.ofReal_mul, Complex.sq_norm, ← Complex.mul_conj]
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
      ← latticePhase_mul_conj]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    ring
  rw [Complex.ofReal_tsum]
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun b _ => summable_sum (fun c _ => hi b c))]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Summable.tsum_finsetSum (fun c _ => hi b c)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [tsum_mul_left, lattice_poisson ha]

/-- The complete exponent cost of a joint frequency vector. -/
def frequencyCost {k : ℕ} (a : Fin k → ℝ) (n : Fin k → ℤ) : ℝ :=
  ∑ j, Real.pi * a j * (n j : ℝ) ^ 2

/-- The frequency weight pays precisely the sum of all coordinate costs. -/
theorem latticeWeight_eq_exp {k : ℕ} (a : Fin k → ℝ) (n : Fin k → ℤ) :
    latticeWeight a n = Real.exp (-frequencyCost a n) := by
  simp only [latticeWeight, weight, frequencyCost, ← Real.exp_sum, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Gaussian majorization of any finite joint frequency support. Its
explicit cost is paid once; the right side keeps the complete signed Gram
form instead of discarding phase correlations. -/
theorem finite_energy_le_gram {k : ℕ} {ι : Type*} [Fintype ι]
    {a : Fin k → ℝ} (ha : ∀ j, 0 < a j) (x : ι → Fin k → ℝ) (w : ι → ℂ)
    (C : Finset (Fin k → ℤ)) {Q : ℝ}
    (hQ : ∀ n ∈ C, frequencyCost a n ≤ Q) :
    (∑ n ∈ C, ‖∑ b, w b * latticePhase n (x b)‖ ^ 2) ≤
      Real.exp Q * (∑ b, ∑ c, (w b * conj (w c)) *
        (latticeKernel a (x b - x c) : ℂ)).re := by
  have hg := congrArg Complex.re (energy_eq_gram ha x w)
  rw [Complex.ofReal_re] at hg
  rw [← hg, ← tsum_mul_left]
  have hs := (summable_energy ha x w).mul_left (Real.exp Q)
  apply (Finset.sum_le_sum (fun n hn => ?_)).trans
    (hs.sum_le_tsum C (fun n _ => mul_nonneg (Real.exp_pos Q).le
      (mul_nonneg (latticeWeight_nonneg a n) (sq_nonneg _))))
  have h : 1 ≤ Real.exp Q * latticeWeight a n := by
    rw [latticeWeight_eq_exp, ← Real.exp_add, Real.one_le_exp_iff]
    linarith [hQ n hn]
  simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right h
    (sq_nonneg ‖∑ b, w b * latticePhase n (x b)‖)

/-- The exact maximum Gaussian cost on a finite joint support, with zero
inserted so the empty support also has a defined cost. -/
def supportCost {k : ℕ} (a : Fin k → ℝ) (C : Finset (Fin k → ℤ)) : ℝ := by
  classical
  exact (insert 0 (C.image (frequencyCost a))).max' (by simp)

/-- The support cost covers every attainable frequency without replacing
the joint support by a box. -/
theorem frequencyCost_le_supportCost {k : ℕ} (a : Fin k → ℝ)
    (C : Finset (Fin k → ℤ)) {n : Fin k → ℤ} (hn : n ∈ C) :
    frequencyCost a n ≤ supportCost a C := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨n, hn, rfl⟩))

/-- The lattice pairing is a character in its real sample vector. -/
theorem latticePhase_add {k : ℕ} (n : Fin k → ℤ) (x y : Fin k → ℝ) :
    latticePhase n (x + y) = latticePhase n x * latticePhase n y := by
  simp only [latticePhase, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, Complex.ofReal_add]
  ring

/-- Multiplying a finite set of phases adds their complete real vectors. -/
theorem product_latticePhase {k : ℕ} {ι : Type*} (S : Finset ι)
    (n : Fin k → ℤ) (x : ι → Fin k → ℝ) :
    (∏ b ∈ S, latticePhase n (x b)) = latticePhase n (∑ b ∈ S, x b) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [latticePhase, phase]
  | @insert b S hb ih => simp [hb, ih, latticePhase_add]

/-- Raising the sample sum to a power keeps every ordered tuple and the
full product of its original complex weights. -/
theorem sample_power_expansion {k : ℕ} {ι : Type*} [Fintype ι]
    (s : ℕ) (n : Fin k → ℤ) (x : ι → Fin k → ℝ) (w : ι → ℂ) :
    (∑ b, w b * latticePhase n (x b)) ^ s =
      ∑ b : Fin s → ι, VinogradovShiftedMoment.tupleWeight s w b *
        latticePhase n (∑ j, x (b j)) := by
  classical
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.prod_mul_distrib, product_latticePhase]
  rfl

/-- The complete signed Gaussian Gram form of the powered sample family.
All tuple weights and all vector differences survive explicitly. -/
def momentGram {k : ℕ} {ι : Type*} [Fintype ι]
    (s : ℕ) (a : Fin k → ℝ) (x : ι → Fin k → ℝ) (w : ι → ℂ) : ℂ :=
  ∑ b : Fin s → ι, ∑ c : Fin s → ι,
    (VinogradovShiftedMoment.tupleWeight s w b *
      conj (VinogradovShiftedMoment.tupleWeight s w c)) *
      (latticeKernel a ((∑ j, x (b j)) - ∑ j, x (c j)) : ℂ)

/-- Every dual moment in the actual two-Hölder reduction has a proved
Gaussian majorant. Its cost is the exact maximum over attainable joint
frequencies; the surviving Gram form keeps all signed tuple correlations. -/
theorem dualMoment_le_gaussian_gram {k : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r s : ℕ) (v : ι → Fin k → ℤ) (x : κ → Fin k → ℝ) (w : κ → ℂ)
    {a : Fin k → ℝ} (ha : ∀ j, 0 < a j) :
    VinogradovMomentReduction.dualMoment r s v
        (fun b j => (x b j : UnitAddCircle)) w ≤
      Real.exp (supportCost a (VinogradovMomentReduction.frequencySupport
        (VinogradovShiftedMoment.tupleFrequency r v))) * (momentGram s a x w).re := by
  have h := finite_energy_le_gram ha (fun b : Fin s → κ => ∑ j, x (b j))
    (VinogradovShiftedMoment.tupleWeight s w)
    (VinogradovMomentReduction.frequencySupport (VinogradovShiftedMoment.tupleFrequency r v))
    (fun _ hn => frequencyCost_le_supportCost a _ hn)
  apply le_trans (le_of_eq ?_) h
  unfold VinogradovMomentReduction.dualMoment
  apply Finset.sum_congr rfl
  intro n hn
  rw [← sample_power_expansion, norm_pow]
  simp_rw [latticePhase_eq_mFourier]
  rw [← pow_mul, Nat.mul_comm s 2]

end
end RiemannGaussian.VinogradovGaussianKernel
