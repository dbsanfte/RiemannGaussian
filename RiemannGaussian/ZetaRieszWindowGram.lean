/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeRieszWindows

/-!
# Exact signed logarithmic-window Gram kernels

The exact arithmetic signs, complex amplitudes and physical cutoffs remain
available alongside their finite energy bounds. No source-scale decay of
the complete signed energy or new zero-free region is asserted.
-/

namespace RiemannGaussian.ZetaRieszWindowGram
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate Classical

/-- The unit feature for a strict moving logarithmic window. -/
def windowAtom (b x v : ℝ) : ℂ := (Ioo x (x + b)).indicator (fun _ => 1) v

/-- Pairing two window features retains precisely their interval
intersection, before any absolute value is taken. -/
theorem windowAtom_mul (b x y : ℝ) :
    (fun v => windowAtom b x v * windowAtom b y v) =
      (Ioo (max x y) (min (x + b) (y + b))).indicator (fun _ => (1 : ℂ)) := by
  funext v
  simp only [windowAtom, indicator_apply, mem_Ioo, max_lt_iff, lt_min_iff]
  split_ifs <;> simp_all

/-- Real unit window features are unchanged by conjugation. -/
theorem conj_windowAtom (b x v : ℝ) : conj (windowAtom b x v) = windowAtom b x v := by
  simp only [windowAtom, indicator_apply]
  split_ifs <;> simp

/-- Every pair of finite window features is genuinely integrable on
the full real line, including disjoint and empty intervals. -/
theorem integrable_windowAtom_mul (b x y : ℝ) :
    Integrable (fun v => windowAtom b x v * windowAtom b y v) := by
  rw [windowAtom_mul]
  exact (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const (by simp))

/-- The interval overlap is exactly the triangular logarithmic-ratio
kernel, with no regularity or generic-position condition on the endpoints. -/
theorem overlap_eq_tent (b x y : ℝ) :
    min (x + b) (y + b) - max x y = b - |x - y| := by
  by_cases h : x ≤ y
  · rw [min_eq_left (by linarith), max_eq_right h, abs_of_nonpos (by linarith)]
    ring
  · have hh : y ≤ x := le_of_not_ge h
    rw [min_eq_right (by linarith), max_eq_left hh, abs_of_nonneg (by linarith)]
    ring

/-- The exact integrated two-feature Gram entry is supported only
where the two logarithmic divisors lie within one window width. -/
theorem integral_windowAtom_mul (b x y : ℝ) :
    (∫ v : ℝ, windowAtom b x v * windowAtom b y v) =
      (max (b - |x - y|) 0 : ℝ) := by
  rw [windowAtom_mul, integral_indicator measurableSet_Ioo, setIntegral_const,
    Real.volume_real_Ioo, overlap_eq_tent]
  simp

/-- The complete complex aggregate of moving windows. -/
def windowLift {ι : Type*} (S : Finset ι) (a : ι → ℂ) (x : ι → ℝ)
    (b v : ℝ) : ℂ := ∑ i ∈ S, a i * windowAtom b (x i) v

/-- Expanding the square keeps every complex cross amplitude and
each exact overlap of its two windows. -/
theorem windowLift_mul_conj {ι : Type*} (S : Finset ι) (a : ι → ℂ) (x : ι → ℝ)
    (b v : ℝ) :
    windowLift S a x b v * conj (windowLift S a x b v) =
      ∑ i ∈ S, ∑ j ∈ S, (a i * conj (a j)) *
        (windowAtom b (x i) v * windowAtom b (x j) v) := by
  simp only [windowLift, map_sum, map_mul, conj_windowAtom, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The complete finite Gram energy is integrable before expansion
of its integral; no unproved square-integrability hypothesis is introduced. -/
theorem integrable_windowLift_mul_conj {ι : Type*} (S : Finset ι) (a : ι → ℂ) (x : ι → ℝ)
    (b : ℝ) :
    Integrable (fun v => windowLift S a x b v * conj (windowLift S a x b v)) := by
  simp_rw [windowLift_mul_conj]
  exact integrable_finsetSum S (fun i _ => integrable_finsetSum S (fun j _ =>
    (integrable_windowAtom_mul b (x i) (x j)).const_mul (a i * conj (a j))))

/-- The full complex window energy is its finite signed triangular
Gram sum. No cross term is replaced by an absolute value. -/
theorem integral_windowLift_mul_conj {ι : Type*} (S : Finset ι) (a : ι → ℂ) (x : ι → ℝ)
    (b : ℝ) :
    (∫ v : ℝ, windowLift S a x b v * conj (windowLift S a x b v)) =
      ∑ i ∈ S, ∑ j ∈ S, (a i * conj (a j)) * (max (b - |x i - x j|) 0 : ℝ) := by
  simp_rw [windowLift_mul_conj]
  rw [integral_finsetSum S (fun i _ => integrable_finsetSum S (fun j _ =>
    (integrable_windowAtom_mul b (x i) (x j)).const_mul (a i * conj (a j))))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum S (fun j _ =>
    (integrable_windowAtom_mul b (x i) (x j)).const_mul (a i * conj (a j)))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, integral_windowAtom_mul]

/-- The actual finite aggregate is genuinely square-integrable. -/
theorem integrable_windowLift_norm_sq {ι : Type*} (S : Finset ι) (a : ι → ℂ) (x : ι → ℝ)
    (b : ℝ) : Integrable (fun v => ‖windowLift S a x b v‖ ^ 2) := by
  have h := (integrable_windowLift_mul_conj S a x b).re
  simpa only [RCLike.re_eq_complex_re, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq] using h

/-- The real energy equals the real part of the complete signed Gram
sum, retaining all complex cross amplitudes. -/
theorem integral_windowLift_norm_sq {ι : Type*} (S : Finset ι) (a : ι → ℂ) (x : ι → ℝ)
    (b : ℝ) :
    (∫ v : ℝ, ‖windowLift S a x b v‖ ^ 2) =
      (∑ i ∈ S, ∑ j ∈ S, (a i * conj (a j)) * (max (b - |x i - x j|) 0 : ℝ)).re := by
  have h := congrArg (RCLike.re : ℂ → ℝ) (integral_windowLift_mul_conj S a x b)
  rw [← integral_re (integrable_windowLift_mul_conj S a x b)] at h
  simpa only [RCLike.re_eq_complex_re, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq] using h

/-- The full cofactor aggregate is an exact finite window lift indexed
by labelled divisors. Original complex amplitudes and Mobius signs remain
coupled across different cofactors. -/
theorem signed_divisor_windows_eq_lift (S : Finset ℕ) (a : ℕ → ℂ) (b v : ℝ) :
    (∑ m ∈ S, a m * (ZetaSquarefreeRieszWindows.signedDivisorWindow b v m : ℂ)) =
      windowLift (S.sigma (fun m => m.divisors))
        (fun z => a z.1 * ((ArithmeticFunction.moebius z.2 : ℤ) : ℂ))
        (fun z => Real.log z.2) b v := by
  simp only [windowLift, Finset.sum_sigma, ZetaSquarefreeRieszWindows.signedDivisorWindow,
    Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro d _
  have he : (v - b < Real.log d ∧ Real.log d < v) ↔
      (Real.log d < v ∧ v < Real.log d + b) := by
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [windowAtom, indicator_apply, mem_Ioo, ← he]
  split_ifs <;> simp

/-- The actual signed divisor-window aggregate has a finite Gram
identity across all cofactor pairs. The triangular kernel keeps exactly
which divisor ratios are close enough to interact. No cancellation across
cofactors is assumed, and no termwise absolute values replace the signs. -/
theorem integral_norm_sq_signed_divisor_windows (S : Finset ℕ) (a : ℕ → ℂ) (b : ℝ) :
    (∫ v : ℝ, ‖∑ m ∈ S, a m * (ZetaSquarefreeRieszWindows.signedDivisorWindow b v m : ℂ)‖ ^ 2) =
      (∑ i ∈ S.sigma (fun m => m.divisors), ∑ j ∈ S.sigma (fun m => m.divisors),
        ((a i.1 * ((ArithmeticFunction.moebius i.2 : ℤ) : ℂ)) *
          conj (a j.1 * ((ArithmeticFunction.moebius j.2 : ℤ) : ℂ))) *
            (max (b - |Real.log i.2 - Real.log j.2|) 0 : ℝ)).re := by
  simp_rw [signed_divisor_windows_eq_lift]
  exact integral_windowLift_norm_sq _ _ _ b

/-- The physical finite integration range remains part of every
Gram entry. Empty intersections contribute zero. -/
def clippedOverlap (a b x y : ℝ) : ℝ :=
  max (min (min (x + b) (y + b)) a - max (max x y) 0) 0

/-- The exact local pair energy is the length of the three-way
intersection with the physical cutoff interval. -/
theorem setIntegral_windowAtom_mul (a b x y : ℝ) :
    (∫ v in Ioo 0 a, windowAtom b x v * windowAtom b y v) =
      (clippedOverlap a b x y : ℂ) := by
  rw [windowAtom_mul, integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo, Ioo_inter_Ioo,
    setIntegral_const, Real.volume_real_Ioo]
  simp [clippedOverlap]

/-- The actual finite cutoff keeps all complex cross amplitudes and
three-way window intersections in one exact finite Gram identity. -/
theorem setIntegral_windowLift_mul_conj {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (x : ι → ℝ) (a b : ℝ) :
    (∫ v in Ioo 0 a, windowLift S c x b v * conj (windowLift S c x b v)) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * conj (c j)) * (clippedOverlap a b (x i) (x j) : ℂ) := by
  simp_rw [windowLift_mul_conj]
  rw [integral_finsetSum S (fun i _ => integrable_finsetSum S (fun j _ =>
    ((integrable_windowAtom_mul b (x i) (x j)).const_mul (c i * conj (c j))).integrableOn))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum S (fun j _ =>
    ((integrable_windowAtom_mul b (x i) (x j)).const_mul (c i * conj (c j))).integrableOn)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, setIntegral_windowAtom_mul]

/-- The local norm energy is the real part of the same full Gram
sum. This retains the cutoff rather than replacing it by the whole line. -/
theorem setIntegral_windowLift_norm_sq {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (x : ι → ℝ) (a b : ℝ) :
    (∫ v in Ioo 0 a, ‖windowLift S c x b v‖ ^ 2) =
      (∑ i ∈ S, ∑ j ∈ S,
        (c i * conj (c j)) * (clippedOverlap a b (x i) (x j) : ℂ)).re := by
  have h := congrArg (RCLike.re : ℂ → ℝ) (setIntegral_windowLift_mul_conj S c x a b)
  rw [← integral_re (integrable_windowLift_mul_conj S c x b).integrableOn] at h
  simpa only [RCLike.re_eq_complex_re, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq] using h

/-- Every finite complex window lift is integrable, including all
step discontinuities. -/
theorem integrable_windowLift {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (x : ι → ℝ) (b : ℝ) : Integrable (windowLift S c x b) := by
  apply integrable_finsetSum S
  intro i _
  apply Integrable.const_mul
  exact (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const (by simp))

/-- Cauchy--Schwarz on the actual finite interval; both integrability
conditions are explicit. No continuity of the step windows is needed. -/
theorem norm_setIntegral_sq_le {f : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hf : IntegrableOn f (Ioo 0 a))
    (hf2 : IntegrableOn (fun v => ‖f v‖ ^ 2) (Ioo 0 a)) :
    ‖∫ v in Ioo 0 a, f v‖ ^ 2 ≤ a * ∫ v in Ioo 0 a, ‖f v‖ ^ 2 := by
  let M : ℝ := ∫ v in Ioo 0 a, ‖f v‖
  have hn : ‖∫ v in Ioo 0 a, f v‖ ≤ M := norm_integral_le_integral_norm f
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hi := hf.norm
  have hc : IntegrableOn (fun _ : ℝ => M ^ 2) (Ioo 0 a) :=
    integrableOn_const (by simp)
  have hv : 0 ≤ ∫ v in Ioo 0 a, (a * ‖f v‖ - M) ^ 2 :=
    integral_nonneg (fun v => sq_nonneg (a * ‖f v‖ - M))
  have he (v : ℝ) : (a * ‖f v‖ - M) ^ 2 =
      a ^ 2 * ‖f v‖ ^ 2 - (2 * a * M) * ‖f v‖ + M ^ 2 := by ring
  simp_rw [he] at hv
  have hsplit := integral_add ((hf2.const_mul (a ^ 2)).sub (hi.const_mul (2 * a * M))) hc
  simp only [Pi.sub_apply] at hsplit
  rw [hsplit, integral_sub (hf2.const_mul (a ^ 2)) (hi.const_mul (2 * a * M)),
    integral_const_mul, integral_const_mul, setIntegral_const,
    Real.volume_real_Ioo] at hv
  simp only [sub_zero, max_eq_left ha.le, smul_eq_mul] at hv
  change 0 ≤ a ^ 2 * (∫ v in Ioo 0 a, ‖f v‖ ^ 2) - 2 * a * M * M + a * M ^ 2 at hv
  have he2 : 0 ≤ a * (a * (∫ v in Ioo 0 a, ‖f v‖ ^ 2) - M ^ 2) := by nlinarith [hv]
  have hb := (mul_nonneg_iff_of_pos_left ha).mp he2
  linarith

/-- The complete finite window integral is controlled by its exact
cutoff-preserving signed Gram energy. Integrability is discharged from the
literal finite step-window construction. -/
theorem norm_setIntegral_windowLift_sq_le {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (x : ι → ℝ) {a : ℝ} (b : ℝ) (ha : 0 < a) :
    ‖∫ v in Ioo 0 a, windowLift S c x b v‖ ^ 2 ≤
      a * (∑ i ∈ S, ∑ j ∈ S,
        (c i * conj (c j)) * (clippedOverlap a b (x i) (x j) : ℂ)).re := by
  rw [← setIntegral_windowLift_norm_sq]
  exact norm_setIntegral_sq_le ha (integrable_windowLift S c x b).integrableOn
    (integrable_windowLift_norm_sq S c x b).integrableOn

/-- Reflection into the physical displacement coordinate preserves
both strict window edges exactly. -/
theorem windowAtom_reflection (b x L s : ℝ) :
    windowAtom b x (L - s) = windowAtom b (L - x - b) s := by
  have he : (x < L - s ∧ L - s < x + b) ↔
      (L - x - b < s ∧ s < L - x - b + b) := by
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [windowAtom, indicator_apply, mem_Ioo, he]

/-- The actual moving cofactor windows use the same physical cutoff
for every divisor and every original complex amplitude. -/
theorem signed_divisor_windows_reflected_eq_lift (S : Finset ℕ) (c : ℕ → ℂ)
    (b L s : ℝ) :
    (∑ m ∈ S, c m * (ZetaSquarefreeRieszWindows.signedDivisorWindow b (L - s) m : ℂ)) =
      windowLift (S.sigma (fun m => m.divisors))
        (fun z => c z.1 * ((ArithmeticFunction.moebius z.2 : ℤ) : ℂ))
        (fun z => L - Real.log z.2 - b) b s := by
  rw [signed_divisor_windows_eq_lift]
  simp only [windowLift, windowAtom_reflection]

/-- The literal fixed-prime arithmetic carrier is bounded by one
complete signed Gram form. The polynomial filter, height phase, original
support, both Mobius factors and physical cutoff are all retained.
This is an energy inequality, not a claim that the energy is small. -/
theorem norm_sum_bandWeight_two_primes_sq_le_gram (S : Finset ℕ) (L : ℝ)
    (P : Polynomial ℂ) (N : ℕ) (t : ℝ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hS : ∀ m ∈ S, ¬ p ∣ m ∧ ¬ q ∣ m) :
    ‖∑ m ∈ S, ZetaRieszConditionedEnergy.bandWeight L P N t (p * (q * m))‖ ^ 2 ≤
      Real.log p * (∑ i ∈ S.sigma (fun m => m.divisors),
        ∑ j ∈ S.sigma (fun m => m.divisors),
          ((ZetaArithmeticBandCorrelation.bandAmplitude L P N t (p * (q * i.1)) *
              ((ArithmeticFunction.moebius i.2 : ℤ) : ℂ)) *
            conj (ZetaArithmeticBandCorrelation.bandAmplitude L P N t (p * (q * j.1)) *
              ((ArithmeticFunction.moebius j.2 : ℤ) : ℂ))) *
          (clippedOverlap (Real.log p) (Real.log q)
            (L - Real.log i.2 - Real.log q) (L - Real.log j.2 - Real.log q) : ℂ)).re := by
  rw [ZetaSquarefreeRieszWindows.sum_bandWeight_two_primes_eq_window_integral
    S L P N t hp hq hpq hS]
  simp_rw [signed_divisor_windows_reflected_eq_lift]
  exact norm_setIntegral_windowLift_sq_le _ _ _ _
    (Real.log_pos (by exact_mod_cast hp.one_lt))

end
end RiemannGaussian.ZetaRieszWindowGram
