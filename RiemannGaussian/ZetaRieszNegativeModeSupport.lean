/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszNegativeModeCascade
import Mathlib.Analysis.Complex.RealDeriv

/-!
# A weak inverse retaining every diagonal derivative

The finite negative-mode response is represented by actual iterated ray
integrals acting on normal derivatives of a test function. Its Laplace
test is exactly `response`. All operations stay in `0 <= s <= d`, so a
test supported strictly below that cone gives zero, including the normal
derivative channels. No individual factorial order is removed.
-/

namespace RiemannGaussian.ZetaRieszNegativeModeSupport
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Classical

/-- Scalar test functions in the cofactor-log and Riesz-cutoff variables. -/
abbrev Test := ℝ → ℝ → ℂ

/-- The double Laplace test used to identify the explicit inverse functional. -/
def laplaceTest (w z : ℂ) : Test := fun s d => Complex.exp (-w*s-z*d)

/-- A primitive in the inverse d-variable acts on tests by a forward ray. -/
def primitive : ℕ → Test → Test
  | 0, f => f
  | r+1, f => fun s d => ∫ t : ℝ in Ioi 0, primitive r f s (d+t)

/-- The sign is the distributional derivative sign, not an absolute value. -/
def normalJet (k : ℕ) (f : Test) : Test :=
  fun s d => (-1 : ℂ)^k * iteratedDeriv k (f s) d

/-- Convolution with a mode supported on the positive diagonal. -/
def rays : List ℂ → Test → Test
  | [], f => f
  | xi::xs, f => fun s d => ∫ t : ℝ in Ioi 0,
      Complex.exp (xi*t) * rays xs f (s+t) (d+t)

private theorem integral_exp_neg {z : ℂ} (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-z*t)) = 1/z := by
  rw [integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hz)]
  simp

theorem primitive_laplace (r : ℕ) (c w z : ℂ) (hz : 0 < z.re) :
    primitive r (fun s d => c*laplaceTest w z s d) =
      fun s d => (c/z^r)*laplaceTest w z s d := by
  induction r with
  | zero => simp [primitive]
  | succ r ih =>
    funext s d
    simp only [primitive, ih]
    have he (t : ℝ) : c/z^r*laplaceTest w z s (d+t) =
        (c/z^r*laplaceTest w z s d)*Complex.exp (-z*t) := by
      simp only [laplaceTest, Complex.ofReal_add]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      ring
    simp_rw [he]
    rw [integral_const_mul, integral_exp_neg hz, pow_succ]
    ring

private theorem iterated_laplace (k : ℕ) (c w z : ℂ) (s : ℝ) :
    iteratedDeriv k (fun d : ℝ => c*laplaceTest w z s d) =
      fun d => c*(-z)^k*laplaceTest w z s d := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext d
    have hd := (((Complex.ofRealCLM.hasDerivAt (x := d)).const_mul (-z)).const_add
      (-w*(s : ℂ))).cexp
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one,
      neg_mul, ← sub_eq_add_neg] at hd
    have hh := hd.const_mul (c*(-z)^k)
    convert hh.deriv using 1 <;> simp only [laplaceTest, pow_succ] <;> ring

theorem normalJet_laplace (k : ℕ) (c w z : ℂ) :
    normalJet k (fun s d => c*laplaceTest w z s d) =
      fun s d => (c*z^k)*laplaceTest w z s d := by
  funext s d
  rw [normalJet, iterated_laplace, neg_pow]
  have he : (-1 : ℂ)^k*(-1)^k = 1 := by rw [← mul_pow]; simp
  calc
    _ = ((-1 : ℂ)^k*(-1)^k)*(c*z^k*laplaceTest w z s d) := by ring
    _ = _ := by rw [he, one_mul]

theorem rays_laplace (xs : List ℂ) (c w z : ℂ)
    (h : ∀ xi ∈ xs, 0 < (w+z-xi).re) :
    rays xs (fun s d => c*laplaceTest w z s d) =
      fun s d => (c/(xs.map (fun xi => w+z-xi)).prod)*laplaceTest w z s d := by
  induction xs with
  | nil => simp [rays]
  | cons xi xs ih =>
    rw [rays, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    funext s d
    have he (t : ℝ) : Complex.exp (xi*t)*
        (c/(xs.map (fun x => w+z-x)).prod*laplaceTest w z (s+t) (d+t)) =
        (c/(xs.map (fun x => w+z-x)).prod*laplaceTest w z s d)*
          Complex.exp (-(w+z-xi)*t) := by
      simp only [laplaceTest, Complex.ofReal_add]
      rw [mul_left_comm, ← Complex.exp_add, mul_assoc, ← Complex.exp_add]
      congr 2
      ring
    simp_rw [he]
    rw [integral_const_mul, integral_exp_neg (h xi (by simp))]
    simp only [List.map_cons, List.prod_cons, div_eq_mul_inv, mul_inv_rev]
    ring

/-- Exact weak inverse; the empty-subset subtraction is retained.
The r-fold primitive is obtained by adding r positive d-rays. -/
def inversePrimitive {ι : Type*} (r : ℕ) (A : Finset ι) (xi : ι → ℂ) (f : Test) : ℂ :=
  primitive (r+2) f 0 0 - ∑ B ∈ A.powerset, (-1 : ℂ)^B.card *
    rays (B.toList.map xi) (primitive (r+2) (normalJet B.card f)) 0 0

theorem inversePrimitive_laplace {ι : Type*} (r : ℕ) (A : Finset ι) (xi : ι → ℂ)
    (w z : ℂ) (hz : 0 < z.re) (h : ∀ i ∈ A, 0 < (w+z-xi i).re) :
    inversePrimitive r A xi (laplaceTest w z) =
      ZetaRieszNegativeModeCascade.response A xi w z/z^r := by
  have hz0 : z ≠ 0 := Complex.ne_zero_of_re_pos hz
  have he (B : Finset ι) (hB : B ∈ A.powerset) :
      rays (B.toList.map xi) (primitive (r+2) (normalJet B.card (laplaceTest w z))) 0 0 =
        (1/z^(r+2))*∏ i ∈ B, z/(w+z-xi i) := by
    rw [show laplaceTest w z = (fun s d => 1*laplaceTest w z s d) by ext; simp,
      normalJet_laplace, primitive_laplace _ _ _ _ hz, rays_laplace]
    · simp only [List.map_map, Function.comp_def, Finset.prod_map_toList,
        laplaceTest, Complex.ofReal_zero, mul_zero, sub_zero,
        Complex.exp_zero, mul_one, one_mul, Finset.prod_div_distrib, Finset.prod_const]
      ring
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact h i (Finset.mem_powerset.mp hB (Finset.mem_toList.mp hi))
  rw [inversePrimitive]
  have hsum1 : (∑ B ∈ A.powerset, (-1 : ℂ)^B.card *
      rays (B.toList.map xi) (primitive (r+2) (normalJet B.card (laplaceTest w z))) 0 0) =
      ∑ B ∈ A.powerset, (-1 : ℂ)^B.card *((1/z^(r+2))*∏ i ∈ B, z/(w+z-xi i)) := by
    apply Finset.sum_congr rfl
    intro B hB
    rw [he B hB]
  rw [hsum1]
  rw [show primitive (r+2) (laplaceTest w z) 0 0 = 1/z^(r+2) by
    conv_lhs => arg 2; rw [show laplaceTest w z = (fun s d => 1*laplaceTest w z s d) by ext; simp]
    rw [primitive_laplace _ _ _ _ hz]; simp [laplaceTest]]
  have hp := Finset.prod_sub (fun _ : ι => (1 : ℂ)) (fun i => z/(w+z-xi i)) A
  simp only [Finset.prod_const_one, mul_one] at hp
  have hf : ∏ i ∈ A, (1-z/(w+z-xi i)) = ∏ i ∈ A, (w-xi i)/(w+z-xi i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hd := Complex.ne_zero_of_re_pos (h i hi)
    field_simp
    ring
  rw [hf] at hp
  have hs : (∑ B ∈ A.powerset, (-1 : ℂ)^B.card *
      ((1/z^(r+2))*∏ i ∈ B, z/(w+z-xi i))) =
      (1/z^(r+2))*(∏ i ∈ A, (w-xi i)/(w+z-xi i)) := by
    rw [hp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B _
    ring
  rw [hs, ZetaRieszNegativeModeCascade.response, pow_add]
  field_simp

/-- Vanishing on the closed cone is preserved by both positive-ray operations. -/
def VanishesOnCone (f : Test) : Prop := ∀ s d, 0 ≤ s → s ≤ d → f s d = 0

theorem primitive_vanishes (r : ℕ) {f : Test} (hf : VanishesOnCone f) :
    VanishesOnCone (primitive r f) := by
  induction r with
  | zero => exact hf
  | succ r ih =>
    intro s d hs hd
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    exact ih s (d+t) hs (by linarith [show 0 < t from ht])

theorem rays_vanish (xs : List ℂ) {f : Test} (hf : VanishesOnCone f) :
    VanishesOnCone (rays xs f) := by
  induction xs with
  | nil => exact hf
  | cons xi xs ih =>
    intro s d hs hd
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    rw [ih (s+t) (d+t) (by linarith [show 0 < t from ht]) (by linarith), mul_zero]

/-- Local zero germs retain every normal derivative, including orders 0 and 1. -/
theorem normalJet_vanishes (k : ℕ) {f : Test}
    (hf : ∀ s d, 0 ≤ s → s ≤ d → f s =ᶠ[𝓝 d] 0) :
    VanishesOnCone (normalJet k f) := by
  intro s d hs hd
  rw [normalJet, (hf s d hs hd).iteratedDeriv_eq k]
  simp

/-- Boundary-aware support of the finite all-negative inverse, tested weakly.
No count, mode, empty-cofactor term or low derivative order is discarded. -/
theorem inversePrimitive_eq_zero {ι : Type*} (r : ℕ) (A : Finset ι) (xi : ι → ℂ)
    {f : Test} (hf : ∀ s d, 0 ≤ s → s ≤ d → f s =ᶠ[𝓝 d] 0) :
    inversePrimitive r A xi f = 0 := by
  have hf0 : VanishesOnCone f := by
    intro s d hs hd
    exact (hf s d hs hd).eq_of_nhds
  rw [inversePrimitive, primitive_vanishes (r+2) hf0 0 0 le_rfl le_rfl]
  have hsum : (∑ B ∈ A.powerset, (-1 : ℂ)^B.card *
      rays (B.toList.map xi) (primitive (r+2) (normalJet B.card f)) 0 0) = 0 := by
    apply Finset.sum_eq_zero
    intro B _
    rw [rays_vanish _ (primitive_vanishes _ (normalJet_vanishes _ hf))
      0 0 le_rfl le_rfl, mul_zero]
  rw [hsum, sub_self]

/-- Tests whose closed support misses the cone kill the original response
itself (`r=0`), not only a primitive. Boundary jets vanish by locality. -/
theorem inversePrimitive_support {ι : Type*} (r : ℕ) (A : Finset ι) (xi : ι → ℂ)
    {f : Test} (hf : tsupport (Function.uncurry f) ⊆ {x : ℝ×ℝ | x.2 < x.1}) :
    inversePrimitive r A xi f = 0 := by
  apply inversePrimitive_eq_zero
  intro s d _ hd
  have hn : (s,d) ∉ tsupport (Function.uncurry f) := by
    intro hx
    exact (not_lt_of_ge hd) (hf hx)
  have he := notMem_tsupport_iff_eventuallyEq.mp hn
  have hc : Tendsto (fun t : ℝ => (s,t)) (𝓝 d) (𝓝 (s,d)) :=
    continuousAt_const.prodMk continuousAt_id
  exact he.comp_tendsto hc

/-- A fixed positive neighborhood of every literal core point is below
the cone. This includes all finite mode multiplicities and normal jets. -/
theorem inversePrimitive_core_patch {ι : Type*} (r : ℕ) (A : Finset ι) (xi : ι → ℂ)
    {u : ℝ} (hu : 1/2 ≤ u) {N K n : ℕ} (hN : 2 ≤ N)
    (hn : n ∈ ZetaRieszParityPacket.coreBand u N K) (p : ℝ) {f : Test}
    (hf : ∀ x ∈ tsupport (Function.uncurry f),
      |x.1-(1-p)| ≤ 7/100 ∧
      |x.2-(SquarefreeVaughanLogSource.length u N/Real.log n-p)| ≤ 7/100) :
    inversePrimitive r A xi f = 0 := by
  apply inversePrimitive_support
  intro x hx
  have hs := (abs_le.mp (hf x hx).1).1
  have hd := (abs_le.mp (hf x hx).2).2
  have hg := ZetaRieszZeroParityCascade.core_support_gap hu hN hn
  change x.2 < x.1
  linarith

end
end RiemannGaussian.ZetaRieszNegativeModeSupport
