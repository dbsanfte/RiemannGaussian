/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorBinaryEulerControl

/-!
# Exact Gamma data are stable on the one-sided positive cone

The unstable signed Mellin inverse does NOT imply instability for
nonnegative coefficient losses. A single deleted integer atom creates
a LINEAR Gamma-prefix deficit. Therefore cofinal o(X) agreement already
forces every dominated positive coefficient to equal actual Mangoldt.
The unit-prime coherent control fails even this weaker condition.

This does not control signed oscillatory errors and proves no prime-moment
non-coherence for actual Mangoldt. It identifies precisely which actual
integer Gamma constraint the earlier positive controls fail.
-/

namespace RiemannGaussian.ArithmeticOperatorGammaConeStability
noncomputable section
open Complex Filter Topology
open scoped BigOperators Classical
open ArithmeticOperatorFactorialUniqueness

/-- Literal deficit from the actual integer Gamma prefix. -/
def deficit (w : ℕ → ℝ) (X : ℕ) : ℝ :=
  Real.log (X.factorial : ℝ)-(factorialPrefix (fun n => (w n : ℂ)) X).re

/-- Exact signed deficit before positivity is used, retaining every
integer quotient and every proper prime-power label. -/
theorem deficit_eq (w : ℕ → ℝ) (X : ℕ) :
    deficit w X = ∑ n ∈ Finset.Icc 1 X,
      ((X/n : ℕ) : ℝ)*(ArithmeticFunction.vonMangoldt n-w n) := by
  have hh := congrArg Complex.re (factorialPrefix_mangoldt X)
  simp only [factorialPrefix,Complex.re_sum,Complex.mul_re,Complex.natCast_re,
    Complex.natCast_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at hh
  unfold deficit
  simp only [factorialPrefix,Complex.re_sum,Complex.mul_re,Complex.natCast_re,
    Complex.natCast_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rw [←hh,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- One coefficient loss survives through its exact floor multiplicity. -/
theorem atom_le_deficit {w : ℕ → ℝ}
    (hw : ∀ n, w n ≤ ArithmeticFunction.vonMangoldt n)
    {n X : ℕ} (hn : 0<n) (hnX : n≤X) :
    ((X/n : ℕ) : ℝ)*(ArithmeticFunction.vonMangoldt n-w n) ≤ deficit w X := by
  rw [deficit_eq]
  exact Finset.single_le_sum
    (fun q _ => mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hw q)))
    (Finset.mem_Icc.mpr ⟨hn,hnX⟩)

/-- A deleted atom costs at least X/(2n) copies once X>=2n; no
continuous approximation or quotient endpoint is discarded. -/
theorem normalized_atom_le_deficit {w : ℕ → ℝ}
    (hw : ∀ n, w n ≤ ArithmeticFunction.vonMangoldt n)
    {n X : ℕ} (hn : 0<n) (hX : 2*n≤X) :
    (ArithmeticFunction.vonMangoldt n-w n)/(2*(n : ℝ)) ≤ deficit w X/(X : ℝ) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hnX : n≤X := by omega
  have hXR : (0 : ℝ)<X := by exact_mod_cast (by omega : 0<X)
  have hq : (1 : ℝ)≤((X/n : ℕ) : ℝ) := by
    exact_mod_cast ((Nat.le_div_iff_mul_le hn).mpr (by simpa using hnX) : 1≤X/n)
  have hx : (X : ℝ)<(n : ℝ)*(((X/n : ℕ) : ℝ)+1) := by
    exact_mod_cast Nat.lt_mul_div_succ X hn
  have hfloor : (X : ℝ)/(2*(n : ℝ)) ≤ ((X/n : ℕ) : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*(n : ℝ))).mpr
    nlinarith only [hx,hq,hnR]
  have hh := (mul_le_mul_of_nonneg_right hfloor (sub_nonneg.mpr (hw n))).trans
    (atom_le_deficit hw hn hnX)
  apply (le_div_iff₀ hXR).mpr
  convert hh using 1
  ring

/-- Cofinal sublinear Gamma agreement determines every positive-index
coefficient in the dominated cone. Exact equality of ALL prefixes is
unnecessary here; signed losses are outside this theorem. -/
theorem coefficients_eq_of_cofinal_sublinear_deficit {w : ℕ → ℝ} {X : ℕ → ℕ}
    (hw : ∀ n, w n ≤ ArithmeticFunction.vonMangoldt n)
    (hX : Tendsto X atTop atTop)
    (ht : Tendsto (fun j : ℕ => deficit w (X j)/(X j : ℝ)) atTop (𝓝 0)) :
    ∀ n : ℕ, 0<n → w n=ArithmeticFunction.vonMangoldt n := by
  intro n hn
  by_contra hh
  have hd : 0<ArithmeticFunction.vonMangoldt n-w n := by
    have := hw n
    exact sub_pos.mpr (lt_of_le_of_ne this hh)
  let c := (ArithmeticFunction.vonMangoldt n-w n)/(2*(n : ℝ))
  have hc : 0<c := div_pos hd (by positivity)
  have he : ∀ᶠ j : ℕ in atTop, c ≤ deficit w (X j)/(X j : ℝ) := by
    filter_upwards [hX.eventually (eventually_ge_atTop (2*n))] with j hj
    exact normalized_atom_le_deficit hw hn hj
  obtain ⟨j,hlo,hhi⟩ := ((ht.eventually_lt_const hc).and he).exists
  exact (not_lt_of_ge hhi) hlo

/-- The ordinary full-limit version is a special case of the cofinal
positive-cone stability theorem. -/
theorem coefficients_eq_of_sublinear_deficit {w : ℕ → ℝ}
    (hw : ∀ n, w n ≤ ArithmeticFunction.vonMangoldt n)
    (ht : Tendsto (fun X : ℕ => deficit w X/(X : ℝ)) atTop (𝓝 0)) :
    ∀ n : ℕ, 0<n → w n=ArithmeticFunction.vonMangoldt n :=
  coefficients_eq_of_cofinal_sublinear_deficit hw tendsto_id ht

/-- Source-retaining binary ordinary-prime controls have a positive
LINEAR Gamma deficit, not just a failed finite exact equality. -/
theorem binary_control_linear_deficit :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ X : ℕ in atTop,
      c ≤ deficit (ArithmeticOperatorPrimeTowerControl.towerCoefficient
        (ArithmeticOperatorBinaryPrimeControl.retainedBase (10001/20000) 54)) X/(X : ℝ) := by
  obtain ⟨p,hp,hdeleted⟩ := ArithmeticOperatorBinaryEulerControl.exists_deleted_prime
  let w := ArithmeticOperatorPrimeTowerControl.towerCoefficient
    (ArithmeticOperatorBinaryPrimeControl.retainedBase (10001/20000) 54)
  have hw : ∀ n, w n ≤ ArithmeticFunction.vonMangoldt n := by
    intro n
    exact (ArithmeticOperatorPrimeTowerControl.towerCoefficient_bounds _
      (fun p => (ArithmeticOperatorBinaryPrimeControl.binaryBase_bounds _ _ p).2) n).2
  have hz : w p=0 := by
    simp only [w,ArithmeticOperatorPrimeTowerControl.towerCoefficient,hp.minFac_eq,
      ArithmeticOperatorBinaryPrimeControl.retainedBase,hdeleted,sub_self,zero_mul]
  have hlog : 0<Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp.pos
  refine ⟨Real.log p/(2*(p : ℝ)),div_pos hlog (by positivity),?_⟩
  filter_upwards [eventually_ge_atTop (2*p)] with X hX
  simpa only [hz,sub_zero,ArithmeticFunction.vonMangoldt_apply_prime hp] using
    normalized_atom_le_deficit hw hp.pos hX

/-- Therefore even asymptotic first-order Gamma precision excludes the
unit Euler control. It remains compatible with upper bounds only. -/
theorem binary_control_not_sublinear_deficit :
    ¬Tendsto (fun X : ℕ => deficit (ArithmeticOperatorPrimeTowerControl.towerCoefficient
        (ArithmeticOperatorBinaryPrimeControl.retainedBase (10001/20000) 54)) X/(X : ℝ))
      atTop (𝓝 0) := by
  intro ht
  obtain ⟨c,hc,he⟩ := binary_control_linear_deficit
  obtain ⟨X,hlo,hhi⟩ := ((ht.eventually_lt_const hc).and he).exists
  exact (not_lt_of_ge hhi) hlo

/-- Passing to ANY cofinal scales cannot hide the linear Gamma deficit
of the coherent unit-prime control. -/
theorem binary_control_not_cofinal_sublinear_deficit {X : ℕ → ℕ}
    (hX : Tendsto X atTop atTop) :
    ¬Tendsto (fun j : ℕ => deficit (ArithmeticOperatorPrimeTowerControl.towerCoefficient
        (ArithmeticOperatorBinaryPrimeControl.retainedBase (10001/20000) 54))
        (X j)/(X j : ℝ)) atTop (𝓝 0) := by
  intro ht
  obtain ⟨c,hc,he⟩ := binary_control_linear_deficit
  obtain ⟨j,hlo,hhi⟩ := ((ht.eventually_lt_const hc).and (hX.eventually he)).exists
  exact (not_lt_of_ge hhi) hlo

end
end RiemannGaussian.ArithmeticOperatorGammaConeStability
