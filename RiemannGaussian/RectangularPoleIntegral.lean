/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FinitePoleRegularization
import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatFiniteExcision
import RiemannGaussian.RiemannXiSuzukiSpectralSignedContourTimeDerivative

/-!
# Rectangular integrals of complete Laurent principal parts

Only the residue coefficient survives a closed contour, but all negative
Laurent powers must be removed to make the remainder analytic. We prove
the rectangular primitive identity directly on its four sides, then use
it to evaluate arbitrary higher-order principal parts with orientation
and all Taylor coefficients explicit.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- A primitive defined on the four complete side lines has zero integral
around their rectangle. Differentiability inside the rectangle is not
required, so this applies to primitives with an interior pole. -/
theorem rectangularBoundaryIntegral_eq_zero_of_primitive
    (l r b u : ℝ) (f F : ℂ → ℂ)
    (hint : rectangularBoundaryIntegrable l r b u f)
    (hb : ∀ x : ℝ, HasDerivAt F (f ((x : ℂ) + (b : ℂ) * I)) ((x : ℂ) + (b : ℂ) * I))
    (hu : ∀ x : ℝ, HasDerivAt F (f ((x : ℂ) + (u : ℂ) * I)) ((x : ℂ) + (u : ℂ) * I))
    (hl : ∀ y : ℝ, HasDerivAt F (f ((l : ℂ) + (y : ℂ) * I)) ((l : ℂ) + (y : ℂ) * I))
    (hr : ∀ y : ℝ, HasDerivAt F (f ((r : ℂ) + (y : ℂ) * I)) ((r : ℂ) + (y : ℂ) * I)) :
    rectangularBoundaryIntegral l r b u f = 0 := by
  have horizontal (v : ℝ)
      (h : ∀ x : ℝ, HasDerivAt F (f ((x : ℂ) + (v : ℂ) * I)) ((x : ℂ) + (v : ℂ) * I))
      (hi : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (v : ℂ) * I)) volume l r) :
      (∫ x : ℝ in l..r, f ((x : ℂ) + (v : ℂ) * I)) =
        F ((r : ℂ) + (v : ℂ) * I) - F ((l : ℂ) + (v : ℂ) * I) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
    intro x _hx
    simpa only [Function.comp_apply, id_eq, mul_one] using!
      ((h x).comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const ((v : ℂ) * I))).comp_ofReal
  have vertical (v : ℝ)
      (h : ∀ y : ℝ, HasDerivAt F (f ((v : ℂ) + (y : ℂ) * I)) ((v : ℂ) + (y : ℂ) * I))
      (hi : IntervalIntegrable (fun y : ℝ => f ((v : ℂ) + (y : ℂ) * I)) volume b u) :
      I * (∫ y : ℝ in b..u, f ((v : ℂ) + (y : ℂ) * I)) =
        F ((v : ℂ) + (u : ℂ) * I) - F ((v : ℂ) + (b : ℂ) * I) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hi.const_mul I)
    intro y _hy
    simpa only [Function.comp_apply, id_eq, one_mul, mul_one, mul_comm] using!
      ((h y).comp (y : ℂ)
        (((hasDerivAt_id (y : ℂ)).mul_const I).const_add (v : ℂ))).comp_ofReal
  unfold rectangularBoundaryIntegral
  rw [horizontal b hb hint.1, horizontal u hu hint.2.1,
    vertical r hr hint.2.2.1, vertical l hl hint.2.2.2]
  ring

private lemma ne_on_side_lines {c : ℂ} {l r b u : ℝ}
    (hl : l < c.re) (hr : c.re < r) (hb : b < c.im) (hu : c.im < u) :
    (∀ x : ℝ, (x : ℂ) + (b : ℂ) * I ≠ c) ∧
    (∀ x : ℝ, (x : ℂ) + (u : ℂ) * I ≠ c) ∧
    (∀ y : ℝ, (l : ℂ) + (y : ℂ) * I ≠ c) ∧
    (∀ y : ℝ, (r : ℂ) + (y : ℂ) * I ≠ c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x h
    have he := congrArg Complex.im h
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, mul_zero, add_zero, zero_add] at he
    linarith
  · intro x h
    have he := congrArg Complex.im h
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, mul_zero, add_zero, zero_add] at he
    linarith
  · intro y h
    have he := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero] at he
    linarith
  · intro y h
    have he := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero] at he
    linarith

/-- Every integer Laurent power other than the simple pole has zero
rectangular integral around its interior center. -/
theorem rectangularBoundaryIntegral_sub_zpow_eq_zero {n : ℤ} (hn : n ≠ -1)
    (c : ℂ) {l r b u : ℝ}
    (hl : l < c.re) (hr : c.re < r) (hb : b < c.im) (hu : c.im < u) :
    rectangularBoundaryIntegral l r b u (fun z => (z - c) ^ n) = 0 := by
  have hside := ne_on_side_lines hl hr hb hu
  have hd (z : ℂ) (hz : z ≠ c) :
      HasDerivAt (fun z => (z - c) ^ (n + 1) / (n + 1)) ((z - c) ^ n) z := by
    convert! ((hasDerivAt_zpow (n + 1) (z - c) (Or.inl (sub_ne_zero.mpr hz))).comp z
      ((hasDerivAt_id z).sub_const c)).div_const (n + 1) using 1
    have hn' : (n + 1 : ℂ) ≠ 0 := by
      rwa [Ne, ← eq_neg_iff_add_eq_zero, ← Int.cast_one, ← Int.cast_neg, Int.cast_inj]
    simp [mul_div_cancel_left₀ _ hn']
  have hcont (g : ℝ → ℂ) (hg : Continuous g) (hne : ∀ x, g x ≠ c) :
      Continuous (fun x => (g x - c) ^ n) := by
    apply Continuous.zpow₀ (hg.sub continuous_const)
    intro x
    exact Or.inl (sub_ne_zero.mpr (hne x))
  apply rectangularBoundaryIntegral_eq_zero_of_primitive l r b u _ _
  · exact ⟨(hcont _ (by fun_prop) hside.1).intervalIntegrable l r,
      (hcont _ (by fun_prop) hside.2.1).intervalIntegrable l r,
      (hcont _ (by fun_prop) hside.2.2.2).intervalIntegrable b u,
      (hcont _ (by fun_prop) hside.2.2.1).intervalIntegrable b u⟩
  · exact fun x => hd _ (hside.1 x)
  · exact fun x => hd _ (hside.2.1 x)
  · exact fun y => hd _ (hside.2.2.1 y)
  · exact fun y => hd _ (hside.2.2.2 y)

/-- Every integer Laurent power is genuinely integrable on all four
sides of a rectangle containing its center strictly in the interior. -/
theorem rectangularBoundaryIntegrable_sub_zpow (n : ℤ) (c : ℂ) {l r b u : ℝ}
    (hl : l < c.re) (hr : c.re < r) (hb : b < c.im) (hu : c.im < u) :
    rectangularBoundaryIntegrable l r b u (fun z => (z - c) ^ n) := by
  have hside := ne_on_side_lines hl hr hb hu
  have hcont (g : ℝ → ℂ) (hg : Continuous g) (hne : ∀ x, g x ≠ c) :
      Continuous (fun x => (g x - c) ^ n) := by
    apply Continuous.zpow₀ (hg.sub continuous_const)
    intro x
    exact Or.inl (sub_ne_zero.mpr (hne x))
  exact ⟨(hcont _ (by fun_prop) hside.1).intervalIntegrable l r,
    (hcont _ (by fun_prop) hside.2.1).intervalIntegrable l r,
    (hcont _ (by fun_prop) hside.2.2.2).intervalIntegrable b u,
    (hcont _ (by fun_prop) hside.2.2.1).intervalIntegrable b u⟩

/-- The complete negative Laurent part has exactly its residue's
counterclockwise rectangular integral, including arbitrary pole orders. -/
theorem rectangularBoundaryIntegral_poleTaylorPrincipalPart (m : ℕ) (F : ℂ → ℂ)
    (c : ℂ) {l r b u : ℝ}
    (hl : l < c.re) (hr : c.re < r) (hb : b < c.im) (hu : c.im < u) :
    rectangularBoundaryIntegral l r b u (poleTaylorPrincipalPart m F c) =
      (2 * Real.pi : ℝ) * I * poleTaylorResidue m F c := by
  have hside := ne_on_side_lines hl hr hb hu
  have heq : rectangularBoundaryIntegral l r b u (poleTaylorPrincipalPart m F c) =
      rectangularBoundaryIntegral l r b u (fun z => ∑ k ∈ Finset.range m,
        (iteratedDeriv k F c / (k.factorial : ℂ)) * (z - c) ^ ((k : ℤ) - (m : ℤ))) := by
    apply rectangularBoundaryIntegral_congr_of_eq_on_sides
    · exact fun x _ => poleTaylorPrincipalPart_eq_sum_zpow_of_ne m F (hside.1 x)
    · exact fun x _ => poleTaylorPrincipalPart_eq_sum_zpow_of_ne m F (hside.2.1 x)
    · exact fun y _ => poleTaylorPrincipalPart_eq_sum_zpow_of_ne m F (hside.2.2.2 y)
    · exact fun y _ => poleTaylorPrincipalPart_eq_sum_zpow_of_ne m F (hside.2.2.1 y)
  rw [heq, rectangularBoundaryIntegral_finsetSum]
  swap
  · intro k _hk
    have hi := rectangularBoundaryIntegrable_sub_zpow ((k : ℤ) - (m : ℤ)) c hl hr hb hu
    exact ⟨hi.1.const_mul _, hi.2.1.const_mul _, hi.2.2.1.const_mul _, hi.2.2.2.const_mul _⟩
  by_cases hm : m = 0
  · simp [hm, poleTaylorResidue]
  have hterm (k : ℕ) (hk : k ∈ Finset.range m) :
      rectangularBoundaryIntegral l r b u (fun z =>
        (iteratedDeriv k F c / (k.factorial : ℂ)) * (z - c) ^ ((k : ℤ) - (m : ℤ))) =
        if k = m - 1 then (2 * Real.pi : ℝ) * I * poleTaylorResidue m F c else 0 := by
    by_cases hkm : k = m - 1
    · rw [if_pos hkm]
      have hexp : (k : ℤ) - (m : ℤ) = -1 := by omega
      simp only [hexp, zpow_neg_one, ← div_eq_mul_inv]
      exact (rectangularBoundaryIntegral_simplePoleKernel_of_mem
        (iteratedDeriv k F c / (k.factorial : ℂ)) c hl hr hb hu).trans (by
          simp only [poleTaylorResidue, if_neg hm, hkm])
    · rw [if_neg hkm, rectangularBoundaryIntegral_const_mul,
        rectangularBoundaryIntegral_sub_zpow_eq_zero (by
          have hkm' := Finset.mem_range.mp hk
          omega) c hl hr hb hu, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  have hmem : m - 1 ∈ Finset.range m := Finset.mem_range.mpr (by omega)
  simp only [Finset.sum_ite_eq' (Finset.range m) (m - 1), if_pos hmem]

/-- The full Laurent principal part is integrable on every side of a
rectangle strictly enclosing its center. -/
theorem rectangularBoundaryIntegrable_poleTaylorPrincipalPart (m : ℕ) (F : ℂ → ℂ)
    (c : ℂ) {l r b u : ℝ}
    (hl : l < c.re) (hr : c.re < r) (hb : b < c.im) (hu : c.im < u) :
    rectangularBoundaryIntegrable l r b u (poleTaylorPrincipalPart m F c) := by
  have hside := ne_on_side_lines hl hr hb hu
  have hcont (g : ℝ → ℂ) (hg : Continuous g) (hne : ∀ x, g x ≠ c) :
      Continuous (fun x => poleTaylorPrincipalPart m F c (g x)) :=
    continuous_comp_of_forall_analyticAt _ _ hg
      (fun x => analyticAt_poleTaylorPrincipalPart_of_ne m F (hne x))
  exact ⟨(hcont _ (by fun_prop) hside.1).intervalIntegrable l r,
    (hcont _ (by fun_prop) hside.2.1).intervalIntegrable l r,
    (hcont _ (by fun_prop) hside.2.2.2).intervalIntegrable b u,
    (hcont _ (by fun_prop) hside.2.2.1).intervalIntegrable b u⟩

/-- A finite set of arbitrary-order genuine pole models gives the exact
counterclockwise rectangular residue identity. All local principal parts
are subtracted before applying Cauchy to the analytic remainder. -/
theorem rectangularBoundaryIntegral_eq_finitePole_residues
    (l r b u : ℝ) (hlr : l ≤ r) (hbu : b ≤ u)
    (S : Finset ℂ) (f : ℂ → ℂ) (order : ℂ → ℕ) (numerator : ℂ → ℂ → ℂ)
    (hS : ∀ c ∈ S, l < c.re ∧ c.re < r ∧ b < c.im ∧ c.im < u)
    (hint : rectangularBoundaryIntegrable l r b u f)
    (hoff : ∀ z ∈ Complex.Rectangle ((l : ℂ) + (b : ℂ) * I) ((r : ℂ) + (u : ℂ) * I),
      z ∉ S → AnalyticAt ℂ f z)
    (hnum : ∀ c ∈ S, AnalyticAt ℂ (numerator c) c)
    (hmodel : ∀ c ∈ S, f =ᶠ[𝓝[≠] c] fun z => numerator c z / (z - c) ^ order c) :
    rectangularBoundaryIntegral l r b u f =
      (2 * Real.pi : ℝ) * I * ∑ c ∈ S, poleTaylorResidue (order c) (numerator c) c := by
  have hSU : ∀ c ∈ S,
      c ∈ Complex.Rectangle ((l : ℂ) + (b : ℂ) * I) ((r : ℂ) + (u : ℂ) * I) := by
    intro c hc
    have hs := hS c hc
    simpa [Complex.Rectangle, Complex.mem_reProdIm, Set.uIcc_of_le hlr, Set.uIcc_of_le hbu]
      using And.intro (And.intro hs.1.le hs.2.1.le) (And.intro hs.2.2.1.le hs.2.2.2.le)
  obtain ⟨H, hH, hHeq⟩ := exists_finitePole_analytic_regularization _ S f order numerator
    hSU hoff hnum hmodel
  have hHint : rectangularBoundaryIntegral l r b u H = 0 :=
    rectangularBoundaryIntegral_eq_zero_of_differentiableOn l r b u H
      (fun z hz => (hH z hz).differentiableAt.differentiableWithinAt)
  have hparts : ∀ c ∈ S,
      rectangularBoundaryIntegrable l r b u
        (poleTaylorPrincipalPart (order c) (numerator c) c) := by
    intro c hc
    have hs := hS c hc
    exact rectangularBoundaryIntegrable_poleTaylorPrincipalPart _ _ _
      hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  have hsum := rectangularBoundaryIntegrable_finsetSum l r b u S _ hparts
  change rectangularBoundaryIntegrable l r b u (finitePolePrincipalSum S order numerator) at hsum
  have hboundary : rectangularBoundaryIntegral l r b u
      (fun z => f z - finitePolePrincipalSum S order numerator z) =
        rectangularBoundaryIntegral l r b u H := by
    apply rectangularBoundaryIntegral_congr_of_eq_on_sides
    · intro x _hx
      apply (hHeq _ _).symm
      intro hc
      have hs := hS _ hc
      exact (ne_on_side_lines hs.1 hs.2.1 hs.2.2.1 hs.2.2.2).1 x rfl
    · intro x _hx
      apply (hHeq _ _).symm
      intro hc
      have hs := hS _ hc
      exact (ne_on_side_lines hs.1 hs.2.1 hs.2.2.1 hs.2.2.2).2.1 x rfl
    · intro y _hy
      apply (hHeq _ _).symm
      intro hc
      have hs := hS _ hc
      exact (ne_on_side_lines hs.1 hs.2.1 hs.2.2.1 hs.2.2.2).2.2.2 y rfl
    · intro y _hy
      apply (hHeq _ _).symm
      intro hc
      have hs := hS _ hc
      exact (ne_on_side_lines hs.1 hs.2.1 hs.2.2.1 hs.2.2.2).2.2.1 y rfl
  rw [rectangularBoundaryIntegral_sub l r b u hint hsum, hHint] at hboundary
  have hsumInt : rectangularBoundaryIntegral l r b u
      (finitePolePrincipalSum S order numerator) =
        (2 * Real.pi : ℝ) * I * ∑ c ∈ S, poleTaylorResidue (order c) (numerator c) c := by
    unfold finitePolePrincipalSum
    rw [rectangularBoundaryIntegral_finsetSum l r b u S _ hparts, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    have hs := hS c hc
    exact rectangularBoundaryIntegral_poleTaylorPrincipalPart _ _ _
      hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  exact (sub_eq_zero.mp hboundary).trans hsumInt

end
end RiemannGaussian
