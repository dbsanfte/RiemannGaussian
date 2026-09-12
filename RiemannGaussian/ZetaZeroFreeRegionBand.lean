/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaFermiGlobalMargin

/-!
# Complete height bands for general zero-free widths

An eventual decreasing zero-free width need not have the form `a/log(t)`.
If it tends to zero, the existing positive margin below its starting height
completes it to a margin for every zero in each sufficiently large band.
The theorem keeps the width function itself, so logarithmic, Littlewood
and Vinogradov--Korobov shapes can use the same downstream interface once
their actual zero-free theorems are proved.

Combining two proved bands uses their maximum, not their minimum. Literal
zeta nonvanishing on the resulting closed edge is also retained. None of
the external quantitative regions is assumed or asserted here.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter Topology

/-- Any positive decreasing eventual width tending to zero supplies its
own common margin for the complete divisor below a sufficiently large
height. The existing global theorem covers all zeros below `T`. -/
theorem exists_eventual_common_margin_of_antitone (w : ℝ → ℝ) {T : ℝ}
    (hT : 1 ≤ T) (hpos : ∀ H : ℝ, T ≤ H → 0 < w H)
    (hanti : AntitoneOn w (Set.Ici T)) (hlim : Tendsto w atTop (𝓝 0))
    (hregion : ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      w |ρ.1.im| < ρ.1.re ∧ ρ.1.re < 1 - w |ρ.1.im|) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      0 < w H ∧ w H < 1 / 4 ∧
        ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H →
          w H < ρ.1.re ∧ ρ.1.re < 1 - w H := by
  have hd := (zetaFermiZeroMargin_bounds T).1
  obtain ⟨U, hU⟩ := eventually_atTop.mp (hlim.eventually_lt_const hd)
  refine ⟨max T U, hT.trans (le_max_left _ _), ?_⟩
  intro H hH
  have hTH : T ≤ H := (le_max_left _ _).trans hH
  have hcap : w H < zetaFermiZeroMargin T := hU H ((le_max_right _ _).trans hH)
  refine ⟨hpos H hTH, hcap.trans (zetaFermiZeroMargin_bounds T).2, ?_⟩
  intro ρ hρH
  by_cases hρT : |ρ.1.im| ≤ T
  · have hm := zetaFermiZeroMargin_antitone_abs
      (show |ρ.1.im| ≤ |T| by simpa only [abs_of_nonneg (by linarith : 0 ≤ T)] using hρT)
    have hz := nontrivialZetaZero_mem_fermi_strip ρ
    exact ⟨(hcap.trans_le hm).trans hz.1, by linarith [hz.2]⟩
  · have hTρ : T ≤ |ρ.1.im| := (lt_of_not_ge hρT).le
    have hm : w H ≤ w |ρ.1.im| := hanti hTρ hTH hρH
    have hz := hregion ρ hTρ
    exact ⟨hm.trans_lt hz.1, by linarith [hz.2]⟩

/-- The boundary-aware version for a published open zero-free region:
non-strict bounds on the surviving zeros remain non-strict on the full
height band. No extra boundary nonvanishing is assumed. -/
theorem exists_eventual_common_weak_margin_of_antitone (w : ℝ → ℝ) {T : ℝ}
    (hT : 1 ≤ T) (hpos : ∀ H : ℝ, T ≤ H → 0 < w H)
    (hanti : AntitoneOn w (Set.Ici T)) (hlim : Tendsto w atTop (𝓝 0))
    (hregion : ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      w |ρ.1.im| ≤ ρ.1.re ∧ ρ.1.re ≤ 1 - w |ρ.1.im|) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      0 < w H ∧ w H < 1 / 4 ∧
        ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H →
          w H ≤ ρ.1.re ∧ ρ.1.re ≤ 1 - w H := by
  have hd := (zetaFermiZeroMargin_bounds T).1
  obtain ⟨U, hU⟩ := eventually_atTop.mp (hlim.eventually_lt_const hd)
  refine ⟨max T U, hT.trans (le_max_left _ _), ?_⟩
  intro H hH
  have hTH : T ≤ H := (le_max_left _ _).trans hH
  have hcap : w H < zetaFermiZeroMargin T := hU H ((le_max_right _ _).trans hH)
  refine ⟨hpos H hTH, hcap.trans (zetaFermiZeroMargin_bounds T).2, ?_⟩
  intro ρ hρH
  by_cases hρT : |ρ.1.im| ≤ T
  · have hm := zetaFermiZeroMargin_antitone_abs
      (show |ρ.1.im| ≤ |T| by simpa only [abs_of_nonneg (by linarith : 0 ≤ T)] using hρT)
    have hz := nontrivialZetaZero_mem_fermi_strip ρ
    exact ⟨((hcap.trans_le hm).trans hz.1).le, by linarith [hz.2]⟩
  · have hTρ : T ≤ |ρ.1.im| := (lt_of_not_ge hρT).le
    have hm : w H ≤ w |ρ.1.im| := hanti hTρ hTH hρH
    have hz := hregion ρ hTρ
    exact ⟨hm.trans hz.1, by linarith [hz.2]⟩

/-- Two valid widths on the same complete height band combine by taking
their larger value. Every zero obeys both bounds, including the edges. -/
theorem nontrivialZetaZero_common_margin_max {H a b : ℝ}
    (ha : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H →
      a < ρ.1.re ∧ ρ.1.re < 1 - a)
    (hb : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H →
      b < ρ.1.re ∧ ρ.1.re < 1 - b) :
    ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H →
      max a b < ρ.1.re ∧ ρ.1.re < 1 - max a b := by
  intro ρ hρ
  obtain ⟨haL, haR⟩ := ha ρ hρ
  obtain ⟨hbL, hbR⟩ := hb ρ hρ
  refine ⟨max_lt haL hbL, ?_⟩
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    exact hbR
  · rw [max_eq_left hba]
    exact haR

/-- A complete band with width below one gives literal nonvanishing on
its closed right edge. The pole is excluded explicitly. -/
theorem riemannZeta_ne_zero_of_common_margin {H m : ℝ} (hm : m < 1)
    (hband : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H → ρ.1.re < 1 - m)
    {s : ℂ} (hs1 : s ≠ 1) (hsH : |s.im| ≤ H) (hs : 1 - m ≤ s.re) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hspos : 0 < s.re := by linarith
  have hpole : riemannZeta₁ s = 0 := by
    rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let ρ : NontrivialZetaZero :=
    ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  have h := hband ρ hsH
  change s.re < 1 - m at h
  linarith

/-- A non-strict bound on the zeros gives literal nonvanishing strictly
to its right. The endpoint is deliberately not included. -/
theorem riemannZeta_ne_zero_of_common_weak_margin {H m : ℝ} (hm : m < 1)
    (hband : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H → ρ.1.re ≤ 1 - m)
    {s : ℂ} (hs1 : s ≠ 1) (hsH : |s.im| ≤ H) (hs : 1 - m < s.re) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hspos : 0 < s.re := by linarith
  have hpole : riemannZeta₁ s = 0 := by
    rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let ρ : NontrivialZetaZero :=
    ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  have h := hband ρ hsH
  change s.re ≤ 1 - m at h
  linarith

end
end RiemannGaussian
