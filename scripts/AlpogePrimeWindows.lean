import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow
import Formalism.GammaFactorNonvanishing.RhOfRight

namespace RiemannGaussian.AlpogeWindow

open Deduction

noncomputable def zetaFamily : CharFamily where
  ι := Unit
  N := fun _ => 1
  χ := fun _ => 1
  a := fun _ => 1
  a_pos := fun _ => zero_lt_one
  adm := fun _ => Or.inl rfl

theorem gm_zeta (x : ℝ) : Gm zetaFamily x = G x := by
  classical
  have hc (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
    rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
  change (∑ _ : Unit, (1 : ℝ) * (Gchi (1 : DirichletCharacter ℂ 1) x).re) = G x
  rw [Fintype.sum_unique, one_mul]
  simp [Gchi, hc, G]

/-- One-sided bounds on arbitrarily far-out power-length windows imply Mathlib's RH. -/
theorem rh_of_smoothed_prime_windows
    (h : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ δ C : ℝ, 0 < δ ∧
      ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), G y ≤ C * y ^ θ) :
    _root_.RiemannHypothesis := by
  apply Formalism.VW.rh_of_right
  intro s hs _
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  have hθ : (1 / 2 : ℝ) < (1 / 2 + s.re) / 2 := by linarith
  have hθs : (1 / 2 + s.re) / 2 < s.re := by linarith
  obtain ⟨δ, C, hδ, hw⟩ := h _ hθ (by linarith)
  have hz := Deduction.zeroFree_of_rpow_window zetaFamily (C := C) (by linarith : 0 < (1 / 2 + s.re) / 2)
    (by linarith) hδ (by simpa only [gm_zeta] using hw)
  simpa only [zetaFamily, DirichletCharacter.LFunction_modOne_eq] using hz () s hθs

end RiemannGaussian.AlpogeWindow
