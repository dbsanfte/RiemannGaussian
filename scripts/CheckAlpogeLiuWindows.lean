import CheckAlpogeZetaWindows
import CheckLiuCofactor

/-! # Liu's checked half-plane applied to Alpöge's modulus-one prime ramp -/

namespace RiemannGaussian.AlpogeWindow

/-- A global bound for the original ramp at Baiying Liu's limiting zero-free exponent. -/
theorem G_le_liu_limiting_boundary :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → Deduction.G x ≤ C*x^CombineV22.limitingBoundary := by
  apply G_le_of_zero_halfplane CombineV22.limitingBoundary_positive.le _ LiuCofactor.zero_re_le_limit
  exact CombineV22ExplicitRoot.boundary_decimal_bracket.2.trans (by norm_num)

/-- The upper endpoint of the certified decimal enclosure works throughout every window. -/
theorem G_le_liu_decimal :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      Deduction.G x ≤ C*x^(874957019420098947 / 10^18 : ℝ) := by
  obtain ⟨C,hC,h⟩ := G_le_liu_limiting_boundary
  exact ⟨C,hC,fun x hx => (h x hx).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hx CombineV22ExplicitRoot.boundary_decimal_bracket.2.le) hC)⟩

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeWindow.G_le_liu_limiting_boundary,
      ``RiemannGaussian.AlpogeWindow.G_le_liu_decimal] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
    logInfo m!"{decl} depends on {axioms}"
