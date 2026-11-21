import CheckAlpogePrimeTailBounds
import CheckLiuCofactor

/-! # Liu's verified half-plane for the averaged ordinary-prime tail -/

namespace RiemannGaussian.AlpogeMined

/-- The upper endpoint of Liu's verified decimal enclosure bounds the deficit
on every fourth-power sample with the full cubic prime cutoff. -/
theorem cubic_tail_liu_decimal :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 8 ≤ n →
      repeatedTailAt (Nat.log 2 n+1) n (n^3) ≤ C*((n:ℝ)^4)^(874957019420098947/10^18:ℝ) := by
  apply cubic_tail_of_zero_bound (by norm_num) (by norm_num)
  intro ρ
  exact (LiuCofactor.zero_re_le_limit ρ).trans CombineV22ExplicitRoot.boundary_decimal_bracket.2.le

end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  let axioms ← Lean.collectAxioms ``RiemannGaussian.AlpogeMined.cubic_tail_liu_decimal
  for ax in axioms do
    unless [``propext,``Classical.choice,``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in the cubic prime tail bound"
  logInfo m!"cubic_tail_liu_decimal depends on {axioms}"
