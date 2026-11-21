import PartIV
import RiemannGaussian.DyadicPrimeZeroBound
import RiemannGaussian.SuzukiLocalCancellationCofactorTail
import Lean.Util.CollectAxioms

/-! Apply Baiying Liu's revised limiting zero-free half-plane to the centered
ordinary-prime sum. Run with `scripts/verify_liu_suzuki.py`. -/

namespace RiemannGaussian.LiuCofactor

theorem zero_re_le_limit (rho : NontrivialZetaZero) :
    rho.1.re ≤ CombineV22.limitingBoundary := by
  apply le_of_not_gt
  intro h
  exact CombineV22.zeta_nonzero rho.1 h rho.2.2.2 rho.2.1

theorem centeredPrimeCofactor_bound {X : ℝ} (hX : 1 ≤ X) :
    |suzukiLocalCenteredPrimeCofactorTail X| ≤
      4100 + 100 * X ^ (CombineV22.limitingBoundary - 1 / 2) := by
  have hb := CombineV22ExplicitRoot.boundary_decimal_bracket
  have hB : CombineV22.limitingBoundary ∈ Set.Icc 0 1 :=
    ⟨CombineV22.limitingBoundary_positive.le, by
      apply hb.2.le.trans
      norm_num⟩
  exact abs_centeredPrimeCofactorTail_le_of_re_le hB zero_re_le_limit hX

theorem centeredPrimeCofactor_bound_decimal {X : ℝ} (hX : 1 ≤ X) :
    |suzukiLocalCenteredPrimeCofactorTail X| ≤
      4100 + 100 * X ^ (374957019420098947 / 10^18 : ℝ) := by
  apply (centeredPrimeCofactor_bound hX).trans
  apply add_le_add (le_refl 4100)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le hX
  have hb := CombineV22ExplicitRoot.boundary_decimal_bracket.2
  change CombineV22.limitingBoundary < _ at hb
  linarith

/-- Liu's verified limiting half-plane applied to the complete integer dyadic prime sum. -/
theorem dyadicPrimeError_bound_decimal {n : ℕ} (hn : 2 ≤ n) :
    DyadicPrime.dyadicPrimeError n ≤ 2 * Real.log (2 * Real.pi) * Real.log 2 +
      (463 / 2500 : ℝ) * (n : ℝ) ^ (874957019420098947 / 10^18 : ℝ) := by
  apply DyadicPrime.dyadicPrimeError_le_of_zero_bound (by norm_num) _ hn
  intro ρ
  exact (zero_re_le_limit ρ).trans CombineV22ExplicitRoot.boundary_decimal_bracket.2.le

end RiemannGaussian.LiuCofactor

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.LiuCofactor.zero_re_le_limit,
      ``RiemannGaussian.LiuCofactor.centeredPrimeCofactor_bound,
      ``RiemannGaussian.LiuCofactor.centeredPrimeCofactor_bound_decimal,
      ``RiemannGaussian.LiuCofactor.dyadicPrimeError_bound_decimal] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
    logInfo m!"{decl} depends on {axioms}"
