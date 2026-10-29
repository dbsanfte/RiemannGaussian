/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetScalarMap
import RiemannGaussian.SemiprimeD1JetInterpretation
import RiemannGaussian.SemiprimeD1DyadicInteger

/-! # Literal CURRENT coefficient-word tables lifted through an integer source
The word vector is read as its literal nonnegative integer coefficients. Each
new precision reduces this same integer lift separately. There is no upward
precision ring homomorphism and no creator replay/recipe or coefficient oracle.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1JetLiteralLift
open scoped BigOperators
open SemiprimeD1JetAlgebra SemiprimeD1JetScalarMap SemiprimeD1JetBoxIndex
  SemiprimeD1JetInterpretation SemiprimeD1DyadicInteger SemiprimeBitArithmetic
noncomputable section

/-- Integral coefficient algebra with exactly the CURRENT old-axis dimensions. -/
abbrev Integral (axes : List ℕ) := Algebra (dims axes) integers

/-- Literal current coefficient words interpreted as actual natural integers. -/
def literal (axes : List ℕ) (ws : List (List Bool)) : Integral axes :=
  ∑i : Fin axes.prod,project (dims axes)
    (MvPowerSeries.monomial (exponent axes i.val) (bitValue ((ws[i.val]?).getD []):integers))

/-- The corresponding exact rational old-jet witness, NOT a requested coefficient table. -/
def rational (axes : List ℕ) (ws : List (List Bool)) : Algebra (dims axes) ℚ :=
  scalarMap (dims axes) integers.subtype (literal axes ws)

/-- At EVERY precision, reducing the actual integer lift gives the actual acquired
word-vector interpretation. No shape, compactness, or canonical-answer premise is needed. -/
theorem literal_reduce (axes : List ℕ) (p : ℕ) (ws : List (List Bool)) :
    scalarMap (dims axes) (reduction p) (literal axes ws)=interpret ⟨axes,p⟩ ws := by
  simp only [literal,map_sum,scalarMap_monomial,map_natCast,interpret,basis,
    SemiprimeD1JetRingBits.coefficient,SemiprimeD1JetAxes.Context.rank]
  rfl

/-- Literal rational coefficients are the actual original word integers, not new rational answers. -/
theorem rational_formula (axes : List ℕ) (ws : List (List Bool)) :
    rational axes ws=∑i : Fin axes.prod,project (dims axes)
      (MvPowerSeries.monomial (exponent axes i.val) (bitValue ((ws[i.val]?).getD []):ℚ)) := by
  simp only [rational,literal,map_sum,scalarMap_monomial,map_natCast]

/-- ALL current old-axis coordinates retain their literal word integer coefficients. -/
theorem literal_coefficient (axes : List ℕ) (ws : List (List Bool))
    (hpos : ∀q∈axes,0<q) (i : ℕ) (hi : i<axes.prod) :
    coefficient (dims axes) (exponent axes i) (exponent_inBox axes i hpos hi) (literal axes ws)=
      (bitValue ((ws[i]?).getD []):integers) := by
  classical
  rw [literal,quotient_coefficient_sum]
  let index : Fin axes.prod:=⟨i,hi⟩
  rw [Finset.sum_eq_single index]
  · simp only [coefficient_project,MvPowerSeries.coeff_monomial,ite_true,index]
  · intro j _ hj
    have hn : exponent axes i≠exponent axes j.val := by
      intro he
      have hij:=exponent_injective axes hpos i j.val hi j.isLt he
      exact hj (Fin.ext hij.symm)
    simp only [coefficient_project,MvPowerSeries.coeff_monomial,hn,ite_false]
  · intro hn
    exact False.elim (hn (Finset.mem_univ index))

/-- The exact rational old-jet witness has actual literal integer coordinates. -/
theorem rational_coefficient (axes : List ℕ) (ws : List (List Bool))
    (hpos : ∀q∈axes,0<q) (i : ℕ) (hi : i<axes.prod) :
    coefficient (dims axes) (exponent axes i) (exponent_inBox axes i hpos hi) (rational axes ws)=
      (bitValue ((ws[i]?).getD []):ℚ) := by
  rw [rational,coefficient_scalarMap,literal_coefficient axes ws hpos i hi]
  exact map_natCast integers.subtype _

end
end RiemannGaussian.SemiprimeD1JetLiteralLift
