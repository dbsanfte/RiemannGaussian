/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketModeOriginal
import RiemannGaussian.SemiprimeD1PacketEntryComponents

/-! # Actual acquired row polynomials use only the packet target modes
The support property is derived from the executed coefficient masks and actual
recipe list. No desired support or semantic coefficient-zero advice is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace RiemannGaussian.SemiprimeD1PacketPolynomialSupport
open scoped BigOperators
open SemiprimeD1SeparatedCoefficient SemiprimeD1PacketModeProjection
open SemiprimeD1PacketEntryBits SemiprimeD1PacketEntryValue SemiprimeD1PacketEntryInputs
open SemiprimeD1JetAxes SemiprimeD1JetInterpretation
noncomputable section
variable {V R : Type*} [CommRing R]

/-- Zero coefficients use no mode. -/
theorem on_zero (S : Set V) : On S (0 : MvPolynomial V R) := by
  intro e he
  have hz : (0 : MvPolynomial V R).coeff e=0 := by simp
  exact False.elim (he hz)

/-- A literal base value uses no mode. -/
theorem on_constant (S : Set V) (c : R) : On S (MvPolynomial.C c) := by
  intro e he v _
  by_cases hz : e=0
  · simp only [hz,Finsupp.zero_apply]
  · exact False.elim (he (MvPolynomial.coeff_C_of_ne_zero hz c))

/-- An acquired mode variable belongs to its actual designated family. -/
theorem on_variable (S : Set V) (v : V) (hv : v∈S) : On S (MvPolynomial.X v : MvPolynomial V R) := by
  classical
  intro e he w hw
  have hz : Finsupp.single v 1=e := by
    by_contra hn
    simp only [MvPolynomial.coeff_X,hn,ite_false,ne_eq,not_true_eq_false] at he
  rw [←hz]
  have hne : v≠w := by intro h;exact hw (h ▸ hv)
  simp only [Finsupp.single_apply,hne,ite_false]

/-- Addition cannot introduce a mode absent from both actual summands. -/
theorem on_add (S : Set V) (P Q : MvPolynomial V R) (hp : On S P) (hq : On S Q) : On S (P+Q) := by
  intro e he v hv
  by_cases hP : P.coeff e=0
  · have hQ : Q.coeff e≠0 := by
      intro hz
      apply he
      simp only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hP,hz,zero_add]
    exact hq e hQ v hv
  · exact hp e hP v hv

/-- Literal list sums preserve support, retaining duplicates rather than deduplicating rows. -/
theorem on_list_sum (S : Set V) (ps : List (MvPolynomial V R)) (hp : ∀p∈ps,On S p) : On S ps.sum := by
  induction ps with
  | nil => exact on_zero S
  | cons p ps ih =>
    exact on_add S p ps.sum (hp p List.mem_cons_self) (ih (fun q hq => hp q (List.mem_cons_of_mem p hq)))

/-- Literal list products preserve the exact repeated row family. -/
theorem on_list_prod (S : Set V) (ps : List (MvPolynomial V R)) (hp : ∀p∈ps,On S p) : On S ps.prod := by
  induction ps with
  | nil => exact on_one S
  | cons p ps ih =>
    exact on_mul S p ps.prod (hp p List.mem_cons_self) (ih (fun q hq => hp q (List.mem_cons_of_mem p hq)))

/-- Actual zero coefficients outside a set imply support of the complete affine row. -/
theorem rowPolynomial_on (S : Set ℕ) (K : ℕ) (row : SemiprimeD1AffineCoefficient.Row R)
    (hc : ∀ j, j < K → j ∉ S → row.coefficients.getD j 0 = 0) :
    On S (SemiprimeD1AffineCoefficient.rowPolynomial K row) := by
  unfold SemiprimeD1AffineCoefficient.rowPolynomial
  apply on_add S _ _ (on_constant S row.base)
  apply on_list_sum
  intro p hp
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
  by_cases hs : j∈S
  · exact on_mul S _ _ (on_constant S _) (on_variable S j hs)
  · have hz := hc j (List.mem_range.mp hj) hs
    simpa only [hz,map_zero,zero_mul] using (on_zero (R:=R) S)

/-- Executed packet masks really zero every coefficient outside the target family. -/
theorem coefficient_zero (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a)
    (item : SemiprimeD1PacketModeMask.Item) (hz : (item.inPacket && item.targetHere)=false) :
    interpret ctx (coefficient ctx z a i t row item).words=0 := by
  simp only [coefficient,hz,Bool.false_and,Bool.false_eq_true,ite_false]
  exact SemiprimeD1JetAffineCoefficient.interpret_zero ctx

/-- The actual acquired coefficient vector, not an advised semantic row, obeys its mask. -/
theorem recipe_coefficient_zero (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a)
    (columns : List (Wire a)) (cache : SemiprimeD1PacketModeMask.Cache) (j : ℕ)
    (hj : j<cache.items.length) (hn : j∉targetSet cache) :
    (SemiprimeD1JetAffineCoefficient.rowValue ctx (recipe ctx z a i t row columns cache.items).value).coefficients.getD j 0=0 := by
  have hf : (cache.items[j].inPacket && cache.items[j].targetHere)=false := by
    apply Bool.eq_false_iff.mpr
    intro he
    apply hn
    change targetEnabled cache.items j=true
    simpa only [targetEnabled,List.getElem?_eq_getElem hj] using he
  have hzero := coefficient_zero ctx z a i t row cache.items[j] hf
  change ((coefficients ctx z a i t row cache.items).value.map (interpret ctx)).getD j 0=0
  rw [coefficients_value,List.map_map]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hj),List.getElem_map]
  exact hzero

/-- The complete ACTUAL row polynomial has the support required by mode separation. -/
theorem packet_polynomial_on (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (columns rows : List (Wire a)) (cache : SemiprimeD1PacketModeMask.Cache) :
    On (targetSet cache) (SemiprimeD1AffineCoefficient.polynomial cache.items.length
      ((recipes ctx z a i t columns cache.items rows).value.map (SemiprimeD1JetAffineCoefficient.rowValue ctx))) := by
  unfold SemiprimeD1AffineCoefficient.polynomial
  apply on_list_prod
  intro p hp
  obtain ⟨row,hrow,rfl⟩ := List.mem_map.mp hp
  apply rowPolynomial_on
  intro j hj hn
  rw [recipes_value,List.map_map] at hrow
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp hrow
  exact recipe_coefficient_zero ctx z a i t original columns cache j hj hn

end
end RiemannGaussian.SemiprimeD1PacketPolynomialSupport
