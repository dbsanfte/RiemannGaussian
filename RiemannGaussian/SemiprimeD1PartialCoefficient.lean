/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1SeparatedCoefficient

/-! # Exact coefficient separation with no owner for absent indices
Optional ownership treats empty inventories without a fictitious packet.
Actual original queries discharge the absent-index zero condition separately.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1PartialCoefficient
open scoped BigOperators
open SemiprimeD1SeparatedCoefficient
variable {V G R : Type*} [Fintype G] [CommRing R]

/-- Disjoint actual owner fibres factor a useful coefficient even when unused
ambient indices have no owner and the actual owner family is empty. -/
theorem coefficient_optional (owner : V → Option G) (P : G → MvPolynomial V R)
    (hp : ∀ g, On {v | owner v = some g} (P g)) (e : V →₀ ℕ)
    (hz : ∀ v, owner v = none → e v = 0) :
    (∏ g, P g).coeff e = ∏ g, (P g).coeff (restrict {v | owner v = some g} e) := by
  classical
  let full : Option G → MvPolynomial V R := fun g => match g with
    | none => 1
    | some g => P g
  have hfull : ∀ g, On {v | owner v = g} (full g) := by
    intro g
    cases g with
    | none => exact on_one _
    | some g => exact hp g
  have h := coefficient_all_owners owner full hfull e
  have he : restrict {v | owner v = none} e = 0 := by
    ext v
    rw [restrict_apply]
    by_cases hv : owner v = none
    · simpa only [Set.mem_ofPred_eq,hv,ite_true,Finsupp.zero_apply] using hz v hv
    · simp only [Set.mem_ofPred_eq,hv,ite_false,Finsupp.zero_apply]
  simpa only [Fintype.prod_option, full, one_mul, he, MvPolynomial.coeff_one, ite_true] using h

end RiemannGaussian.SemiprimeD1PartialCoefficient
