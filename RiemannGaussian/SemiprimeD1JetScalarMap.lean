/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetAlgebra

/-! # Coefficient-ring maps of the actual rectangular old-jet quotient
Only coefficient ring homomorphisms are lifted. In particular this construction
does not create an upward-precision map between modular coefficient rings.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1JetScalarMap
open SemiprimeD1JetAlgebra
noncomputable section
variable {σ R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- Mapping original coefficients preserves the actual vanishing ideal. -/
theorem map_vanishing (dims : σ→ℕ) (f : R →+* S) (x : MvPowerSeries σ R)
    (hx : x∈vanishing dims) : (MvPowerSeries.map f) x∈vanishing dims := by
  intro e he
  rw [MvPowerSeries.coeff_map,hx e he,map_zero]

/-- Every actual vanishing representative maps to quotient zero. -/
theorem project_map_zero (dims : σ→ℕ) (f : R →+* S) (x : MvPowerSeries σ R)
    (hx : x∈vanishing (R:=R) dims) :
    project (R:=S) dims ((MvPowerSeries.map f) x)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (map_vanishing dims f x hx)

/-- The actual coefficientwise scalar map on the original quotient. -/
def scalarMap (dims : σ→ℕ) (f : R →+* S) : Algebra dims R →+* Algebra dims S :=
  Ideal.Quotient.lift (vanishing (R:=R) dims)
    ((project (R:=S) dims).comp (MvPowerSeries.map f)) (fun x hx => project_map_zero dims f x hx)

/-- The quotient scalar map retains the supplied representative's literal coefficient map. -/
theorem scalarMap_project (dims : σ→ℕ) (f : R →+* S) (x : MvPowerSeries σ R) :
    scalarMap dims f (project dims x)=project dims ((MvPowerSeries.map f) x) := rfl

/-- Every bounded original coefficient commutes with the actual quotient scalar map. -/
theorem coefficient_scalarMap (dims : σ→ℕ) (f : R →+* S) (x : Algebra dims R)
    (e : σ→₀ℕ) (he : InBox dims e) :
    coefficient dims e he (scalarMap dims f x)=f (coefficient dims e he x) := by
  induction x using Quotient.inductionOn with
  | h x =>
    change coefficient dims e he (scalarMap dims f (project dims x))=_
    rw [scalarMap_project,coefficient_project]
    change (MvPowerSeries.coeff e) ((MvPowerSeries.map f) x)=f ((MvPowerSeries.coeff e) x)
    exact MvPowerSeries.coeff_map f e x

/-- Original scalar constants commute with the actual old-jet coefficient map. -/
theorem scalarMap_constants (dims : σ→ℕ) (f : R →+* S) (r : R) :
    scalarMap dims f (constants dims r)=constants dims (f r) := by
  simp only [constants,RingHom.comp_apply,scalarMap_project,MvPowerSeries.map_C]

/-- Original finite monomial coordinate images commute with the actual scalar map. -/
theorem scalarMap_monomial (dims : σ→ℕ) (f : R →+* S) (e : σ→₀ℕ) (r : R) :
    scalarMap dims f (project dims (MvPowerSeries.monomial e r))=
      project dims (MvPowerSeries.monomial e (f r)) := by
  rw [scalarMap_project,MvPowerSeries.map_monomial]

/-- Scalar-map composition agrees on ALL old coordinates, without a faithfulness oracle. -/
theorem scalarMap_comp (dims : σ→ℕ) (f : R →+* S) (g : S →+* T) (x : Algebra dims R) :
    scalarMap dims g (scalarMap dims f x)=scalarMap dims (g.comp f) x := by
  apply SemiprimeD1JetAlgebra.ext dims
  intro e he
  simp only [coefficient_scalarMap,RingHom.comp_apply]

end
end RiemannGaussian.SemiprimeD1JetScalarMap
