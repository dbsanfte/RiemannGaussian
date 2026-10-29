/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootCopyContraction
import RiemannGaussian.SemiprimeD1JetAffineCoefficient

/-! # Root scalar projection at the actual empty-axis context
The map is the quotient's actual constant coefficient, not an advised decoder.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1RootScalar
open SemiprimeD1JetAlgebra SemiprimeD1JetBoxIndex SemiprimeD1JetInterpretation
noncomputable section

/-- The empty-axis quotient's actual scalar coefficient map. -/
def scalar {R : Type*} [CommRing R] : Algebra (dims []) R→+*R :=
  Ideal.Quotient.lift (vanishing (R:=R) (dims [])) MvPowerSeries.constantCoeff
    (fun _f hf => hf 0 (fun i => Fin.elim0 i))

/-- The scalar map reads exactly the actual source series constant coefficient. -/
theorem scalar_project {R : Type*} [CommRing R] (f : MvPowerSeries (Fin 0) R) :
    scalar (project (dims []) f)=MvPowerSeries.constantCoeff f := rfl

/-- Actual coefficient constants are decoded without residue change. -/
theorem scalar_constants {R : Type*} [CommRing R] (c : R) :
    scalar (constants (dims []) c)=c := by
  rw [constants,RingHom.comp_apply,scalar_project,MvPowerSeries.constantCoeff_C]

/-- There are no hidden nonconstant coordinates in the root quotient. -/
theorem constants_scalar {R : Type*} [CommRing R] (c : Algebra (dims []) R) :
    constants (dims []) (scalar c)=c := by
  induction c using Quotient.inductionOn with
  | h f =>
    change project (dims []) (MvPowerSeries.C (MvPowerSeries.constantCoeff f))=project (dims []) f
    congr 1
    ext e
    have he : e=0 := by ext i; exact Fin.elim0 i
    simp [he]

/-- The scalar map of an actual interpreted root word is its physical
coefficient at dense index zero, for every precision and every input byte list. -/
theorem scalar_interpret (p : ℕ) (words : List (List Bool)) :
    scalar (interpret ⟨[],p⟩ words)=SemiprimeD1JetRingBits.coefficient ⟨[],p⟩ words 0 := by
  unfold interpret
  change scalar (∑i : Fin 1,basis ⟨[],p⟩ i.val (SemiprimeD1JetRingBits.coefficient ⟨[],p⟩ words i.val))=_
  rw [Fin.sum_univ_one]
  unfold basis
  rw [scalar_project]
  change MvPowerSeries.constantCoeff (MvPowerSeries.monomial (exponent [] 0)
    (SemiprimeD1JetRingBits.coefficient ⟨[],p⟩ words 0))=_
  rw [SemiprimeD1JetAffineCoefficient.exponent_zero,←MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_monomial,ite_eq_left rfl]

end
end RiemannGaussian.SemiprimeD1RootScalar
