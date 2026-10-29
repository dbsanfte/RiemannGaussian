/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBlockArrayExecution
import RiemannGaussian.SemiprimeUniversalSourceExecution

/-!
# Acquiring the original network's source coefficient arrays

The word search, complete-block packing, integer binomial solve and universal
interpolation all run from finite input data. The final arrays contain the
original-variable pullbacks, including the leftover identity rows. Mathematical
polynomials appear only in the correctness theorems.

The Run reports retain interpolation and array arithmetic. Constructing words,
packing, the binomial data and finite expressions still has to be paid separately;
these reports are not asserted to be the complete primitive-bit runtime.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceArrayAcquisition
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes Subexp.ConstructivePacking SqrtLog
open SemiprimeFibreArrayExecution SemiprimeJetArray

variable {I E : Type} [Fintype I] [DecidableEq I] [DecidableEq E]
variable {n r Q : ℕ}

/-- Universal coefficient arrays produced by the actual integer parity solver. -/
def universal (R : ℕ) (a y : UniversalType r Q 1) : Run :=
  ⟨SemiprimeUniversalSourceExecution.universalRow
    (Subexp.TailInterval.intervalStart r Q R) R a y,0⟩

/-- The arrays contain the literal centered universal source polynomial. -/
theorem universal_spec (R : ℕ) (a y : UniversalType r Q 1) :
    Spec (R+1) (universal R a y) ((SemiprimeSourceLayout.universalLayout r Q R).row a y) :=
  SemiprimeUniversalSourceExecution.source_universal_coefficient R a y

/-- Original-variable arrays, computed from the searched incidence packing. -/
def row (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (ε : ℚ) (R : ℕ)
    (i : I) (v : Fin n) : Run :=
  let pack := SemiprimeFiniteEnumerations.searchPacking owner factor en ε
  SemiprimeBlockArrayExecution.sourceRow pack owner (R+1) (universal R) i v

/-- No requested coefficient is an input: the resulting array equals the
mathematical searched layout's actual row. -/
theorem row_spec (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (ε : ℚ) (R : ℕ)
    (i : I) (v : Fin n) :
    Spec (R+1) (row owner factor en ε R i v)
      ((SemiprimeSourceLayout.builtLayout owner factor en ε R).row i v) := by
  exact SemiprimeBlockArrayExecution.sourceRow_spec
    (SemiprimeFiniteEnumerations.searchPacking owner factor en ε) owner (R+1)
    (universal R) (SemiprimeSourceLayout.universalLayout r Q R).row
    (universal_spec R) i v

/-- Materialize the polynomial-sized full source array family in explicit input
incidence order. All later counter invocations can share this immutable array. -/
def acquire (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (ε : ℚ) (R : ℕ) :
    Array (Array (Array ℚ)) :=
  let pack := SemiprimeFiniteEnumerations.searchPacking owner factor en ε
  Array.ofFn (fun k : Fin en.incidences.values.length => Array.ofFn (fun v : Fin n =>
    (SemiprimeBlockArrayExecution.sourceRow pack owner (R+1) (universal R)
      (en.incidences.equivFin k) v).jet.coefficients))

/-- Read a cached original row without regenerating coefficients. The empty
defaults make the runtime accessor total; construction proves they are unused. -/
def read (en : FiniteEnumeration I) (a : Array (Array (Array ℚ)))
    (i : I) (v : Fin n) : Array ℚ :=
  ((a[(en.equivFin.symm i).val]?).getD #[])[v.val]?.getD #[]

/-- The cached source accessor is exactly the acquired row array. -/
theorem acquire_read (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (ε : ℚ) (R : ℕ)
    (i : I) (v : Fin n) :
    read en.incidences (acquire owner factor en ε R) i v =
      (row owner factor en ε R i v).jet.coefficients := by
  simp [read,acquire,row]

/-- Every cached coefficient is the original layout coefficient. -/
theorem acquire_coefficient (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (ε : ℚ) (R : ℕ)
    (i : I) (v : Fin n) (k : ℕ) (hk : k≤R) :
    coefficient (read en.incidences (acquire owner factor en ε R) i v) k =
      ((SemiprimeSourceLayout.builtLayout owner factor en ε R).row i v).coeff k := by
  rw [acquire_read]
  exact row_spec owner factor en ε R i v k (by omega)

/-- The materialized family has one entry per original incidence. -/
theorem acquire_size (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (ε : ℚ) (R : ℕ) :
    (acquire owner factor en ε R).size=en.incidences.values.length := by
  simp [acquire]

end RiemannGaussian.SemiprimeSourceArrayAcquisition
