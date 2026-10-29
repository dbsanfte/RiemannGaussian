/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeFibreArrayExecution

/-! # Indexed native certificates backed by executed representative scans -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RiemannGaussian.SemiprimeIndexedNodeCertificate
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Polynomial SemiprimeCounterCompose SemiprimeLayoutCertificates
open SemiprimeRepresentativeExecution SemiprimeFibreArrayExecution
open SemiprimeCounterSeparation SemiprimeSharedSummary
variable {A E : Type} [Fintype A] [DecidableEq A] [Fintype E]

/-- Literal indexed groups and bounded original integer measurements, with native locality. -/
structure Data (arity : E → ℕ) (rows : (e : E) → Fin (arity e) → A → ℚ) where
  /-- Number of groups. -/
  r : ℕ
  /-- Local Boolean dimensions. -/
  h : Fin r → ℕ
  /-- Original selected measurement-row counts. -/
  m : Fin r → ℕ
  /-- Literal integer entry bounds. -/
  W : Fin r → ℕ
  /-- Original variable partition. -/
  grouping : A ≃ ((g : Fin r) × Fin (h g))
  /-- Local factor owner. -/
  assigned : E → Fin r
  /-- Original integer measurements, without basis normalization. -/
  C : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ
  /-- Literal entry bounds. -/
  bounded : ∀ g j i, |C g j i| ≤ (W g : ℤ)
  /-- Actual off-group native row span. -/
  span : ∀ e i g, g ≠ assigned e → ∃ c : Fin (m g) → ℚ,
    ∀ v, rows e i (grouping.symm ⟨g,v⟩) = ∑ j, c j * (C g j v : ℚ)


/-- Certificate whose representatives execute integer equality tests and false-first search. -/
abbrev certificate {arity : E → ℕ} {rows : (e : E) → Fin (arity e) → A → ℚ}
    (d : Data arity rows) : NodeCertificate arity rows where
  Group := Fin d.r
  groupFinite := inferInstanceAs (Fintype (Fin d.r))
  groupDecEq := inferInstanceAs (DecidableEq (Fin d.r))
  Local := fun g => Fin (d.h g)
  localFinite := fun g => inferInstanceAs (Fintype (Fin (d.h g)))
  grouping := d.grouping
  assigned := d.assigned
  Index := fun g => Fin (d.m g)
  indexFinite := fun g => inferInstanceAs (Fintype (Fin (d.m g)))
  measureRows := fun g j i => (d.C g j i : ℚ)
  Summary := fun g => Summary (Fin (d.h g)) (Fin (d.m g)) (d.W g)
  summaryFinite := fun g => inferInstanceAs (Fintype (Summary (Fin (d.h g)) (Fin (d.m g)) (d.W g)))
  measurement := fun g => measurement (d.C g) (d.W g) (d.bounded g)
  readout := fun g => readout (d.W g)
  readout_eq := fun g x j => readout_measurement (d.C g) (d.W g) (d.bounded g) x j
  row_span := d.span
  representative := fun y g => summaryRepresentative (d.h g) (d.m g) (d.W g) (d.C g) (y g)
  representative_valid := fun y g hy =>
    summaryRepresentative_valid (d.h g) (d.m g) (d.W g) (d.C g) (d.bounded g) (y g) hy


/-- Native grouped rows with literal Fin local coordinates. -/
def localRows {arity : E → ℕ} {rows : (e : E) → Fin (arity e) → A → ℚ}
    (d : Data arity rows) (e : E) (i : Fin (arity e)) (g : Fin d.r) (v : Fin (d.h g)) : ℚ :=
  rows e i (d.grouping.symm ⟨g,v⟩)

/-- Actual forced-coordinate gate, in the original variable partition. -/
def forced {arity : E → ℕ} {rows : (e : E) → Fin (arity e) → A → ℚ}
    (d : Data arity rows) (S : Finset A) (g : Fin d.r) (i : Fin (d.h g)) : Bool :=
  decide (d.grouping.symm ⟨g,i⟩ ∈ S)

/-- The exact mathematical summand of the existing native fibre packet. -/
def term {arity : E → ℕ} {rows : (e : E) → Fin (arity e) → A → ℚ}
    (d : Data arity rows) (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (correction : (e : E) → Fin (arity e) → Polynomial ℚ) (S : Finset A)
    (y : (g : Fin d.r) → Summary (Fin (d.h g)) (Fin (d.m g)) (d.W g)) : Polynomial ℚ :=
  ∏ g, ∑ a : Fin (d.h g) → Bool,
    if (certificate d).measurement g a = y g ∧
        localForced arity rows (certificate d) S g a then
      groupValue arity T d.assigned (localRows d) correction g
        (Function.update ((certificate d).representative y) g a)
    else 0


omit [Fintype A] in
/-- Executed finite scans match one actual native fibre-packet summand.
Only the local callback specification is supplied; no full fibre value is assumed. -/
theorem fibreAt_native_spec {arity : E → ℕ} {rows : (e : E) → Fin (arity e) → A → ℚ}
    (d : Data arity rows) (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (correction : (e : E) → Fin (arity e) → Polynomial ℚ) (S : Finset A) (J : ℕ)
    (y : (g : Fin d.r) → Summary (Fin (d.h g)) (Fin (d.m g)) (d.W g))
    (value : (g : Fin d.r) → ((k : Fin d.r) → Fin (d.h k) → Bool) → Run)
    (hv : ∀ g x, Spec J (value g x)
      (groupValue arity T d.assigned (localRows d) correction g x)) :
    Spec J (fibreAt J d.r d.h d.m d.W d.C y (forced d S) value)
      (term d T correction S y) := by
  have hs := fibreAt_spec J d.r d.h d.m d.W d.C y (forced d S) value
    (fun g x => groupValue arity T d.assigned (localRows d) correction g x) hv
  have he (g : Fin d.r) (a : Fin (d.h g) → Bool) :
      (∀ j, (∑ i, if a i then d.C g j i else 0) =
        summaryTarget (d.h g) (d.m g) (d.W g) (y g) j) ↔
        (certificate d).measurement g a = y g := by
    exact (measurementTest_correct (d.h g) (d.m g) (d.C g) _ a).symm.trans
      (summaryTest_correct (d.h g) (d.m g) (d.W g) (d.C g) (d.bounded g) (y g) a)
  have hf (g : Fin d.r) (a : Fin (d.h g) → Bool) :
      (∀ i, forced d S g i = true → a i = true) ↔
        localForced arity rows (certificate d) S g a := by
    simp only [forced, decide_eq_true_eq, localForced]
  have hp : (∏ g, ∑ a : Fin (d.h g) → Bool,
      if (∀ j, (∑ i, if a i then d.C g j i else 0) =
          summaryTarget (d.h g) (d.m g) (d.W g) (y g) j) ∧
          (∀ i, forced d S g i = true → a i = true) then
        groupValue arity T d.assigned (localRows d) correction g
          (Function.update (fun k => summaryRepresentative (d.h k) (d.m k) (d.W k) (d.C k) (y k)) g a)
      else 0) = term d T correction S y := by
    unfold term
    apply Finset.prod_congr rfl
    intro g _
    apply Finset.sum_congr rfl
    intro a _
    simp only [he g a, hf g a]
  rw [hp] at hs
  exact hs



end RiemannGaussian.SemiprimeIndexedNodeCertificate
