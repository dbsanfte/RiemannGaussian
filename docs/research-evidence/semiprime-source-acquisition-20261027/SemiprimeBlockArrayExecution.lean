/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePacketArrayExecution
import RiemannGaussian.SemiprimeFiniteEnumerations

/-!
# Computed complete-block rows and original-variable coefficient arrays

Executable packing lookup replaces the mathematical extension by zero. All
polynomial rows occur only in specifications; runtime callbacks return arrays.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeBlockArrayExecution
open scoped BigOperators
open Polynomial SemiprimeFibreArrayExecution SemiprimePacketArrayExecution
open OAI.Algorithms.SubexponentialSAT
open Subexp.ConstructivePacking SqrtLog

variable {I U : Type} [DecidableEq I] [DecidableEq U]

/-- Look up both incidence addresses; rows outside their common block are zero.
An uncovered input incidence retains its literal identity row. -/
def assembled (P : PackingData I U) (J : ℕ) (universal : U → U → Run) (i v : I) : Run :=
  match P.lookup i with
  | none => if v=i then oneRun J else zeroRun J
  | some z =>
      match P.lookup v with
      | none => zeroRun J
      | some y => if y.1=z.1 then universal z.2 y.2 else zeroRun J

/-- Exact block assembly from the actual computed inverse lookup. -/
theorem assembled_spec [Fintype U] (P : PackingData I U) (J : ℕ)
    (universal : U → U → Run) (rows : U → U → Polynomial ℚ)
    (hrows : ∀ u v, Spec J (universal u v) (rows u v)) (i v : I) :
    Spec J (assembled P J universal i v) (LayoutBlocks.assembledRow P.completeBlocks rows i v) := by
  classical
  cases hi : P.lookup i with
  | none =>
    rw [LayoutBlocks.assembledRow_outside P.completeBlocks rows i ((P.lookup_none_iff i).mp hi)]
    simp only [assembled,hi]
    by_cases hv : v=i
    · simp only [ite_eq_left hv, C_1]
      exact oneRun_spec J
    · simp only [ite_eq_right hv, C_0]
      exact zeroRun_spec J
  | some z =>
    have hiz := (P.lookup_some_iff i z).mp hi
    have hirow : LayoutBlocks.assembledRow P.completeBlocks rows i =
        LayoutPullback.row (P.completeBlocks.blockEmbedding z.1) (rows z.2) := by
      rw [← hiz, LayoutBlocks.assembledRow_apply]
    rw [hirow]
    simp only [assembled,hi]
    cases hv : P.lookup v with
    | none =>
      dsimp only
      have hout : v ∉ Set.range (P.completeBlocks.blockEmbedding z.1) := by
        rintro ⟨u,hu⟩
        exact ((P.lookup_none_iff v).mp hv) ⟨(z.1,u),hu⟩
      rw [LayoutPullback.row_eq_zero _ _ _ hout]
      exact zeroRun_spec J
    | some y =>
      dsimp only
      have hvy := (P.lookup_some_iff v y).mp hv
      by_cases hblock : y.1=z.1
      · rw [ite_eq_left hblock]
        have hvrow : LayoutPullback.row (P.completeBlocks.blockEmbedding z.1) (rows z.2) v =
            rows z.2 y.2 := by
          rw [← hvy]
          have he : P.completeBlocks.embed y = P.completeBlocks.blockEmbedding z.1 y.2 := by
            change P.completeBlocks.embed y = P.completeBlocks.embed (z.1,y.2)
            congr 1
            exact Prod.ext hblock rfl
          rw [he]
          exact LayoutPullback.row_apply_injective _ (P.completeBlocks.blockEmbedding z.1).injective _ _
        rw [hvrow]
        exact hrows z.2 y.2
      · rw [ite_eq_right hblock]
        have hout : v ∉ Set.range (P.completeBlocks.blockEmbedding z.1) := by
          rintro ⟨u,hu⟩
          have he := P.completeBlocks.embed.injective (hvy.trans hu.symm)
          have hh : y.1=(z.1,u).1 := congrArg Prod.fst he
          exact hblock hh
        rw [LayoutPullback.row_eq_zero _ _ _ hout]
        exact zeroRun_spec J

/-- Lookup/finite-index work is paid separately; the returned array report
retains every universal-row callback actually invoked. -/
theorem assembled_work (P : PackingData I U) (J B : ℕ) (universal : U → U → Run)
    (hrows : ∀ u v, (universal u v).work ≤ B) (i v : I) :
    (assembled P J universal i v).work ≤ B+J+1 := by
  unfold assembled
  split
  · split <;> simp only [oneRun,zeroRun,Run.work,SemiprimeArrayOps.oneJet,SemiprimeArrayOps.zeroJet]
    all_goals omega
  · split
    · simp only [zeroRun,Run.work,SemiprimeArrayOps.zeroJet]
      omega
    · split
      · exact (hrows _ _).trans (by omega)
      · simp only [zeroRun,Run.work,SemiprimeArrayOps.zeroJet]
        omega

/-- Pull back to one original variable by the explicit incidence enumeration. -/
def pullback {n : ℕ} (en : FiniteEnumeration I) (owner : I → Fin n) (J : ℕ)
    (copy : I → Run) (v : Fin n) : Run :=
  sumCodes J en.values.length (fun k =>
    let i := en.equivFin k
    if owner i=v then copy i else zeroRun J)

/-- The computed finite sum is exactly the source's original-coordinate row. -/
theorem pullback_spec {n : ℕ} [Fintype I]
    (en : FiniteEnumeration I) (owner : I → Fin n) (J : ℕ)
    (copy : I → Run) (rows : I → Polynomial ℚ)
    (hrows : ∀ i, Spec J (copy i) (rows i)) (v : Fin n) :
    Spec J (pullback en owner J copy v) (LayoutPullback.row owner rows v) := by
  classical
  unfold LayoutPullback.row
  rw [← en.equivFin.sum_comp]
  apply sumCodes_spec
  intro k
  by_cases h : owner (en.equivFin k)=v
  · simp only [ite_eq_left h]
    exact hrows _
  · simp only [ite_eq_right h]
    exact zeroRun_spec J

theorem pullback_work {n : ℕ} (en : FiniteEnumeration I) (owner : I → Fin n) (J B : ℕ)
    (copy : I → Run) (hrows : ∀ i, (copy i).work ≤ B) (v : Fin n) :
    (pullback en owner J copy v).work ≤ (J+1)+en.values.length*(B+J+1+(4*J+1)) := by
  apply sumCodes_work
  intro k
  by_cases h : owner (en.equivFin k)=v
  · simp only [ite_eq_left h]
    exact (hrows _).trans (by omega)
  · simp only [ite_eq_right h,zeroRun,Run.work,SemiprimeArrayOps.zeroJet]
    omega

/-- Coefficients of one full source row from complete blocks and leftovers. -/
def sourceRow {n : ℕ} (P : PackingData I U) (owner : I → Fin n) (J : ℕ)
    (universal : U → U → Run) (i : I) (v : Fin n) : Run :=
  pullback P.vertices owner J (assembled P J universal i) v

theorem sourceRow_spec {n : ℕ} [Fintype I] [Fintype U]
    (P : PackingData I U) (owner : I → Fin n) (J : ℕ)
    (universal : U → U → Run) (rows : U → U → Polynomial ℚ)
    (hrows : ∀ u v, Spec J (universal u v) (rows u v)) (i : I) (v : Fin n) :
    Spec J (sourceRow P owner J universal i v)
      (LayoutPullback.row owner (LayoutBlocks.assembledRow P.completeBlocks rows i) v) :=
  pullback_spec P.vertices owner J _ _ (fun j => assembled_spec P J universal rows hrows i j) v

theorem sourceRow_work {n : ℕ} (P : PackingData I U) (owner : I → Fin n) (J B : ℕ)
    (universal : U → U → Run) (hrows : ∀ u v, (universal u v).work ≤ B) (i : I) (v : Fin n) :
    (sourceRow P owner J universal i v).work ≤
      (J+1)+P.vertices.values.length*(B+2*(J+1)+(4*J+1)) := by
  have h := pullback_work P.vertices owner J (B+J+1) (assembled P J universal i)
    (fun j => assembled_work P J B universal hrows i j) v
  exact h.trans_eq (by ring)

end RiemannGaussian.SemiprimeBlockArrayExecution
