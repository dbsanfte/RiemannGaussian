/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1NetworkOwnerBits
import RiemannGaussian.SemiprimeD1OriginalStateResources

/-! # Original reachable-state bounds for physical owner reads
Every cache dimension and address acquisition bound follows from the real
original-root reachable state. This remains a displayed-report theorem, with
native setup digit extraction and full heap/tape lowering explicitly separate.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1NetworkOwnerOriginal
open SemiprimeD1NetworkOwnerBits SemiprimeD1TensorNetwork
open SemiprimeD1NetworkStateResources SemiprimeD1RecursiveCallTree
open SemiprimeD1OriginalStateResources

/-- Actual reachable-state dimensions discharge all physical lookup caps. -/
theorem bound_reports (s : ℕ) (call : Call) (hb : Bound s call)
    (i : Incidence call.net.rows) :
    (acquire call.net.rows).clock ≤ 5*s*(SemiprimeSourceHistogramPortKeys.encodeBudget (5*s)+4)+5*(5*s)+1 ∧
    (query (acquire call.net.rows) i.1.val i.2.val).clock ≤ queryBudget (5*s) := by
  have hn : call.net.leftCount ≤ 5*s := by
    have h:=hb.vertex_count
    unfold vertexCount at h
    omega
  have hF : call.net.rows.length ≤ 5*s := by
    have h:=hb.vertex_count
    unfold vertexCount at h
    omega
  have hM : call.net.rows.flatten.length ≤ 5*s := by
    rw [rows_flatten_length]
    have h:=hb.edge_count
    change scope call.net.rows ≤ s at h
    omega
  exact ⟨acquire_clock_uniform call.net.rows (5*s) hn hF hM,
    query_clock call.net.rows i (5*s) hn hF hM⟩

/-- Original N/prefix/reach endpoint: no caller-supplied state size or owner answer. -/
theorem eventually_original_reports : ∀ᶠ ell : ℕ in Filter.atTop,
    ∀ (N : ℕ) (hN : 0<N), SemiprimeMacroParameters.bitLength N=ell →
      ∀ (fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount N)×Bool)) (next : Call),
      Reach (SemiprimeD1PublicPackingReady.scale ell) (originalCall N hN fixed) next →
      ∀ i : Incidence next.net.rows,
      (query (acquire next.net.rows) i.1.val i.2.val).clock ≤
        queryBudget (5*SemiprimeD1PublicPackingReady.scale ell) := by
  filter_upwards [SemiprimeD1OriginalStateResources.eventually_original] with ell hell
  intro N hN hEll fixed next hr i
  exact (bound_reports _ next (hell N hN hEll fixed next hr) i).2

/-- Original reachable states pay the entire closed serialization-and-read path. -/
theorem bound_complete (s : ℕ) (call : Call) (hb : Bound s call)
    (i : Incidence call.net.rows) :
    (fromRows call.net.rows i.1.val i.2.val).clock ≤
      5*s*(SemiprimeSourceHistogramPortKeys.encodeBudget (5*s)+4)+5*(5*s)+1+
        queryBudget (5*s)+3 := by
  have h:=bound_reports s call hb i
  unfold fromRows
  dsimp only
  omega

/-- The closed actual N/prefix/reach path includes setup, not an advised bank. -/
theorem eventually_original_complete : ∀ᶠ ell : ℕ in Filter.atTop,
    ∀ (N : ℕ) (hN : 0<N), SemiprimeMacroParameters.bitLength N=ell →
      ∀ (fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount N)×Bool)) (next : Call),
      Reach (SemiprimeD1PublicPackingReady.scale ell) (originalCall N hN fixed) next →
      ∀ i : Incidence next.net.rows,
      (fromRows next.net.rows i.1.val i.2.val).clock ≤
        5*SemiprimeD1PublicPackingReady.scale ell*
          (SemiprimeSourceHistogramPortKeys.encodeBudget (5*SemiprimeD1PublicPackingReady.scale ell)+4)+
          5*(5*SemiprimeD1PublicPackingReady.scale ell)+1+
          queryBudget (5*SemiprimeD1PublicPackingReady.scale ell)+3 := by
  filter_upwards [SemiprimeD1OriginalStateResources.eventually_original] with ell hell
  intro N hN hEll fixed next hr i
  exact bound_complete _ next (hell N hN hEll fixed next hr) i

end RiemannGaussian.SemiprimeD1NetworkOwnerOriginal
