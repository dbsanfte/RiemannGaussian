/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1LeafCounterBounds

/-! # Closed eager leaf polynomial and retained literal storage
Input table storage is explicitly separated from newly allocated global storage.
When original scopes have at mostM ports, the entire retained encoding has the
same polynomial times2^M scale. Native index cells are not claimed to be a tape
address-bit representation.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1LeafCounterResources
open SemiprimeD1LeafCounter SemiprimeD1LeafCounterBounds SemiprimeD1JetAxes

/-- Literal fixed polynomial cofactor of the complete eager report. -/
def polynomialEnvelope (M axes N p V L : ℕ) : ℕ :=
  (9*p+3*N+8)+L*(3*M+9)+V*(N*(3*p+4)+1+
    SemiprimeD1JetRingBounds.mulBudget axes N p p+8)+
      (N*(3*p+4)+1)+(N*(6*N+11*p+9*p+17)+10*N+5)+13

/-- The actual report budget is EXACTLY this fixed polynomial times2^M. -/
theorem budget_eq (M : ℕ) (ctx : Context) (vertices : List Vertex) :
    budget M ctx vertices=
      polynomialEnvelope M ctx.axes.length ctx.rank ctx.precision vertices.length (scopeSize vertices)*2^M := rfl

/-- Pure numerical monotonicity, without semantic execution expressions in context. -/
theorem polynomialEnvelope_mono {M axes N p V L A B C D E F : ℕ}
    (hM : M ≤ A) (ha : axes ≤ B) (hN : N ≤ C) (hp : p ≤ D) (hV : V ≤ E) (hL : L ≤ F) :
    polynomialEnvelope M axes N p V L ≤ polynomialEnvelope A B C D E F := by
  unfold polynomialEnvelope SemiprimeD1JetRingBounds.mulBudget
    SemiprimeD1JetRingBounds.mulAtBudget SemiprimeD1JetRingBounds.termBudget
  gcongr

/-- An explicit fixed monomial controls every polynomial cofactor, not a cost oracle. -/
theorem polynomialEnvelope_diagonal (S : ℕ) :
    polynomialEnvelope S S S S S S ≤ 100000*(S+1)^8 := by
  unfold polynomialEnvelope SemiprimeD1JetRingBounds.mulBudget
    SemiprimeD1JetRingBounds.mulAtBudget SemiprimeD1JetRingBounds.termBudget
  nlinarith [Nat.zero_le (S^2),Nat.zero_le (S^3),Nat.zero_le (S^4),Nat.zero_le (S^5),
    Nat.zero_le (S^6),Nat.zero_le (S^7),Nat.zero_le (S^8)]

/-- ORIGINAL literal data caps give a concrete fixed-polynomial eager counter report. -/
theorem run_clock_polynomial (M : ℕ) (ctx : Context) (vertices : List Vertex)
    (hg : Good ctx vertices) (S : ℕ) (hM : M ≤ S) (ha : ctx.axes.length ≤ S)
    (hN : ctx.rank ≤ S) (hp : ctx.precision ≤ S) (hV : vertices.length ≤ S) (hL : scopeSize vertices ≤ S) :
    (run M ctx vertices).clock ≤ 100000*(S+1)^8*2^M := by
  have h:=run_clock M ctx vertices hg
  rw [budget_eq] at h
  exact h.trans (Nat.mul_le_mul_right _
    ((polynomialEnvelope_mono hM ha hN hp hV hL).trans (polynomialEnvelope_diagonal S)))

/-- Literal held-input inventory: native port cells, table encoding and record tags. -/
def inputStorage : List Vertex → ℕ
  | [] => 0
  | v::vs => v.ports.length+SemiprimeD1TensorTables.storage v.table+1+inputStorage vs

/-- Complete input-table storage is paid, rather than silently assumed cheap. -/
theorem inputStorage_bound (M : ℕ) (ctx : Context) (vertices : List Vertex)
    (hg : Good ctx vertices) (hs : ∀v∈vertices,v.ports.length ≤ M) :
    inputStorage vertices ≤ scopeSize vertices+
      vertices.length*((ctx.rank*(3*ctx.precision+4)+3)*2^M) := by
  induction vertices with
  | nil => simp [inputStorage,scopeSize]
  | cons v vs ih =>
    have ht:=SemiprimeD1TensorTables.storage_bound ctx v.table (hg v List.mem_cons_self)
    have hp:=Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (hs v List.mem_cons_self)
    have hv:=ht.trans (Nat.mul_le_mul_left _ hp)
    have hi:=ih (fun w hw => hg w (List.mem_cons_of_mem v hw))
      (fun w hw => hs w (List.mem_cons_of_mem v hw))
    simp only [inputStorage,scopeSize,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul] at *
    omega

/-- Held original tables, entire global table and final coefficient-vector encoding. -/
def retainedStorage (M : ℕ) (ctx : Context) (vertices : List Vertex) : ℕ :=
  inputStorage vertices+SemiprimeD1TensorTables.storage (run M ctx vertices).table+
    (copyVector (run M ctx vertices).words).2+2

/-- Actual retained literal data have the same eager exponential scale. This is an
encoding inventory; it does not assert a full heap/tape scratch-space simulation. -/
theorem retainedStorage_bound (M : ℕ) (ctx : Context) (vertices : List Vertex)
    (hg : Good ctx vertices) (hs : ∀v∈vertices,v.ports.length ≤ M) :
    retainedStorage M ctx vertices ≤ scopeSize vertices+
      (vertices.length+2)*((ctx.rank*(3*ctx.precision+4)+3)*2^M) := by
  have hi:=inputStorage_bound M ctx vertices hg hs
  have ht:=run_table_storage M ctx vertices
  have ho:=copyVector_clock_le (run M ctx vertices).words ctx.precision
    (fun w hw => ((run_good M ctx vertices).2 w hw).2)
  rw [(run_good M ctx vertices).1] at ho
  have hp : 1 ≤ 2^M := Nat.one_le_two_pow
  have hpaid : ctx.rank*(3*ctx.precision+4)+3 ≤ (ctx.rank*(3*ctx.precision+4)+3)*2^M :=
    Nat.le_mul_of_pos_right _ hp
  dsimp [retainedStorage]
  rw [Nat.add_mul]
  nlinarith

/-- Standard actual scope distinctness and original port bounds derive the needed
scope-size guard; it is not a table-storage answer premise. -/
theorem scope_length_of_nodup (M : ℕ) (v : Vertex) (hbound : ∀p∈v.ports,p < M)
    (hnd : v.ports.Nodup) : v.ports.length ≤ M := by
  have hsub : v.ports.toFinset⊆Finset.range M := by
    intro p hp
    exact Finset.mem_range.mpr (hbound p (List.mem_toFinset.mp hp))
  have h:=Finset.card_le_card hsub
  simpa only [List.toFinset_card_of_nodup hnd,Finset.card_range] using h

/-- On actual well-formed ports the physical default is never used: local data
are precisely the original bounded global assignment coordinates. -/
theorem localAssignment_bounded {M : ℕ} (bits : Fin M→Bool) (v : Vertex)
    (hbound : ∀p∈v.ports,p < M) (j : Fin v.ports.length) :
    localAssignment bits v j=bits ⟨v.ports[j.val],hbound _ (List.getElem_mem j.isLt)⟩ := by
  have hp:=hbound _ (List.getElem_mem j.isLt)
  simp [localAssignment,hp]

/-- Original finite-scope well-formedness discharges the complete retained-input
storage guard directly from actual port lists and their distinctness. -/
theorem retainedStorage_of_wellFormed (M : ℕ) (ctx : Context) (vertices : List Vertex)
    (hg : Good ctx vertices) (hw : WellFormed M vertices)
    (hn : ∀v∈vertices,v.ports.Nodup) :
    retainedStorage M ctx vertices ≤ scopeSize vertices+
      (vertices.length+2)*((ctx.rank*(3*ctx.precision+4)+3)*2^M) := by
  exact retainedStorage_bound M ctx vertices hg (fun v hv =>
    scope_length_of_nodup M v (hw v hv) (hn v hv))

end RiemannGaussian.SemiprimeD1LeafCounterResources
