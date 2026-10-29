/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildNetworkIntegrand
import RiemannGaussian.SemiprimeD1OriginalDoubleAssignments

/-! # Original double sums equal products of actual child contractions
Only computed original assignment bijections and literal child-scope equalities
are used. The right side is the executed eager leaf contraction of each actual
cached child; no assignment inverse, contraction or solver answer is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 120000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ChildContractionSum
open scoped BigOperators
open SemiprimeD1TensorNetwork
open SemiprimeD1JetAxes SemiprimeD1JetInterpretation
open SemiprimeD1ChildOldEntrySemantics SemiprimeD1ChildOldEntryAssignment
open SemiprimeD1ChildNetworkIntegrand

/-- The ACTUAL emitted child variable count is the acquired physical endpoint scope. -/
theorem child_scope (net : Network) (old : Context) (extra : List ℕ) (p r a u : ℕ)
    (q : Fin a) (g : Fin r) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :
    edgeCount (child net old extra p r a u q g z t beta)=
      SemiprimeD1ChildAssignmentEquiv.scope net.leftCount net.rows.length r a
        (arity net.rows) (owner net.rows) q g := by
  change scope (SemiprimeD1ChildOldEntryAssignment.rows net r a q g)=
    (data net r a q g).graph.factors.flatten.length
  exact SemiprimeD1TensorNetworkLayout.child_scope (data net r a q g).graph

/-- Exact finite-coordinate assignment transport, with its literal inverse. -/
def castBits {M N : ℕ} (h : M=N) : (Fin N→Bool) ≃ (Fin M→Bool) where
  toFun bits j := bits ((finCongr h) j)
  invFun bits j := bits ((finCongr h).symm j)
  left_inv bits := by
    funext j
    exact congrArg bits ((finCongr h).apply_symm_apply j)
  right_inv bits := by
    funext j
    exact congrArg bits ((finCongr h).symm_apply_apply j)

/-- Literal coordinate-identity assignment cast, from the ACTUAL derived child scopes. -/
def assignmentCast (net : Network) (old : Context) (extra : List ℕ) (p r a u : ℕ)
    (q : Fin a) (g : Fin r) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :
    (Fin (SemiprimeD1ChildAssignmentEquiv.scope net.leftCount net.rows.length r a
      (arity net.rows) (owner net.rows) q g)→Bool) ≃
    (Fin (edgeCount (child net old extra p r a u q g z t beta))→Bool) :=
  castBits (child_scope net old extra p r a u q g z t beta)

/-- The coordinate cast is EXACTLY the canonical networkAssignment already used by the executed integrand. -/
theorem assignmentCast_value (net : Network) (old : Context) (extra : List ℕ) (p r a u : ℕ)
    [NeZero r] (q : Fin a) (g : Fin r) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (bits : Incidence net.rows×Bool→Bool) :
    assignmentCast net old extra p r a u q g z t beta
      (SemiprimeD1ChildAssignmentEquiv.assignments net.leftCount net.rows.length r a
        (arity net.rows) (owner net.rows) q bits g)=networkAssignment net r a q g bits := rfl

/-- The actual leaf contraction is the sum of its actual executed assignment products. -/
theorem leaf_sum_evaluations (ctx : Context) (hpos : ctx.Positive) (net : Network) :
    interpret ctx (leaf ctx net).words=
      ∑bits : Fin (edgeCount net)→Bool,
        interpret ctx (SemiprimeD1LeafCounter.evaluateAssignment ctx (vertices net) (List.ofFn bits)).words := by
  rw [leaf_value ctx hpos net]
  apply Finset.sum_congr rfl
  intro bits _
  exact (SemiprimeD1LeafCounter.evaluateAssignment_value ctx hpos (vertices net) bits).symm

/-- Exact original X/Y double sum of actual cached child assignment products equals
independent ACTUAL child contractions. No supplied inverse, count or projection is used. -/
theorem sum_child_contractions (net : Network) (old : Context) (extra : List ℕ)
    (p r a u : ℕ) [NeZero r] (q : Fin a) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (hpos : (⟨extra++old.axes,p⟩ : Context).Positive) :
    (∑X : SemiprimeD1OriginalDoubleAssignments.Bits net.leftCount net.rows.length r a
        (arity net.rows) (owner net.rows),
      ∑Y : SemiprimeD1OriginalDoubleAssignments.Bits net.leftCount net.rows.length r a
        (arity net.rows) (owner net.rows),
        ∏g : Fin r,interpret ⟨extra++old.axes,p⟩
          (SemiprimeD1LeafCounter.evaluateAssignment ⟨extra++old.axes,p⟩
            (vertices (child net old extra p r a u q g z t beta))
            (List.ofFn (networkAssignment net r a q g
              (SemiprimeD1PacketAssignmentRows.tagBits net.leftCount net.rows.length r a
                (arity net.rows) (owner net.rows) X Y)))).words)=
      ∏g : Fin r,interpret ⟨extra++old.axes,p⟩
        (leaf ⟨extra++old.axes,p⟩ (child net old extra p r a u q g z t beta)).words := by
  classical
  have h:=SemiprimeD1OriginalDoubleAssignments.sum_child_products net.leftCount net.rows.length r a
    (arity net.rows) (owner net.rows) q
    (fun g bits => interpret ⟨extra++old.axes,p⟩
      (SemiprimeD1LeafCounter.evaluateAssignment ⟨extra++old.axes,p⟩
        (vertices (child net old extra p r a u q g z t beta))
        (List.ofFn (assignmentCast net old extra p r a u q g z t beta bits))).words)
  calc
    _=∏g : Fin r,∑bits : Fin (SemiprimeD1ChildAssignmentEquiv.scope net.leftCount net.rows.length r a
        (arity net.rows) (owner net.rows) q g)→Bool,
      interpret ⟨extra++old.axes,p⟩
        (SemiprimeD1LeafCounter.evaluateAssignment ⟨extra++old.axes,p⟩
          (vertices (child net old extra p r a u q g z t beta))
          (List.ofFn (assignmentCast net old extra p r a u q g z t beta bits))).words := by
      convert h using 1
      apply Finset.sum_congr (by ext; simp)
      intro X _
      apply Finset.sum_congr (by ext; simp)
      intro Y _
      apply Finset.prod_congr (by ext; simp)
      intro g _
      rw [assignmentCast_value]
      rfl
    _=_ := by
      apply Finset.prod_congr rfl
      intro g _
      exact ((assignmentCast net old extra p r a u q g z t beta).sum_comp
        (fun bits => interpret ⟨extra++old.axes,p⟩
          (SemiprimeD1LeafCounter.evaluateAssignment ⟨extra++old.axes,p⟩
            (vertices (child net old extra p r a u q g z t beta)) (List.ofFn bits)).words)).trans
        (leaf_sum_evaluations ⟨extra++old.axes,p⟩ hpos (child net old extra p r a u q g z t beta)).symm
end RiemannGaussian.SemiprimeD1ChildContractionSum
