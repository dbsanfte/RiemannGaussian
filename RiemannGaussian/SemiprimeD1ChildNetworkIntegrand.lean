/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildPacketEntrySemantics

/-! # Actual child assignment evaluation has original left/packet factors
The complete executed cache product is identified pointwise under the actual
computed child assignment. Parent values are literal individual lifts; packet
values are original physically acquired entries. No A/Q/L or local-value family
is supplied to the constructor or theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 140000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ChildNetworkIntegrand
open scoped BigOperators
open SemiprimeD1TensorNetwork
open SemiprimeD1JetAxes SemiprimeD1JetInterpretation
open SemiprimeD1ChildOldEntrySemantics SemiprimeD1ChildOldEntryAssignment
open SemiprimeD1ChildPacketEntrySemantics

/-- Actual executed product equals the product of actual executed local evaluations. -/
theorem assignment_product (ctx : Context) (hpos : ctx.Positive)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (bits : List Bool) :
    interpret ctx (SemiprimeD1LeafCounter.evaluateAssignment ctx vertices bits).words=
      (vertices.map (fun v => interpret ctx (SemiprimeD1LeafCounter.evaluateVertex v bits).words)).prod := by
  induction vertices with
  | nil => exact SemiprimeD1JetAffineCoefficient.interpret_one ctx hpos
  | cons v vs ih =>
    change interpret ctx (SemiprimeD1JetRingBits.mul ctx
      (SemiprimeD1LeafCounter.evaluateVertex v bits).words
      (SemiprimeD1LeafCounter.evaluateAssignment ctx vs bits).words).words=_
    rw [SemiprimeD1JetOperations.interpret_mul ctx _ _ hpos,ih]
    rfl

/-- Literal vector cache traversal has the finite product over its actual cached entries. -/
theorem vector_product {A R : Type*} [CommMonoid R] {K : ℕ} (xs : Vector A K) (f : A→R) :
    (xs.toList.map f).prod=∏i : Fin K,f xs[i.val] := by
  have h : xs.toList.map f=List.ofFn (fun i : Fin K => f xs[i.val]) := by
    apply List.ext_getElem
    · simp only [List.length_map,Vector.length_toList,List.length_ofFn]
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_ofFn,Vector.getElem_toList]
  rw [h,List.prod_ofFn]

/-- Both actual vertex caches occur once, including every zero-port tensor. -/
theorem network_product (ctx : Context) (hpos : ctx.Positive) (net : Network) (bits : List Bool) :
    interpret ctx (SemiprimeD1LeafCounter.evaluateAssignment ctx (vertices net) bits).words=
      (∏v : Fin net.leftCount,interpret ctx (SemiprimeD1LeafCounter.evaluateVertex net.left[v.val] bits).words)*
      ∏e : Fin net.rows.length,interpret ctx (SemiprimeD1LeafCounter.evaluateVertex net.right[e.val] bits).words := by
  rw [assignment_product ctx hpos (vertices net) bits]
  simp only [vertices,List.map_append,List.prod_append,vector_product]

/-- Actual emitted original-node child network, not an arbitrary network supplier. -/
abbrev child (net : Network) (old : Context) (extra : List ℕ) (p r a u : ℕ)
    (q : Fin a) (g : Fin r) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :=
  (SemiprimeD1ChildNetwork.acquire net old extra p r a u q.val q g z t beta).network

/-- Actual child row count is exactly the actual acquired original packet count. -/
theorem child_packet_count (net : Network) (old : Context) (extra : List ℕ) (p r a u : ℕ)
    (q : Fin a) (g : Fin r) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :
    (child net old extra p r a u q g z t beta).rows.length=(original net r a).state.packets.length :=
  packet_length net r a q g

/-- Pointwise integrand of the ACTUAL complete child cache evaluation under the
computed GLOBAL assignment. No table/gather/mask/row/source-value answers occur. -/
theorem evaluate_child (net : Network) (hw : WellFormed net) (old : Context) (extra : List ℕ)
    (p r a u : ℕ) [NeZero r] (q : Fin a) (g : Fin r) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (bits : Incidence net.rows×Bool→Bool) (hpos : (⟨extra++old.axes,p⟩ : Context).Positive) :
    interpret ⟨extra++old.axes,p⟩
      (SemiprimeD1LeafCounter.evaluateAssignment ⟨extra++old.axes,p⟩
        (vertices (child net old extra p r a u q g z t beta))
        (List.ofFn (networkAssignment net r a q g bits))).words=
      (∏v : Fin (net.leftCount+net.rows.length),
        if vertexColour net r a q v=g then
          interpret ⟨extra++old.axes,p⟩ (SemiprimeD1ChildTableCopy.lift old extra p
            (SemiprimeD1TensorTables.valueAt (SemiprimeD1ChildNetwork.parentVertex net v).table
              (parentBits net hw bits v))).words else 1)*
      ∏f : Fin (original net r a).state.packets.length,
        packetTerm net r a u old.precision q g ⟨extra++old.axes,p⟩ z t beta bits f := by
  classical
  rw [network_product _ hpos]
  apply congrArg₂ (·*·)
  · apply Finset.prod_congr rfl
    intro v hv
    rw [evaluate_acquire_left net hw old extra p r a u q.val q g z t beta bits v]
    split_ifs <;> simp only [unitWords_interpret ⟨extra++old.axes,p⟩ hpos]
  · let e : Fin (original net r a).state.packets.length ≃
        Fin (child net old extra p r a u q g z t beta).rows.length :=
      finCongr (child_packet_count net old extra p r a u q g z t beta).symm
    symm
    apply Fintype.prod_equiv e
    intro f
    exact (evaluate_acquire_right net old extra p r a u q g z t beta bits f).symm
end RiemannGaussian.SemiprimeD1ChildNetworkIntegrand
