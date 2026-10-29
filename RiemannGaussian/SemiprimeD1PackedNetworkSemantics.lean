/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootLocalAssignments
/-! # Natural coefficient semantics for the actual empty-axis network
This is proof-side semantics of the literal words. No contraction, owner value
or natural-number evaluator is added to the finite source. Full unreduced
natural coefficients remain available until the final root reduction.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
noncomputable section
namespace RiemannGaussian.SemiprimeD1PackedNetworkSemantics
open scoped BigOperators
open SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkLayout
open SemiprimeD1LeafCounter SemiprimeD1TensorTables
open SemiprimeD1RootScalar SemiprimeD1JetInterpretation
attribute [local instance] Classical.propDecidable
/-- Literal first coefficient of an empty-axis word, with the actual zero default. -/
def wordNat (words : List (List Bool)) : ℕ := SemiprimeBitArithmetic.bitValue ((words[0]?).getD [])
/-- Scalar decoding is a natural cast at EVERY precision, without modulo-four transport. -/
theorem scalar_wordNat (p : ℕ) (words : List (List Bool)) :
    scalar (interpret ⟨[],p⟩ words)=(wordNat words : ZMod (2^p)) := by
  rw [scalar_interpret]
  rfl
/-- Exact natural singleton-value information determines the actual decoded coefficient. -/
theorem wordNat_of_values (words : List (List Bool)) (n : ℕ)
    (h : words.map SemiprimeBitArithmetic.bitValue=[n]) : wordNat words=n := by
  cases words with
  | nil => cases h
  | cons w ws =>
    have he : SemiprimeBitArithmetic.bitValue w=n := (List.cons.inj h).1
    exact he
/-- Natural value of the actual local gather and literal tensor entry. -/
def entry {M : ℕ} (vertex : Vertex) (a : Fin M→Bool) : ℕ :=
  wordNat (valueAt vertex.table (localAssignment a vertex))
/-- Full unreduced natural contraction, used only as a semantic reference. -/
def naturalContraction (net : Network) : ℕ :=
  ∑a : Fin (edgeCount net)→Bool,((vertices net).map (fun vertex => entry vertex a)).prod
/-- The actual modular leaf scalar is the final reduction of the full natural contraction. -/
theorem leaf_scalar (p : ℕ) (net : Network) :
    scalar (interpret ⟨[],p⟩ (leaf ⟨[],p⟩ net).words)=
      (naturalContraction net : ZMod (2^p)) := by
  rw [leaf_value ⟨[],p⟩ (by simp)]
  simp only [map_sum,map_list_prod,List.map_map,Function.comp_def]
  unfold naturalContraction
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Nat.cast_list_prod,List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro vertex _
  exact scalar_wordNat p (valueAt vertex.table (localAssignment a vertex))
/-- Literal complete vector product, valid over natural coefficients as well as rings. -/
theorem vector_product {S : Type*} [CommMonoid S] {n : ℕ} (cache : Vector Vertex n) (read : Vertex→S) :
    (cache.toList.map read).prod=∏i : Fin n,read cache[i.val] := by
  have h:=congrArg (fun xs : List Vertex => (xs.map read).prod) (List.ofFn_getElem (xs:=cache.toList))
  simpa only [Vector.length_toList,Vector.getElem_toList,List.map_ofFn,Function.comp_def,List.prod_ofFn,Fin.val_cast] using h.symm
/-- The natural factor-side product retains all original ordered factor entries. -/
def rightValue (net : Network) (a : Fin (edgeCount net)→Bool) : ℕ :=
  (net.right.toList.map (fun vertex => entry vertex a)).prod
/-- Complete owner-fibre reads give the natural copy weight, including isolated owners. -/
theorem owner_entry (net : Network) (hw : WellFormed net) (fixed : List (Fin net.leftCount×Bool))
    (hentry : ∀v : Fin net.leftCount,∀bits : List Bool,bits.length=(leftPorts net.rows v).length→
      wordNat (lookup (net.left[v.val]).table bits).words=SemiprimeD1RootOwnerTables.weight fixed v bits)
    (a : Fin (edgeCount net)→Bool) (v : Fin net.leftCount) :
    entry (net.left[v.val]) a=SemiprimeD1RootCopyContraction.copyWeight
      (leftGroup net.rows) (fun v b => SemiprimeD1RootOwnerTables.allowed fixed v b=true) a v := by
  let vertex:=net.left[v.val]
  let bits:=vertex.ports.map (fun p => ((List.ofFn a)[p]?).getD false)
  have hp : vertex.ports=leftPorts net.rows v := hw.1 v
  have hb : bits.length=(leftPorts net.rows v).length := by
    dsimp only [bits]
    rw [List.length_map]
    exact congrArg List.length hp
  change wordNat (valueAt vertex.table (localAssignment a vertex))=_
  rw [SemiprimeD1RootLocalAssignments.valueAt_global_lookup]
  have h:=hentry v bits hb
  rw [h]
  change (SemiprimeD1RootOwnerTables.weight fixed v
    (vertex.ports.map (fun p => ((List.ofFn a)[p]?).getD false)) : ℕ)=_
  rw [hp]
  exact SemiprimeD1RootOwnerSemantics.weight_fibre (R:=ℕ) (leftGroup net.rows) fixed v _
    (leftPorts_lt _ _) (leftGroup_mem _ _) a
/-- Exact natural copy elimination retains every weighted right entry before ANY modular reduction.
The actual original-network instantiation must discharge the owner-entry premise from its real words. -/
theorem copy_elimination (net : Network) (hw : WellFormed net) (fixed : List (Fin net.leftCount×Bool))
    (hentry : ∀v : Fin net.leftCount,∀bits : List Bool,bits.length=(leftPorts net.rows v).length→
      wordNat (lookup (net.left[v.val]).table bits).words=SemiprimeD1RootOwnerTables.weight fixed v bits) :
    naturalContraction net=
      ∑bits : Fin net.leftCount→Bool,if ∀v,SemiprimeD1RootOwnerTables.allowed fixed v (bits v)=true then
        rightValue net (fun i => bits (leftGroup net.rows i)) else 0 := by
  have hleft (a : Fin (edgeCount net)→Bool) :
      (net.left.toList.map (fun vertex => entry vertex a)).prod=
        ∏v : Fin net.leftCount,SemiprimeD1RootCopyContraction.copyWeight
          (leftGroup net.rows) (fun v b => SemiprimeD1RootOwnerTables.allowed fixed v b=true) a v := by
    rw [vector_product]
    exact Finset.prod_congr rfl (fun v _ => owner_entry net hw fixed hentry a v)
  unfold naturalContraction
  simp only [vertices,List.map_append,List.prod_append]
  simp_rw [hleft]
  have h:=SemiprimeD1RootCopyContraction.contraction (R:=ℕ) (leftGroup net.rows)
    (fun v b => SemiprimeD1RootOwnerTables.allowed fixed v b=true) (rightValue net)
  conv_lhs => arg 2;ext a;rw [Nat.mul_comm]
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro bits _
  exact ite_cond_congr rfl
end RiemannGaussian.SemiprimeD1PackedNetworkSemantics
end
