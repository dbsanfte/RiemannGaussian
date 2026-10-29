/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildVertexEndpointBanks
/-! # Semantic whole169-word endpoint capacity for physical child cleanup
The stopped bytes are bounded by source words, acquired dimensions and native
Good-table storage. Neither a source runtime nor a subtree elapsed clock occurs.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildVertexEndpoint
open SemiprimeD1StackChildVertexChoice SemiprimeD1StackChildVertexChoiceSpec
open SemiprimeD1StackChildVertexChoiceView SemiprimeD1StackChildVertexEndpointBanks
open SemiprimeD1TensorTapeCodec (tape)
variable {d : ℕ}
/-- Pure source-resource/arity scale, independent of every elapsed operation. -/
def scale (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) : ℕ:=
  (resource old extra oldp newp parent order ports)^2*2^ports.length
/-- Source bytes and both actual native table byte counts fit the same semantic scale. -/
theorem semantic_caps (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order ports : List ℕ) :
    resource old extra oldp newp parent order ports ≤ scale old extra oldp newp parent order ports ∧
    1 ≤ scale old extra oldp newp parent order ports ∧
    (tape (SemiprimeD1StackChildLiftVertexOriginal.vertex old extra newp parent order ports).table).length ≤ 
      10*scale old extra oldp newp parent order ports ∧
    (SemiprimeD1StackChildUnitVertexFrames.tableWord (extra++old.axes) newp).length ≤ 
      10*scale old extra oldp newp parent order ports := by
  let r:=resource old extra oldp newp parent order ports
  let e:=2^ports.length
  have hb:=resource_bounds old extra oldp newp parent order ports
  have he1 : 1 ≤ e:=Nat.one_le_pow _ _ (by decide : 1 ≤ (2:ℕ))
  have hs : r^2 ≤ r^2*e:=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (r^2) he1
  have h1 : 1 ≤ r^2*e:=Nat.mul_le_mul (Nat.one_le_pow _ _ hb.1) he1
  have hr : r ≤ r^2*e:=(Nat.le_pow (by decide : 0<2)).trans hs
  have ha : (AB.resource old extra oldp newp parent order ports)^2*e ≤ r^2*e:=
    Nat.mul_le_mul_right e (Nat.pow_le_pow_left hb.2.1 2)
  have hu : (UB.resource (extra++old.axes) newp+1)^2 ≤ r^2*e:=
    (Nat.pow_le_pow_left hb.2.2 2).trans hs
  have hn:=SemiprimeD1StackChildTableEntryOriginal.appended_positive old.axes extra ho he
  refine ⟨hr,h1,?_,?_⟩
  · have ht:=SemiprimeD1StackChildLiftVertexBounds.table_bytes old extra he oldp newp parent hg order ports
    exact ht.trans (by simpa only [scale,r,e,Nat.mul_assoc] using Nat.mul_le_mul_left 10 ha)
  · exact (SemiprimeD1StackChildUnitVertexBounds.table_bytes (extra++old.axes) newp hn).trans
      (Nat.mul_le_mul_left 10 hu)
/-- Exact active constructor endpoint: retained134 words, table/port framing and no transient scratch. -/
theorem active_word_le (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order ports : List ℕ) (k : A.Stack) :
    ((AO.done old extra oldp newp parent order ports).data k).length ≤ 
      100*scale old extra oldp newp parent order ports := by
  have hc:=semantic_caps old ho extra he oldp newp parent hg order ports
  have hb:=resource_bounds old extra oldp newp parent order ports
  have har:AB.resource old extra oldp newp parent order ports ≤ scale old extra oldp newp parent order ports:=
    hb.2.1.trans hc.1
  have hp : (SemiprimeD1StackVertexReadExecution.portTape ports).length ≤ scale old extra oldp newp parent order ports:=
    (show (SemiprimeD1StackVertexReadExecution.portTape ports).length ≤ AB.resource old extra oldp newp parent order ports from Nat.le_add_left _ _).trans har
  rcases k with k|k
  · have h:=active_table_word_le old extra oldp newp parent order ports k
    change (SemiprimeD1StackChildLiftVertexOriginal.tableData old extra oldp newp parent order ports k).length ≤ _
    omega
  · cases k with
    | record=>
      change (SemiprimeD1StackVertexProduct.records [SemiprimeD1StackChildLiftVertexOriginal.vertex old extra newp parent order ports]).length ≤ _
      rw [record_length]
      change 2*(SemiprimeD1StackVertexReadExecution.portTape ports).length+
        2*(tape (SemiprimeD1StackChildLiftVertexOriginal.vertex old extra newp parent order ports).table).length+4 ≤ _
      omega
    | scratch=>exact Nat.zero_le _
/-- Exact inactive endpoint includes new context markers and both actual table/record copies, rather than elapsed cache-construction time. -/
theorem inactive_word_le (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order ports : List ℕ) (k : U.Stack) :
    ((UO.done (extra++old.axes) newp).data k).length ≤ 100*scale old extra oldp newp parent order ports := by
  have hc:=semantic_caps old ho extra he oldp newp parent hg order ports
  have hb:=resource_bounds old extra oldp newp parent order ports
  have hr : UB.resource (extra++old.axes) newp ≤ scale old extra oldp newp parent order ports:=by omega
  have h:=unit_word_le (extra++old.axes) newp k
  omega
/-- A complete physical bank counts empty private/shadow words as well as retained data words. -/
theorem bank_word_le (a : A.Stack→List Bool) (u : U.Stack→List Bool) (bits : List Bool) (cap : ℕ)
    (ha : ∀k,(a k).length ≤ cap) (hu : ∀k,(u k).length ≤ cap) (hb : bits.length ≤ cap) (k : Stack) :
    (bank a u bits k).length ≤ cap := by
  rcases k with k|k
  · exact ha k
  · rcases k with k|k
    · change (if shared k then [] else u k).length ≤ cap
      split
      · exact Nat.zero_le _
      · exact hu k
    · exact hb
/-- The proof-side exact overlay preserves the common cap on both source words and every foreign word. -/
theorem overlay_word_le (a : A.Stack→List Bool) (u : U.Stack→List Bool) (cap : ℕ)
    (ha : ∀k,(a k).length ≤ cap) (hu : ∀k,(u k).length ≤ cap) (k : Stack) :
    (inactiveResult a u k).length ≤ cap := by
  unfold inactiveResult
  split
  · exact hu _
  · exact bank_word_le a (fun _=>[]) [] cap ha (fun _=>Nat.zero_le _) (Nat.zero_le _) k
/-- Every one of the169 complete stopped words has a semantic endpoint cap in either actual branch. -/
theorem endpoint_word_le (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order ports : List ℕ) (bit : Bool) (k : Stack) :
    ((done old extra oldp newp parent order ports bit).data k).length ≤ 
      100*scale old extra oldp newp parent order ports := by
  cases bit
  · apply overlay_word_le _ _ _ _ (inactive_word_le old ho extra he oldp newp parent hg order ports) k
    intro role
    have h:=SemiprimeD1StackChildLiftVertexStorage.initial_length old extra oldp newp parent order ports role
    have hb:=resource_bounds old extra oldp newp parent order ports
    have hc:=semantic_caps old ho extra he oldp newp parent hg order ports
    omega
  · exact bank_word_le _ (fun _=>[]) [] _ (active_word_le old ho extra he oldp newp parent hg order ports)
      (fun _=>Nat.zero_le _) (Nat.zero_le _) k
/-- Total semantic endpoint capacity, sufficient for any physical cleanup subset excluding aliased headers. -/
def capacity (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) : ℕ:=
  10^6*scale old extra oldp newp parent order ports
/-- ALL169 stopped data words, including the actual record and every counted shadow, fit this semantic cap. -/
theorem endpoint_words_le (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order ports : List ℕ) (bit : Bool) :
    (∑k : Stack,((done old extra oldp newp parent order ports bit).data k).length) ≤ 
      capacity old extra oldp newp parent order ports := by
  have h:=SemiprimeD1StackChildLiftVertexStorage.finite_sum_bound _ _
    (endpoint_word_le old ho extra he oldp newp parent hg order ports bit)
  rw [stack_card] at h
  unfold capacity
  omega
end RiemannGaussian.SemiprimeD1StackChildVertexEndpoint
