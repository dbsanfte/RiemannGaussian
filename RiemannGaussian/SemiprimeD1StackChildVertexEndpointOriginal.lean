/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildVertexEndpoint
/-! # Actual original child-source endpoints and semantic cleanup subsets
The endpoint bound concerns the complete stopped bank of the SAME acquired
source. Actual parent-stream parsing and physical cleanup stay caller code.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildVertexEndpointOriginal
open SemiprimeD1StackChildVertexChoice SemiprimeD1StackChildVertexChoiceSpec
open SemiprimeD1StackChildVertexChoiceOriginal SemiprimeD1StackChildVertexEndpoint
open SemiprimeD1TensorNetwork (Network)
open SemiprimeD1ChildOldEntrySemantics (data order)
/-- Any literal physical cleanup subset, including or excluding the retained header aliases, has this semantic byte cap. -/
theorem cleanup_subset_le {d : ℕ} (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (permutation scope : List ℕ) (bit : Bool) (roles : Finset Stack) :
    (∑k∈roles,((done old extra oldp newp parent permutation scope bit).data k).length) ≤
      capacity old extra oldp newp parent permutation scope := by
  have hcard : roles.card ≤ 169 := by
    have h:=Finset.card_le_univ (s:=roles)
    rw [stack_card] at h
    exact h
  have h := Finset.sum_le_sum (s:=roles)
    (fun k _=>endpoint_word_le old ho extra he oldp newp parent hg permutation scope bit k)
  have hs : (∑_k∈roles,100*scale old extra oldp newp parent permutation scope)=
      roles.card*(100*scale old extra oldp newp parent permutation scope) := by
    simp only [Finset.sum_const,smul_eq_mul]
  rw [hs] at h
  have hm:=Nat.mul_le_mul_right (100*scale old extra oldp newp parent permutation scope) hcard
  unfold capacity
  omega
/-- One EOF pop per real cleanup role adds at most169 to the actual semantic byte scan. -/
theorem cleanup_subset_steps {d : ℕ} (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (permutation scope : List ℕ) (bit : Bool) (roles : Finset Stack) :
    (∑k∈roles,((done old extra oldp newp parent permutation scope bit).data k).length)+roles.card ≤
      capacity old extra oldp newp parent permutation scope+169 := by
  have hb:=cleanup_subset_le old ho extra he oldp newp parent hg permutation scope bit roles
  have hcard : roles.card ≤ 169 := by
    have h:=Finset.card_le_univ (s:=roles)
    rw [stack_card] at h
    exact h
  omega
/-- Complete actual original169 endpoint, using native acquired scope/order and parent Good internally. -/
theorem acquired_words_le (net : Network) (r a : ℕ) (q : Fin a) (g : Fin r)
    (old : SemiprimeD1JetAxes.Context) (ho : old.Positive) (extra : List ℕ) (he : 0<extra.prod)
    (oldp newp : List Bool) (hg : SemiprimeD1TensorNetwork.Good old net)
    (v : Fin (net.leftCount+net.rows.length)) :
    (∑k : Stack,((acquiredDone net r a q g old extra oldp newp v).data k).length) ≤
      capacity old extra oldp newp (SemiprimeD1ChildNetwork.parentVertex net v).table
        (order net r a q g v).order (ports net r a q g v) :=
  endpoint_words_le old ho extra he oldp newp (SemiprimeD1ChildNetwork.parentVertex net v).table
    (SemiprimeD1ChildNetwork.parentVertex_good old net hg v)
    (order net r a q g v).order (ports net r a q g v) (activityBit net r a q g v)
/-- SAME actual whole source/native record together with the independent semantic cleanup endpoint cap. -/
theorem source_run_actual_endpoint (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (old : SemiprimeD1JetAxes.Context) (ho : old.Positive) (extra : List ℕ) (he : 0<extra.prod)
    (oldp newp : List Bool) (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (hg : SemiprimeD1TensorNetwork.Good old net) (v : Fin (net.leftCount+net.rows.length)) :
    ∃t ≤ SemiprimeD1StackChildVertexChoiceBounds.polynomial old extra oldp newp
      (SemiprimeD1ChildNetwork.parentVertex net v).table (order net r a q g v).order (ports net r a q g v),
      SemiprimeD1StackCalls.run program t (acquiredSource net r a q g old extra oldp newp v)=
        some (acquiredDone net r a q g old extra oldp newp v) ∧
      (acquiredDone net r a q g old extra oldp newp v).data output=
        SemiprimeD1StackVertexProduct.records
          [(SemiprimeD1ChildNetworkTape.leftOne net (data net r a q g) old extra
            (SemiprimeBitArithmetic.bitValue newp) v).1] ∧
      (∑k : Stack,((acquiredDone net r a q g old extra oldp newp v).data k).length) ≤
        capacity old extra oldp newp (SemiprimeD1ChildNetwork.parentVertex net v).table
          (order net r a q g v).order (ports net r a q g v) := by
  obtain ⟨t,ht,hr,hout⟩:=source_run_actual net r a q g old ho extra he oldp newp hp hg v
  exact ⟨t,ht,hr,hout,acquired_words_le net r a q g old ho extra he oldp newp hg v⟩
end RiemannGaussian.SemiprimeD1StackChildVertexEndpointOriginal
