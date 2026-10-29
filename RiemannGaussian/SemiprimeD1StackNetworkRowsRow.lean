/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkRowsPorts
/-! # Actual completed binary-owner row reversal, real logger, cleanup and ONEfactor tally -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkRowsRow
open SemiprimeD1StackNetworkRows SemiprimeD1StackNetworkRowsPrimitives SemiprimeD1StackNetworkRowsView
open SemiprimeD1StackNetworkRowsEncoding SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => Label.local
/-- Complete actual row construction/logging pays its actual physical row bytes; even [] emits ONErow. -/
theorem finish_row (index:I.Stack→List Bool) (reader history factors occurrences:List Bool) (owners:List (List Bool)) :
    ∃q≤ 40*((vectorBits owners).length+1),Runs program q (ctl .rowSeed)
      (view index reader [] (payload owners).reverse history factors occurrences) (ctl .factorLoop)
      (view index reader [] [] ((chunk (vectorBits owners)).reverse++history) (true::factors) occurrences) :=by
  let base:=view index reader [] (payload owners).reverse history factors occurrences
  let b1:=Function.update base (aux .row) [false]
  let b2:=Function.update (view index reader [] [] history factors occurrences) (aux .row) (vectorBits owners)
  let b3:=Function.update b2 (aux .history) ((chunk (vectorBits owners)).reverse++history)
  let b4:=Function.update b3 (aux .row) []
  have h0:=push_run .rowSeed (ctl .rowReverse) (aux .row) false base rfl
  have h1:=reverse_call .row .rowReverse .logRow rfl b1 (payload owners).reverse [false] rfl rfl
  simp only [List.reverse_reverse] at h1
  have he1:Function.update (Function.update b1 (aux .rowHistory) []) (aux .row) (payload owners++[false])=b2:=by
    rw [payload_vector]
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · cases k <;> rfl
  change Runs program (2*(payload owners).reverse.length+3) (ctl .rowReverse) b1 (ctl .logRow)
    (Function.update (Function.update b1 (aux .rowHistory) []) (aux .row) (payload owners++[false])) at h1
  rw [he1] at h1
  obtain ⟨b,hb,h2⟩:=body_call b2 (vectorBits owners) history rfl rfl rfl
  have h3:=drain_loop .clearRow (ctl .countFactor) (aux .row) rfl b3 (vectorBits owners) rfl
  have h4:=push_run .countFactor (ctl .factorLoop) (aux .factors) true b4 rfl
  have hh:=join (join (join (join h0 h1) h2) h3) h4
  have he:Function.update b4 (aux .factors) (true::b4 (aux .factors))=
      view index reader [] [] ((chunk (vectorBits owners)).reverse++history) (true::factors) occurrences:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · cases k <;> rfl
  rw [he] at hh
  refine ⟨1+(2*(payload owners).reverse.length+3)+b+((vectorBits owners).length+1)+1,?_,hh⟩
  have hlen:=congrArg List.length (payload_vector owners)
  rw [List.length_append] at hlen
  simp only [List.length_cons,List.length_nil] at hlen
  rw [List.length_reverse]
  omega
/-- Actual owner-word widths bound the actual row bytes; no row-size promise is a runtime input. -/
theorem row_length_le (n:Nat) (owners:List (List Bool)) (hw:∀w∈owners,w.length≤ n+1) :
    (vectorBits owners).length≤ 2*(n+2)*owners.length+1 :=by
  have hs:(owners.map List.length).sum≤(n+1)*owners.length:=by
    induction owners with
    | nil=>simp
    | cons w owners ih=>
      have h0:=hw w (List.mem_cons_self)
      have ht:=ih (fun x hx=>hw x (List.mem_cons_of_mem w hx))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one]
      omega
  rw [vector_length]
  nlinarith only [hs]
/-- Sum of actual owner-row logger/reversal costs at acquired owner width. -/
theorem finish_row_bounded (index:I.Stack→List Bool) (reader history factors occurrences:List Bool)
    (owners:List (List Bool)) (n:Nat) (hw:∀w∈owners,w.length≤ n+1) :
    ∃q≤ 40*(2*(n+2)*owners.length+2),Runs program q (ctl .rowSeed)
      (view index reader [] (payload owners).reverse history factors occurrences) (ctl .factorLoop)
      (view index reader [] [] ((chunk (vectorBits owners)).reverse++history) (true::factors) occurrences) :=by
  obtain ⟨q,hq,hr⟩:=finish_row index reader history factors occurrences owners
  have hlen:=row_length_le n owners hw
  exact ⟨q,hq.trans (by omega),hr⟩
end RiemannGaussian.SemiprimeD1StackNetworkRowsRow
