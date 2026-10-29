/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkRowsEncoding
/-! # Exact original factor/local-slot order, including repeated and empty rows
These equalities identify the source's physically resolved rows with the OLD
literal network rows. They provide no runtime incidence/owner getter or advice.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkRowsOrder
open SemiprimeD1StackNetworkRowsEncoding
open SemiprimeD1TensorNetwork
/-- A static nodup enumeration's single selected block retains the block's literal internal order. -/
theorem selected_block {A B:Type} [DecidableEq A] (xs:List A) (a:A) (f:A→List B)
    (hn:xs.Nodup) (ha:a∈xs) :xs.flatMap (fun b=>if b=a then f b else [])=f a :=by
  induction xs with
  | nil=>cases ha
  | cons b xs ih=>
    have ht:=List.nodup_cons.mp hn
    by_cases h:b=a
    · subst b
      have hz:xs.flatMap (fun b=>if b=a then f b else [])=[]:=List.flatMap_eq_nil_iff.mpr (by
        intro b hb
        have hba:b≠a:=by intro he;subst b;exact ht.1 hb
        simp only [hba,ite_false])
      simp only [List.flatMap_cons,ite_true,hz,List.append_nil]
    · have ham:a∈xs:=by
        rcases List.mem_cons.mp ha with he|he
        · exact (h he.symm).elim
        · exact he
      simp only [List.flatMap_cons,h,ite_false,List.nil_append]
      exact ih ht.2 ham
/-- Original incidence filtering yields the factor's actual ascending local slots, with no permutation. -/
theorem incidence_fibre {n:Nat} (rows:Rows n) (e:Fin rows.length) :
    ((incidences rows).filter (fun i=>decide (i.1=e)))=
      (List.finRange (arity rows e)).map (Sigma.mk e) :=by
  let block (j:Fin rows.length) :List (Incidence rows):=
    (List.finRange (arity rows j)).map (fun k=>⟨j,k⟩)
  change ((List.finRange rows.length).flatMap block).filter (fun i=>decide (i.1=e))=block e
  rw [List.filter_flatMap]
  have h:∀j:Fin rows.length,(block j).filter (fun i=>decide (i.1=e))=if j=e then block j else []:=by
    intro j
    by_cases hj:j=e
    · subst j
      simp [block,List.filter_map,Function.comp_def]
    · simp [block,List.filter_map,Function.comp_def,hj]
  simp_rw [h]
  exact selected_block (List.finRange rows.length) e block (List.nodup_finRange _) (List.mem_finRange _)
/-- Resolving one actual incidence's global ID returns its original literal owner coordinate. -/
theorem ownerAt_edge (net:Network) (i:Incidence net.rows) :
    ownerAt net (edgeID net.rows i)=Owner.ownerWord net.leftCount (owner net.rows i).val :=by
  have hp:=edgeID_lt net.rows i
  simp only [ownerAt,hp,dite_eq_left]
  have he:(⟨edgeID net.rows i,hp⟩:Fin (scope net.rows))=SemiprimeD1TensorNetworkLayout.edgeEquiv net.rows i:=by
    apply Fin.ext
    rfl
  rw [he]
  unfold SemiprimeD1TensorNetworkLayout.leftGroup
  rw [Equiv.symm_apply_apply]
/-- ALLoriginal factor ports recover the literal factor row in its exact original local-slot order. -/
theorem right_owner_words (net:Network) (e:Fin net.rows.length) :
    (rightPorts net.rows e).map (ownerAt net)=
      net.rows[e.val].map (fun v=>Owner.ownerWord net.leftCount v.val) :=by
  unfold rightPorts
  rw [List.map_map]
  simp only [Function.comp_def]
  have hm:(((incidences net.rows).filter (fun i=>decide (i.1=e))).map
      (fun i=>ownerAt net (edgeID net.rows i)))=
      ((incidences net.rows).filter (fun i=>decide (i.1=e))).map
        (fun i=>Owner.ownerWord net.leftCount (owner net.rows i).val):=by
    apply List.map_congr_left
    intro i _
    exact ownerAt_edge net i
  rw [hm,incidence_fibre,List.map_map]
  change (List.finRange net.rows[e.val].length).map
    (fun j=>Owner.ownerWord net.leftCount net.rows[e.val][j.val].val)=_
  have h:=congrArg (List.map (fun v:Fin net.leftCount=>Owner.ownerWord net.leftCount v.val))
    (List.ofFn_getElem (xs:=net.rows[e.val]))
  simpa only [List.map_ofFn,List.ofFn_eq_map,List.map_map,Function.comp_def] using h
/-- Every actual right-record port is in the original global scope; no scope bound is runtime advice. -/
theorem right_port_lt (net:Network) (hw:WellFormed net) (v:SemiprimeD1LeafCounter.Vertex)
    (hv:v∈net.right.toList) (p:Nat) (hp:p∈v.ports) :p<scope net.rows :=
  wellFormed_vertices net hw v (List.mem_append_right _ hv) p hp
/-- The complete physical resolved-row interpretation equals EXACTold net.rows, not a permuted table. -/
theorem resolvedRows_original (net:Network) (hw:WellFormed net) :
    resolvedRows net=net.rows.map (fun row=>row.map (fun v=>Owner.ownerWord net.leftCount v.val)) :=by
  apply List.ext_getElem
  · simp only [resolvedRows,List.length_map,Vector.length_toList]
  · intro i hi _
    have hs:i<net.rows.length:=by simpa only [resolvedRows,List.length_map,Vector.length_toList] using hi
    simp only [resolvedRows,List.getElem_map,Vector.getElem_toList]
    rw [hw.2 ⟨i,hs⟩]
    exact right_owner_words net ⟨i,hs⟩
/-- Actual factor count includes every zero-port factor once. -/
theorem factor_count (net:Network) :(resolvedRows net).length=net.rows.length :=by
  simp only [resolvedRows,List.length_map,Vector.length_toList]
/-- Actual occurrence count keeps every repeated local occurrence and equals the original row flatten length. -/
theorem occurrence_count (net:Network) (hw:WellFormed net) :
    (net.right.toList.map (fun v=>v.ports.length)).sum=net.rows.flatten.length :=by
  have h:=congrArg (fun rows:List (List (List Bool))=>(rows.map List.length).sum) (resolvedRows_original net hw)
  simpa only [resolvedRows,List.map_map,Function.comp_def,List.length_map,List.length_flatten] using h
/-- The exact entire physically acquired nested-row ABI agrees with the OLDoriginal network row tape. -/
theorem rowsTape_original (net:Network) (hw:WellFormed net) :rowsTape (resolvedRows net)=originalTape net :=by
  rw [resolvedRows_original net hw]
  rfl
end RiemannGaussian.SemiprimeD1StackNetworkRowsOrder
