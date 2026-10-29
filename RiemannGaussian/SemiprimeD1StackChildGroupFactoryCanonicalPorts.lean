/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ParentTagOrder
/-! # Exact canonical left ports from the actual flattened vertex stream
This structural byte-order bridge uses the original acquired incidence order,
not a chosen permutation or a new runtime getter. It includes isolated vertices.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryCanonicalPorts
/-- In a duplicate-free actual list, each generated ordinal is its exact first index. -/
theorem nodup_zipIdx {A:Type} [BEq A] [LawfulBEq A] (xs:List A) (hn:xs.Nodup):
    xs.zipIdx=xs.map (fun x=>(x,xs.idxOf x)):=by
  apply List.ext_getElem
  · simp only [List.length_zipIdx,List.length_map]
  · intro i hi hj
    have hix:i<xs.length:=by simpa only [List.length_zipIdx] using hi
    have he:=hn.idxOf_getElem i hix
    simp only [List.getElem_zipIdx,List.getElem_map,Nat.zero_add]
    exact Prod.ext rfl he.symm
/-- The canonical original left scope is exactly the flattened vertex fibre in generated global order. -/
theorem leftPorts_zipIdx {n:Nat} (rows:SemiprimeD1TensorNetwork.Rows n) (v:Fin n):
    SemiprimeD1TensorNetwork.leftPorts rows v=
      ((rows.flatten.zipIdx).filter (fun p=>decide (p.1=v))).map Prod.snd:=by
  rw [←SemiprimeD1ParentTagOrder.incidence_owners rows,List.zipIdx_map,
    nodup_zipIdx _ (SemiprimeD1TensorNetwork.incidences_nodup rows)]
  simp only [List.map_map,List.filter_map,Function.comp_def,Prod.map,id_eq]
  rfl
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryCanonicalPorts
