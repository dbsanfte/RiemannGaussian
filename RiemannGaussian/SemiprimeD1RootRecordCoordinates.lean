/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFullFactorCatalogueClosed
import RiemannGaussian.SemiprimeD1StackOwnerRecordsPrefixResources
import RiemannGaussian.SemiprimeD1RootStateResources
import RiemannGaussian.SemiprimeD1TensorTapeLookup
/-! # Literal original root vertices equal the acquired owner-first record families
This is an identity of ordered ports and entire finite tables. All original
prefix assignments, including repeated or conflicting ones, are retained.
No native acquisition report or clock is transported.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1RootRecordCoordinates
open SemiprimePublicAcquiredExecution (wireCount factorCount indexedArity)
open SemiprimeD1TensorNetwork (Incidence arity incidences owner edgeID leftPorts rightPorts)
open SemiprimeD1RootTensorTables (Port)
namespace F
export SemiprimeD1StackFullFactorCatalogueOriginal (localVertex factorVertices local_ports local_table)
end F
namespace O
export SemiprimeD1StackOwnerRecordOriginal (vertex mappedVertex mapped_table)
end O
namespace I
export SemiprimeD1StackOwnerFibreOriginal (enumeration)
export SemiprimeD1BooleanFactorCatalogueIndicesOriginal (portOrdinal)
end I
namespace R
export SemiprimeD1RootNetwork (rows fromCache copyNode)
export SemiprimeD1RootEntrySemantics (factorIndex factorVertex ownerVertex)
export SemiprimeD1RootCoordinates (portIndex owner_portIndex original_arity)
end R
attribute [local irreducible] wireCount factorCount indexedArity
attribute [local irreducible] SemiprimeD1RootTensorTables.acquirePositive
/-- Reindex only proof-equal finite factor and local-slot bounds, retaining both numerical coordinates. -/
def incidenceCast {m n:Nat} {a:Fin m→Nat} {b:Fin n→Nat}
    (h:m=n) (ha:∀i,a i=b (Fin.cast h i)) (p:(i:Fin m)×Fin (a i)) : (i:Fin n)×Fin (b i):=
  ⟨Fin.cast h p.1,Fin.cast (ha p.1) p.2⟩
/-- Such proof-equal coordinate transport preserves the exact factor-major enumeration. -/
theorem incidence_values {m n:Nat} {a:Fin m→Nat} {b:Fin n→Nat}
    (h:m=n) (ha:∀i,a i=b (Fin.cast h i)) :
    (SemiprimeFiniteEnumerations.indexedIncidences n b).values=
      (SemiprimeFiniteEnumerations.indexedIncidences m a).values.map (incidenceCast h ha):=by
  cases h
  have hab:a=b:=funext ha
  subst b
  have hm:incidenceCast rfl ha=id:=by funext p;cases p;rfl
  rw [hm,List.map_id]
/-- Proof-equal incidence transport is injective, including repeated owner coordinates. -/
theorem incidence_cast_injective {m n:Nat} {a:Fin m→Nat} {b:Fin n→Nat}
    (h:m=n) (ha:∀i,a i=b (Fin.cast h i)) :Function.Injective (incidenceCast h ha):=by
  cases h
  have hab:a=b:=funext ha
  subst b
  intro p q he
  exact he
/-- A literal injective map leaves every computed list index unchanged. -/
theorem idxOf_map {A B:Type} [DecidableEq A] [DecidableEq B]
    (f:A→B) (hf:Function.Injective f) (xs:List A) (x:A) :
    (xs.map f).idxOf (f x)=xs.idxOf x:=by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>
    by_cases h:a=x
    · subst a;simp
    · have hn:f a≠f x:=fun he=>h (hf he)
      simp only [List.map_cons,List.idxOf_cons,beq_iff_eq,h,hn,ite_false,ih]
/-- Original source incidence reindexing is exactly the typed root port coordinate constructor. -/
theorem port_map (N:Nat) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) :
    incidenceCast (RiemannGaussian.SemiprimeD1RootNetwork.rows_length
      (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)).symm
      (fun i=>(R.original_arity N hN fixed i).symm)=
      (fun p:Port N=>R.portIndex N hN fixed p.1 p.2):=by
  funext p
  cases p
  rfl
/-- The typed root incidence list is the unchanged original factor-major list with proof-only casts. -/
theorem original_incidence_values (N:Nat) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) :
    incidences (R.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed))=
      (I.enumeration N).values.map (fun p=>R.portIndex N hN fixed p.1 p.2):=by
  have h:=incidence_values (RiemannGaussian.SemiprimeD1RootNetwork.rows_length
    (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)).symm
    (fun i=>(R.original_arity N hN fixed i).symm)
  rw [port_map] at h
  exact h
/-- Original global occurrence ordinals equal the old typed root's computed edgeID search. -/
theorem original_ordinal (N:Nat) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) (p:Port N) :
    edgeID (R.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed))
      (R.portIndex N hN fixed p.1 p.2)=I.portOrdinal N p:=by
  have hi:=incidence_cast_injective (RiemannGaussian.SemiprimeD1RootNetwork.rows_length
    (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)).symm
    (fun i=>(R.original_arity N hN fixed i).symm)
  rw [port_map] at hi
  unfold edgeID
  rw [original_incidence_values,idxOf_map _ hi]
  rfl
/-- Every original owner keeps its complete ordered occurrence fibre in old typed root coordinates. -/
theorem owner_ports (N:Nat) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) (e:Fin (wireCount N)) :
    leftPorts (R.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)) e=
      (O.vertex N hN fixed e).ports:=by
  change _=(SemiprimeD1RootTensorTables.ownerPorts N
    (SemiprimeD1RootTensorTables.acquirePositive N hN fixed).records e).map (I.portOrdinal N)
  rw [SemiprimeD1RootTensorTables.acquirePositive_records,
    SemiprimeD1RootTensorTablesBounds.ownerPorts_records]
  unfold leftPorts
  rw [original_incidence_values]
  simp only [List.filter_map,List.map_map,Function.comp_def]
  simp_rw [R.owner_portIndex,original_ordinal]
  rfl
/-- Original factor ownership tests depend only on the unchanged first finite coordinate. -/
theorem factor_test (N:Nat) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool))
    (f:Fin (factorCount N)) (p:Port N) :
    decide ((R.portIndex N hN fixed p.1 p.2).1=R.factorIndex N hN fixed f)=decide (p.1=f):=by
  congr 1
  rw [Fin.ext_iff,Fin.ext_iff]
  rfl
/-- Every original factor keeps its ordered local occurrence names in the typed root. -/
theorem factor_ports (N:Nat) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) (f:Fin (factorCount N)) :
    rightPorts (R.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed))
      (R.factorIndex N hN fixed f)=(F.localVertex N hN f).ports:=by
  rw [F.local_ports,SemiprimeD1RootTensorTables.factorNode_ports]
  unfold rightPorts
  rw [original_incidence_values]
  simp only [List.filter_map,List.map_map,Function.comp_def]
  simp_rw [factor_test,original_ordinal]
  change ((SemiprimeFiniteEnumerations.indexedIncidences (factorCount N) (indexedArity N)).values.filter
    (fun p=>decide (p.1=f))).map (I.portOrdinal N)=_
  rw [SemiprimeD1RootNetworkOrder.indexed_filter,List.map_map]
  rfl
/-- Entire literal tables are determined by their actual lookup words on every full local assignment. -/
theorem table_ext {n:Nat} (x y:SemiprimeD1TensorTables.Table n)
    (h:∀bits:List Bool,bits.length=n →
      (SemiprimeD1TensorTables.lookup x bits).words=(SemiprimeD1TensorTables.lookup y bits).words) :x=y:=by
  induction x with
  | leaf words=>
    cases y with
    | leaf other=>
      have hh:=h [] rfl
      simp only [SemiprimeD1TensorTables.lookup,SemiprimeD1JetAxes.copyVector_value] at hh
      exact congrArg SemiprimeD1TensorTables.Table.leaf hh
  | @fork n low high ihlow ihhigh=>
    cases y with
    | fork otherLow otherHigh=>
      have hl:low=otherLow:=ihlow otherLow (by
        intro bits hb
        have hh:=h (false::bits) (by simp only [List.length_cons];omega)
        simpa only [SemiprimeD1TensorTables.lookup,List.head?_cons,Option.getD_some,
          Bool.false_eq_true,ite_false,List.tail_cons] using hh)
      have hr:high=otherHigh:=ihhigh otherHigh (by
        intro bits hb
        have hh:=h (true::bits) (by simp only [List.length_cons];omega)
        simpa only [SemiprimeD1TensorTables.lookup,List.head?_cons,Option.getD_some,
          ite_true,List.tail_cons] using hh)
      exact congrArg₂ SemiprimeD1TensorTables.Table.fork hl hr
/-- Equal table bytes at equal intrinsic dimensions have identical literal lookup words. -/
theorem tape_lookup {m n:Nat} (h:m=n) (x:SemiprimeD1TensorTables.Table m)
    (y:SemiprimeD1TensorTables.Table n)
    (ht:SemiprimeD1TensorTapeCodec.tape x=SemiprimeD1TensorTapeCodec.tape y) (bits:List Bool) :
    (SemiprimeD1TensorTables.lookup x bits).words=(SemiprimeD1TensorTables.lookup y bits).words:=by
  cases h
  have hx:=SemiprimeD1TensorTapeLookup.read_correct x bits []
  have hy:=SemiprimeD1TensorTapeLookup.read_correct y bits []
  simp only [List.append_nil] at hx hy
  rw [ht] at hx
  exact hx.1.symm.trans hy.1
/-- Literal port equality and all literal lookup words determine the entire dependent vertex record. -/
theorem vertex_ext (x y:SemiprimeD1LeafCounter.Vertex) (hp:x.ports=y.ports)
    (ht:∀bits:List Bool,bits.length=x.ports.length →
      (SemiprimeD1TensorTables.lookup x.table bits).words=(SemiprimeD1TensorTables.lookup y.table bits).words) :x=y:=by
  cases x with
  | mk ps tx=>
    cases y with
    | mk qs ty=>
      change ps=qs at hp
      subst qs
      have hh:=table_ext tx ty ht
      exact congrArg (SemiprimeD1LeafCounter.Vertex.mk ps) hh
/-- Naming a cached node's ports by literal ordinals does not change any table entry. -/
theorem mapped_lookup {A:Type} (code:A→Nat) (node:SemiprimeD1RootTensorTables.Node A) (bits:List Bool) :
    (SemiprimeD1TensorTables.lookup (O.mappedVertex code node).table bits).words=
      (SemiprimeD1TensorTables.lookup node.table bits).words:=
  tape_lookup (List.length_map (as:=node.ports) code) _ _ (O.mapped_table code node) bits
/-- The typed root owner vector carries its declared canonical left-port list. -/
theorem root_owner_ports (N:Nat) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) (e:Fin (wireCount N)) :
    (R.ownerVertex N hN fixed e).ports=
      leftPorts (R.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)) e:=by
  simp only [R.ownerVertex,R.fromCache,Vector.getElem_map,Vector.getElem_ofFn,
    SemiprimeD1RootNetwork.copyNode_ports]
/-- The typed root factor vector carries its declared canonical right-port list. -/
theorem root_factor_ports (N:Nat) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) (f:Fin (factorCount N)) :
    (R.factorVertex N hN fixed f).ports=
      rightPorts (R.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)) (R.factorIndex N hN fixed f):=by
  simp only [R.factorVertex,R.fromCache,Vector.getElem_map,Vector.getElem_ofFn,
    SemiprimeD1RootNetwork.copyNode_ports]
/-- Each old typed root owner is EXACTLY the corresponding physically acquired original owner vertex. -/
theorem owner_vertex (N:Nat) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) (e:Fin (wireCount N)) :
    R.ownerVertex N hN fixed e=O.vertex N hN fixed e:=by
  apply vertex_ext _ _ ((root_owner_ports N hN fixed e).trans (owner_ports N hN fixed e))
  intro bits hb
  have hbp:bits.length=(leftPorts (R.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)) e).length:=
    hb.trans (congrArg List.length (root_owner_ports N hN fixed e))
  have hr:=SemiprimeD1RootEntrySemantics.fromCache_left_lookup
    (SemiprimeD1RootTensorTables.acquirePositive N hN fixed) e bits hbp
  change (SemiprimeD1TensorTables.lookup (R.ownerVertex N hN fixed e).table bits).words=_ at hr
  rw [SemiprimeD1RootEntrySemantics.owner_cache_at N hN fixed e] at hr
  exact hr.trans (mapped_lookup (I.portOrdinal N)
    (SemiprimeD1RootTensorTables.ownerNode N fixed
      (SemiprimeD1RootTensorTables.acquirePositive N hN fixed).records e) bits).symm
/-- Each old typed root arithmetic/Boolean factor is EXACTLY its acquired full original vertex. -/
theorem factor_vertex (N:Nat) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) (f:Fin (factorCount N)) :
    R.factorVertex N hN fixed f=F.localVertex N hN f:=by
  apply vertex_ext _ _ ((root_factor_ports N hN fixed f).trans (factor_ports N hN fixed f))
  intro bits hb
  have hbp:bits.length=(rightPorts (R.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed))
      (R.factorIndex N hN fixed f)).length:=
    hb.trans (congrArg List.length (root_factor_ports N hN fixed f))
  have hr:=SemiprimeD1RootEntrySemantics.fromCache_right_lookup
    (SemiprimeD1RootTensorTables.acquirePositive N hN fixed) (R.factorIndex N hN fixed f) bits hbp
  change (SemiprimeD1TensorTables.lookup (R.factorVertex N hN fixed f).table bits).words=
    (SemiprimeD1TensorTables.lookup
      (((SemiprimeD1RootTensorTables.acquirePositive N hN fixed).factors[f.val]?).getD
        (SemiprimeD1RootNetwork.defaultNode _)).table bits).words at hr
  rw [SemiprimeD1RootEntrySemantics.factor_cache_at N hN fixed f] at hr
  have hs:(F.localVertex N hN f).ports.length=(SemiprimeD1RootTensorTables.factorNode N hN f).ports.length:=by
    rw [F.local_ports,List.length_map]
  exact hr.trans (tape_lookup hs _ _ (F.local_table N hN f) bits).symm
/-- The actual typed root's left vector is in the same ascending original owner order. -/
theorem owner_vector (N:Nat) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) :
    (SemiprimeD1RootStateResources.root N hN fixed).left.toList=
      SemiprimeD1StackOwnerRecordsOriginal.vertices N hN fixed:=by
  have hl:(SemiprimeD1RootStateResources.root N hN fixed).left.toList=
      List.ofFn (R.ownerVertex N hN fixed):=by
    apply List.ext_getElem
    · simp only [Vector.length_toList,List.length_ofFn]
      rfl
    · intro i hi hj
      rw [Vector.getElem_toList,List.getElem_ofFn]
      rfl
  rw [hl]
  exact congrArg List.ofFn (funext (owner_vertex N hN fixed))
/-- The actual typed root's right vector is in the complete unchanged original factor order. -/
theorem factor_vector (N:Nat) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) :
    (SemiprimeD1RootStateResources.root N hN fixed).right.toList=
      F.factorVertices N hN (SemiprimeD1BooleanFactorCatalogueIndices.indices N):=by
  have hr:(SemiprimeD1RootStateResources.root N hN fixed).right.toList=
      List.ofFn (R.factorVertex N hN fixed):=by
    apply List.ext_getElem
    · simp only [Vector.length_toList,List.length_ofFn]
      exact RiemannGaussian.SemiprimeD1RootNetwork.rows_length _
    · intro i hi hj
      rw [Vector.getElem_toList,List.getElem_ofFn]
      rfl
  rw [hr]
  have hf:=congrArg List.ofFn (funext (factor_vertex N hN fixed))
  change List.ofFn (R.factorVertex N hN fixed)=
    (List.finRange (factorCount N)).map (F.localVertex N hN)
  rw [hf,List.finRange,List.map_ofFn]
  rfl
/-- ALL original typed root vertices are exactly the acquired owner-first records, for every prefix list. -/
theorem vertices_original (N:Nat) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) :
    SemiprimeD1TensorNetwork.vertices (SemiprimeD1RootStateResources.root N hN fixed)=
      SemiprimeD1StackOwnerRecordsOriginal.vertices N hN fixed++
        F.factorVertices N hN (SemiprimeD1BooleanFactorCatalogueIndices.indices N):=by
  exact congrArg₂ List.append (owner_vector N hN fixed) (factor_vector N hN fixed)
end RiemannGaussian.SemiprimeD1RootRecordCoordinates
