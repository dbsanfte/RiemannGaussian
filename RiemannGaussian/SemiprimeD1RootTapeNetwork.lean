/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildNetworkTape
import RiemannGaussian.SemiprimeD1RootNetwork

/-! # Original root acquisition with actual sequential table recopy
Original factor/owner production is acquired once. Every canonical root-table
copy then executes full tape serialization/read, including skipped subtrees.
Only literal network data agree with the former builder; clocks stay distinct.
Original checker arrays and native dimension/index/control lowering remain
separate from this explicit table-memory backend.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RootTapeNetwork
open SemiprimeD1RootTensorTables
open SemiprimeD1RootNetwork (rows defaultNode)
open SemiprimeD1ChildNetworkTape (copyTable)
open SemiprimeD1TensorNetwork (leftPorts rightPorts)

/-- Source-table byte equality gives the exact former canonical root vertex. -/
theorem copyNode_vertex {I : Type} (ports : List ℕ) (source : Node I) :
    (copyTable ports source.table).1=(SemiprimeD1RootNetwork.copyNode ports source).1 := by
  have h:=SemiprimeD1TensorTapeLeaf.build_table_congr ports.length
    (fun bits=>SemiprimeD1TensorTapeLookup.fromTable source.table bits)
    (SemiprimeD1TensorTables.lookup source.table)
    (fun bits=>SemiprimeD1TensorTapeLookup.fromTable_words source.table bits)
  exact congrArg (fun tab=>(⟨ports,tab⟩:SemiprimeD1LeafCounter.Vertex)) h

/-- Entire original root cache is copied through the actual sequential backend. -/
def fromCache {n F : ℕ} {arity : Fin F→ℕ} (data : Acquired n F arity) : SemiprimeD1RootNetwork.Run :=
  let rs:=rows data
  let left:=Vector.ofFn (fun v:Fin n=>
    copyTable (leftPorts rs v) (data.owners[v.val]?.getD (defaultNode _)).table)
  let right:=Vector.ofFn (fun e:Fin rs.length=>
    copyTable (rightPorts rs e) (data.factors[e.val]?.getD (defaultNode _)).table)
  ⟨⟨n,rs,left.map Prod.fst,right.map Prod.fst⟩,
    data.clock+(left.toList.map Prod.snd).sum+(right.toList.map Prod.snd).sum+
      10*(data.records.length+F+n+1)^3⟩

/-- Literal whole-network equality, excluding all changed memory-access clocks. -/
theorem fromCache_network {n F : ℕ} {arity : Fin F→ℕ} (data : Acquired n F arity) :
    (fromCache data).network=(SemiprimeD1RootNetwork.fromCache data).network := by
  have hl:(Vector.ofFn (fun v:Fin n=>
      copyTable (leftPorts (rows data) v) (data.owners[v.val]?.getD (defaultNode _)).table)).map Prod.fst=
      (Vector.ofFn (fun v:Fin n=>SemiprimeD1RootNetwork.copyNode
        (leftPorts (rows data) v) (data.owners[v.val]?.getD (defaultNode _)))).map Prod.fst:=by
    apply Vector.ext
    intro k hk
    simp only [Vector.getElem_map,Vector.getElem_ofFn,copyNode_vertex]
  have hr:(Vector.ofFn (fun e:Fin (rows data).length=>
      copyTable (rightPorts (rows data) e) (data.factors[e.val]?.getD (defaultNode _)).table)).map Prod.fst=
      (Vector.ofFn (fun e:Fin (rows data).length=>SemiprimeD1RootNetwork.copyNode
        (rightPorts (rows data) e) (data.factors[e.val]?.getD (defaultNode _)))).map Prod.fst:=by
    apply Vector.ext
    intro k hk
    simp only [Vector.getElem_map,Vector.getElem_ofFn,copyNode_vertex]
  dsimp only [fromCache,SemiprimeD1RootNetwork.fromCache]
  rw [hl,hr]

/-- Original input/prefix only; no source cache or memory-read supplier. -/
def acquirePositive (N : ℕ) (hN : 0<N)
    (fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount N)×Bool)) : SemiprimeD1RootNetwork.Run :=
  fromCache (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)

/-- New original-input builder produces the exact original well-formed network. -/
theorem acquirePositive_network (N : ℕ) (hN : 0<N)
    (fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount N)×Bool)) :
    (acquirePositive N hN fixed).network=(SemiprimeD1RootNetwork.acquirePositive N hN fixed).network :=
  fromCache_network _

/-- Original root source reports are retained before every new tape-copy report. -/
theorem fromCache_retains {n F : ℕ} {arity : Fin F→ℕ} (data : Acquired n F arity) :
    data.clock ≤ (fromCache data).clock := by dsimp only [fromCache];omega

end RiemannGaussian.SemiprimeD1RootTapeNetwork
