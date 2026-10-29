/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildNetwork
import RiemannGaussian.SemiprimeD1TensorNetworkRecursion
import RiemannGaussian.SemiprimeD1RootPortCounts

/-! # Literal recursive network data and table inventories
These bounds count actual stored tables, ports and row cells. They are data
inventories and retained component reports, not a primitive tape clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1NetworkStateResources
open scoped BigOperators
open SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkLayout
open SemiprimeD1JetAxes SemiprimeD1TensorTables
open SemiprimeD1TensorNetworkRecursion

/-- Actual number of stored owner and factor vertices, retaining isolated ones. -/
def vertexCount (net : Network) : ℕ := net.leftCount+net.rows.length

/-- The complete literal cache has exactly its declared number of vertices. -/
theorem vertices_length (net : Network) : (vertices net).length=vertexCount net := by
  simp only [vertices,List.length_append,Vector.length_toList,vertexCount]

/-- Literal table/port inventory, including each vertex header. Table storage
already counts all copied bit payload and branching tags. Nat addresses are cells. -/
def inventory (net : Network) : ℕ :=
  ((vertices net).map (fun v => storage v.table+v.ports.length+1)).sum+
    net.rows.flatten.length+net.rows.length+1

/-- The original cached owner rows contain precisely one cell per real occurrence. -/
theorem rows_flatten_length {n : ℕ} (rows : Rows n) : rows.flatten.length=scope rows := by
  have h:=congrArg List.length (SemiprimeD1RootPortCounts.incidence_owners rows)
  simpa only [List.length_map,scope] using h.symm

/-- A literal finite cache sum is bounded by its actual length times a per-cell cap. -/
theorem sum_map_le {A : Type*} (xs : List A) (f : A→ℕ) (B : ℕ)
    (h : ∀x∈xs,f x≤B) : (xs.map f).sum≤xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh:=h x List.mem_cons_self
    have ht:=ih (fun y hy=>h y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- Every actual table leaf/branch, physical payload, port and row cell is covered.
The only shape inputs are actual Good tables and the actual cached degree cap. -/
theorem inventory_bound (ctx : Context) (net : Network) (D : ℕ)
    (hg : ∀v∈vertices net,Good ctx v.table) (hd : DegreeBound net D) :
    inventory net ≤ vertexCount net*((ctx.rank*(3*ctx.precision+4)+3)*2^D+D)+
      edgeCount net+net.rows.length+1 := by
  have hs:=sum_map_le (vertices net) (fun v=>storage v.table+v.ports.length+1)
    ((ctx.rank*(3*ctx.precision+4)+3)*2^D+D) (by
      intro v hv
      have ht:=storage_bound ctx v.table (hg v hv)
      have hp:=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (hd v hv)
      have hm:=Nat.mul_le_mul_left (ctx.rank*(3*ctx.precision+4)+3) hp
      have hD:=hd v hv
      omega)
  rw [vertices_length] at hs
  unfold inventory edgeCount
  rw [rows_flatten_length]
  omega

/-- Dense copied lookup has a polynomial read/copy allowance once rank,
precision and stored scope are bounded; no table-value oracle is supplied. -/
theorem lookup_budget (ctx : Context) (v : SemiprimeD1LeafCounter.Vertex)
    (hg : Good ctx v.table) (D : ℕ) (hd : v.ports.length≤D) (bits : List Bool) :
    (lookup v.table bits).clock≤ctx.rank*(3*ctx.precision+4)+1+4*D := by
  exact (lookup_clock ctx v.table hg bits).trans (by omega)

/-- The actual child retains ALL old vertices on its owner side. -/
theorem child_vertexCount {r a : ℕ} (net : Network)
    (source : SemiprimeD1ChildNetwork.Source net a) (i : Fin a) (g : Fin r)
    (old : Context) (extra : List ℕ) (p : ℕ) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :
    vertexCount (SemiprimeD1ChildNetwork.fromSource net source i g old extra p z t beta).network=
      vertexCount net+source.packets.state.packets.length := by
  unfold vertexCount
  change net.leftCount+net.rows.length+
    (SemiprimeD1TensorNetworkLayout.childRows (SemiprimeD1ChildNetwork.graph net source i g)).length=_
  rw [childRows_length]
  unfold SemiprimeD1ChildNetwork.graph
  rw [SemiprimeD1ChildGraphSemantics.factors_length]

/-- A factor-eight real-edge contraction and the actual3M packet addition give
one telescoping potential, rather than a depth times vertex-count estimate. -/
theorem vertex_potential (parent child : Network)
    (hNF : vertexCount child≤vertexCount parent+3*edgeCount parent)
    (hM : 8*edgeCount child≤edgeCount parent) :
    vertexCount child+4*edgeCount child≤vertexCount parent+4*edgeCount parent := by
  omega

end RiemannGaussian.SemiprimeD1NetworkStateResources
