/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorNetworkLayout
import RiemannGaussian.SemiprimeD1PartitionedTensor

/-! # Multilinear factorization of the ACTUAL literal network tensor caches
Well-formed literal port data derives each scope partition. Thus the identity
applies to products of individual current table entries, including isolated
vertices, without pretending that multilinear extension is multiplicative on
overlapping scopes or that upward modular lifting preserves products.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1TensorNetworkFactorization
open scoped BigOperators
open SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkLayout
variable {R : Type*} [CommRing R]

/-- The complete actual left vertex scope is exactly its owner fibre. -/
def leftScope (net : Network) (hw : WellFormed net) (v : Fin net.leftCount) :
    Fin (net.left[v.val]).ports.length ≃ {j // leftGroup net.rows j = v} :=
  portEquiv (leftGroup net.rows) v (net.left[v.val]).ports
    (by rw [hw.1 v]; exact leftPorts_lt net.rows v)
    (by rw [hw.1 v]; exact leftPorts_nodup net.rows v)
    (by rw [hw.1 v]; exact leftGroup_mem net.rows v)

/-- The complete actual right vertex scope is exactly its factor fibre. -/
def rightScope (net : Network) (hw : WellFormed net) (e : Fin net.rows.length) :
    Fin (net.right[e.val]).ports.length ≃ {j // rightGroup net.rows j = e} :=
  portEquiv (rightGroup net.rows) e (net.right[e.val]).ports
    (by rw [hw.2 e]; exact rightPorts_lt net.rows e)
    (by rw [hw.2 e]; exact rightPorts_nodup net.rows e)
    (by rw [hw.2 e]; exact rightGroup_mem net.rows e)

/-- The physical gather's proof-side value is the actual bounded global read. -/
theorem localAssignment_value {M : ℕ} (vertex : SemiprimeD1LeafCounter.Vertex)
    (hb : ∀ p ∈ vertex.ports, p < M) (bits : Fin M → Bool) (j : Fin vertex.ports.length) :
    SemiprimeD1LeafCounter.localAssignment bits vertex j =
      bits ⟨vertex.ports[j.val], hb _ (List.getElem_mem j.isLt)⟩ := by
  have hp := hb _ (List.getElem_mem j.isLt)
  change ((List.ofFn bits)[vertex.ports[j.val]]?).getD false = _
  rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using hp)]
  simp only [List.getElem_ofFn, Option.getD_some]

/-- A local left table receives precisely its acquired port order in the fibre. -/
noncomputable def leftTensor (net : Network) (hw : WellFormed net)
    (read : List (List Bool) → R) (v : Fin net.leftCount)
    (bits : {j // leftGroup net.rows j = v} → Bool) : R :=
  read (SemiprimeD1TensorTables.valueAt (net.left[v.val]).table
    (fun j => bits (leftScope net hw v j)))

/-- A local right table receives precisely its acquired port order in the fibre. -/
noncomputable def rightTensor (net : Network) (hw : WellFormed net)
    (read : List (List Bool) → R) (e : Fin net.rows.length)
    (bits : {j // rightGroup net.rows j = e} → Bool) : R :=
  read (SemiprimeD1TensorTables.valueAt (net.right[e.val]).table
    (fun j => bits (rightScope net hw e j)))

omit [CommRing R] in
/-- At global Boolean data the left fibre tensor is the INDIVIDUAL literal table entry. -/
theorem leftTensor_global (net : Network) (hw : WellFormed net)
    (read : List (List Bool) → R) (v : Fin net.leftCount) (bits : Fin (edgeCount net) → Bool) :
    leftTensor net hw read v (fun j => bits j.val) =
      read (SemiprimeD1TensorTables.valueAt (net.left[v.val]).table
        (SemiprimeD1LeafCounter.localAssignment bits (net.left[v.val]))) := by
  unfold leftTensor
  congr 2
  funext j
  exact (localAssignment_value _ (by rw [hw.1 v]; exact leftPorts_lt net.rows v) bits j).symm

omit [CommRing R] in
/-- At global Boolean data the right fibre tensor is the INDIVIDUAL literal table entry. -/
theorem rightTensor_global (net : Network) (hw : WellFormed net)
    (read : List (List Bool) → R) (e : Fin net.rows.length) (bits : Fin (edgeCount net) → Bool) :
    rightTensor net hw read e (fun j => bits j.val) =
      read (SemiprimeD1TensorTables.valueAt (net.right[e.val]).table
        (SemiprimeD1LeafCounter.localAssignment bits (net.right[e.val]))) := by
  unfold rightTensor
  congr 2
  funext j
  exact (localAssignment_value _ (by rw [hw.2 e]; exact rightPorts_lt net.rows e) bits j).symm

/-- A complete literal cache product is exactly its finite vertex-indexed product. -/
theorem vector_product {n : ℕ} (cache : Vector SemiprimeD1LeafCounter.Vertex n)
    (read : SemiprimeD1LeafCounter.Vertex → R) :
    (cache.toList.map read).prod = ∏ i : Fin n, read cache[i.val] := by
  have h := congrArg (fun xs : List SemiprimeD1LeafCounter.Vertex => (xs.map read).prod)
    (List.ofFn_getElem (xs := cache.toList))
  simpa only [Vector.length_toList, Vector.getElem_toList, List.map_ofFn,
    Function.comp_def, List.prod_ofFn, Fin.val_cast] using h.symm

/-- The global left multilinear extension factors into extensions of the ACTUAL
individual literal tables because the acquired left scopes partition variables. -/
theorem left_factor (net : Network) (hw : WellFormed net) (read : List (List Bool) → R)
    (x : Fin (edgeCount net) → R) :
    SemiprimeStreamingTensor.evaluate (edgeCount net)
      (fun bits => (net.left.toList.map (fun v => read
        (SemiprimeD1TensorTables.valueAt v.table (SemiprimeD1LeafCounter.localAssignment bits v)))).prod) x =
      ∏ v, SemiprimeD1PartitionedTensor.evaluate (leftTensor net hw read v)
        (fun j : {j // leftGroup net.rows j = v} => x j.val) := by
  have hpoint (bits : Fin (edgeCount net) → Bool) :
      (net.left.toList.map (fun v => read
        (SemiprimeD1TensorTables.valueAt v.table (SemiprimeD1LeafCounter.localAssignment bits v)))).prod =
        ∏ v, leftTensor net hw read v (fun j => bits j.val) := by
    rw [vector_product]
    exact Finset.prod_congr rfl (fun v _ => (leftTensor_global net hw read v bits).symm)
  simp_rw [hpoint]
  rw [SemiprimeD1PartitionedTensor.evaluate_fin]
  exact SemiprimeD1PartitionedTensor.evaluate_product (leftGroup net.rows) (leftTensor net hw read) x

/-- The same exact factorization holds for the actual factor-side cache. -/
theorem right_factor (net : Network) (hw : WellFormed net) (read : List (List Bool) → R)
    (x : Fin (edgeCount net) → R) :
    SemiprimeStreamingTensor.evaluate (edgeCount net)
      (fun bits => (net.right.toList.map (fun v => read
        (SemiprimeD1TensorTables.valueAt v.table (SemiprimeD1LeafCounter.localAssignment bits v)))).prod) x =
      ∏ e, SemiprimeD1PartitionedTensor.evaluate (rightTensor net hw read e)
        (fun j : {j // rightGroup net.rows j = e} => x j.val) := by
  have hpoint (bits : Fin (edgeCount net) → Bool) :
      (net.right.toList.map (fun v => read
        (SemiprimeD1TensorTables.valueAt v.table (SemiprimeD1LeafCounter.localAssignment bits v)))).prod =
        ∏ e, rightTensor net hw read e (fun j => bits j.val) := by
    rw [vector_product]
    exact Finset.prod_congr rfl (fun e _ => (rightTensor_global net hw read e bits).symm)
  simp_rw [hpoint]
  rw [SemiprimeD1PartitionedTensor.evaluate_fin]
  exact SemiprimeD1PartitionedTensor.evaluate_product (rightGroup net.rows) (rightTensor net hw read) x

end RiemannGaussian.SemiprimeD1TensorNetworkFactorization
