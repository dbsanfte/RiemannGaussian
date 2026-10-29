/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsNetwork
/-! # Exact unchanged topology and intrinsic NEW-precision data for the marked network -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsTopology
open SemiprimeD1StackMarkedRootRecordsNetwork
/-- Generic finite-index vector read, checked before concrete original graphs are instantiated. -/
def rightAt (net : SemiprimeD1TensorNetwork.Network) (i : Fin net.rows.length) : SemiprimeD1LeafCounter.Vertex :=
  net.right[i.val]
/-- Explicit unchanged-row index transport avoids unfolding original acquired graph data. -/
noncomputable def rightIndex (N : Nat) (hN : 0 < N) (i : Fin (old N hN).rows.length) : Fin (network N hN).rows.length :=
  Fin.cast (rows_length_eq N hN).symm i
/-- Generic changed-right projection, before any concrete original graph is instantiated. -/
theorem right_projection (base : SemiprimeD1TensorNetwork.Network) (F : Nat) (h : base.rows.length=F)
    (f : Fin F → SemiprimeD1LeafCounter.Vertex) (i : Fin base.rows.length) :
    ({base with right := Vector.ofFn (fun j => f (Fin.cast h j))}.right[i.val])=f (Fin.cast h i) := by
  simp only [Vector.getElem_ofFn]
/-- Every new right vertex preserves the exact old ordered occurrence names. -/
theorem right_ports (N : Nat) (hN : 0 < N) (i : Fin (old N hN).rows.length) :
    (rightAt (network N hN) (rightIndex N hN i)).ports=(rightAt (old N hN) i).ports := by
  let f := Fin.cast (old_right_length N hN) i
  have ho : rightAt (old N hN) i=SemiprimeD1StackFullFactorCatalogueOriginal.localVertex N hN f :=
    SemiprimeD1RootRecordCoordinates.factor_vertex N hN [] f
  have hn : rightAt (network N hN) (rightIndex N hN i)=factor N hN f :=
    right_projection (old N hN) _ (old_right_length N hN) (factor N hN) i
  exact (congrArg SemiprimeD1LeafCounter.Vertex.ports hn).trans
    ((factor_ports N hN f).trans (congrArg SemiprimeD1LeafCounter.Vertex.ports ho).symm)
/-- Exact same owner/factor port order, including every repeated and isolated incidence. -/
theorem vertex_ports (N : Nat) (hN : 0 < N) :
    (SemiprimeD1TensorNetwork.vertices (network N hN)).map SemiprimeD1LeafCounter.Vertex.ports=
      (SemiprimeD1TensorNetwork.vertices (old N hN)).map SemiprimeD1LeafCounter.Vertex.ports := by
  have hr : (network N hN).right.toList.map SemiprimeD1LeafCounter.Vertex.ports=
      (old N hN).right.toList.map SemiprimeD1LeafCounter.Vertex.ports := by
    apply List.ext_getElem
    · simp only [List.length_map,Vector.length_toList]
      rfl
    · intro i hi hj
      simp only [List.getElem_map,Vector.getElem_toList]
      exact right_ports N hN ⟨i,by simpa only [List.length_map,Vector.length_toList] using hj⟩
  unfold SemiprimeD1TensorNetwork.vertices
  simp only [List.map_append]
  exact congrArg₂ List.append rfl hr
/-- The same literal incidence rows license all original factor/owner routing without recomputation. -/
theorem wellFormed (N : Nat) (hN : 0 < N) : SemiprimeD1TensorNetwork.WellFormed (network N hN) := by
  have hw := SemiprimeD1RootNetwork.acquirePositive_wellFormed N hN []
  refine ⟨hw.1,?_⟩
  intro i
  exact (right_ports N hN i).trans (hw.2 i)
/-- All owner and marked factor coefficients are compact and fit the actual NEW2ell precision. -/
theorem good (N : Nat) (hN : 0 < N) :
    SemiprimeD1TensorNetwork.Good ⟨[],SemiprimeD1PackedMomentPrecision.precision N⟩ (network N hN) := by
  have hOld := SemiprimeD1RootNetwork.acquirePositive_good N hN []
  have hp : 2 ≤ SemiprimeD1PackedMomentPrecision.precision N := by
    have hL := SemiprimeMacroParameters.bitLength_pos hN
    unfold SemiprimeD1PackedMomentPrecision.precision
    omega
  intro vertex hv
  rw [vertices_original] at hv
  rcases List.mem_append.mp hv with ho|hf
  · apply SemiprimeD1StackMarkedRootRecordsIntegral.good_mono [] 2 _ hp _
    apply hOld vertex
    apply List.mem_append_left
    exact (congrArg (fun vs => vertex∈vs) (SemiprimeD1RootRecordCoordinates.owner_vector N hN [])).mpr ho
  · obtain ⟨f,_,rfl⟩ := List.mem_map.mp hf
    exact factor_good N hN f
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsTopology
