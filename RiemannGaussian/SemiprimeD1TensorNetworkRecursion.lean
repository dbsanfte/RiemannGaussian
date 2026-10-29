/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorNetworkLayout
import RiemannGaussian.SemiprimeD1PackingReady

/-! # Actual network-data scope contraction for the recursive schedule
The original selector's degree premises are derived from literal stored tensor
ports. The child scope is its acquired endpoint count, and the numeric packing
guard follows uniformly from the public root scale, not an acceptance oracle.
The construction and semantics of the child literal tables are separate joins.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeD1TensorNetworkRecursion
open scoped BigOperators
open SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkLayout

/-- A degree cap refers only to the actual cached tensor-port data. -/
def DegreeBound (net : Network) (degree : ℕ) : Prop :=
  ∀ v ∈ vertices net, v.ports.length ≤ degree

/-- Every cached left table belongs to the actual full vertex cache. -/
theorem left_mem (net : Network) (v : Fin net.leftCount) : net.left[v.val] ∈ vertices net := by
  apply List.mem_append_left
  have hm := List.getElem_mem (l := net.left.toList)
    (show v.val < net.left.toList.length by simpa only [Vector.length_toList] using v.isLt)
  simpa only [Vector.getElem_toList] using hm

/-- Every cached right table belongs to the actual full vertex cache. -/
theorem right_mem (net : Network) (e : Fin net.rows.length) : net.right[e.val] ∈ vertices net := by
  apply List.mem_append_right
  have hm := List.getElem_mem (l := net.right.toList)
    (show e.val < net.right.toList.length by simpa only [Vector.length_toList] using e.isLt)
  simpa only [Vector.getElem_toList] using hm

/-- Original sparse owner multiplicity is exactly the actual left table degree. -/
theorem owner_multiplicity {n : ℕ} (rows : Rows n) (Q : ℕ) (v : Fin n) :
    SemiprimeSourceHistogramGrouping.multiplicity (fun i => (owner rows i).val)
      (SemiprimeD1CollisionOriginal.ports n rows.length Q (arity rows)) v.val =
        (leftPorts rows v).length := by
  rw [original_ports]
  simp only [SemiprimeSourceHistogramGrouping.multiplicity, leftPorts,
    List.length_map, ← List.countP_eq_length_filter, Fin.ext_iff]

/-- Original sparse factor multiplicity is exactly the actual right table degree. -/
theorem factor_multiplicity {n : ℕ} (rows : Rows n) (Q : ℕ) (e : Fin rows.length) :
    SemiprimeSourceHistogramGrouping.multiplicity (fun i : Incidence rows => n+i.1.val)
      (SemiprimeD1CollisionOriginal.ports n rows.length Q (arity rows)) (n+e.val) =
        (rightPorts rows e).length := by
  rw [original_ports]
  simp only [SemiprimeSourceHistogramGrouping.multiplicity, rightPorts,
    List.length_map, ← List.countP_eq_length_filter, Nat.add_left_cancel_iff, Fin.ext_iff]

/-- The original selector's BOTH degree contracts are derived from literal layout
and cached port lengths, with no supplied colour or fibre-count answers. -/
theorem original_degree_contract (net : Network) (hw : WellFormed net) (degree Q : ℕ)
    (hd : DegreeBound net degree) :
    (∀ i ∈ SemiprimeD1CollisionOriginal.ports net.leftCount net.rows.length Q (arity net.rows),
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => (owner net.rows i).val)
        (SemiprimeD1CollisionOriginal.ports net.leftCount net.rows.length Q (arity net.rows))
        (owner net.rows i).val ≤ degree) ∧
    (∀ i ∈ SemiprimeD1CollisionOriginal.ports net.leftCount net.rows.length Q (arity net.rows),
      SemiprimeSourceHistogramGrouping.multiplicity (fun i : Incidence net.rows => net.leftCount+i.1.val)
        (SemiprimeD1CollisionOriginal.ports net.leftCount net.rows.length Q (arity net.rows))
        (net.leftCount+i.1.val) ≤ degree) := by
  constructor
  · intro i _
    rw [owner_multiplicity, ← hw.1 (owner net.rows i)]
    exact hd _ (left_mem net _)
  · intro i _
    rw [factor_multiplicity, ← hw.2 i.1]
    exact hd _ (right_mem net _)

/-- Literal native child owner rows from the original physical sparse builder. -/
def child (net : Network) (a : ℕ) (q : Fin a) (g : Fin 64) : Rows (net.leftCount+net.rows.length) :=
  childRows (SemiprimeD1ChildGraph.acquire net.leftCount net.rows.length 64 a
    (arity net.rows) (owner net.rows) q g)

/-- Actual acquired child variables shrink by16, derived from the stored parent
tables and the literal original packing inequality. -/
theorem child_shrink (net : Network) (hw : WellFormed net) (degree a : ℕ)
    (hd : DegreeBound net degree) (hsmall : 2*(64^(2*a))^2*degree ≤ edgeCount net)
    (q : Fin a) (g : Fin 64) : 16*scope (child net a q g) ≤ edgeCount net := by
  have hdegrees := original_degree_contract net hw degree a hd
  have hnumeric : 2*(64^(2*a))^2*degree ≤
      (SemiprimeD1CollisionOriginal.ports net.leftCount net.rows.length a (arity net.rows)).length := by
    rwa [original_ports]
  have h := SemiprimeD1ChildGraphBounds.child64_shrink net.leftCount net.rows.length a
    (arity net.rows) (owner net.rows) degree hdegrees.1 hdegrees.2 hnumeric q g
  rw [SemiprimeD1ChildGraphPartition.arity_sum, original_ports] at h
  change 16*scope (childRows (SemiprimeD1ChildGraph.acquire net.leftCount net.rows.length 64 a
    (arity net.rows) (owner net.rows) q g)) ≤ edgeCount net
  rw [child_scope]
  exact h

/-- The conservative factor8 used by the exponent ledger holds for the ACTUAL
acquired child graph, rather than an assumed recursive size sequence. -/
theorem child_shrink_eight (net : Network) (hw : WellFormed net) (degree a : ℕ)
    (hd : DegreeBound net degree) (hsmall : 2*(64^(2*a))^2*degree ≤ edgeCount net)
    (q : Fin a) (g : Fin 64) : scope (child net a q g)*8 ≤ edgeCount net := by
  have h := child_shrink net hw degree a hd hsmall q g
  omega

/-- Uniform original-scale acceptance gives the scope contraction for EVERY
actual well-formed network at EVERY active recursive depth. No separate packing
acceptance, child size, or local fibre-count premise remains. -/
theorem eventually_actual_children : ∀ᶠ s : ℕ in Filter.atTop,
    ∀ (depth : ℕ) (net : Network), WellFormed net →
      DegreeBound net (SemiprimeD1PackingReady.degreeCap s) →
      SemiprimeD1Schedule.Active s (SemiprimeD1PackingReady.logarithm s) depth (edgeCount net) →
      ∀ (q : Fin (SemiprimeD1Schedule.exponent (SemiprimeD1PackingReady.logarithm s) depth)) (g : Fin 64),
        scope (child net (SemiprimeD1Schedule.exponent (SemiprimeD1PackingReady.logarithm s) depth) q g)*8 ≤
          edgeCount net := by
  filter_upwards [SemiprimeD1PackingReady.eventually_all_depths] with s hs
  intro depth net hw hd ha q g
  have hg := hs depth (edgeCount net) (SemiprimeD1PackingReady.degreeCap s) ha le_rfl
  exact child_shrink_eight net hw _ _ hd hg.1.le q g

end RiemannGaussian.SemiprimeD1TensorNetworkRecursion
