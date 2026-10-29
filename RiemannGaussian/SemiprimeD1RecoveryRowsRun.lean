/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryWeightRunBounds
import RiemannGaussian.SemiprimeD1IntegerRecoveryAcquisition

/-! # Cached canonical recovery rows from the original grid
All original node producers are executed internally. The native signed integer
and rational-normalization boundary is explicit; no physical-bit clock is claimed.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1RecoveryRowsRun
open SemiprimeD1RecoveryScalarRun SemiprimeD1RecoveryWeightRun
open SemiprimeD1WireKernelOriginal SemiprimeD1TaperedLoss SemiprimeD1JetRecoveryGrid

/-- An actual cached canonical row with its original node and retained jet index. -/
structure Row where
  /-- Original grid node. -/
  node : ℕ
  /-- Original local retained coefficient index. -/
  index : ℕ
  /-- Actual computed canonical signed numerator. -/
  numerator : ℤ
  /-- Actual computed canonical positive denominator. -/
  denominator : ℕ
  deriving Repr

/-- Native grid enumeration with explicit traversal report. -/
def nodeIndices (a : ℕ) : Run (List (Fin (size a))) :=
  let g:=geometry a 0
  let ns:=indices g.size
  let values:=ns.value.attach.map fun t =>
    (⟨t.val,by
      have ht : t.val ∈ (indices (geometry a 0).size).value := t.property
      simpa only [indices_value,geometry_size,List.mem_range] using ht⟩:Fin (size a))
  ⟨values,g.work+ns.work+4*ns.value.length+3⟩

/-- Original node ordering, without an advised node list. -/
theorem nodeIndices_values (a : ℕ) :
    (nodeIndices a).value.map Fin.val=List.range (size a) := by
  simp [nodeIndices,indices_value,geometry_size]

/-- Cached per-node row data and the full native acquisition report. -/
structure RowsReport where
  /-- Actual original rows in node-major, local-index-major order. -/
  rows : List Row
  /-- All original node producers and copied canonical rows retained. -/
  work : ℕ

/-- Actual row traversal. Even inactive nodes are acquired before filtering,
a polynomial-overhead choice that avoids an unpaid multiplicity oracle. -/
def gather (a M u : ℕ) : List (Fin (size a)) → RowsReport
  | [] => ⟨[],1⟩
  | t::ts =>
    let current:=SemiprimeD1RecoveryWeightRun.acquire a M u t
    let tail:=gather a M u ts
    if t.val=center a ∨ current.data.retained=0 then
      ⟨tail.rows,current.work+tail.work+4⟩
    else
      let js:=indices current.rows.length
      let rows:=js.value.map fun j =>
        let r:=(current.rows[j]?).getD ⟨0,1⟩
        Row.mk t.val j r.numerator r.denominator
      ⟨rows++tail.rows,current.work+tail.work+js.work+8*current.rows.length+5⟩

/-- Complete original-grid acquisition, internally generating all nodes. -/
def acquire (a M u : ℕ) : RowsReport :=
  let ns:=nodeIndices a
  let rows:=gather a M u ns.value
  ⟨rows.rows,ns.work+rows.work+3⟩

/-- Full canonical row list with the precise original active-node ordering. -/
def originalRows (a M u : ℕ) : List Row :=
  (List.range (size a)).flatMap fun t =>
    let w:=SemiprimeD1JetRecoveryWeights.acquire a (height M u) u t
    if t=center a ∨ w.retained=0 then [] else
      (List.range w.weights.size).map fun j =>
        let q:=SemiprimeJetArray.coefficient w.weights j
        Row.mk t j q.num q.den

/-- Actual cached canonical row access uses the corresponding acquired scalar. -/
theorem canonical_at (a M u : ℕ) (t : Fin (size a)) (j : ℕ) :
    ((SemiprimeD1RecoveryWeightRun.acquire a M u t).rows[j]?).getD ⟨0,1⟩=
      let q:=SemiprimeJetArray.coefficient
        (SemiprimeD1JetRecoveryWeights.acquire a (height M u) u t.val).weights j
      CanonicalRow.mk q.num q.den := by
  rw [acquire_original_rows]
  simp only [List.getElem?_map,Array.getElem?_toList,SemiprimeJetArray.coefficient]
  cases (SemiprimeD1JetRecoveryWeights.acquire a (height M u) u t.val).weights[j]? <;> rfl

/-- Actual canonical cache length agrees with the acquired weight array. -/
theorem canonical_length (a M u : ℕ) (t : Fin (size a)) :
    (SemiprimeD1RecoveryWeightRun.acquire a M u t).rows.length=
      (SemiprimeD1JetRecoveryWeights.acquire a (height M u) u t.val).weights.size := by
  rw [acquire_original_rows]
  simp

/-- Every recursive row-acquisition frame agrees with the original finite data. -/
theorem gather_rows (a M u : ℕ) (ts : List (Fin (size a))) :
    (gather a M u ts).rows=(ts.map Fin.val).flatMap fun t =>
      let w:=SemiprimeD1JetRecoveryWeights.acquire a (height M u) u t
      if t=center a ∨ w.retained=0 then [] else
        (List.range w.weights.size).map fun j =>
          let q:=SemiprimeJetArray.coefficient w.weights j
          Row.mk t j q.num q.den := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [gather,List.map_cons,List.flatMap_cons,acquire_data]
    split_ifs
    · exact ih
    · simp only [indices_value,canonical_length,canonical_at,ih]

/-- Original-input row acquisition equals the original canonical weight data. -/
theorem acquire_rows (a M u : ℕ) : (acquire a M u).rows=originalRows a M u := by
  simp only [acquire,gather_rows,nodeIndices_values,originalRows]

/-- Every ACTUALLY cached canonical weight row has a positive denominator and
original-derived dyadic numerator/denominator bounds. No height answer is supplied. -/
theorem canonical_bounds (a M u : ℕ) (t : Fin (size a)) (j : ℕ)
    (hj : j < (SemiprimeD1RecoveryWeightRun.acquire a M u t).rows.length) :
    let r:=((SemiprimeD1RecoveryWeightRun.acquire a M u t).rows[j]?).getD ⟨0,1⟩
    0 < r.denominator ∧
    r.denominator ≤ 2^SemiprimeD1HermiteWeightBits.weightExponent a (height M u) u t.val ∧
    r.numerator.natAbs ≤ 2^SemiprimeD1HermiteWeightBits.weightExponent a (height M u) u t.val := by
  rw [canonical_length,SemiprimeD1JetRecoveryWeights.acquire_weights_size] at hj
  have hp : 0 < nodeMultiplicity a (height M u) u t.val := by omega
  have hb:=SemiprimeD1HermiteWeightBits.original_weight_bits a (height M u) u t hp j hj
  rw [canonical_at]
  exact ⟨Rat.den_pos _,hb⟩

/-- Actual canonical rows contain exactly the retained original multiplicity. -/
theorem canonical_length_le (a M u : ℕ) (t : Fin (size a)) :
    (SemiprimeD1RecoveryWeightRun.acquire a M u t).rows.length ≤ (height M u)*u := by
  rw [canonical_length,SemiprimeD1JetRecoveryWeights.acquire_weights_size]
  rw [← multiplicityRun_value a (height M u) u t.val t.val t.isLt]
  exact SemiprimeD1RecoveryWeightRunBounds.multiplicity_value_le _ _ _ _

/-- Original row count bounds every recursive global cache frame. -/
theorem gather_length (a M u : ℕ) (ts : List (Fin (size a))) :
    (gather a M u ts).rows.length ≤ ts.length*((height M u)*u) := by
  induction ts with
  | nil => simp [gather]
  | cons t ts ih =>
    have hc:=canonical_length_le a M u t
    simp only [gather]
    split_ifs <;> dsimp only
    · simp only [List.length_cons]; nlinarith
    · simp only [List.length_append,List.length_map,indices_value,List.length_range,List.length_cons]
      nlinarith

/-- The original full grid producer stores at most N*h*u canonical rows. -/
theorem acquire_length (a M u : ℕ) :
    (acquire a M u).rows.length ≤ size a*((height M u)*u) := by
  have h:=gather_length a M u (nodeIndices a).value
  have hn : (nodeIndices a).value.length=size a := by
    have hv:=congrArg List.length (nodeIndices_values a)
    simpa using hv
  simpa only [acquire,hn] using h

/-- All stages of original grid enumeration are retained. -/
theorem nodeIndices_work (a : ℕ) :
    (nodeIndices a).work=3*a+8+(size a*size a+4*size a+1)+4*size a+3 := by
  simp [nodeIndices,geometry,intPower_work,indices_work,indices_value,List.length_range,
    ← geometry_size a 0]

/-- Actual per-node cache traversal has a uniform original-parameter polynomial. -/
def nodeCacheBudget (a N h u : ℕ) : ℕ :=
  SemiprimeD1RecoveryWeightRunBounds.nodeBudget a N h u+(h*u)^2+12*(h*u)+6

/-- Every global row-cache recursion retains the complete actual node producer. -/
theorem gather_work (a M u : ℕ) (ts : List (Fin (size a))) :
    (gather a M u ts).work ≤ ts.length*nodeCacheBudget a (size a) (height M u) u+1 := by
  induction ts with
  | nil => simp [gather]
  | cons t ts ih =>
    simp only [nodeCacheBudget] at ih
    have hn:=SemiprimeD1RecoveryWeightRunBounds.acquire_work a M u t
    have hl:=canonical_length_le a M u t
    have hi : (SemiprimeD1RecoveryWeightRun.acquire a M u t).rows.length^2 ≤ ((height M u)*u)^2 := by gcongr
    simp only [gather]
    split_ifs <;> dsimp only
    · simp only [List.length_cons,nodeCacheBudget,Nat.add_mul,Nat.one_mul]
      omega
    · simp only [List.length_cons,indices_work,nodeCacheBudget,Nat.add_mul,Nat.one_mul]
      simp only [pow_two] at hi ih ⊢
      omega

/-- Full original-input canonical row-cache acquisition budget. -/
def budget (a M u : ℕ) : ℕ :=
  3*a+8+(size a*size a+4*size a+1)+4*size a+3+
    size a*nodeCacheBudget a (size a) (height M u) u+4

/-- Actual original scalar/canonical row producer, with no work/weight advice.
The bound is a retained native report; scalar normalization requires bit refinement. -/
theorem acquire_work (a M u : ℕ) : (acquire a M u).work ≤ budget a M u := by
  have hg:=gather_work a M u (nodeIndices a).value
  have hn : (nodeIndices a).value.length=size a := by
    have hv:=congrArg List.length (nodeIndices_values a)
    simpa using hv
  simp only [acquire,nodeIndices_work,budget]
  rw [hn] at hg
  omega

end RiemannGaussian.SemiprimeD1RecoveryRowsRun
