/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursiveCorrectness
import RiemannGaussian.SemiprimeD1PathRate

/-! # Exact finite call inventory of the closed recursive controller
The inventory enumerates the actual grid branches, acquired modes and64 groups.
It is an erased view of execution, not an assertion that the counter allocates
this trace or that its component reports are a whole primitive clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RecursiveCallTree
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1WireKernelOriginal
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- Literal state at a recursive call; no solved value is stored. -/
structure Call where
  /-- Original schedule depth. -/
  depth : ℕ
  /-- Actual current nilpotent axes and coordinate precision. -/
  ctx : Context
  /-- Actual finite cached tensor network. -/
  net : Network

/-- One actual mode/group child, constructed by the same cached constructors
as the phase. No child count or entry answer is an argument. -/
def child (parent : Call) (a u : ℕ) (t : Fin (size a)) (i : Fin a)
    (beta : List ℕ) (g : Fin 64) : Call :=
  let source := SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
    parent.net.rows.length 64 a u i.val parent.ctx.precision
    (arity parent.net.rows) (owner parent.net.rows)
  let q := SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u * (u-i.val)
  let fresh := SemiprimeD1FreshJetBits.acquireFresh parent.ctx q source.precision
  ⟨parent.depth+1,⟨q::parent.ctx.axes,source.precision⟩,
    (SemiprimeD1ChildNetwork.fromSource parent.net source i g parent.ctx [q]
      source.precision fresh t beta).network⟩

/-- Exact actual phase call list, including its original signed-point test. -/
def phaseChildren (parent : Call) (a u : ℕ) (t : Fin (size a)) : List Call :=
  let geometry := SemiprimeD1RecoveryWeightRun.geometry a t.val
  let order := SemiprimeD1RecoveryScalarRun.orderFuel geometry.size geometry.point.natAbs
  if hi : order.value < a ∧ order.value < u ∧ geometry.point ≠ 0 then
    let i : Fin a := ⟨order.value,hi.1⟩
    let source := SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
      parent.net.rows.length 64 a u i.val parent.ctx.precision
      (arity parent.net.rows) (owner parent.net.rows)
    source.modes.values.flatMap (fun beta => (List.finRange 64).map (child parent a u t i beta))
  else []

/-- Exact children of the actual active branch; failed schedule tests are leaves. -/
def children (s : ℕ) (parent : Call) : List Call :=
  let lam := SemiprimeD1PackingReady.logarithm s
  if activeTest s lam parent.depth (edgeCount parent.net) then
    let a := SemiprimeD1Schedule.exponent lam parent.depth
    let u := SemiprimeD1Schedule.levels lam parent.depth
    (List.finRange (size a)).flatMap (phaseChildren parent a u)
  else []

/-- Actual finite-fuel preorder inventory. Every node includes its own call once. -/
def trace (s : ℕ) : ℕ → Call → List Call
  | 0,parent => [parent]
  | fuel+1,parent => parent::(children s parent).flatMap (trace s fuel)

/-- Exact call count recurrence, not an advised branching upper bound. -/
def count (s : ℕ) : ℕ → Call → ℕ
  | 0,_ => 1
  | fuel+1,parent => 1+((children s parent).map (count s fuel)).sum

/-- Literal preorder size is the executed-call recurrence. -/
theorem trace_length (s fuel : ℕ) (parent : Call) : (trace s fuel parent).length = count s fuel parent := by
  induction fuel generalizing parent with
  | zero => rfl
  | succ fuel ih =>
    simp only [trace,List.length_cons,List.length_flatMap,count]
    simp_rw [ih]
    exact Nat.add_comm _ _

/-- Reachability refers to actual child membership, not arbitrary network histories. -/
inductive Reach (s : ℕ) (root : Call) : Call → Prop
  | root : Reach s root root
  | step {parent next : Call} : Reach s root parent → next ∈ children s parent → Reach s root next

/-- Exact phase-membership witnesses retain original grid guard, acquired mode
membership and literal group index. Duplicate modes/calls keep multiplicity. -/
theorem mem_phaseChildren (parent : Call) (a u : ℕ) (t : Fin (size a)) (next : Call) :
    next ∈ phaseChildren parent a u t ↔
    ∃ hi : (SemiprimeD1RecoveryScalarRun.orderFuel
        (SemiprimeD1RecoveryWeightRun.geometry a t.val).size
        (SemiprimeD1RecoveryWeightRun.geometry a t.val).point.natAbs).value < a ∧
      (SemiprimeD1RecoveryScalarRun.orderFuel
        (SemiprimeD1RecoveryWeightRun.geometry a t.val).size
        (SemiprimeD1RecoveryWeightRun.geometry a t.val).point.natAbs).value < u ∧
      (SemiprimeD1RecoveryWeightRun.geometry a t.val).point ≠ 0,
      ∃ beta ∈ (SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
        parent.net.rows.length 64 a u
        (SemiprimeD1RecoveryScalarRun.orderFuel
          (SemiprimeD1RecoveryWeightRun.geometry a t.val).size
          (SemiprimeD1RecoveryWeightRun.geometry a t.val).point.natAbs).value
        parent.ctx.precision (arity parent.net.rows) (owner parent.net.rows)).modes.values,
      ∃ g : Fin 64, next = child parent a u t ⟨_,hi.1⟩ beta g := by
  dsimp only [phaseChildren]
  split
  · rename_i hi
    simp only [List.mem_flatMap,List.mem_map,List.mem_finRange,true_and]
    constructor
    · rintro ⟨beta,hbeta,g,rfl⟩
      exact ⟨hi,beta,hbeta,g,rfl⟩
    · rintro ⟨_,beta,hbeta,g,rfl⟩
      exact ⟨beta,hbeta,g,rfl⟩
  · rename_i hno
    simp only [List.not_mem_nil,false_iff]
    rintro ⟨hi,_⟩
    exact hno hi

/-- Exact active-grid child membership. -/
theorem mem_children (s : ℕ) (parent next : Call) : next ∈ children s parent ↔
    activeTest s (SemiprimeD1PackingReady.logarithm s) parent.depth (edgeCount parent.net) = true ∧
    ∃ t : Fin (size (SemiprimeD1Schedule.exponent (SemiprimeD1PackingReady.logarithm s) parent.depth)),
      next ∈ phaseChildren parent
        (SemiprimeD1Schedule.exponent (SemiprimeD1PackingReady.logarithm s) parent.depth)
        (SemiprimeD1Schedule.levels (SemiprimeD1PackingReady.logarithm s) parent.depth) t := by
  dsimp only [children]
  split
  · rename_i h
    simp only [h,true_and,List.mem_flatMap,List.mem_finRange,true_and]
  · rename_i h
    simp only [List.not_mem_nil,h,Bool.false_eq_true,false_and]

/-- Actual child depth is incremented exactly once. -/
theorem child_depth (parent : Call) (a u : ℕ) (t : Fin (size a)) (i : Fin a)
    (beta : List ℕ) (g : Fin 64) : (child parent a u t i beta g).depth = parent.depth+1 := rfl

/-- Every actual constructed child has its canonical incidence ports. -/
theorem child_wellFormed (parent : Call) (a u : ℕ) (t : Fin (size a)) (i : Fin a)
    (beta : List ℕ) (g : Fin 64) : WellFormed (child parent a u t i beta g).net :=
  SemiprimeD1ChildNetwork.fromSource_wellFormed _ _ _ _ _ _ _ _ _ _

/-- Parent table shape and a positive actual fresh axis imply child table shape. -/
theorem child_good (parent : Call) (a u : ℕ) (t : Fin (size a)) (i : Fin a)
    (beta : List ℕ) (g : Fin 64) (hg : Good parent.ctx parent.net)
    (hq : 0 < SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u * (u-i.val)) :
    Good (child parent a u t i beta g).ctx (child parent a u t i beta g).net := by
  exact SemiprimeD1ChildNetwork.fromSource_good _ _ _ _ _ _ _ _ _ _ hg
    (by simpa only [List.prod_cons,List.prod_nil,mul_one] using hq)

end RiemannGaussian.SemiprimeD1RecursiveCallTree
