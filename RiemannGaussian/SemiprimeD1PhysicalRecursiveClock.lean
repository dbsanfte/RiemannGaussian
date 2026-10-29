/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PhysicalRecursiveBounds
import RiemannGaussian.SemiprimeD1RecursiveCallTree

/-! # Exact child-report separation for the actual physical recursive controller
Clock erasure below is a proof-side contribution measure retaining actual child
payloads. It is not claimed to execute those payloads for free. Local phase work
retains repeated source/header construction, including acquired menu reports.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1PhysicalRecursiveClock
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveCallTree
open SemiprimeD1JetAffineCoefficient (JetRun)
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- Proof-side removal of a continuation's report, retaining its actual payload. -/
def eraseClock (next : Context → Network → JetRun) (ctx : Context) (net : Network) : JetRun :=
  ⟨(next ctx net).words,0⟩

/-- Cached products preserve payload equality and exactly add child contributions. -/
theorem product_map {A : Type} (ctx : Context) (xs : List A)
    (f g : A → JetRun) (cost : A → ℕ)
    (hw : ∀ x ∈ xs, (f x).words=(g x).words)
    (hc : ∀ x ∈ xs, (f x).clock=(g x).clock+cost x) :
    (product ctx (xs.map f)).words=(product ctx (xs.map g)).words ∧
    (product ctx (xs.map f)).clock=(product ctx (xs.map g)).clock+(xs.map cost).sum := by
  induction xs with
  | nil => simp [product]
  | cons x xs ih =>
    have ht:=ih (fun y hy => hw y (by simp [hy])) (fun y hy => hc y (by simp [hy]))
    have hword:=hw x (by simp)
    have hcost:=hc x (by simp)
    constructor
    · simp only [List.map_cons,product,hword,ht.1]
    · simp only [List.map_cons,product,List.sum_cons]
      rw [hword,ht.1,hcost,ht.2]
      omega

/-- Cached sums preserve payload equality and exactly add child contributions. -/
theorem sum_map {A : Type} (ctx : Context) (xs : List A)
    (f g : A → JetRun) (cost : A → ℕ)
    (hw : ∀ x ∈ xs, (f x).words=(g x).words)
    (hc : ∀ x ∈ xs, (f x).clock=(g x).clock+cost x) :
    (SemiprimeD1JetAffineCoefficient.sumRuns ctx (xs.map f)).words=
      (SemiprimeD1JetAffineCoefficient.sumRuns ctx (xs.map g)).words ∧
    (SemiprimeD1JetAffineCoefficient.sumRuns ctx (xs.map f)).clock=
      (SemiprimeD1JetAffineCoefficient.sumRuns ctx (xs.map g)).clock+(xs.map cost).sum := by
  induction xs with
  | nil => simp [SemiprimeD1JetAffineCoefficient.sumRuns]
  | cons x xs ih =>
    have ht:=ih (fun y hy => hw y (by simp [hy])) (fun y hy => hc y (by simp [hy]))
    have hword:=hw x (by simp)
    have hcost:=hc x (by simp)
    constructor
    · simp only [List.map_cons,SemiprimeD1JetAffineCoefficient.sumRuns,hword,ht.1]
    · simp only [List.map_cons,SemiprimeD1JetAffineCoefficient.sumRuns,List.sum_cons]
      rw [hword,ht.1,hcost,ht.2]
      omega

/-- The literal mode/group product in one phase, as a proof-side named subterm. -/
def phaseTerm (next : Context → Network → JetRun) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a) (beta : List ℕ) : JetRun :=
  let source:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
    parent.net.rows.length 64 a u i.val parent.ctx.precision
    (arity parent.net.rows) (owner parent.net.rows)
  let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
  let fresh:=SemiprimeD1FreshJetBits.acquireFresh parent.ctx q source.precision
  let current : Context:=⟨q::parent.ctx.axes,source.precision⟩
  product current ((List.finRange 64).map (fun g =>
    let data:=SemiprimeD1ChildNetwork.fromSource parent.net source i g parent.ctx [q]
      source.precision fresh t beta
    let answer:=next current data.network
    (⟨answer.words,data.clock+answer.clock+5⟩:JetRun)))

/-- Exact one-mode report separation retains every repeated child/header/source
construction cost in the erased local term. -/
theorem phaseTerm_clock (next : Context → Network → JetRun) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a) (beta : List ℕ) :
    (phaseTerm next parent a u t i beta).words=
      (phaseTerm (eraseClock next) parent a u t i beta).words ∧
    (phaseTerm next parent a u t i beta).clock=
      (phaseTerm (eraseClock next) parent a u t i beta).clock+
      ((List.finRange 64).map (fun g =>
        (next (child parent a u t i beta g).ctx (child parent a u t i beta g).net).clock)).sum := by
  unfold phaseTerm
  apply product_map
  · intro g hg
    rfl
  · intro g hg
    dsimp only [eraseClock,child]
    omega

/-- The literal sum of acquired-mode products in a guarded phase. -/
def phaseTotal (next : Context → Network → JetRun) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a) : JetRun :=
  let source:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
    parent.net.rows.length 64 a u i.val parent.ctx.precision
    (arity parent.net.rows) (owner parent.net.rows)
  let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
  SemiprimeD1JetAffineCoefficient.sumRuns ⟨q::parent.ctx.axes,source.precision⟩
    (source.modes.values.map (phaseTerm next parent a u t i))

/-- The sum of literal child clocks over an original active mode/group menu. -/
def modeChildClocks (next : Context → Network → JetRun) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a) : ℕ :=
  let source:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
    parent.net.rows.length 64 a u i.val parent.ctx.precision
    (arity parent.net.rows) (owner parent.net.rows)
  (source.modes.values.map (fun beta => ((List.finRange 64).map (fun g =>
    (next (child parent a u t i beta g).ctx (child parent a u t i beta g).net).clock)).sum)).sum

/-- Actual mode sums preserve payloads and add exactly their real child clocks. -/
theorem phaseTotal_clock (next : Context → Network → JetRun) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a) :
    (phaseTotal next parent a u t i).words=
      (phaseTotal (eraseClock next) parent a u t i).words ∧
    (phaseTotal next parent a u t i).clock=
      (phaseTotal (eraseClock next) parent a u t i).clock+modeChildClocks next parent a u t i := by
  unfold phaseTotal modeChildClocks
  apply sum_map
  · intro beta hb
    exact (phaseTerm_clock next parent a u t i beta).1
  · intro beta hb
    exact (phaseTerm_clock next parent a u t i beta).2

/-- Literal flat-map child inventory retains multiplicities in its clock sum. -/
theorem sum_flatMap {A B : Type} (xs : List A) (f : A → List B) (cost : B → ℕ) :
    ((xs.flatMap f).map cost).sum=(xs.map (fun x => ((f x).map cost).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,ih,
      List.map_cons,List.sum_cons]

/-- Exact phase report separation on the literal original grid and child menu.
The local replay retains EVERY nonrecursive source/header/acquisition report. -/
theorem phase_clock (next : Context → Network → JetRun) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) :
    (phase next parent.ctx parent.net a u t).blocks=
      (phase (eraseClock next) parent.ctx parent.net a u t).blocks ∧
    (phase next parent.ctx parent.net a u t).precision=
      (phase (eraseClock next) parent.ctx parent.net a u t).precision ∧
    (phase next parent.ctx parent.net a u t).clock=
      (phase (eraseClock next) parent.ctx parent.net a u t).clock+
      ((phaseChildren parent a u t).map (fun c => (next c.ctx c.net).clock)).sum := by
  dsimp only [phase,phaseChildren]
  split
  · rename_i hi
    let i : Fin a:=⟨_,hi.1⟩
    let source:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
      parent.net.rows.length 64 a u i.val parent.ctx.precision
      (arity parent.net.rows) (owner parent.net.rows)
    let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
    have ht:=phaseTotal_clock next parent a u t i
    have hw : (phaseTotal next parent a u t i).words=
        (phaseTotal (eraseClock next) parent a u t i).words := ht.1
    refine ⟨?_,rfl,?_⟩
    · simp only [List.map_map,Function.comp_def]
      change ((List.range q).map (fun j =>
          (SemiprimeD1JetBlockBits.extract parent.ctx j (phaseTotal next parent a u t i).words).words)).toArray=
        ((List.range q).map (fun j =>
          (SemiprimeD1JetBlockBits.extract parent.ctx j
            (phaseTotal (eraseClock next) parent a u t i).words).words)).toArray
      rw [hw]
    · have hc:=ht.2
      have hsum : ((source.modes.values.flatMap (fun beta =>
          (List.finRange 64).map (child parent a u t i beta))).map
          (fun c => (next c.ctx c.net).clock)).sum=modeChildClocks next parent a u t i := by
        rw [sum_flatMap]
        simp only [List.map_map,Function.comp_def,modeChildClocks,source]
      change _+(phaseTotal next parent a u t i).clock+
        (((List.range q).map (fun j =>
          SemiprimeD1JetBlockBits.extract parent.ctx j (phaseTotal next parent a u t i).words)).map
          (fun block => block.clock)).sum+_ =
        _+(phaseTotal (eraseClock next) parent a u t i).clock+
        (((List.range q).map (fun j => SemiprimeD1JetBlockBits.extract parent.ctx j
          (phaseTotal (eraseClock next) parent a u t i).words)).map
          (fun block => block.clock)).sum+_+_
      rw [hw,hsum]
      omega
  · simp only [List.map_nil,List.sum_nil,Nat.add_zero,and_self]

/-- Coordinate acquisition consumes only literal phase blocks, not phase reports. -/
theorem coordinate_congr (xs ys : Array PhaseRun) (k : ℕ)
    (h : xs.map PhaseRun.blocks=ys.map PhaseRun.blocks) : coordinate xs k=coordinate ys k := by
  let convert : Array (Array (List (List Bool))) → CoordinateData := fun blocks =>
    let rows:=blocks.map (fun block =>
      let copied:=block.map (fun words => SemiprimeD1JetBlockBits.readCopy words k)
      (copied.map (fun out => out.bits),(copied.toList.map (fun out => out.clock)).sum+5*copied.size+3))
    ⟨rows.map Prod.fst,(rows.toList.map Prod.snd).sum+5*rows.size+3⟩
  have hx : coordinate xs k=convert (xs.map PhaseRun.blocks) := by
    simp only [coordinate,convert,Array.map_map,Function.comp_def]
  have hy : coordinate ys k=convert (ys.map PhaseRun.blocks) := by
    simp only [coordinate,convert,Array.map_map,Function.comp_def]
  exact hx.trans ((congrArg convert h).trans hy.symm)

/-- The actual retained payload array is unchanged by proof-side child-report erasure. -/
theorem retained_blocks (next : Context → Network → JetRun) (parent : Call) (a u : ℕ) :
    (SemiprimeD1RecursiveRecovery.retained next parent.ctx parent.net a u).map PhaseRun.blocks=
    (SemiprimeD1RecursiveRecovery.retained (eraseClock next) parent.ctx parent.net a u).map PhaseRun.blocks := by
  apply Array.toList_inj.mp
  simp only [SemiprimeD1RecursiveRecovery.retained,Array.toList_map,
    List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro t ht
  exact (phase_clock next parent a u t).1

/-- Both the physical coordinate payload AND its entire local report are
unchanged by erasing only phase-level child reports. -/
theorem recoverCoordinate_congr (ctx : Context) (a M u P : ℕ) (xs ys : Array PhaseRun)
    (k : ℕ) (h : xs.map PhaseRun.blocks=ys.map PhaseRun.blocks) :
    SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate ctx a M u P xs k=
      SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate ctx a M u P ys k := by
  unfold SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate
  rw [coordinate_congr xs ys k h]

/-- Exact sum of the actual retained phase reports; duplicate children keep their
multiplicity and every local source/header report remains in the erased term. -/
theorem phases_clock (next : Context → Network → JetRun) (parent : Call) (a u : ℕ) :
    (((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
      (phase next parent.ctx parent.net a u)).map PhaseRun.clock).sum=
    (((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
      (phase (eraseClock next) parent.ctx parent.net a u)).map PhaseRun.clock).sum+
    (((List.finRange (SemiprimeD1WireKernelOriginal.size a)).flatMap
      (phaseChildren parent a u)).map (fun c => (next c.ctx c.net).clock)).sum := by
  rw [sum_flatMap]
  simp only [List.map_map,Function.comp_def]
  have h : ∀ t ∈ List.finRange (SemiprimeD1WireKernelOriginal.size a),
      (phase next parent.ctx parent.net a u t).clock=
      (phase (eraseClock next) parent.ctx parent.net a u t).clock+
        ((phaseChildren parent a u t).map (fun c => (next c.ctx c.net).clock)).sum := by
    intro t ht
    exact (phase_clock next parent a u t).2.2
  rw [show (List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
      (fun t => (phase next parent.ctx parent.net a u t).clock)=
      (List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
      (fun t => (phase (eraseClock next) parent.ctx parent.net a u t).clock+
        ((phaseChildren parent a u t).map (fun c => (next c.ctx c.net).clock)).sum) from
        List.map_congr_left h]
  exact List.sum_map_add

end RiemannGaussian.SemiprimeD1PhysicalRecursiveClock
