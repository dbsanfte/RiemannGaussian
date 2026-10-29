/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildWordNetwork
import RiemannGaussian.SemiprimeD1TensorTapeRecursiveCounter

/-! # Actual recursive phases with word packet factories and tape parent tables
The literal original grid/menu/group order and every source/child report remain
on the executed data path. Positivity is derived from actual retained guards.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace RiemannGaussian.SemiprimeD1WordTapeRecursivePhase
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCallState
open SemiprimeD1JetAffineCoefficient (JetRun)
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- One finite internal recursion phase. The continuation is wired to the
structural predecessor in `run`; it is never an external solver input. -/
def phase (next : Context → Network → JetRun) (ctx : Context) (net : Network)
    (a u : ℕ) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) : PhaseRun :=
  let M := edgeCount net
  let geometry := SemiprimeD1RecoveryWeightRun.geometry a t.val
  let order := SemiprimeD1RecoveryScalarRun.orderFuel geometry.size geometry.point.natAbs
  let i := order.value
  if hi : i < a ∧ i < u ∧ geometry.point ≠ 0 then
    let index : Fin a := ⟨i,hi.1⟩
    let source := SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64
      a u i ctx.precision (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)
    let height := SemiprimeD1ModeRate.jetHeight M u
    let q := height*(u-i)
    let fresh := SemiprimeD1FreshJetBits.acquireFresh ctx q source.precision
    let current : Context := ⟨q::ctx.axes,source.precision⟩
    let terms := source.modes.values.map (fun beta =>
      let children := (List.finRange 64).map (fun g =>
        let child := SemiprimeD1ChildWordNetwork.fromSource net source index g
          ctx [q] source.precision fresh t beta
        let answer := next current child.network
        (⟨answer.words,child.clock+answer.clock+5⟩ : JetRun))
      product current children)
    let total := SemiprimeD1JetAffineCoefficient.sumRuns current terms
    let blocks := (List.range q).map (fun j => SemiprimeD1JetBlockBits.extract ctx j total.words)
    ⟨(blocks.map (fun block => block.words)).toArray,source.precision,
      geometry.work+order.work+source.work+fresh.clock+total.clock+
        (blocks.map (fun block => block.clock)).sum+
        10*(M+a+u+i+q+source.modes.values.length+1)⟩
  else ⟨#[],0,geometry.work+order.work+a+u+i+8⟩

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
    let data:=SemiprimeD1ChildWordNetwork.fromSource parent.net source i g parent.ctx [q]
      source.precision fresh t beta
    let answer:=next current data.network
    (⟨answer.words,data.clock+answer.clock+5⟩:JetRun)))

/-- The literal sum of acquired-mode products in a guarded phase. -/
def phaseTotal (next : Context → Network → JetRun) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a) : JetRun :=
  let source:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
    parent.net.rows.length 64 a u i.val parent.ctx.precision
    (arity parent.net.rows) (owner parent.net.rows)
  let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
  SemiprimeD1JetAffineCoefficient.sumRuns ⟨q::parent.ctx.axes,source.precision⟩
    (source.modes.values.map (phaseTerm next parent a u t i))

/-- Deterministic physical products depend only on the literal word payloads. -/
theorem product_words {A : Type} (ctx : Context) (xs : List A) (f g : A → JetRun)
    (h : ∀x∈xs,(f x).words=(g x).words) :
    (product ctx (xs.map f)).words=(product ctx (xs.map g)).words := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hh:=h x (by simp)
    have ht:=ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons,product,hh,ht]

/-- Deterministic physical sums depend only on the literal word payloads. -/
theorem sum_words {A : Type} (ctx : Context) (xs : List A) (f g : A → JetRun)
    (h : ∀x∈xs,(f x).words=(g x).words) :
    (SemiprimeD1JetAffineCoefficient.sumRuns ctx (xs.map f)).words=
      (SemiprimeD1JetAffineCoefficient.sumRuns ctx (xs.map g)).words := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hh:=h x (by simp)
    have ht:=ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons,SemiprimeD1JetAffineCoefficient.sumRuns,hh,ht]

/-- Actual active scope and retained valuation create a positive fresh context. -/
theorem current_positive (ctx : Context) (M u i p : ℕ) (hp : ctx.Positive)
    (huM : u ≤ M) (hi : i<u) :
    (⟨SemiprimeD1ModeRate.jetHeight M u*(u-i)::ctx.axes,p⟩ : Context).Positive := by
  have hh:=height_positive M u (by omega) huM
  have hq:=Nat.mul_pos hh (Nat.sub_pos_of_lt hi)
  intro q hmem
  rcases List.mem_cons.mp hmem with h | h
  · exact h.symm ▸ hq
  · exact hp q h

/-- Per-mode child data and products refine the original literal network with
fresh positivity proved from actual phase guards, not supplied backend answers. -/
theorem phaseTerm_words (f g : Context → Network → JetRun) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a) (beta : List ℕ)
    (hp : parent.ctx.Positive) (huM : u ≤ edgeCount parent.net) (hi : i.val<u)
    (hn : ∀ctx net,ctx.Positive → (f ctx net).words=(g ctx net).words) :
    (phaseTerm f parent a u t i beta).words=
      (SemiprimeD1PhysicalRecursiveClock.phaseTerm g parent a u t i beta).words := by
  let source:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
    parent.net.rows.length 64 a u i.val parent.ctx.precision (arity parent.net.rows) (owner parent.net.rows)
  let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
  let fresh:=SemiprimeD1FreshJetBits.acquireFresh parent.ctx q source.precision
  let current : Context:=⟨q::parent.ctx.axes,source.precision⟩
  have hc : current.Positive := current_positive parent.ctx _ _ _ _ hp huM hi
  unfold phaseTerm SemiprimeD1PhysicalRecursiveClock.phaseTerm
  apply product_words
  intro group hg
  have he:=SemiprimeD1ChildWordNetwork.fromSource_network parent.net source i group
    parent.ctx [q] source.precision fresh t beta hc
  change (f current (SemiprimeD1ChildWordNetwork.fromSource parent.net source i group
      parent.ctx [q] source.precision fresh t beta).network).words=
    (g current (SemiprimeD1ChildNetwork.fromSource parent.net source i group
      parent.ctx [q] source.precision fresh t beta).network).words
  exact (hn _ _ hc).trans (congrArg (fun net => (g current net).words) he)

/-- Full actual acquired-mode sum refines the old literal phase payload. -/
theorem phaseTotal_words (f g : Context → Network → JetRun) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a)
    (hp : parent.ctx.Positive) (huM : u ≤ edgeCount parent.net) (hi : i.val<u)
    (hn : ∀ctx net,ctx.Positive → (f ctx net).words=(g ctx net).words) :
    (phaseTotal f parent a u t i).words=
      (SemiprimeD1PhysicalRecursiveClock.phaseTotal g parent a u t i).words := by
  unfold phaseTotal SemiprimeD1PhysicalRecursiveClock.phaseTotal
  apply sum_words
  intro beta hb
  exact phaseTerm_words f g parent a u t i beta hp huM hi hn

/-- Actual retained blocks and precision agree; changed acquisition clocks do not. -/
theorem phase_data (f g : Context → Network → JetRun) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (hp : parent.ctx.Positive)
    (huM : u ≤ edgeCount parent.net)
    (hn : ∀ctx net,ctx.Positive → (f ctx net).words=(g ctx net).words) :
    (phase f parent.ctx parent.net a u t).blocks=(SemiprimeD1RecursiveCounter.phase g parent.ctx parent.net a u t).blocks ∧
    (phase f parent.ctx parent.net a u t).precision=(SemiprimeD1RecursiveCounter.phase g parent.ctx parent.net a u t).precision := by
  dsimp only [phase,SemiprimeD1RecursiveCounter.phase]
  split
  · rename_i hi
    let i : Fin a:=⟨_,hi.1⟩
    let source:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
      parent.net.rows.length 64 a u i.val parent.ctx.precision (arity parent.net.rows) (owner parent.net.rows)
    let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
    have ht:=phaseTotal_words f g parent a u t i hp huM hi.2.1 hn
    refine ⟨?_,rfl⟩
    simp only [List.map_map,Function.comp_def]
    change ((List.range q).map (fun j =>
      (SemiprimeD1JetBlockBits.extract parent.ctx j (phaseTotal f parent a u t i).words).words)).toArray=
      ((List.range q).map (fun j =>
      (SemiprimeD1JetBlockBits.extract parent.ctx j (SemiprimeD1PhysicalRecursiveClock.phaseTotal g parent a u t i).words).words)).toArray
    rw [ht]
  · exact ⟨rfl,rfl⟩

end RiemannGaussian.SemiprimeD1WordTapeRecursivePhase
