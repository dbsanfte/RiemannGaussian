/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordTapeRecursivePhase

/-! # Exact actual phase report separation for word/tape child construction
All new child factory clocks remain in the local term. Only recursive answer
reports are separated, after actual positive-context network refinement.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace RiemannGaussian.SemiprimeD1WordTapeRecursiveClock
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveCallTree SemiprimeD1PhysicalRecursiveClock
open SemiprimeD1JetAffineCoefficient (JetRun)
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- Exact one-mode report separation preserves every new word/tape producer report. -/
theorem phaseTerm_clock (next : Context → Network → JetRun) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a) (beta : List ℕ)
    (hp : parent.ctx.Positive) (huM : u ≤ edgeCount parent.net) (hi : i.val<u) :
    (SemiprimeD1WordTapeRecursivePhase.phaseTerm next parent a u t i beta).words=
      (SemiprimeD1WordTapeRecursivePhase.phaseTerm (eraseClock next) parent a u t i beta).words ∧
    (SemiprimeD1WordTapeRecursivePhase.phaseTerm next parent a u t i beta).clock=
      (SemiprimeD1WordTapeRecursivePhase.phaseTerm (eraseClock next) parent a u t i beta).clock+
      ((List.finRange 64).map (fun g =>
        (next (child parent a u t i beta g).ctx (child parent a u t i beta g).net).clock)).sum := by
  let source:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
    parent.net.rows.length 64 a u i.val parent.ctx.precision (arity parent.net.rows) (owner parent.net.rows)
  let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
  let fresh:=SemiprimeD1FreshJetBits.acquireFresh parent.ctx q source.precision
  let current : Context:=⟨q::parent.ctx.axes,source.precision⟩
  have hc : current.Positive := SemiprimeD1WordTapeRecursivePhase.current_positive parent.ctx _ _ _ _ hp huM hi
  unfold SemiprimeD1WordTapeRecursivePhase.phaseTerm
  apply product_map
  · intro g hg
    rfl
  · intro g hg
    let data:=SemiprimeD1ChildWordNetwork.fromSource parent.net source i g parent.ctx [q]
      source.precision fresh t beta
    have he:=SemiprimeD1ChildWordNetwork.fromSource_network parent.net source i g parent.ctx [q]
      source.precision fresh t beta hc
    change data.clock+(next current data.network).clock+5=
      data.clock+0+5+(next current
        (SemiprimeD1ChildNetwork.fromSource parent.net source i g parent.ctx [q]
          source.precision fresh t beta).network).clock
    change data.network=_ at he
    rw [he]
    omega

/-- Literal acquired-mode sum separates only the actual recursive child reports. -/
theorem phaseTotal_clock (next : Context → Network → JetRun) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a)
    (hp : parent.ctx.Positive) (huM : u ≤ edgeCount parent.net) (hi : i.val<u) :
    (SemiprimeD1WordTapeRecursivePhase.phaseTotal next parent a u t i).words=
      (SemiprimeD1WordTapeRecursivePhase.phaseTotal (eraseClock next) parent a u t i).words ∧
    (SemiprimeD1WordTapeRecursivePhase.phaseTotal next parent a u t i).clock=
      (SemiprimeD1WordTapeRecursivePhase.phaseTotal (eraseClock next) parent a u t i).clock+
        modeChildClocks next parent a u t i := by
  unfold SemiprimeD1WordTapeRecursivePhase.phaseTotal modeChildClocks
  apply sum_map
  · intro beta hb
    exact (phaseTerm_clock next parent a u t i beta hp huM hi).1
  · intro beta hb
    exact (phaseTerm_clock next parent a u t i beta hp huM hi).2

/-- Exact report over the original grid/tuple/group call inventory. The new
source, word packet, tape copies and all recopy/setup reports stay in local work. -/
theorem phase_clock (next : Context → Network → JetRun) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (hp : parent.ctx.Positive) (huM : u ≤ edgeCount parent.net) :
    (SemiprimeD1WordTapeRecursivePhase.phase next parent.ctx parent.net a u t).blocks=
      (SemiprimeD1WordTapeRecursivePhase.phase (eraseClock next) parent.ctx parent.net a u t).blocks ∧
    (SemiprimeD1WordTapeRecursivePhase.phase next parent.ctx parent.net a u t).precision=
      (SemiprimeD1WordTapeRecursivePhase.phase (eraseClock next) parent.ctx parent.net a u t).precision ∧
    (SemiprimeD1WordTapeRecursivePhase.phase next parent.ctx parent.net a u t).clock=
      (SemiprimeD1WordTapeRecursivePhase.phase (eraseClock next) parent.ctx parent.net a u t).clock+
      ((phaseChildren parent a u t).map (fun c => (next c.ctx c.net).clock)).sum := by
  dsimp only [SemiprimeD1WordTapeRecursivePhase.phase,phaseChildren]
  split
  · rename_i hi
    let i : Fin a:=⟨_,hi.1⟩
    let source:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
      parent.net.rows.length 64 a u i.val parent.ctx.precision (arity parent.net.rows) (owner parent.net.rows)
    let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
    have ht:=phaseTotal_clock next parent a u t i hp huM hi.2.1
    have hw:=ht.1
    refine ⟨?_,rfl,?_⟩
    · simp only [List.map_map,Function.comp_def]
      change ((List.range q).map (fun j =>
        (SemiprimeD1JetBlockBits.extract parent.ctx j (SemiprimeD1WordTapeRecursivePhase.phaseTotal next parent a u t i).words).words)).toArray=
        ((List.range q).map (fun j =>
        (SemiprimeD1JetBlockBits.extract parent.ctx j (SemiprimeD1WordTapeRecursivePhase.phaseTotal (eraseClock next) parent a u t i).words).words)).toArray
      rw [hw]
    · have hsum : ((source.modes.values.flatMap (fun beta => (List.finRange 64).map
          (child parent a u t i beta))).map (fun c => (next c.ctx c.net).clock)).sum=
        modeChildClocks next parent a u t i := by
        rw [sum_flatMap]
        simp only [List.map_map,Function.comp_def,modeChildClocks,source]
      change _+(SemiprimeD1WordTapeRecursivePhase.phaseTotal next parent a u t i).clock+
        (((List.range q).map (fun j => SemiprimeD1JetBlockBits.extract parent.ctx j
          (SemiprimeD1WordTapeRecursivePhase.phaseTotal next parent a u t i).words)).map (fun block => block.clock)).sum+_ =
        _+(SemiprimeD1WordTapeRecursivePhase.phaseTotal (eraseClock next) parent a u t i).clock+
        (((List.range q).map (fun j => SemiprimeD1JetBlockBits.extract parent.ctx j
          (SemiprimeD1WordTapeRecursivePhase.phaseTotal (eraseClock next) parent a u t i).words)).map (fun block => block.clock)).sum+_+_
      rw [hw,hsum]
      omega
  · simp only [List.map_nil,List.sum_nil,Nat.add_zero,and_self]

/-- Actual retained word/tape phase payload cache, not an external getter. -/
def retained (next : Context → Network → JetRun) (parent : Call) (a u : ℕ) : Array PhaseRun :=
  ((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
    (SemiprimeD1WordTapeRecursivePhase.phase next parent.ctx parent.net a u)).toArray

/-- Erasing child reports preserves the actual retained payload blocks. -/
theorem retained_blocks (next : Context → Network → JetRun) (parent : Call) (a u : ℕ)
    (hp : parent.ctx.Positive) (huM : u ≤ edgeCount parent.net) :
    (retained next parent a u).map PhaseRun.blocks=
      (retained (eraseClock next) parent a u).map PhaseRun.blocks := by
  apply Array.toList_inj.mp
  simp only [retained,Array.toList_map,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro t ht
  exact (phase_clock next parent a u t hp huM).1

/-- Every grid point and repeated tuple/group child keeps its literal multiplicity. -/
theorem phases_clock (next : Context → Network → JetRun) (parent : Call) (a u : ℕ)
    (hp : parent.ctx.Positive) (huM : u ≤ edgeCount parent.net) :
    (((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
      (SemiprimeD1WordTapeRecursivePhase.phase next parent.ctx parent.net a u)).map PhaseRun.clock).sum=
    (((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
      (SemiprimeD1WordTapeRecursivePhase.phase (eraseClock next) parent.ctx parent.net a u)).map PhaseRun.clock).sum+
    (((List.finRange (SemiprimeD1WireKernelOriginal.size a)).flatMap
      (phaseChildren parent a u)).map (fun c => (next c.ctx c.net).clock)).sum := by
  rw [sum_flatMap]
  simp only [List.map_map,Function.comp_def]
  have h : ∀t∈List.finRange (SemiprimeD1WireKernelOriginal.size a),
      (SemiprimeD1WordTapeRecursivePhase.phase next parent.ctx parent.net a u t).clock=
      (SemiprimeD1WordTapeRecursivePhase.phase (eraseClock next) parent.ctx parent.net a u t).clock+
      ((phaseChildren parent a u t).map (fun c => (next c.ctx c.net).clock)).sum := by
    intro t ht
    exact (phase_clock next parent a u t hp huM).2.2
  rw [show (List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
      (fun t => (SemiprimeD1WordTapeRecursivePhase.phase next parent.ctx parent.net a u t).clock)=
      (List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
      (fun t => (SemiprimeD1WordTapeRecursivePhase.phase (eraseClock next) parent.ctx parent.net a u t).clock+
        ((phaseChildren parent a u t).map (fun c => (next c.ctx c.net).clock)).sum) from List.map_congr_left h]
  exact List.sum_map_add

end RiemannGaussian.SemiprimeD1WordTapeRecursiveClock
