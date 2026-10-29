import RiemannGaussian.SemiprimeD1HybridCorrectness
import RiemannGaussian.SemiprimeD1WordTapeFrameBudget

/-! Active acquired frame bounds for the concrete boundary recursion. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace RiemannGaussian.SemiprimeD1HybridActiveBudget
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveCallTree SemiprimeD1WordTapeRecursivePhase
open SemiprimeD1WordTapePhaseBudget
open SemiprimeD1PhysicalRecursiveClock (eraseClock)
open SemiprimeD1JetAffineCoefficient (JetRun)
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire
/-- One actual erased mode product retains all64 child construction reports,
including their repeated source/header acquisitions. Structural run canonicality
discharges the physical vector input caps internally. -/
theorem hybrid_term_clock (s fuel : ℕ) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a) (beta : List ℕ)
    (hpos : parent.ctx.Positive) (huM : u ≤ edgeCount parent.net) (hiu : i.val < u) :
    (phaseTerm (eraseClock (SemiprimeD1HybridRecursiveCounter.run s fuel (parent.depth+1)))
      parent a u t i beta).clock ≤ childClocks parent a u t i beta+
      64*(SemiprimeD1LeafCounterBounds.productBudget (current parent a u i)+8)+
      SemiprimeD1LeafCounterBounds.oneBudget (current parent a u i) := by
  unfold phaseTerm
  apply (product_clock _ _ ?_).trans
  · simp only [eraseClock,List.map_map,Function.comp_def,List.length_map,List.length_finRange,
      Nat.add_zero]
    simp only [show ∀ x : ℕ, x+0+5=x+5 from fun x => by omega]
    rw [List.sum_map_add]
    simp only [List.map_const',List.length_finRange,List.sum_const_nat]
    unfold childClocks current
    dsimp only
    omega
  · intro value hv
    obtain ⟨g,hg,rfl⟩:=List.mem_map.mp hv
    exact SemiprimeD1HybridRecursiveCounter.run_good _ _ _ _ _
      (SemiprimeD1WordTapeRecursivePhase.current_positive parent.ctx _ _ _ _ hpos huM hiu)

/-- All acquired-mode sums retain every repeated actual child constructor and
have a source-derived physical vector overhead, without child-cost advice. -/
theorem hybrid_total_clock (s fuel : ℕ) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a)
    (hpos : parent.ctx.Positive) (huM : u ≤ edgeCount parent.net) (hiu : i.val < u) :
    let source:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
      parent.net.rows.length 64 a u i.val parent.ctx.precision
      (arity parent.net.rows) (owner parent.net.rows)
    (phaseTotal (eraseClock (SemiprimeD1HybridRecursiveCounter.run s fuel (parent.depth+1)))
      parent a u t i).clock ≤
      (source.modes.values.map (childClocks parent a u t i)).sum+
      source.modes.values.length*modeOverhead (current parent a u i)+
      (current parent a u i).rank+1 := by
  let src:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
    parent.net.rows.length 64 a u i.val parent.ctx.precision
    (arity parent.net.rows) (owner parent.net.rows)
  have h:=sumRuns_map_clock (current parent a u i) src.modes.values
    (phaseTerm (eraseClock (SemiprimeD1HybridRecursiveCounter.run s fuel (parent.depth+1)))
      parent a u t i)
    (childClocks parent a u t i)
    (64*(SemiprimeD1LeafCounterBounds.productBudget (current parent a u i)+8)+
      SemiprimeD1LeafCounterBounds.oneBudget (current parent a u i))
    (by
      intro beta hb
      have h:=phaseTerm_good
        (eraseClock (SemiprimeD1HybridRecursiveCounter.run s fuel (parent.depth+1))) parent a u t i beta
      exact ⟨h.1,fun w hw => (h.2 w hw).2⟩)
    (by
      intro beta hb
      simpa only [Nat.add_assoc] using hybrid_term_clock s fuel parent a u t i beta hpos huM hiu)
  simpa only [phaseTotal,current,modeOverhead,src,Nat.add_assoc] using h

/-- The actual erased phase has a literal nonrecursive original-data bound.
All repeated source construction remains visible for the later uniform envelope. -/
theorem hybrid_phase_clock (s fuel : ℕ) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (hpos : parent.ctx.Positive) (huM : u ≤ edgeCount parent.net) :
    (SemiprimeD1WordTapeRecursivePhase.phase (eraseClock (SemiprimeD1HybridRecursiveCounter.run s fuel (parent.depth+1)))
      parent.ctx parent.net a u t).clock ≤ phaseBudget parent a u t := by
  dsimp only [SemiprimeD1WordTapeRecursivePhase.phase,phaseBudget]
  split
  · rename_i hi
    let i : Fin a:=⟨_,hi.1⟩
    let source:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
      parent.net.rows.length 64 a u i.val parent.ctx.precision
      (arity parent.net.rows) (owner parent.net.rows)
    let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
    let next:=eraseClock (SemiprimeD1HybridRecursiveCounter.run s fuel (parent.depth+1))
    have ht:=hybrid_total_clock s fuel parent a u t i hpos huM hi.2.1
    have hg:=phaseTotal_good next parent a u t i
    have hb:=blocks_clock parent q source.precision (phaseTotal next parent a u t i) hg
    have hf:=SemiprimeD1FreshJetBits.acquireFresh_clock parent.ctx q source.precision
    have ht' : (phaseTotal next parent a u t i).clock ≤
        (source.modes.values.map (childClocks parent a u t i)).sum+
        source.modes.values.length*modeOverhead (current parent a u i)+
        (current parent a u i).rank+1 := ht
    change (((List.range q).map (fun j => SemiprimeD1JetBlockBits.extract parent.ctx j
        (phaseTotal next parent a u t i).words)).map (fun block => block.clock)).sum ≤
        q*(parent.ctx.rank*(3*(current parent a u i).rank+3*source.precision+5)+5*parent.ctx.rank+5) at hb
    let fixedStages:=(SemiprimeD1RecoveryWeightRun.geometry a t.val).work+
      (SemiprimeD1RecoveryScalarRun.orderFuel (SemiprimeD1RecoveryWeightRun.geometry a t.val).size
        (SemiprimeD1RecoveryWeightRun.geometry a t.val).point.natAbs).work+source.work
    let allowance:=10*(edgeCount parent.net+a+u+i.val+q+source.modes.values.length+1)
    change fixedStages+(SemiprimeD1FreshJetBits.acquireFresh parent.ctx q source.precision).clock+
        (phaseTotal next parent a u t i).clock+
        (((List.range q).map (fun j => SemiprimeD1JetBlockBits.extract parent.ctx j
          (phaseTotal next parent a u t i).words)).map (fun block => block.clock)).sum+allowance ≤
      fixedStages+(9*source.precision+3*(q*parent.ctx.rank)+10)+
        ((source.modes.values.map (childClocks parent a u t i)).sum+
          source.modes.values.length*modeOverhead (current parent a u i)+(current parent a u i).rank+1)+
        q*(parent.ctx.rank*(3*(current parent a u i).rank+3*source.precision+5)+5*parent.ctx.rank+5)+allowance
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left hf fixedStages) ht') hb) allowance
  · exact le_rfl


/-- Active local work retains the unchanged acquired phase budget, with the
new run's own canonically encoded child words and erased child reports. -/
theorem active_localWork_le (s fuel : Nat) (parent : Call) (hpos : parent.ctx.Positive)
    (ha : activeTest s (SemiprimeD1PackingReady.logarithm s) parent.depth
      (edgeCount parent.net) = true) :
    SemiprimeD1HybridRecursiveCounter.localWork s (fuel+1) parent ≤
      SemiprimeD1WordTapeFrameBudget.budget s parent := by
  change (SemiprimeD1HybridRecursiveKernel.frame SemiprimeD1BoundaryLeaf.checked s parent
    (eraseClock (SemiprimeD1HybridRecursiveCounter.run s fuel (parent.depth+1)))).clock ≤ _
  rw [SemiprimeD1HybridRecursiveKernel.frame_active _ _ _ _ ha]
  dsimp only [SemiprimeD1WordTapeRecursiveCounter.frame,SemiprimeD1WordTapeFrameBudget.budget]
  rw [ha]
  simp only [ite_true]
  let lam := SemiprimeD1PackingReady.logarithm s
  let a := SemiprimeD1Schedule.exponent lam parent.depth
  let u := SemiprimeD1Schedule.levels lam parent.depth
  let next := eraseClock (SemiprimeD1HybridRecursiveCounter.run s fuel (parent.depth+1))
  have hu : u ≤ edgeCount parent.net := ((activeTest_correct _ _ _ _).mp ha).2.2
  have hp : (((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
      (SemiprimeD1WordTapeRecursivePhase.phase next parent.ctx parent.net a u)).map PhaseRun.clock).sum ≤
      ((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map (phaseBudget parent a u)).sum := by
    simp only [List.map_map,Function.comp_def]
    apply List.sum_le_sum
    intro t _
    exact hybrid_phase_clock s fuel parent a u t hpos hu
  have hr := SemiprimeD1WordTapeFrameBudget.recoveries_clock next parent a u hpos hu
  dsimp only at hr
  change _+_+_+_ ≤ _+_+_+_
  simp only [List.length_map,List.length_finRange]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hp hr) _) _

end RiemannGaussian.SemiprimeD1HybridActiveBudget
