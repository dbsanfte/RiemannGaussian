/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersLoop
/-! # Actual retained heap, unary references and complete-bank cleanup mass -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseParametersResources
open SemiprimeD1StackRootPhaseParameters SemiprimeD1StackRootPhaseParametersEncoding
open SemiprimeD1StackRootPhaseParametersRows SemiprimeD1StackRootPhaseParametersLoop
open SemiprimeSourceHistogramKeyBits (frame)
/-- All126 retained root/grid data-cell bytes are counted, not silently erased. -/
def rootMass (root:G.Stack→List Bool) : Nat :=∑k:G.Stack,(root k).length
/-- Actual total stopped48-word mass, including all rejected and empty output fields. -/
def stoppedMass (a u edges:Nat) (t:List Bool) : Nat :=∑k:P.Stack,(stopped a u edges t k).length
/-- The serializer reads exactly the actual stopped bank mass. -/
theorem phaseMass_eq (root:G.Stack→List Bool) (a u edges:Nat) (t tail hp:List Bool) (n:Nat) (hist:List Bool) :
    SemiprimeD1StackRootPhaseParametersSerialize.phaseMass
      (view root (stopped a u edges t) tail t [] hp (List.replicate n true) [] hist [])=stoppedMass a u edges t :=rfl
/-- Every actual reference vector row is paid at its actual word length. -/
theorem stream_length_le (rows:List (List Bool)) (W:Nat) (hw:∀w∈rows,w.length ≤ W) :
    (stream rows).length ≤ rows.length*(2*W+2) :=by
  induction rows with
  | nil=>simp only [stream,List.foldr_nil,List.length_nil,Nat.zero_mul,le_refl]
  | cons w ws ih=>
    have h0:=hw w (List.mem_cons_self)
    have h1:=ih (fun v hv=>hw v (List.mem_cons_of_mem w hv))
    change (true::frame w (stream ws)).length ≤ (w::ws).length*(2*W+2)
    simp only [List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length] at *
    nlinarith
/-- Actual unary reference words retain their acquired ordinal lengths. -/
theorem references_length (n:Nat) : (references n).length=n :=by simp only [references,List.length_map,List.length_range]
/-- Every physical allocation reference is at most the actual accumulated counter. -/
theorem references_word (n:Nat) (word:List Bool) (hw:word∈references n) : word.length ≤ n :=by
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hw
  have hlt:=List.mem_range.mp hi
  simp only [List.length_replicate]
  omega
/-- Ordered reference history has quadratic byte mass, with every unary ordinal paid. -/
theorem references_stream_le (n:Nat) : (stream (references n)).length ≤ n*(2*n+2) :=by
  simpa only [references_length] using stream_length_le (references n) n (references_word n)
/-- Physical heap framing visits actual records once and adds one delimiter per allocation. -/
theorem heap_fold_bound (rows:List (List Bool)) (seed:List Bool) (R:Nat)
    (hw:∀w∈rows,w.length ≤ R) :
    (rows.foldl (fun bytes word=>frame word bytes) seed).length ≤ seed.length+rows.length*(2*R+1) :=by
  induction rows generalizing seed with
  | nil=>simp only [List.foldl_nil,List.length_nil,Nat.zero_mul,Nat.add_zero,le_refl]
  | cons w ws ih=>
    have h0:=hw w (List.mem_cons_self)
    have h1:=ih (frame w seed) (fun v hv=>hw v (List.mem_cons_of_mem w hv))
    change (ws.foldl (fun bytes word=>frame word bytes) (frame w seed)).length ≤ seed.length+(w::ws).length*(2*R+1)
    rw [SemiprimeSourceHistogramKeyBits.frame_length] at h1
    simp only [List.length_cons]
    nlinarith
/-- All acquired cached record bytes, plus every physical delimiter, remain charged. -/
theorem heap_bound (cached:List (List Bool)) (R:Nat) (hw:∀w∈cached,w.length ≤ R) :
    (SemiprimeD1StackHeapAllocate.heapBytes cached).length ≤ cached.length*(2*R+1) :=by
  simpa only [SemiprimeD1StackHeapAllocate.heapBytes,List.length_nil,Nat.zero_add] using heap_fold_bound cached [] R hw
/-- Full cleanup data mass is bounded from the ACTUAL retained words and counters.
The heap and reference histories accumulate, and their ordinal scan costs remain. -/
theorem logged_mass_le (root:G.Stack→List Bool) (a u edges:Nat) (t tail hp:List Bool) (n K R:Nat)
    (hR:1 ≤ R) (hn:n ≤ K) (hK:K ≤ R) (hroot:rootMass root ≤ R)
    (hphase:stoppedMass a u edges t ≤ R) (ht:t.length ≤ R) (htail:tail.length ≤ R)
    (hrecord:(record a u edges t).length ≤ R) (hheap:hp.length ≤ n*(2*R+1)) :
    SemiprimeD1StackRootPhaseParametersCleanup.mass
      (logged root a u edges t tail hp n (stream (references n)).reverse) ≤ 1880*(K+1)*R :=by
  have hcap:R ≤ 10*(K+1)*R:=by nlinarith
  have hnext:(nextHistory n (stream (references n)).reverse).length ≤ 6*(K+1)*R:=by
    rw [nextHistory_references]
    simp only [List.length_reverse]
    have h:=references_stream_le (n+1)
    have hprod:=Nat.mul_le_mul (show n+1 ≤ K+1 by omega) (show 2*(n+1)+2 ≤ 6*R by omega)
    calc
      _ ≤ (n+1)*(2*(n+1)+2):=h
      _ ≤ (K+1)*(6*R):=hprod
      _=_:=by ring
  have hword:∀k:Stack,((logged root a u edges t tail hp n (stream (references n)).reverse) k).length ≤ 10*(K+1)*R:=by
    intro k
    rcases k with k|k
    · exact (Finset.single_le_sum (f:=fun k:G.Stack=>(root k).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)).trans (hroot.trans hcap)
    · rcases k with k|k
      · exact (Finset.single_le_sum (f:=fun k:P.Stack=>(stopped a u edges t k).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)).trans (hphase.trans hcap)
      · cases k <;> simp only [logged,view,data,work,Sum.elim_inr,List.length_nil,List.length_replicate]
        all_goals first | exact Nat.zero_le _ | exact htail.trans hcap | exact ht.trans hcap | exact hrecord.trans hcap | skip
        · rw [SemiprimeSourceHistogramKeyBits.frame_length]
          have hmul:=Nat.mul_le_mul_right (2*R+1) hn
          nlinarith
        · nlinarith
        · nlinarith
        · nlinarith
  unfold SemiprimeD1StackRootPhaseParametersCleanup.mass
  calc
    _ ≤ ∑_k:Stack,10*(K+1)*R:=Finset.sum_le_sum (fun k _=>hword k)
    _=188*(10*(K+1)*R):=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
    _=_:=by ring
/-- Actual whole-row budget is linear in retained mass and in the acquired
ordinal/heap widths; no old report or expected clock is transported. -/
theorem rowBound_le (root:G.Stack→List Bool) (a u edges:Nat) (t tail hp:List Bool) (n K R:Nat)
    (hR:1 ≤ R) (hn:n ≤ K) (hK:K ≤ R) (hroot:rootMass root ≤ R)
    (ha:a ≤ R) (hu:u ≤ R) (hm:edges ≤ R) (ht:t.length ≤ R) (htail:tail.length ≤ R)
    (hclock:SemiprimeD1StackPhaseWorkingPrecisionExecution.runBound a u edges t [false,true] ≤ R)
    (hphase:stoppedMass a u edges t ≤ R) (hrecord:(record a u edges t).length ≤ R)
    (hheap:hp.length ≤ n*(2*R+1)) :
    rowBound root a u edges t tail hp n (stream (references n)).reverse ≤ 10^8*(K+1)*R :=by
  have hc:=logged_mass_le root a u edges t tail hp n K R hR hn hK hroot hphase ht htail hrecord hheap
  unfold rowBound
  rw [phaseMass_eq]
  have hnR:n ≤ R:=hn.trans hK
  have hprod:R ≤ (K+1)*R:=by nlinarith
  nlinarith
end RiemannGaussian.SemiprimeD1StackRootPhaseParametersResources
