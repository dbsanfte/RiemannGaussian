/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceTermControl
/-! # Actual two-edge incidence term selection from three retained binary powers -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceTerm
open SemiprimeD1StackSourceIncidence SemiprimeD1StackSourceIncidenceEncoding
open SemiprimeD1StackSourceIncidencePrimitives SemiprimeD1StackSourceIncidenceLoopView
open SemiprimeD1StackSourceIncidenceEdges SemiprimeD1StackSourceIncidenceEdgeFinish
open SemiprimeD1StackSourceIncidenceTermControl SemiprimeD1StackProcedureTrace
open SemiprimeD1StackSourceIncidenceSpec (Status edge payload)
/-- Own physical term clock pays two complete classifiers, actual cached-payload copy and finite reads. -/
def termClock (i:Inputs) (lo lf ro rf:List Bool) :Nat :=
  edgeClock i.ids lo ro+edgeClock i.ids lf rf+5*(i.square.length+i.cube.length+i.fourth.length)+20
/-- Complete first edge real call, return and physical two-byte status dispatch. -/
theorem owner_call (i:Inputs) (outer inner lo lf ro rf total:List Bool) :
    ∃q≤edgeClock i.ids lo ro+4,
      Runs program q .ownerCall (bank i outer inner lo lf ro rf [] [] [] [] total)
        (.factorCall (edge i.ids lo ro)) (bank i outer inner lo lf ro rf [] [] [] [] total) :=by
  obtain ⟨q,hq,hr⟩:=edge_in_bank i outer inner lo lf ro rf total .owner
  change q≤edgeClock i.ids lo ro at hq
  change Runs program q _ _ _ (bank i outer inner lo lf ro rf []
    [SemiprimeD1StackSourceIncidenceSpec.possible (edge i.ids lo ro),SemiprimeD1StackSourceIncidenceSpec.drop (edge i.ids lo ro)] [] [] total) at hr
  have h0:=local_edge_call .ownerCall .owner .ownerPossible rfl q _ _ hr
  have h1:=owner_flags i outer inner lo lf ro rf total (edge i.ids lo ro)
  exact ⟨_,by omega,join h0 h1⟩
/-- Complete second edge real call, return and actual finite dispatch retains the first physical outcome. -/
theorem factor_call (i:Inputs) (outer inner lo lf ro rf total:List Bool) (first:Status) :
    ∃q≤edgeClock i.ids lf rf+4,
      Runs program q (.factorCall first) (bank i outer inner lo lf ro rf [] [] [] [] total)
        (.payload first (edge i.ids lf rf)) (bank i outer inner lo lf ro rf [] [] [] [] total) :=by
  obtain ⟨q,hq,hr⟩:=edge_in_bank i outer inner lo lf ro rf total .factor
  change q≤edgeClock i.ids lf rf at hq
  change Runs program q _ _ _ (bank i outer inner lo lf ro rf []
    [SemiprimeD1StackSourceIncidenceSpec.possible (edge i.ids lf rf),SemiprimeD1StackSourceIncidenceSpec.drop (edge i.ids lf rf)] [] [] total) at hr
  have h0:=local_edge_call (.factorCall first) .factor (.factorPossible first) rfl q _ _ hr
  have h1:=factor_flags i outer inner lo lf ro rf total first (edge i.ids lf rf)
  exact ⟨_,by omega,join h0 h1⟩
/-- Every actual outcome branch selects the physically retained source payload or the empty zero word. -/
theorem payload_run (i:Inputs) (outer inner lo lf ro rf total:List Bool) (first second:Status) :
    ∃q≤5*(i.square.length+i.cube.length+i.fourth.length)+4,
      Runs program q (.payload first second) (bank i outer inner lo lf ro rf [] [] [] [] total) .copySum
        (bank i outer inner lo lf ro rf [] [] [] (payload i.square i.cube i.fourth first second) total) :=by
  cases first <;> cases second
  · exact ⟨1,by omega,jump_run (.payload .reject .reject) .copySum _ rfl⟩
  · exact ⟨1,by omega,jump_run (.payload .reject .stable) .copySum _ rfl⟩
  · exact ⟨1,by omega,jump_run (.payload .reject .free) .copySum _ rfl⟩
  · exact ⟨1,by omega,jump_run (.payload .stable .reject) .copySum _ rfl⟩
  · have h:=copy_call (.power .fourth) (.payload .stable .stable) .copySum rfl
      (bank i outer inner lo lf ro rf [] [] [] [] total) rfl rfl
    change Runs program (5*i.fourth.length+4) _ _ _
      (Function.update (bank i outer inner lo lf ro rf [] [] [] [] total) (aux .term) i.fourth) at h
    rw [update_term] at h
    exact ⟨_,by omega,h⟩
  · have h:=copy_call (.power .cube) (.payload .stable .free) .copySum rfl
      (bank i outer inner lo lf ro rf [] [] [] [] total) rfl rfl
    change Runs program (5*i.cube.length+4) _ _ _
      (Function.update (bank i outer inner lo lf ro rf [] [] [] [] total) (aux .term) i.cube) at h
    rw [update_term] at h
    exact ⟨_,by omega,h⟩
  · exact ⟨1,by omega,jump_run (.payload .free .reject) .copySum _ rfl⟩
  · have h:=copy_call (.power .cube) (.payload .free .stable) .copySum rfl
      (bank i outer inner lo lf ro rf [] [] [] [] total) rfl rfl
    change Runs program (5*i.cube.length+4) _ _ _
      (Function.update (bank i outer inner lo lf ro rf [] [] [] [] total) (aux .term) i.cube) at h
    rw [update_term] at h
    exact ⟨_,by omega,h⟩
  · have h:=copy_call (.power .square) (.payload .free .free) .copySum rfl
      (bank i outer inner lo lf ro rf [] [] [] [] total) rfl rfl
    change Runs program (5*i.square.length+4) _ _ _
      (Function.update (bank i outer inner lo lf ro rf [] [] [] [] total) (aux .term) i.square) at h
    rw [update_term] at h
    exact ⟨_,by omega,h⟩
/-- Complete actual two-edge count source, preserving stream positions, all cached inputs and total. -/
theorem term_run (i:Inputs) (outer inner lo lf ro rf total:List Bool) :
    ∃q≤termClock i lo lf ro rf,
      Runs program q .ownerCall (bank i outer inner lo lf ro rf [] [] [] [] total) .copySum
        (bank i outer inner lo lf ro rf [] [] []
          (SemiprimeD1StackSourceIncidenceSpec.term i.ids i.square i.cube i.fourth (lo,lf) (ro,rf)) total) :=by
  obtain ⟨q,hq,h0⟩:=owner_call i outer inner lo lf ro rf total
  obtain ⟨u,hu,h1⟩:=factor_call i outer inner lo lf ro rf total (edge i.ids lo ro)
  obtain ⟨v,hv,h2⟩:=payload_run i outer inner lo lf ro rf total (edge i.ids lo ro) (edge i.ids lf rf)
  refine ⟨_,?_,join (join h0 h1) h2⟩
  unfold termClock
  omega
end RiemannGaussian.SemiprimeD1StackSourceIncidenceTerm
