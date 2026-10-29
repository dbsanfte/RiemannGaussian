/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseCleanup
/-! # Real six-field pair and eight-field coefficient cache drains -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseRegisterClear
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseCalls SemiprimeD1StackNormalizedInverseCleanup
open SemiprimeD1StackProcedureTrace
/-- Exactly the six actual parsed/product fields, retaining the suffix accumulator. -/
def pairSlot (i : Fin 6) : Stack := regRole ⟨i.val,by omega⟩
/-- Physical cache state after the six actual drains. -/
def pairClear (w : Words) : Words :=
  {w with registers:=fun k=>if k.1=.acc then w.registers k else []}
/-- Exact literal six-slot inventory, independently of all runtime words. -/
theorem pair_roles : roles pairSlot=[reg .left false,reg .left true,reg .right false,reg .right true,reg .product false,reg .product true] := by decide
/-- The physical sweep preserves all52 other fields literally. -/
theorem pair_cleared (w : Words) : cleared pairSlot (store w) 6=store (pairClear w) := by
  classical
  funext k
  rw [cleared_full,pair_roles]
  rcases k with k|k
  · simp [reg,store,bank,pairClear]
  · rcases k with ⟨r,den⟩|k
    · cases r <;> cases den <;> simp [reg,store,bank,pairClear]
    · simp [reg,store,bank,pairClear]
/-- Six REAL drains count every old field byte and six actual EOF branches. -/
theorem pair_run (w : Words) :
    ∃q≤6*(mass (store w)+1),Runs program q (ctl (.clearPair 0)) (store w)
      (ctl .decrementA) (store (pairClear w)) := by
  have hc : ∀i:Fin 6,program (ctl (.clearPair i))=.base
      (.pop (pairSlot i) (next (fun j=>ctl (.clearPair j)) (ctl .decrementA) i)
        (ctl (.clearPair i)) (ctl (.clearPair i))) := by
    intro i
    have hh:i.val+1<6 ↔ i.val<6-1 := by omega
    simp only [program,ctl,pairSlot,pairNext,next,hh]
  obtain ⟨q,hq,hr⟩:=sweep (by decide:0<6) pairSlot (fun j=>ctl (.clearPair j)) (ctl .decrementA) hc 5 0 rfl (store w)
  refine ⟨q,by omega,?_⟩
  simpa only [cleared_zero,pair_cleared,show (⟨0,by decide⟩:Fin 6)=0 from Fin.ext rfl] using hr
/-- Every eight-field cache address is a literal static word. -/
theorem all_roles : roles regRole=[reg .left false,reg .left true,reg .right false,reg .right true,
    reg .product false,reg .product true,reg .acc false,reg .acc true] := by decide
/-- Actual whole-register cleanup retains W, array, counters, built prefix and output. -/
theorem registers_cleared (w : Words) : cleared regRole (store w) 8=store {w with registers:=fun _=>[]} := by
  classical
  funext k
  rw [cleared_full,all_roles]
  rcases k with k|k
  · simp [reg,store,bank]
  · rcases k with ⟨r,den⟩|k
    · cases r <;> cases den <;> simp [reg,store,bank]
    · simp [reg,store,bank]
/-- All eight coefficient field drains are actual instructions before the acquired prefix count increases. -/
theorem registers_run (w : Words) :
    ∃q≤8*(mass (store w)+1),Runs program q (ctl (.clearCoefficient 0)) (store w)
      (ctl .bump) (store {w with registers:=fun _=>[]}) := by
  have hc : ∀i:Fin 8,program (ctl (.clearCoefficient i))=.base
      (.pop (regRole i) (next (fun j=>ctl (.clearCoefficient j)) (ctl .bump) i)
        (ctl (.clearCoefficient i)) (ctl (.clearCoefficient i))) := by
    intro i
    have hh:i.val+1<8 ↔ i.val<8-1 := by omega
    simp only [program,ctl,coefficientNext,next,hh]
  obtain ⟨q,hq,hr⟩:=sweep (by decide:0<8) regRole (fun j=>ctl (.clearCoefficient j)) (ctl .bump) hc 7 0 rfl (store w)
  refine ⟨q,by omega,?_⟩
  simpa only [cleared_zero,registers_cleared,show (⟨0,by decide⟩:Fin 8)=0 from Fin.ext rfl] using hr
end RiemannGaussian.SemiprimeD1StackNormalizedInverseRegisterClear
