/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateExecution
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateRowBounds
/-! # Same physical whole-source quartic clock
All actual nested scans/copies/arithmetic/parsers/logs/returns and cleanup are
charged. Neither a native coordinate clock nor a subtree runtime is substituted.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinateBounds
open SemiprimeD1StackRecoveryCoordinate SemiprimeD1StackRecoveryCoordinateEncoding
open SemiprimeD1StackRecoveryCoordinateCapacities SemiprimeD1StackRecoveryCoordinateRowBounds
open SemiprimeD1StackRecoveryCoordinatePhase SemiprimeD1StackRecoveryCoordinateExecution
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace Loop
export SemiprimeD1StackRecoveryCoordinateLoop (budget)
end Loop
/-- Actual physical source operand bytes, including retained binary query padding. -/
def resource (phases:Phases) (key:List Bool):Nat:=(tape phases).length+key.length
/-- Sum of the actual whole phase clocks, independent of prior outer history. -/
def phaseSum (key:List Bool):Phases→Nat
  | []=>0
  | blocks::rest=>phaseTime key blocks+phaseSum key rest
/-- Exact actual outer-loop cost: real phase steps and one final physical history reverse. -/
theorem budget_eq (phases:Phases) (key history:List Bool):
    Loop.budget key phases history=phaseSum key phases+
      2*(chunks ((columns phases key).map vectorBits)).length+2*history.length+4:=by
  induction phases generalizing history with
  | nil=>
    simp only [Loop.budget,phaseSum,columns,List.map_nil,chunks,List.foldr_nil,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
  | cons blocks phases ih=>
    have hr:(columns (blocks::phases) key).map vectorBits=phaseRow key blocks::(columns phases key).map vectorBits:=rfl
    rw [Loop.budget,ih,phaseSum,hr,chunks_cons_length,List.length_append,List.length_reverse]
    omega
/-- Actual phase-clock sum has the same cubic at each actual input occurrence. -/
theorem phase_sum_bound (phases:Phases) (key:List Bool) (L:Nat)
    (hl:∀blocks∈phases,(vectorBits (blocks.map vectorBits)).length ≤L):
    phaseSum key phases ≤1000000000*phases.length*(L+key.length+1)^3:=by
  induction phases with
  | nil=>simp only [phaseSum,List.length_nil,Nat.mul_zero,Nat.zero_mul,Nat.le_refl]
  | cons blocks phases ih=>
    have h0:=phase_time key blocks L (hl blocks (List.mem_cons_self))
    have h1:=ih (fun bs hbs=>hl bs (List.mem_cons_of_mem blocks hbs))
    simp only [phaseSum,List.length_cons,Nat.mul_add,Nat.add_mul,Nat.mul_one]
    omega
/-- One fixed quartic bound in the two real input tape lengths. -/
def runBound (phases:Phases) (key:List Bool):Nat:=1000000000000*(resource phases key+1)^4
/-- SAME actual whole source clock lies below its own fixed input-byte polynomial. -/
theorem timeBound_le (phases:Phases) (key:List Bool):timeBound phases key ≤runBound phases key:=by
  let L:=(tape phases).length
  let S:=L+key.length+1
  have hs:=phase_sum_bound phases key L (fun blocks hb=>phase_length phases blocks hb)
  have hn:phases.length ≤S:=(phase_count phases).trans (by dsimp [L,S];omega)
  have hsum:phaseSum key phases ≤1000000000*S^4:=by
    calc
      _ ≤1000000000*phases.length*S^3:=hs
      _ ≤1000000000*S*S^3:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 1000000000 hn)
      _=1000000000*S^4:=by ring
  have hout:(chunks ((columns phases key).map vectorBits)).length ≤L:=by
    have h0:=result_length phases key
    have h1:=chunks_length ((columns phases key).map vectorBits)
    change (chunks ((columns phases key).map vectorBits)).length+1=(result phases key).length at h1
    dsimp only [L]
    omega
  have hlin:S ≤S^4:=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by dsimp [S];omega:1 ≤S) (by decide:1 ≤4)
  have hL:L+1 ≤S:=by dsimp [S];omega
  unfold timeBound bodyTime runBound resource
  change 5*L+5+Loop.budget key phases []+1 ≤1000000000000*S^4
  rw [budget_eq]
  simp only [List.length_nil,Nat.mul_zero,Nat.add_zero]
  omega
/-- Actual whole source executes within the bound for the same fixed physical program. -/
theorem source_run_bounded (phases:Phases) (key:List Bool):
    ∃q ≤runBound phases key,SemiprimeD1StackCalls.run program q (initial (tape phases) key)=some (done phases key):=
  ⟨timeBound phases key,timeBound_le phases key,source_run phases key⟩
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinateBounds
