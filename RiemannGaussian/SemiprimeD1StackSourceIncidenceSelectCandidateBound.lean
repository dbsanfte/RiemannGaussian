/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectCandidate
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectResources
import RiemannGaussian.SemiprimeD1StackSourceIncidenceBounds
/-! # Fixed polynomial actual candidate-step budget in physical acquired bytes
The query allowance comes from its SAME closed47-role source. Actual stored
prefix/tag bytes and binary accumulator widths give the remaining bounds; no
old native score/report clock or supplied evaluator allowance is transported.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectCandidateBound
open SemiprimeD1StackSourceIncidenceSelectCandidate SemiprimeD1StackSourceIncidenceSelectResources
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace B
export SemiprimeD1StackSourceIncidenceBounds (pow_mono)
end B
/-- Actual pair-record tags pay the number of occurrences independently of key values and padding. -/
theorem records_count_le (rows:List (List Bool×List Bool)) :
    rows.length ≤ (SemiprimeD1StackOwnerLookup.records rows []).length :=by
  rw [SemiprimeD1StackOwnerLookupBounds.records_length]
  simp only [List.length_nil]
  omega
/-- The actual binary score width is cubic in the acquired source/power byte bound, regardless of selected prefix values. -/
theorem scoreWord_uniform (ids:List (List Bool)) (id:List Bool) (rows:List (List Bool×List Bool))
    (square cube fourth:List Bool) (S:Nat)
    (hd:(SemiprimeD1StackOwnerLookup.records rows []).length+square.length+cube.length+fourth.length ≤ S) :
    (scoreWord ids id rows square cube fourth).length ≤ (S+1)^3 :=by
  have hM:rows.length ≤ S:=(records_count_le rows).trans (by omega)
  have hp:square.length+cube.length+fourth.length+1 ≤ S+1:=by omega
  have hs:=SemiprimeD1StackSourceIncidenceSpec.total_length (id::ids) square cube fourth rows
  change (scoreWord ids id rows square cube fourth).length ≤ _ at hs
  calc
    _ ≤ rows.length*rows.length*(square.length+cube.length+fourth.length+1):=hs
    _ ≤ S*S*(S+1):=Nat.mul_le_mul (Nat.mul_le_mul hM hM) hp
    _ ≤ (S+1)*(S+1)*(S+1):=Nat.mul_le_mul_right _ (Nat.mul_self_le_mul_self (by omega : S ≤ S+1))
    _=(S+1)^3:=by ring
/-- A single actual temporary candidate step has a fixed polynomial cap, chosen before every original graph and alphabet. -/
theorem candidateBound_uniform (ids:List (List Bool)) (id colour:List Bool)
    (rows:List (List Bool×List Bool)) (square cube fourth oldID oldScore:List Bool) (S:Nat)
    (hn:ids.length+1 ≤ S) (hw:∀word∈ids,word.length ≤ S)
    (hi:id.length+colour.length ≤ S) (hb:oldID.length ≤ S) (hs:oldScore.length ≤ (S+1)^3)
    (hd:(SemiprimeD1StackOwnerLookup.records rows []).length+square.length+cube.length+fourth.length ≤ S) :
    candidateBound ids id colour (vectorBits ids) rows square cube fourth oldID oldScore ≤
      100000000000000000000*(S+1)^12 :=by
  let i:=SemiprimeD1StackSourceIncidenceSelectEvaluate.scoreInputs ids id (vectorBits ids) rows square cube fourth
  have hcw:∀word∈id::ids,word.length ≤ S:=by
    intro word hword
    rcases List.mem_cons.mp hword with rfl|hword
    · omega
    · exact hw word hword
  have hc:=cache_uniform (id::ids) ids id S (by simpa only [List.length_cons] using hn) (by omega)
    (by omega) hcw hw
  have h12:S+1 ≤ (S+1)^12:=by simpa only [pow_one] using B.pow_mono (S+1) (by omega) 1 12 (by decide)
  have h02:1 ≤ (S+1)^2:=by simpa only [pow_zero] using B.pow_mono (S+1) (by omega) 0 2 (by decide)
  have h1two:S+1 ≤ (S+1)^2:=by simpa only [pow_one] using B.pow_mono (S+1) (by omega) 1 2 (by decide)
  have h312:(S+1)^3 ≤ (S+1)^12:=B.pow_mono (S+1) (by omega) 3 12 (by decide)
  have hsize:SemiprimeD1StackSourceIncidenceEncoding.inputSize i ≤ 21*(S+1)^2:=by
    change (SemiprimeD1StackOwnerLookup.records rows []).length+
      SemiprimeD1StackSourceEnvironmentBounds.cacheSize (id::ids) id [] (vectorBits ids)+
      square.length+cube.length+fourth.length ≤ _
    omega
  have hquery:SemiprimeD1StackSourceIncidenceExecution.runBound i ≤ 1000000000000000000*(S+1)^12:=by
    calc
      _ ≤ 1000000000*(SemiprimeD1StackSourceIncidenceEncoding.inputSize i)^6:=
        SemiprimeD1StackSourceIncidenceBounds.runBound_le i
      _ ≤ 1000000000*(21*(S+1)^2)^6:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 6)
      _=(1000000000*21^6)*(S+1)^12:=by ring
      _ ≤ 1000000000000000000*(S+1)^12:=Nat.mul_le_mul_right _ (by norm_num)
  have hk:=SemiprimeD1StackSourceEnvironmentEncoding.variableKey_length ids.length
  have hnew:=scoreWord_uniform ids id rows square cube fourth S hd
  unfold candidateBound
  dsimp only [i] at hquery
  omega
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectCandidateBound
