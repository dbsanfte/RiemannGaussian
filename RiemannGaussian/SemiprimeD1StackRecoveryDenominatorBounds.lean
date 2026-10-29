/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorExecution
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorCapacities
import RiemannGaussian.SemiprimeD1StackWordFitBounds
/-! # Own fixed quartic actual row/template source clock
All row fields, raw product padding, parser drains, complete multiplier traces,
real returns and the final actual fit are paid by actual input byte lengths.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryDenominatorBounds
open SemiprimeD1StackRecoveryDenominator SemiprimeD1StackRecoveryDenominatorEncoding
open SemiprimeD1StackRecoveryDenominatorLoop SemiprimeD1StackRecoveryDenominatorExecution
open SemiprimeD1StackRecoveryDenominatorCapacities
namespace O
export SemiprimeD1StackRecoveryDenominatorOperators (multiplyTime)
end O
/-- Actual denominator-first multiplier call, including its real outer return. -/
theorem multiply_time (xs ys:List Bool):O.multiplyTime xs ys ≤1000*(xs.length+ys.length+2)^3+1:=by
  have h:=SemiprimeD1StackMultiplierExecution.source_time xs ys
  have h0:=SemiprimeD1StackMultiplierExecution.timeBound_le_cube xs.length ys.length
  unfold O.multiplyTime
  omega
/-- Actual row parser/drain and full-product step has a fixed cubic physical-byte bound. -/
theorem row_time (r:Row) (acc:List Bool) (L:Nat) (hr:fieldMass r ≤L) (ha:acc.length ≤2*L+1):
    rowTime r acc ≤100000*(L+1)^3:=by
  have hd:=denominator_le r
  have hm:=multiply_time (r 4) acc
  have hb:(r 4).length+acc.length+2 ≤3*(L+1):=by omega
  have hpow:( (r 4).length+acc.length+2)^3 ≤27*(L+1)^3:=by
    simpa only [Nat.mul_pow,show (3:Nat)^3=27 from rfl] using Nat.pow_le_pow_left hb 3
  have hl:L+1 ≤(L+1)^3:=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1 ≤L+1) (by decide:1 ≤3)
  unfold rowTime SemiprimeD1StackRecoveryDenominatorFields.time
  unfold fieldMass at hr
  omega
/-- SAME finite loop clock over each actually parsed row, keeping raw padding linear. -/
theorem budget_cap (rs:List Row) (acc widthTemplate:List Bool) (seen:Bool) (L cap:Nat)
    (hc:acc.length+2*denominatorMass rs ≤cap) (hcap:cap ≤2*L+1)
    (hr:∀r∈rs,fieldMass r ≤L):
    budget widthTemplate seen rs acc ≤100000*rs.length*(L+1)^3+cap+10*widthTemplate.length+10:=by
  induction rs generalizing acc seen with
  | nil=>
    have hf:=SemiprimeD1StackWordFitBounds.totalTime_le acc widthTemplate
    simp only [denominatorMass,List.map_nil,List.sum_nil,Nat.mul_zero,Nat.add_zero] at hc
    cases seen <;> simp only [budget,Bool.false_eq_true,ite_false,ite_true,List.length_nil,Nat.mul_zero,Nat.zero_mul,Nat.zero_add] <;> omega
  | cons r rs ih=>
    have hm:=SemiprimeBitArithmetic.mulBits_length (r 4) acc
    have hn:(SemiprimeBitArithmetic.mulBits (r 4) acc).bits.length+2*denominatorMass rs ≤cap:=by
      simp only [denominatorMass,List.map_cons,List.sum_cons] at hc ⊢
      omega
    have ht:=ih (SemiprimeBitArithmetic.mulBits (r 4) acc).bits true hn (fun s hs=>hr s (List.mem_cons_of_mem r hs))
    have hd:=row_time r acc L (hr r (List.mem_cons_self)) (by omega)
    simp only [budget,List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_mul]
    omega
/-- Actual two-input byte resource; no count or product answer is supplied. -/
def resource (rs:List Row) (widthTemplate:List Bool):Nat:=(tape rs).length+widthTemplate.length
/-- Fixed coefficient and degree before every possible physical input. -/
def runBound (rs:List Row) (widthTemplate:List Bool):Nat:=1000000000000*(resource rs widthTemplate+1)^4
/-- SAME whole actual source clock, including copies, all row iterations, final fit and halt. -/
theorem timeBound_le (rs:List Row) (widthTemplate:List Bool):timeBound rs widthTemplate ≤runBound rs widthTemplate:=by
  let L:=(tape rs).length
  let S:=resource rs widthTemplate+1
  have hm:=denominator_mass_tape rs
  have hc:1+2*denominatorMass rs ≤2*L+1:=by dsimp [L];omega
  have hr:∀r∈rs,fieldMass r ≤L:=fun r he=>(field_mass_le rs r he).trans (payload_le_tape rs)
  have hb:=budget_cap rs [true] widthTemplate false L (1+2*denominatorMass rs) (by simp) hc hr
  have hn:=rows_length rs
  have hs:1 ≤S:=by dsimp [S];omega
  have hl:L+1 ≤S:=by dsimp [L,S,resource];omega
  have hpow:(L+1)^4 ≤S^4:=Nat.pow_le_pow_left hl 4
  have hterms:rs.length*(L+1)^3 ≤S^4:=by
    calc
      _ ≤(L+1)*(L+1)^3:=Nat.mul_le_mul_right _ (by dsimp [L];omega)
      _=(L+1)^4:=by ring
      _ ≤S^4:=hpow
  have hbase:S ≤S^4:=by simpa only [pow_one] using Nat.pow_le_pow_right hs (by decide:1 ≤4)
  have hlS:L+widthTemplate.length+1=S:=rfl
  unfold timeBound bodyTime
  change _ ≤1000000000000*S^4
  have hscaled:=Nat.mul_le_mul_left 100000 hterms
  dsimp [L] at hb hlS hc hscaled
  simp only [Nat.mul_assoc] at hb
  omega
/-- The actual parameterless two-input source halts within its own uniform quartic input-byte clock. -/
theorem source_run_bounded (rs:List Row) (widthTemplate:List Bool):
    ∃q ≤runBound rs widthTemplate,SemiprimeD1StackCalls.run program q (initial (tape rs) widthTemplate)=some (done rs widthTemplate):=
  ⟨timeBound rs widthTemplate,timeBound_le rs widthTemplate,source_run rs widthTemplate⟩
end RiemannGaussian.SemiprimeD1StackRecoveryDenominatorBounds
