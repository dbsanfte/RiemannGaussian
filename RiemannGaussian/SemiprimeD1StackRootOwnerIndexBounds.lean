/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootNetworkRecordsResources
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexBounds
import RiemannGaussian.SemiprimeD1StackRootOwnerIndexExecution
/-! # Own whole-root/index source clock from actual acquired input bytes
The root source pays both retained input words to the physical index. Its
own bound is squared after the actual root/output/count trace is charged.
No native graph report or supplied owner/count answer enters these bounds.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootOwnerIndexBounds
namespace RC
export SemiprimeD1StackRootNetworkRecords (Stack program initialPrefix output)
end RC
namespace RE
export SemiprimeD1StackRootNetworkRecordsExecution (done timeBound source_run_prefix)
export SemiprimeD1StackRootNetworkRecordsAcquisition (prescription)
end RE
namespace RB
export SemiprimeD1StackRootNetworkRecordsBounds (prefixPolynomial runBoundPrefix timeBound_le_prefix)
end RB
namespace RR
export SemiprimeD1StackRootNetworkRecordsResources (initial_prefix_length)
end RR
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (wireCount)
/-- The same successful source trace pays both physical index input words. -/
theorem index_input_cap (bytes count cap:Nat) (hb:bytes ≤cap) (hc:count ≤cap) :
    10000*(bytes+count+1)^2 ≤10000*(2*cap+1)^2:=by
  exact Nat.mul_le_mul_left 10000 (Nat.pow_le_pow_left (by omega) 2)
/-- One quadratic cap includes the actual root call, index call and final halt. -/
theorem combined_cap (n P rootTime rootCap indexTime:Nat) (ht:rootTime ≤rootCap)
    (hi:indexTime ≤10000*(2*(n+P+rootTime)+1)^2) :
    rootTime+indexTime+4 ≤50000*(n+P+rootCap+1)^2:=by
  let S:=n+P+rootCap+1
  have hs:1 ≤S:=by dsimp [S];omega
  have hlin:2*(n+P+rootTime)+1 ≤2*S:=by dsimp [S];omega
  have hpow:=Nat.pow_le_pow_left hlin 2
  have hindex:indexTime ≤40000*S^2:=by
    have h:=hi.trans (Nat.mul_le_mul_left 10000 hpow)
    convert h using 1;ring
  have hsq:1 ≤S^2:=Nat.one_le_pow _ _ hs
  have hself:S ≤S^2:=Nat.le_pow (by decide:0<(2:Nat))
  have htime:rootTime ≤S^2:=by
    have h:rootTime ≤S:=by dsimp [S];omega
    exact h.trans hself
  change _ ≤50000*S^2
  omega
/-- A single actual exponential factor is squared only after the whole physical source cost is bounded. -/
theorem quadratic_rate (n P r E:Nat) (he:1 ≤E):
    50000*(n+P+r*E+1)^2 ≤50000*(n+P+r+1)^2*E^2:=by
  have h: n+P+1 ≤(n+P+1)*E:=by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n+P+1) he
  have hlin:n+P+r*E+1 ≤(n+P+r+1)*E:=by nlinarith only [h]
  have hp:=Nat.mul_le_mul_left 50000 (Nat.pow_le_pow_left hlin 2)
  convert hp using 1;ring
/-- Fixed base-two arithmetic identifies the squared actual root-source exponent. -/
theorem scope_square (B:Nat):(2^(19*B))^2=2^(38*B):=by
  rw [←pow_mul]
  congr 1
  omega
/-- A fixed quadratic transform preserves fixed monomial witnesses in total actual input bytes. -/
theorem quadratic_monomial {f:Nat→Nat→Nat}
    (hf:∃a d:Nat,∀n P,f n P ≤a*(n+P+1)^d):
    ∃a d:Nat,∀n P,50000*(n+P+f n P+1)^2 ≤a*(n+P+1)^d:=by
  obtain ⟨a,d,hf⟩:=hf
  refine ⟨50000*(1+a)^2,2*(d+1),?_⟩
  intro n P
  let S:=n+P+1
  have hs:1 ≤S:=by dsimp [S];omega
  have hd:S^d ≤S^(d+1):=Nat.pow_le_pow_right hs (by omega)
  have hself:S ≤S^(d+1):=by
    simpa only [pow_one] using Nat.pow_le_pow_right hs (by omega:1 ≤d+1)
  have hpoly:f n P ≤a*S^(d+1):=(hf n P).trans (Nat.mul_le_mul_left a hd)
  have hlin:n+P+f n P+1 ≤(1+a)*S^(d+1):=by
    have he:n+P+f n P+1=S+f n P:=by dsimp [S];omega
    rw [he]
    nlinarith only [hself,hpoly]
  have h:=Nat.mul_le_mul_left 50000 (Nat.pow_le_pow_left hlin 2)
  change _ ≤(50000*(1+a)^2)*S^(2*(d+1))
  calc
    _ ≤50000*((1+a)*S^(d+1))^2:=h
    _= _:=by rw [mul_pow,←pow_mul,Nat.mul_comm (d+1) 2];ring
/-- Every actually acquired root data word is bounded by the SAME successful source trace. -/
theorem root_word_length (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) (k:RC.Stack):
    ((RE.done bits hN fixed tail).data k).length ≤
      bits.length+(RE.prescription bits fixed tail).length+RE.timeBound bits hN fixed tail:=by
  obtain ⟨time,ht,hr⟩:=RE.source_run_prefix bits hc hN fixed tail
  have hd:=SemiprimeD1StackReturnLink.run_data_bound RC.program time
    (bits.length+(RE.prescription bits fixed tail).length) _ _
    (RR.initial_prefix_length bits (RE.prescription bits fixed tail)) hr k
  exact hd.trans (Nat.add_le_add_left ht _)
/-- Conservative quadratic cap for the two actual source calls and actual caller halt. -/
def runCapPrefix (bits:List Bool) (P:Nat):Nat:=
  50000*(bits.length+P+RB.runBoundPrefix bits P+1)^2
/-- A fixed physical input/prefix polynomial before every original input. -/
def prefixPolynomial (n P:Nat):Nat:=50000*(n+P+RB.prefixPolynomial n P+1)^2
/-- Same actual combined-program rate, with the squared original root-source exponent. -/
def runBoundPrefix (bits:List Bool) (P:Nat):Nat:=
  prefixPolynomial bits.length P*2^(38*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits)
/-- Standard N-only entry physically seeds its single false prescription marker. -/
def runBound (bits:List Bool):Nat:=runBoundPrefix bits 1
/-- The full quadratic caller cap fits its own fixed original scope-rate envelope. -/
theorem runCapPrefix_le (bits:List Bool) (P:Nat):runCapPrefix bits P ≤runBoundPrefix bits P:=by
  have he:1 ≤2^(19*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits):=Nat.pow_pos (by decide)
  have h:=quadratic_rate bits.length P (RB.prefixPolynomial bits.length P)
    (2^(19*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits)) he
  simpa only [runCapPrefix,runBoundPrefix,RB.runBoundPrefix,prefixPolynomial,scope_square] using h
/-- The caller-prefix polynomial has fixed witnesses before both N and all physical prefix bytes. -/
theorem prefix_polynomial_monomial:∃coef degree:Nat,∀n P,prefixPolynomial n P ≤coef*(n+P+1)^degree:=
  quadratic_monomial SemiprimeD1StackRootNetworkRecordsResources.prefix_polynomial_monomial
/-- N-only polynomial witnesses use the original positive width argument n+1. -/
theorem polynomial_monomial:∃coef degree:Nat,∀n,prefixPolynomial n 1 ≤coef*(n+1)^degree:=by
  obtain ⟨coef,degree,h⟩:=prefix_polynomial_monomial
  refine ⟨coef*2^degree,degree,?_⟩
  intro n
  have hs:n+1+1 ≤2*(n+1):=by omega
  have hp:=Nat.pow_le_pow_left hs degree
  have hh:prefixPolynomial n 1 ≤coef*(2*(n+1))^degree:=(h n 1).trans (Nat.mul_le_mul_left coef hp)
  simpa only [mul_pow,Nat.mul_assoc] using hh
namespace X
export SemiprimeD1StackRootOwnerIndexExecution (timeBound done source_run source_run_prefix)
end X
namespace Q
export SemiprimeD1StackRootOwnerIndexComponents (rootowners rootSuffix indexSource root_output root_left
  indexSource_vertices indexSource_leftCount)
end Q
namespace IE
export SemiprimeD1StackNetworkOwnerIndexExecution (timeBound)
end IE
open SemiprimeD1StackRootOwnerIndex
attribute [local irreducible] Q.rootowners Q.rootSuffix IE.timeBound RE.timeBound
/-- The actual index source's own quadratic budget is paid by its two physically shared root words. -/
theorem index_timeBound_physical (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool):
    IE.timeBound (Q.rootowners bits hN fixed) (Q.rootSuffix bits hN fixed) ≤10000*
      (((RE.done bits hN fixed tail).data RC.output).length+
        ((RE.done bits hN fixed tail).data SemiprimeD1StackRootOwnerIndexCoordinates.leftCount).length+1)^2:=by
  rw [Q.root_output bits hc hN fixed tail,Q.indexSource_vertices,Q.root_left bits hN fixed tail,
    Q.indexSource_leftCount,List.length_replicate]
  exact SemiprimeD1StackNetworkOwnerIndexBounds.timeBound_le _ _
/-- Both physical input lengths are charged to the SAME successful whole root source execution. -/
theorem index_timeBound_cap (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool):
    IE.timeBound (Q.rootowners bits hN fixed) (Q.rootSuffix bits hN fixed) ≤10000*
      (2*(bits.length+(RE.prescription bits fixed tail).length+RE.timeBound bits hN fixed tail)+1)^2:=by
  have hv:=root_word_length bits hc hN fixed tail RC.output
  have hn:=root_word_length bits hc hN fixed tail SemiprimeD1StackRootOwnerIndexCoordinates.leftCount
  exact (index_timeBound_physical bits hc hN fixed tail).trans (index_input_cap _ _ _ hv hn)
/-- The same whole caller budget includes both actual source calls, the N-only seed, and the final halt. -/
theorem timeBound_cap (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool):
    X.timeBound bits hN fixed tail ≤runCapPrefix bits (RE.prescription bits fixed tail).length:=by
  have hr:RE.timeBound bits hN fixed tail ≤RB.runBoundPrefix bits (RE.prescription bits fixed tail).length:=
    (Nat.le_succ _).trans (RB.timeBound_le_prefix bits hc hN fixed tail)
  have hi:=index_timeBound_cap bits hc hN fixed tail
  unfold X.timeBound runCapPrefix
  exact combined_cap _ _ _ _ _ hr hi
/-- Actual caller-prefix time fits one fixed polynomial and the squared actual table exponent. -/
theorem timeBound_le_prefix (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool):
    X.timeBound bits hN fixed tail ≤runBoundPrefix bits (RE.prescription bits fixed tail).length:=
  (timeBound_cap bits hc hN fixed tail).trans (runCapPrefix_le _ _)
/-- Standard N-only source clock includes the physically seeded false prefix marker. -/
theorem timeBound_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits):
    X.timeBound bits hN [] [] ≤runBound bits:=by
  have h:=timeBound_le_prefix bits hc hN [] []
  simpa only [SemiprimeD1StackRootNetworkRecordsAcquisition.prescription_empty,List.length_singleton,runBound] using h
/-- Actual N-only finite-program source trace with its own whole acquired-index clock. -/
theorem source_run_bounded (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits):
    ∃time ≤runBound bits,SemiprimeD1StackCalls.run program time (initial bits)=some (X.done bits hN [] []):=by
  obtain ⟨time,ht,hr⟩:=X.source_run bits hc hN
  exact ⟨time,ht.trans (timeBound_le bits hc hN),hr⟩
/-- Every repeated/conflicting actual caller-prefix and retained tail follows the same bounded source. -/
theorem source_run_prefix_bounded (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool):
    ∃time ≤runBoundPrefix bits (RE.prescription bits fixed tail).length,
      SemiprimeD1StackCalls.run program time (initialPrefix bits (RE.prescription bits fixed tail))=
        some (X.done bits hN fixed tail):=by
  obtain ⟨time,ht,hr⟩:=X.source_run_prefix bits hc hN fixed tail
  exact ⟨time,ht.trans (timeBound_le_prefix bits hc hN fixed tail),hr⟩
end RiemannGaussian.SemiprimeD1StackRootOwnerIndexBounds
