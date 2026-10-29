/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootNetworkRowsExecution
/-! # Own original-network row source clock from the actual record acquisition
The actual original record/count bytes are paid by their SAMEsource trace.
The cubic row budget is applied to those physical bytes, not to a native graph
report or to an externally supplied routing/count answer. Its exponent is
three times the actual record-source exponent; the already paid quadratic
index source fits this same bound.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootNetworkRowsBounds
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (wireCount)
namespace RC
export SemiprimeD1StackRootNetworkRecords (Stack output)
end RC
namespace RE
export SemiprimeD1StackRootNetworkRecordsExecution (done timeBound)
export SemiprimeD1StackRootNetworkRecordsAcquisition (prescription)
end RE
namespace RB
export SemiprimeD1StackRootNetworkRecordsBounds (prefixPolynomial runBoundPrefix)
end RB
namespace RI
export SemiprimeD1StackRootOwnerIndexExecution (timeBound)
end RI
namespace X
export SemiprimeD1StackRootNetworkRowsExecution (timeBound done source_run source_run_prefix)
end X
namespace A
export SemiprimeD1StackRootOwnerIndexComponents (rootowners rootSuffix root_output root_left indexSource_vertices indexSource_leftCount)
end A
namespace Q
export SemiprimeD1StackNetworkRowsExecution (timeBound)
end Q
namespace J
export SemiprimeD1StackRootNetworkRowsComponents (rootfactors)
end J
/-- A single cubic cap includes actual record/index acquisition, actual row construction, calls and halt. -/
theorem combined_cap (n P rootTime rootCap indexTime rowsTime:Nat) (ht:rootTime≤rootCap)
    (hi:indexTime≤50000*(n+P+rootCap+1)^2)
    (hr:rowsTime≤10000000000*(2*(n+P+rootTime)+1)^3) :
    indexTime+rowsTime+3≤1000000000000*(n+P+rootCap+1)^3 :=by
  let S:=n+P+rootCap+1
  have hs:1≤S:=by dsimp [S];omega
  have hlin:2*(n+P+rootTime)+1≤2*S:=by dsimp [S];omega
  have hp:=Nat.pow_le_pow_left hlin 3
  have hrows:rowsTime≤80000000000*S^3:=by
    have h:=hr.trans (Nat.mul_le_mul_left 10000000000 hp)
    convert h using 1;ring
  have hsq:S^2≤S^3:=Nat.pow_le_pow_right hs (by decide:2≤(3:Nat))
  have hindex:indexTime≤50000*S^3:=hi.trans (Nat.mul_le_mul_left 50000 hsq)
  have h1:1≤S^3:=Nat.one_le_pow _ _ hs
  change _≤1000000000000*S^3
  omega
/-- Cubing the SAMEactual acquired-record rate preserves its one exponential factor honestly. -/
theorem cubic_rate (n P r E:Nat) (he:1≤E) :
    1000000000000*(n+P+r*E+1)^3≤1000000000000*(n+P+r+1)^3*E^3 :=by
  have h:n+P+1≤(n+P+1)*E:=by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n+P+1) he
  have hl:n+P+r*E+1≤(n+P+r+1)*E:=by nlinarith only [h]
  have hp:=Nat.mul_le_mul_left 1000000000000 (Nat.pow_le_pow_left hl 3)
  convert hp using 1;ring
/-- Exact arithmetic on the actual source exponent, independent of N. -/
theorem scope_cube (B:Nat) :(2^(19*B))^3=2^(57*B) :=by
  rw [←pow_mul]
  congr 1
  omega
/-- A fixed cubic source transformation has fixed monomial witnesses before all input/prefix lengths. -/
theorem cubic_monomial {f:Nat→Nat→Nat}
    (hf:∃a d:Nat,∀n P,f n P≤a*(n+P+1)^d) :
    ∃a d:Nat,∀n P,1000000000000*(n+P+f n P+1)^3≤a*(n+P+1)^d :=by
  obtain ⟨a,d,hf⟩:=hf
  refine ⟨1000000000000*(1+a)^3,3*(d+1),?_⟩
  intro n P
  let S:=n+P+1
  have hs:1≤S:=by dsimp [S];omega
  have hd:S^d≤S^(d+1):=Nat.pow_le_pow_right hs (by omega)
  have hself:S≤S^(d+1):=by
    simpa only [pow_one] using Nat.pow_le_pow_right hs (by omega:1≤d+1)
  have hpoly:f n P≤a*S^(d+1):=(hf n P).trans (Nat.mul_le_mul_left a hd)
  have hlin:n+P+f n P+1≤(1+a)*S^(d+1):=by
    have he:n+P+f n P+1=S+f n P:=by dsimp [S];omega
    rw [he]
    nlinarith only [hself,hpoly]
  have h:=Nat.mul_le_mul_left 1000000000000 (Nat.pow_le_pow_left hlin 3)
  change _≤(1000000000000*(1+a)^3)*S^(3*(d+1))
  calc
    _≤1000000000000*((1+a)*S^(d+1))^3:=h
    _= _:=by rw [mul_pow,←pow_mul,Nat.mul_comm (d+1) 3];ring
/-- Whole physical row clock expressed in the two actual original root input words. -/
theorem rows_timeBound_physical (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<bitValue bits) (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    Q.timeBound (A.rootowners bits hN fixed) (J.rootfactors bits hN fixed)≤10000000000*
      (((RE.done bits hN fixed tail).data RC.output).length+
        ((RE.done bits hN fixed tail).data SemiprimeD1StackRootOwnerIndexCoordinates.leftCount).length+1)^3 :=by
  rw [A.root_output bits hc hN fixed tail,A.indexSource_vertices,A.root_left bits hN fixed tail,
    A.indexSource_leftCount,List.length_replicate]
  exact SemiprimeD1StackNetworkRowsBounds.timeBound_le _ _
/-- Both original input words are paid by the SAMEactual record source run, including their real acquisition. -/
theorem rows_timeBound_cap (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<bitValue bits) (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    Q.timeBound (A.rootowners bits hN fixed) (J.rootfactors bits hN fixed)≤10000000000*
      (2*(bits.length+(RE.prescription bits fixed tail).length+RE.timeBound bits hN fixed tail)+1)^3 :=by
  have hv:=SemiprimeD1StackRootOwnerIndexBounds.root_word_length bits hc hN fixed tail RC.output
  have hn:=SemiprimeD1StackRootOwnerIndexBounds.root_word_length bits hc hN fixed tail
    SemiprimeD1StackRootOwnerIndexCoordinates.leftCount
  have hlin:((RE.done bits hN fixed tail).data RC.output).length+
      ((RE.done bits hN fixed tail).data SemiprimeD1StackRootOwnerIndexCoordinates.leftCount).length+1≤
        2*(bits.length+(RE.prescription bits fixed tail).length+RE.timeBound bits hN fixed tail)+1:=by omega
  exact (rows_timeBound_physical bits hc hN fixed tail).trans
    (Nat.mul_le_mul_left 10000000000 (Nat.pow_le_pow_left hlin 3))
/-- Conservative actual complete-program bound before extracting its original scope exponent. -/
def runCapPrefix (bits:List Bool) (P:Nat) :Nat :=
  1000000000000*(bits.length+P+RB.runBoundPrefix bits P+1)^3
/-- Fixed physical input/prefix polynomial, independent of every N. -/
def prefixPolynomial (n P:Nat) :Nat :=1000000000000*(n+P+RB.prefixPolynomial n P+1)^3
/-- Whole own source rate uses the CUBEDactual record-source factor, not a transported native graph report. -/
def runBoundPrefix (bits:List Bool) (P:Nat) :Nat :=
  prefixPolynomial bits.length P*2^(57*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits)
/-- N-only entry pays its actual single false prescription seed. -/
def runBound (bits:List Bool) :Nat :=runBoundPrefix bits 1
/-- The same actual complete-program cap fits its fixed scope-rate envelope. -/
theorem runCapPrefix_le (bits:List Bool) (P:Nat) :runCapPrefix bits P≤runBoundPrefix bits P :=by
  have he:1≤2^(19*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits):=Nat.pow_pos (by decide)
  have h:=cubic_rate bits.length P (RB.prefixPolynomial bits.length P)
    (2^(19*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits)) he
  simpa only [runCapPrefix,runBoundPrefix,RB.runBoundPrefix,prefixPolynomial,scope_cube] using h
/-- Fixed polynomial coefficient and degree before every original N and every physical prefix. -/
theorem prefix_polynomial_monomial :∃coef degree:Nat,∀n P,prefixPolynomial n P≤coef*(n+P+1)^degree :=
  cubic_monomial SemiprimeD1StackRootNetworkRecordsResources.prefix_polynomial_monomial
/-- N-only fixed polynomial witnesses are independent of the original input. -/
theorem polynomial_monomial :∃coef degree:Nat,∀n,prefixPolynomial n 1≤coef*(n+1)^degree :=by
  obtain ⟨coef,degree,h⟩:=prefix_polynomial_monomial
  refine ⟨coef*2^degree,degree,?_⟩
  intro n
  have hs:n+1+1≤2*(n+1):=by omega
  have hp:=Nat.pow_le_pow_left hs degree
  have hh:prefixPolynomial n 1≤coef*(2*(n+1))^degree:=(h n 1).trans (Nat.mul_le_mul_left coef hp)
  simpa only [mul_pow,Nat.mul_assoc] using hh
open SemiprimeD1StackRootNetworkRows
attribute [local irreducible] A.rootowners A.rootSuffix Q.timeBound RE.timeBound RI.timeBound
/-- Whole actual source call/index/row/halt clock lies below its OWNcomplete-program cap. -/
theorem timeBound_cap (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    X.timeBound bits hN fixed tail≤runCapPrefix bits (RE.prescription bits fixed tail).length :=by
  have hr:RE.timeBound bits hN fixed tail≤RB.runBoundPrefix bits (RE.prescription bits fixed tail).length:=
    (Nat.le_succ _).trans (SemiprimeD1StackRootNetworkRecordsBounds.timeBound_le_prefix bits hc hN fixed tail)
  have hi:=SemiprimeD1StackRootOwnerIndexBounds.timeBound_cap bits hc hN fixed tail
  have hrows:=rows_timeBound_cap bits hc hN fixed tail
  unfold X.timeBound runCapPrefix
  exact combined_cap _ _ _ _ _ _ hr hi hrows
/-- Whole actual caller-prefix clock fits the original scope-rate envelope. -/
theorem timeBound_le_prefix (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    X.timeBound bits hN fixed tail≤runBoundPrefix bits (RE.prescription bits fixed tail).length :=
  (timeBound_cap bits hc hN fixed tail).trans (runCapPrefix_le _ _)
/-- Standard N-only actual source clock includes all preprocessing and the real seed. -/
theorem timeBound_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    X.timeBound bits hN [] []≤runBound bits :=by
  have h:=timeBound_le_prefix bits hc hN [] []
  simpa only [SemiprimeD1StackRootNetworkRecordsAcquisition.prescription_empty,List.length_singleton,runBound] using h
/-- Complete actual binary-N-only acquisition, including the real final halt. -/
theorem source_run_bounded (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃q≤runBound bits,SemiprimeD1StackCalls.run program q (initial bits)=some (X.done bits hN [] []) :=by
  obtain ⟨q,hq,hr⟩:=X.source_run bits hc hN
  exact ⟨q,hq.trans (timeBound_le bits hc hN),hr⟩
/-- All real caller prescriptions and tails execute under the same fixed whole-source bound. -/
theorem source_run_prefix_bounded (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<bitValue bits) (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ∃q≤runBoundPrefix bits (RE.prescription bits fixed tail).length,
      SemiprimeD1StackCalls.run program q (initialPrefix bits (RE.prescription bits fixed tail))=
        some (X.done bits hN fixed tail) :=by
  obtain ⟨q,hq,hr⟩:=X.source_run_prefix bits hc hN fixed tail
  exact ⟨q,hq.trans (timeBound_le_prefix bits hc hN fixed tail),hr⟩
end RiemannGaussian.SemiprimeD1StackRootNetworkRowsBounds
