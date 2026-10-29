/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInversePair
import RiemannGaussian.SemiprimeD1StackNormalizedInverseIndices
import RiemannGaussian.SemiprimeD1StackNormalizedInverseRecurrence
/-! # Actual complete descending inverse-coefficient dot loop -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseInner
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseCalls SemiprimeD1StackNormalizedInverseReadBuffers
open SemiprimeD1StackNormalizedInverseRegisterAlgebra SemiprimeD1StackNormalizedInversePair
open SemiprimeD1StackNormalizedInverseSpec SemiprimeD1StackNormalizedInverseIndices
open SemiprimeD1StackNormalizedInverseRecurrence SemiprimeD1StackProcedureTrace
/-- Actual per-step caps are summed in the same descending order as the literal source instructions. -/
def innerBound (w : Words) (a reversed : List SemiprimeRationalBits.RationalWord) (width : List Bool) :
    ℕ→SemiprimeRationalBits.RationalWord→ℕ
  | 0,_=>1
  | n+1,acc=>1+pairBound (indexed w n (n+1) n acc) a reversed n width+2+
      innerBound w a reversed width n (combine width (readWord a (n+1),readWord reversed n) acc)
/-- Physical list-array words at the actual left query are EXACT native array bytes. -/
theorem read_array (a : List SemiprimeRationalBits.RationalWord) (n : ℕ) :
    readWord a n=SemiprimeJetBits.wordAt a.toArray n := by
  simpa only [List.toList_toArray] using read_toList a.toArray n
/-- Whole real loop from physically acquired indices and accumulator; no pair/clock or result is supplied. -/
theorem inner_run (w : Words) (a reversed : List SemiprimeRationalBits.RationalWord) (width : List Bool)
    (n : ℕ) (acc : SemiprimeRationalBits.RationalWord)
    (hr : w.rational=emptyRational width)
    (ha : store w (readSource .denominator)=tape a) (hb : store w (readSource .prefix)=tape reversed)
    (hreader : w.auxiliary .reader=[]) (htodo : w.auxiliary .readTodo=[])
    (hs : w.auxiliary .fieldFrameScratch=[]) (hv : w.auxiliary .valid=[]) (hc : w.auxiliary .copyScratch=[])
    (he : ∀r≠Reg.acc,∀den,w.registers (r,den)=[]) :
    ∃q ≤ innerBound w a reversed width n acc,
      Runs program q (ctl .terms) (store (indexed w n n (n-1) acc)) (ctl (.seedNeg false))
        (store (indexed w 0 0 0 (dotLoop width a.toArray reversed n acc))) := by
  induction n generalizing acc with
  | zero=>exact ⟨1,le_rfl,term_zero w acc⟩
  | succ n ih=>
    have h0:=term_succ w n acc
    have hsparse : ∀r≠Reg.acc,∀den,(indexed w n (n+1) n acc).registers (r,den)=[] := by
      intro r hn den
      change (putReg (counters w n (n+1) n) .acc acc).registers (r,den)=[]
      rw [putReg_other _ .acc r acc den hn]
      exact he r hn den
    obtain ⟨q1,hq1,h1⟩:=pair_run (indexed w n (n+1) n acc) a reversed n width hr ha hb rfl rfl
      hreader htodo hs hv hc hsparse (putReg_nonempty (counters w n (n+1) n) .acc acc)
    have hg : getReg (indexed w n (n+1) n acc) .acc=acc := getReg_put _ .acc acc
    rw [hg] at h1
    let next:=combine width (readWord a (n+1),readWord reversed n) acc
    have heq : putReg (indexed w n (n+1) n acc) .acc next=indexed w n (n+1) n next :=
      putReg_idem _ .acc acc next
    rw [heq] at h1
    have h2:=decrement_run w n next
    obtain ⟨q3,hq3,h3⟩:=ih next
    have h:=PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3
    have hout : dotLoop width a.toArray reversed (n+1) acc=dotLoop width a.toArray reversed n next := by
      rw [dotLoop]
      congr 1
      rw [pairAt,←read_array]
    rw [←hout] at h
    refine ⟨1+q1+2+q3,?_,?_⟩
    · change 1+q1+2+q3≤1+pairBound (indexed w n (n+1) n acc) a reversed n width+2+
        innerBound w a reversed width n next
      omega
    · simpa only [Nat.add_sub_cancel] using h
end RiemannGaussian.SemiprimeD1StackNormalizedInverseInner
