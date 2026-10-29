/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsIndices
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsPair
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsSpec
/-! # Whole actual descending pair loop, exact raw native right-fold accumulator -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsInner
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsCalls SemiprimeD1StackRecoveryWeightsIndices SemiprimeD1StackProcedureTrace
open SemiprimeRationalBits (RationalWord)
namespace Spec
export SemiprimeD1StackRecoveryWeightsSpec (dotLoop combine)
end Spec
/-- Replacing an actually acquired accumulator removes BOTH previous fields exactly. -/
theorem indexed_put (w:Words) (terms a b:Nat) (old out:RationalWord):
    replace (indexed w terms a b old) (Old.putReg (indexed w terms a b old).toWords .acc out)=indexed w terms a b out:=by
  change replace w (Old.putReg (Old.putReg (SemiprimeD1StackNormalizedInverseIndices.counters w.toWords terms a b) .acc old) .acc out)=_
  rw [SemiprimeD1StackNormalizedInverseRegisterAlgebra.putReg_idem]
  rfl
/-- A real cache replacement retains all other parsed/product fields. -/
theorem indexed_other (w:Words) (terms a b:Nat) (acc:RationalWord) (r:I.Reg) (den:Bool) (hr:r≠.acc):
    (indexed w terms a b acc).registers (r,den)=w.registers (r,den):=by
  exact SemiprimeD1StackNormalizedInverseView.putReg_other _ .acc r acc den hr
/-- Every original source/helper word outside the three actual indices is preserved. -/
theorem indexed_aux (w:Words) (terms a b:Nat) (acc:RationalWord) (k:I.Aux)
    (ht:k≠.terms) (ha:k≠.aIndex) (hb:k≠.bIndex):
    (indexed w terms a b acc).auxiliary k=w.auxiliary k:=by
  change Function.update (Function.update (Function.update w.auxiliary .terms (unary terms)) .aIndex (unary a)) .bIndex (unary b) k=_
  rw [Function.update_of_ne hb,Function.update_of_ne ha,Function.update_of_ne ht]
/-- Exact sum of THIS program's actual pair traces, marker pops and TWO index pops. -/
def timeBound (w:Words) (inverse powers:List RationalWord) (width:List Bool) (j:Nat):Nat→RationalWord→Nat
  | 0,_=>1
  | n+1,acc=>1+SemiprimeD1StackRecoveryWeightsPair.timeBound (indexed w n n (j+n) acc) inverse powers n (j+n) width+2+
      timeBound w inverse powers width j n (Spec.combine width inverse powers j (j+n) acc)
/-- Every pair is acquired by actual parses and R36 calls; both actual counters descend before the next prefix. -/
theorem inner_run (w:Words) (inverse powers:List RationalWord) (width:List Bool) (j n:Nat) (acc:RationalWord)
    (hi:w.auxiliary .denominator=SemiprimeD1StackNormalizedInverse.tape inverse)
    (hp:w.auxiliary .prefixReverse=SemiprimeD1StackNormalizedInverse.tape powers)
    (hr:w.rational=Old.emptyRational width) (he:∀r den,w.registers (r,den)=[])
    (hreader:w.auxiliary .reader=[]) (htodo:w.auxiliary .readTodo=[])
    (hs:w.auxiliary .fieldFrameScratch=[]) (hv:w.auxiliary .valid=[]) (hc:w.auxiliary .copyScratch=[]):
    ∃time ≤ timeBound w inverse powers width j n acc,
      Runs program time (.local .terms) (bank (indexed w n (n-1) (j+n-1) acc)) (.local (.clearIndices false))
        (bank (indexed w 0 0 (j-1) (Spec.dotLoop width inverse powers j n acc))):=by
  induction n generalizing acc with
  | zero=>exact ⟨1,le_rfl,term_zero w j acc⟩
  | succ n ih=>
    let atPair:=indexed w n n (j+n) acc
    have h0:=term_succ w j n acc
    have hepair:∀r≠SemiprimeD1StackNormalizedInverse.Reg.acc,∀den,atPair.registers (r,den)=[]:=by
      intro r hr den
      rw [indexed_other w n n (j+n) acc r den hr]
      exact he r den
    have hn:atPair.registers (.acc,false)≠[]:=
      SemiprimeD1StackNormalizedInverseRegisterAlgebra.putReg_nonempty _ .acc acc
    obtain ⟨m,hm,h1⟩:=SemiprimeD1StackRecoveryWeightsPair.pair_run atPair inverse powers n (j+n) width hi hp rfl rfl hr hepair hn hreader htodo hs hv hc
    let out:=SemiprimeD1StackNormalizedInverseSpec.combine width
      (SemiprimeD1StackNormalizedInverseSpec.readWord inverse n,SemiprimeD1StackNormalizedInverseSpec.readWord powers (j+n)) acc
    have hout:out=Spec.combine width inverse powers j (j+n) acc:=by
      dsimp only [out,SemiprimeD1StackNormalizedInverseSpec.combine,Spec.combine]
      rw [show j+n-j=n by omega]
      rfl
    change Runs program m _ _ _ (bank (replace atPair (Old.putReg atPair.toWords .acc out))) at h1
    rw [indexed_put,hout] at h1
    have h2:=decrement_run w j n (Spec.combine width inverse powers j (j+n) acc)
    obtain ⟨s,hbound,h3⟩:=ih (Spec.combine width inverse powers j (j+n) acc)
    have hh:=P.join (P.join (P.join h0 h1) h2) h3
    refine ⟨1+m+2+s,?_,?_⟩
    · dsimp only [timeBound]
      dsimp only [atPair] at hm
      omega
    · convert hh using 1
      · congr 2
      · rfl
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsInner
