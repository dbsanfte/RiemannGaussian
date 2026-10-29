/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsBounds
/-! # ALL60 physical data roles, every allocated shadow and real returns at every SAME compiled source prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsStorage
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsExecution
open SemiprimeD1StackRecoveryWeightsBounds SemiprimeD1StackRecoveryWeightsWidths
open SemiprimeRationalBits (RationalWord)
/-- The complete60-role input contains exactly the six acquired words, all paid by actual source bytes. -/
theorem initial_role_bound (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool) (role:Stack):
    ((initial (SemiprimeD1StackNormalizedInverse.tape inverse) (SemiprimeD1StackNormalizedInverse.tape powers)
      (SemiprimeD1StackNormalizedInverse.signed scalar) scalar.denominator (SemiprimeD1StackRecoveryWeightsIndices.unary q) width).data role).length ≤ inputSize inverse powers scalar q width:=by
  have hs:=input_caps inverse powers scalar q width
  rcases role with (r|r)|r
  · change (if r=SemiprimeD1StackRationalOperation.aux .template then width else []).length ≤ _
    split
    · exact hs.2.2.2.2.2
    · exact Nat.zero_le _
  · rcases r with r|r
    · exact Nat.zero_le _
    · cases r <;> first | exact Nat.zero_le _ | exact hs.2.1 | exact hs.2.2.1 | (change (SemiprimeD1StackRecoveryWeightsIndices.unary q).length ≤ _;simpa only [SemiprimeD1StackRecoveryWeightsIndices.unary,List.length_replicate] using hs.2.2.2.2.1)
  · have hc:=hs.2.2.2.1
    unfold SemiprimeD1StackNormalizedInverseWidths.bytes at hc
    cases r
    · change (SemiprimeD1StackNormalizedInverse.signed scalar).length ≤ _;omega
    · change scalar.denominator.length ≤ _;omega
/-- No successful actual prefix runs past the true halt of the SAME whole program. -/
theorem prefix_fuel (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial (SemiprimeD1StackNormalizedInverse.tape inverse)
      (SemiprimeD1StackNormalizedInverse.tape powers) (SemiprimeD1StackNormalizedInverse.signed scalar) scalar.denominator
      (SemiprimeD1StackRecoveryWeightsIndices.unary q) width)=some out):fuel ≤ polynomial inverse powers scalar q width:=by
  obtain ⟨s,hs,hstop⟩:=source_run_bounded inverse powers scalar q width
  have hb:fuel ≤ s:=by
    by_contra hn
    have he:fuel=s+(1+(fuel-(s+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (done inverse powers scalar q width)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact hb.trans hs
/-- Every role/shadow counts, rather than only currently used arithmetic tapes. -/
theorem word_sum (data:Stack→List Bool) (cap:Nat) (h:∀role,(data role).length ≤ cap):
    (∑role:Stack,(data role).length) ≤ 60*cap:=by
  calc
    _ ≤ ∑_role:Stack,cap:=Finset.sum_le_sum (fun role _=>h role)
    _=_:=by rw [Finset.sum_const,Finset.card_univ,stack_card];rfl
/-- The SAME actual source prefix has all60 Boolean words AND genuine finite return cells paid. -/
theorem prefix_cells (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial (SemiprimeD1StackNormalizedInverse.tape inverse)
      (SemiprimeD1StackNormalizedInverse.tape powers) (SemiprimeD1StackNormalizedInverse.signed scalar) scalar.denominator
      (SemiprimeD1StackRecoveryWeightsIndices.unary q) width)=some out):
    (∑role:Stack,(out.data role).length)+out.frames.length ≤ 61*(inputSize inverse powers scalar q width+polynomial inverse powers scalar q width):=by
  have hf:=prefix_fuel inverse powers scalar q width fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize inverse powers scalar q width) _ out
    (initial_role_bound inverse powers scalar q width) hr
  have hm:=word_sum out.data (inputSize inverse powers scalar q width+fuel) hd
  have hret:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hret
  omega
/-- Fixed whole-space coefficient/degree precede all six actual source words. -/
def spacePolynomial (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):Nat:=
  10^53*(inputSize inverse powers scalar q width)^10
/-- Actual input cells plus SAME-source own clock give this all60-plus-returns cap. -/
theorem cells_le (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):
    61*(inputSize inverse powers scalar q width+polynomial inverse powers scalar q width) ≤ spacePolynomial inverse powers scalar q width:=by
  have hp:inputSize inverse powers scalar q width ≤ (inputSize inverse powers scalar q width)^10:=Nat.le_pow (by decide:0<10)
  unfold polynomial spacePolynomial
  omega
/-- EVERY compiled prefix of the SAME fixed60-role machine, including all real saved-return alphabets. -/
theorem machine_prefix_cells (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool)
    (fuel:Nat) (cfg:machine.Cfg)
    (hp:(fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration
      (initial (SemiprimeD1StackNormalizedInverse.tape inverse) (SemiprimeD1StackNormalizedInverse.tape powers)
        (SemiprimeD1StackNormalizedInverse.signed scalar) scalar.denominator (SemiprimeD1StackRecoveryWeightsIndices.unary q) width)))=some cfg):
    (∑role:Stack,(cfg.stk (some role)).length)+(cfg.stk none).length ≤ spacePolynomial inverse powers scalar q width:=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .denominator) (aux .output) (.local .start) program fuel
    (initial (SemiprimeD1StackNormalizedInverse.tape inverse) (SemiprimeD1StackNormalizedInverse.tape powers)
      (SemiprimeD1StackNormalizedInverse.signed scalar) scalar.denominator (SemiprimeD1StackRecoveryWeightsIndices.unary q) width)
  have hh:=he.trans hp
  cases hout:SemiprimeD1StackCalls.run program fuel
      (initial (SemiprimeD1StackNormalizedInverse.tape inverse) (SemiprimeD1StackNormalizedInverse.tape powers)
        (SemiprimeD1StackNormalizedInverse.signed scalar) scalar.denominator (SemiprimeD1StackRecoveryWeightsIndices.unary q) width) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hc:cfg=SemiprimeD1StackCalls.configuration out:=(Option.some.inj hh).symm
    subst cfg
    exact (prefix_cells inverse powers scalar q width fuel out hout).trans (cells_le inverse powers scalar q width)
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsStorage
