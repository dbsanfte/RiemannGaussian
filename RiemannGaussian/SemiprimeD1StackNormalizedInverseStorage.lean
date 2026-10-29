/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseBounds
/-! # Every actual prefix counts all58 physical words AND the saved-return word -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseStorage
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseStateBounds SemiprimeD1StackNormalizedInverseBounds
open SemiprimeD1StackNormalizedInverseEncoding SemiprimeD1StackNormalizedInverseReadBuffers
/-- Only the three actual physical source words are initially present; q VALUE is fully paid by its markers. -/
theorem initial_length (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) (k : Stack) :
    ((initial (tape a) (unary q) width).data k).length ≤ inputSize a q width := by
  have hs:=inputSize_caps a q width
  rcases k with k|k
  · change (if k=R.aux .template then width else []).length ≤ _
    split
    · exact hs.2.2.2
    · exact Nat.zero_le _
  · rcases k with ⟨r,den⟩|k
    · exact Nat.zero_le _
    · cases k <;> first
      | exact Nat.zero_le _
      | exact hs.2.1
      | (change (unary q).length ≤ _;simpa only [unary,List.length_replicate] using hs.2.2.1)
/-- Fixed storage coefficient/degree precede every coefficient array, q and W. -/
def cellsPolynomial (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) : ℕ :=
  10^45*(inputSize a q width)^10
/-- Every SAME-program actual source prefix pays all58 words, alias shadows and its real caller return stack. -/
theorem prefix_cells (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool)
    (fuel : ℕ) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial (tape a) (unary q) width)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ cellsPolynomial a q width := by
  obtain ⟨t,ht,hs⟩:=source_run_bounded a q width
  have hf : fuel≤t := by
    by_contra hn
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hs,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hh : SemiprimeD1StackCalls.run program 1 (done a q width)=none := rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize a q width)
    (initial (tape a) (unary q) width) out (initial_length a q width) hr
  have hsum:=SemiprimeD1StackNormalizedInverseCleanup.word_sum out.data (inputSize a q width+fuel) hd
  change (∑k : Stack,(out.data k).length)≤58*(inputSize a q width+fuel) at hsum
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel (initial (tape a) (unary q) width) out hr
  change out.frames.length≤0+fuel at hframes
  have hl : inputSize a q width ≤ (inputSize a q width)^10 := Nat.le_self_pow (by decide:10≠0) _
  unfold cellsPolynomial polynomial at *
  nlinarith only [ht,hf,hsum,hframes,hl]
/-- The actual compiled prepared machine counts its SAME58 data words and its actual none-label return tape. -/
theorem machine_prefix_cells (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool)
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun z=>z.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial (tape a) (unary q) width)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ cellsPolynomial a q width := by
  have he:=SemiprimeD1StackCalls.run_correct (aux .denominator) (aux .output) (ctl .start) program fuel
    (initial (tape a) (unary q) width)
  have hh:=he.trans hr
  cases hout : SemiprimeD1StackCalls.run program fuel (initial (tape a) (unary q) width) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have heq : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells a q width fuel out hout
end RiemannGaussian.SemiprimeD1StackNormalizedInverseStorage
