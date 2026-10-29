/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishNewton
import RiemannGaussian.SemiprimeD1StackRecoveryFinishCache
/-! # Own actual scalar-stage clock and intrinsic cache-width bounds
The scalar caps are derived from actual canonical source outputs. Public callers
will supply only original input words and unary WIDTH; no intermediate bound or
answer is added to runtime control or to the final public source theorem.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishOperatorBounds
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinishPrimitives
namespace M
export SemiprimeD1StackRecoveryFinishMultiply (word target loadTime bodyTime time result)
end M
namespace A
export SemiprimeD1StackRecoveryFinishCorrection (word time result)
end A
namespace K
export SemiprimeD1StackRecoveryFinishCache (word reducerTime time)
end K
/-- All actual binary scalar caches and final output, excluding the potentially long original binary operands. -/
def sizedSlots:List Slot:=[.aux .inverseInput,.aux .negative,.aux .two,.aux .current,.aux .product,
  .aux .opposite,.aux .correction,.aux .signedResidue,.aux .numeratorResidue,.output]
/-- Intrinsic physically acquired scalar widths at an actual iteration boundary. -/
structure Small (v:Values) (p:Nat):Prop where
  /-- Actual physically supplied precision count. -/
  width:(v .width).length=p
  /-- All actual scalar caches were acquired by source canonical reduction/products/sums. -/
  bounded:∀s∈sizedSlots,(v s).length≤p
/-- One linear value/byte factor is bounded by its fixed cubic monomial. -/
theorem linear_cube (p:Nat):p+1≤(p+1)^3:=by
  simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1≤p+1) (by decide:1≤3)
/-- Replacing any non-WIDTH scalar/output role by an actual bounded word preserves intrinsic scalar caps. -/
theorem small_update (v:Values) (p:Nat) (hv:Small v p) (s:Slot) (hs:s≠.width) (bits:List Bool) (hb:bits.length≤p):
    Small (Function.update v s bits) p:=by
  constructor
  · rw [Function.update_of_ne hs.symm]
    exact hv.width
  · intro t ht
    by_cases he:t=s
    · subst t
      rw [Function.update_same]
      exact hb
    · rw [Function.update_of_ne he]
      exact hv.bounded t ht
/-- Updating a genuine non-scalar work word such as the actual todo tape does not require an advised width bound. -/
theorem small_foreign (v:Values) (p:Nat) (hv:Small v p) (s:Slot) (hs:s≠.width) (hn:s∉sizedSlots) (bits:List Bool):
    Small (Function.update v s bits) p:=by
  constructor
  · rw [Function.update_of_ne hs.symm]
    exact hv.width
  · intro t ht
    have he:t≠s:=by intro h;subst t;exact hn ht
    rw [Function.update_of_ne he]
    exact hv.bounded t ht
/-- Actual left product operands come from intrinsically bounded scalar caches. -/
theorem left_bound (v:Values) (p:Nat) (hv:Small v p) (site:MulSite):(v (multiplyFromLeft site)).length≤p:=by
  cases site <;> exact hv.bounded _ (by simp [sizedSlots,multiplyFromLeft])
/-- Actual right product operands come from intrinsically bounded scalar caches. -/
theorem right_bound (v:Values) (p:Nat) (hv:Small v p) (site:MulSite):(v (multiplyFromRight site)).length≤p:=by
  cases site <;> exact hv.bounded _ (by simp [sizedSlots,multiplyFromRight])
/-- Every actual old destination cache is paid, including its physical drain. -/
theorem target_bound (v:Values) (p:Nat) (hv:Small v p) (site:MulSite):(v (M.target site)).length≤p:=by
  cases site <;> exact hv.bounded _ (by simp [sizedSlots,M.target])
/-- Actual modular-product output bounds are intrinsic even before scalar operand caps are used. -/
theorem multiply_word_length (v:Values) (p:Nat) (hv:Small v p) (site:MulSite):(M.word v site).length≤p:=by
  have h:=SemiprimeD1JetScalarBits.mul_length (v .width).length (v (multiplyFromLeft site)) (v (multiplyFromRight site))
  simpa only [M.word,hv.width] using h
/-- Actual product-cache replacement inherits its bound from the real acquired canonical output. -/
theorem small_multiply (v:Values) (p:Nat) (hv:Small v p) (site:MulSite):Small (M.result v site) p:=by
  apply small_update v p hv (M.target site) _ (M.word v site) (multiply_word_length v p hv site)
  cases site <;> decide
/-- Actual correction output bound is intrinsic to the real canonical scalar sum. -/
theorem correction_word_length (v:Values) (p:Nat) (hv:Small v p):(A.word v).length≤p:=by
  have h:=SemiprimeD1JetScalarBits.add_length (v .width).length (v (.aux .two)) (v (.aux .opposite))
  simpa only [A.word,hv.width] using h
/-- Actual correction-cache replacement inherits its bound from the real scalar-sum output. -/
theorem small_correction (v:Values) (p:Nat) (hv:Small v p):Small (A.result v) p:=
  small_update v p hv (.aux .correction) (by decide) (A.word v) (correction_word_length v p hv)
/-- SAME actual nested multiplier source clock has a fixed cubic bound on bounded physical scalar inputs. -/
theorem scalar_multiply_time (v:Values) (p:Nat) (hv:Small v p) (site:MulSite):
    SemiprimeD1StackJetScalarMulExecution.totalTime (v (multiplyFromLeft site)) (v (multiplyFromRight site)) (v .width)
      ≤54000*(p+1)^3:=by
  have hl:=left_bound v p hv site
  have hr:=right_bound v p hv site
  have hw:=hv.width
  calc
    _≤2000*((v (multiplyFromLeft site)).length+(v (multiplyFromRight site)).length+(v .width).length+3)^3:=
      (SemiprimeD1StackJetScalarMulExecution.totalTime_le _ _ _).trans
        (SemiprimeD1StackJetScalarMulExecution.timeBound_le_cube _ _ _)
    _≤2000*(3*(p+1))^3:=by gcongr;omega
    _=54000*(p+1)^3:=by ring
/-- Every full real cached-product call charges both operand copies, old cache drain, output move and real returns. -/
theorem multiply_time (v:Values) (p:Nat) (hv:Small v p) (site:MulSite):M.time v site≤100000*(p+1)^3:=by
  have hl:=left_bound v p hv site
  have hr:=right_bound v p hv site
  have ht:=target_bound v p hv site
  have hw:=multiply_word_length v p hv site
  have hm:=scalar_multiply_time v p hv site
  have hc:=linear_cube p
  unfold M.time M.bodyTime M.loadTime
  split <;> omega
/-- Actual full scalar correction source charges its two copies, actual adder, old cache drain and output transfer. -/
theorem correction_time (v:Values) (p:Nat) (hv:Small v p):A.time v≤1000*(p+1)^3:=by
  have ht:=hv.bounded (.aux .two) (by simp [sizedSlots])
  have ho:=hv.bounded (.aux .opposite) (by simp [sizedSlots])
  have hc:=hv.bounded (.aux .correction) (by simp [sizedSlots])
  have hw:=correction_word_length v p hv
  have ha:=SemiprimeD1StackJetScalarAddExecution.totalTime_le (v (.aux .two)) (v (.aux .opposite)) (v .width)
  change SemiprimeD1StackJetScalarAddExecution.totalTime _ _ _≤30*((v (.aux .two)).length+(v (.aux .opposite)).length+(v .width).length+2) at ha
  rw [hv.width] at ha
  have hp:=linear_cube p
  unfold A.time
  omega
/-- Real direct reducer clock pays even all high input/counter leftovers, rather than using the native prefix-only report. -/
theorem reducer_time (v:Values):K.reducerTime v≤5*((v .reduceInput).length+(v .width).length)+11:=by
  have h:=(SemiprimeD1StackReduceExecution.sourceReduce (v .reduceInput) (v .width)).steps_le_m
  change SemiprimeD1StackReduceExecution.trimTime ((v .reduceInput).take (v .width).length).reverse+
    SemiprimeD1StackReduceExecution.prefixTime (v .reduceInput) (v .width)≤_ at h
  unfold K.reducerTime
  omega
/-- Every actual copy/reduce/cache stage is linear in real input bytes and real WIDTH markers. -/
theorem cache_time (v:Values):K.time v≤100*((v .reduceInput).length+(v .width).length+1):=by
  have hr:=reducer_time v
  have hw:=SemiprimeD1JetScalarBits.reduce_length (v .width).length (v .reduceInput)
  change (K.word v).length≤(v .width).length at hw
  unfold K.time
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryFinishOperatorBounds
