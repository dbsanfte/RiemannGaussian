/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1NormalizedLinearBits
import RiemannGaussian.SemiprimeD1KernelDenominatorBits
import RiemannGaussian.SemiprimeEncodedRowSelection

/-! # Original kernel entry words
All normalized factors are acquired from actual grid words. Physical products
of their acquired contents and exact bit division produce the remaining power.
Native dimension/displacement and digit-construction stages remain explicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1KernelEntryBits
open scoped BigOperators
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitIndexClipping
open SemiprimeBitIndexGeometry SemiprimeD1RecoveryIntegerBits
open SemiprimeD1WireKernelFactors SemiprimeD1WireKernelOriginal

/-- Ordered cached factor reports and their complete acquisition clock. -/
structure Factors where
  /-- Each retained factor is acquired once. -/
  values : List SemiprimeD1NormalizedLinearBits.Run
  /-- All skip tests, normalization reports and list construction. -/
  clock : ℕ

/-- Physical zero test for the cancelled grid word, without native decoding. -/
def distinct (q d : List Bool) : NonzeroReport :=
  nonzeroBits (subSignedBits (positive q) (positive d)).word.magnitude

/-- The actual cancellation test compares unsigned numeric words. -/
theorem distinct_value (q d : List Bool) :
    (distinct q d).nonzero=true ↔bitValue q≠bitValue d := by
  rw [distinct,nonzeroBits_correct,←signedWord_natAbs,subSignedBits_value]
  simp only [positive_value,Int.natAbs_pos,sub_ne_zero]
  constructor
  · intro h he
    exact h (congrArg (fun n:ℕ=>(n:ℤ)) he)
  · intro h he
    apply h
    exact_mod_cast he

/-- Acquire the omitted grid in its actual order, retaining all reports. -/
def gather (k : ℕ) (j d : List Bool) : List (List Bool) → Factors
  | [] => ⟨[],1⟩
  | q::qs =>
    let delta:=subSignedBits (positive q) (positive d)
    let test:=nonzeroBits delta.word.magnitude
    let tail:=gather k j d qs
    if test.nonzero then
      let factor:=SemiprimeD1NormalizedLinearBits.acquire k j q
      ⟨factor::tail.values,delta.clock+test.clock+tail.clock+factor.clock+5⟩
    else ⟨tail.values,delta.clock+test.clock+tail.clock+3⟩

/-- Cached factors are exactly the physically tested omitted grid. -/
theorem gather_values (k : ℕ) (j d : List Bool) (qs : List (List Bool)) :
    (gather k j d qs).values=
      (qs.filter (fun q=>decide (bitValue q≠bitValue d))).map
        (SemiprimeD1NormalizedLinearBits.acquire k j) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    by_cases h:bitValue q≠bitValue d
    · have ht:=(distinct_value q d).mpr h
      change (nonzeroBits (subSignedBits (positive q) (positive d)).word.magnitude).nonzero=true at ht
      simp only [gather,ht,ite_true,ih,List.filter_cons,decide_eq_true_eq,ite_eq_left h,List.map_cons]
    · have ht:(distinct q d).nonzero=false:=by
        cases he:(distinct q d).nonzero
        · rfl
        · exact False.elim (h ((distinct_value q d).mp he))
      change (nonzeroBits (subSignedBits (positive q) (positive d)).word.magnitude).nonzero=false at ht
      simp only [gather,ht,Bool.false_eq_true,ite_false,ih,List.filter_cons,
        decide_eq_true_eq,ite_eq_right h]

/-- Proof-only original linear interpretation of an acquired factor. -/
def linear (f : SemiprimeD1NormalizedLinearBits.Run) : Linear :=
  ⟨f.constant.value,bitValue f.slope⟩

/-- Every acquired factor has the original normalized linear interpretation. -/
theorem linear_value (k : ℕ) (j q : List Bool)
    (hj:bitValue j<2^k) (hq:bitValue q<2^k) :
    linear (SemiprimeD1NormalizedLinearBits.acquire k j q)=
      normalizedFactor k (bitValue j) (bitValue q) := by
  have hc:=SemiprimeD1NormalizedLinearBits.acquire_constant k j q
  have hs:=SemiprimeD1NormalizedLinearBits.acquire_slope k j q hj hq
  cases he:normalizedFactor k (bitValue j) (bitValue q) with
  | mk c s =>
    rw [he] at hc hs
    change (⟨_,_⟩:Linear)=⟨c,s⟩
    simp only [hc,hs]

/-- Original normalized factors in the actual input word order. -/
theorem gather_linear (k : ℕ) (j d : List Bool) (qs : List (List Bool))
    (hj:bitValue j<2^k) (hqs:∀q∈qs,bitValue q<2^k) :
    ((gather k j d qs).values.map linear)=
      (((qs.map bitValue).filter (fun q=>decide (q≠bitValue d))).map
        (normalizedFactor k (bitValue j))) := by
  rw [gather_values]
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    have hq:=hqs q List.mem_cons_self
    have ht:=ih (fun z hz=>hqs z (List.mem_cons_of_mem q hz))
    by_cases he:bitValue q≠bitValue d
    · simp only [List.map_cons,List.filter_cons,decide_eq_true_eq,ite_eq_left he,
        linear_value k j q hj hq,ht]
    · simp only [List.map_cons,List.filter_cons,decide_eq_true_eq,ite_eq_right he,ht]

/-- Acquired contents multiply to their exact original dyadic product. -/
theorem gather_contents (k : ℕ) (j d : List Bool) (qs : List (List Bool)) :
    ((gather k j d qs).values.map (fun f=>bitValue f.content)).prod=
      ((((qs.map bitValue).filter (fun q=>decide (q≠bitValue d))).map
        (fun q=>2^factorOrder k (bitValue j) q))).prod := by
  rw [gather_values]
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    by_cases he:bitValue q≠bitValue d
    · simp only [List.map_cons,List.filter_cons,decide_eq_true_eq,ite_eq_left he,
        SemiprimeD1NormalizedLinearBits.acquire_content,List.prod_cons,ih]
    · simp only [List.map_cons,List.filter_cons,decide_eq_true_eq,ite_eq_right he,ih]

/-- Complete physical original entry and its acquired content product. -/
structure Run where
  /-- Ordered actual linear factor words. -/
  factors : List SemiprimeD1NormalizedLinearBits.Run
  /-- Remaining integral power, acquired by physical quotient. -/
  powerFactor : List Bool
  /-- Actual signed odd normalizer word. -/
  denominator : SignedWord
  /-- Actual numerator content product, retained for audit/composition. -/
  numeratorContent : List Bool
  /-- Every setup, factor, product, denominator and division report. -/
  clock : ℕ

/-- Original-input constructor. No factor, denominator or exponent is supplied. -/
def acquireOriginal (a : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) : Run :=
  let grid:=SemiprimeSourceCompactWordIds.acquire (size a)
  let j:=SemiprimeEncodedRowSelection.digits (a+1) t.val
  let d:=SemiprimeEncodedRowSelection.digits (a+1) (displacement a x y).val
  let fs:=gather (a+1) j.bits d.bits grid.value
  let numerator:=SemiprimeD1KernelProductBits.run (fs.values.map (fun f=>positive f.content))
  let denominator:=SemiprimeD1KernelDenominatorBits.run a
  let power:=divideBits numerator.word.magnitude denominator.content
  ⟨fs.values,power.quotient,denominator.word,numerator.word.magnitude,
    grid.work+j.work+d.work+fs.clock+numerator.clock+denominator.clock+power.clock+12⟩

/-- The actual signed odd denominator is the original constructor's unit. -/
theorem acquire_denominator (a : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) :
    (acquireOriginal a t x y).denominator.value=
      (SemiprimeD1WireKernelOriginal.acquireOriginal a t x y).denominator :=
  SemiprimeD1KernelDenominatorBits.run_value a
/-- Unsigned physical content multiplication has no signed-value ambiguity. -/
theorem positive_product_value (xs : List (List Bool)) :
    bitValue (SemiprimeD1KernelProductBits.run (xs.map positive)).word.magnitude=
      (xs.map bitValue).prod := by
  rw [←signedWord_natAbs,SemiprimeD1KernelProductBits.run_value]
  have he:((xs.map positive).map SignedWord.value).prod=
      ((xs.map bitValue).prod:ℤ):=by
    rw [Nat.cast_list_prod,List.map_map,List.map_map]
    rfl
  rw [he,Int.natAbs_natCast]

/-- Ordered acquired words give precisely the original entry factor list. -/
theorem acquire_factors (a : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) :
    ((acquireOriginal a t x y).factors.map linear)=
      (SemiprimeD1WireKernelOriginal.acquireOriginal a t x y).factors := by
  dsimp only [acquireOriginal]
  rw [gather_linear]
  · rw [SemiprimeSourceCompactWordIds.acquire_values,
      SemiprimeEncodedRowSelection.digits_value (a+1) t.val t.isLt,
      SemiprimeEncodedRowSelection.digits_value (a+1) (displacement a x y).val
        (displacement a x y).isLt]
    rfl
  · rw [SemiprimeEncodedRowSelection.digits_value (a+1) t.val t.isLt]
    exact t.isLt
  · intro q hq
    exact SemiprimeSourceCompactWordIds.acquire_value_lt (size a) q hq

/-- Physical content multiplication is the original finite power product. -/
theorem acquire_numeratorContent (a : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) :
    bitValue (acquireOriginal a t x y).numeratorContent=
      2^(∑q∈(Finset.range (size a)).erase (displacement a x y).val,
        factorOrder (a+1) t.val q) := by
  dsimp only [acquireOriginal]
  have hp (fs:List SemiprimeD1NormalizedLinearBits.Run) :
      bitValue (SemiprimeD1KernelProductBits.run
        (fs.map (fun f=>positive f.content))).word.magnitude=
        (fs.map (fun f=>bitValue f.content)).prod := by
    simpa only [List.map_map,Function.comp_def] using positive_product_value (fs.map (fun f=>f.content))
  rw [hp]
  rw [gather_contents,SemiprimeSourceCompactWordIds.acquire_values,
    SemiprimeEncodedRowSelection.digits_value (a+1) t.val t.isLt,
    SemiprimeEncodedRowSelection.digits_value (a+1) (displacement a x y).val
      (displacement a x y).isLt]
  change ((SemiprimeD1WireKernelEntry.indices (a+1) (displacement a x y).val).map _).prod=_
  rw [←List.prod_toFinset _ (SemiprimeD1WireKernelEntry.indices_nodup _ _),
    SemiprimeD1WireKernelEntry.indices_toFinset,Finset.prod_pow_eq_pow_sum]
  rfl
/-- Original denominator cancellation is computed by physical unsigned division. -/
theorem acquire_powerFactor (a : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) :
    bitValue (acquireOriginal a t x y).powerFactor=
      2^(SemiprimeD1WireKernelOriginal.acquireOriginal a t x y).power := by
  have hn:=acquire_numeratorContent a t x y
  have hd:=SemiprimeD1KernelDenominatorBits.run_content a
  have he:=omitted_content_ge (a+1) t.val (displacement a x y).val t.isLt
    (displacement a x y).isLt
  have hex:(∑q∈(Finset.range (size a)).erase (displacement a x y).val,
      factorOrder (a+1) t.val q)=
      SemiprimeD1WireKernelEntry.content (a+1)+excess (a+1) t.val (displacement a x y).val:=by
    unfold excess SemiprimeD1WireKernelEntry.content
    exact Nat.sub_add_cancel he |>.symm.trans (Nat.add_comm _ _)
  change bitValue (divideBits (acquireOriginal a t x y).numeratorContent
      (SemiprimeD1KernelDenominatorBits.run a).content).quotient=_
  rw [(divideBits_correct _ _).1,hn,hd,hex,pow_add]
  have hp:0<2^SemiprimeD1WireKernelEntry.content (a+1):=by positivity
  exact Nat.mul_div_right _ hp
end RiemannGaussian.SemiprimeD1KernelEntryBits
