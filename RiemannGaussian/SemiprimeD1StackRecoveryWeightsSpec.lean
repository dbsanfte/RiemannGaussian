/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryNodeBits
import RiemannGaussian.SemiprimeD1StackRecoveryPowersOriginal
/-! # Exact complete native local-weight bytes in physical descending-fold order
These are proof-side word/order descriptions. The actual source will parse the
acquired two-field tapes and run every normalized/twice-fitted operation itself.
No native report clock, coefficient getter or operation callback is executed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsSpec
open SemiprimeRationalBits
/-- Actual rational-array lookup specification, including literal unfitted ZERO on EOF. -/
def readWord (xs:List RationalWord) (i:Nat):RationalWord:=(xs[i]?).getD zeroWord
/-- The actual native address/read report returns EXACT same raw word at every visited original index. -/
theorem read_native (q:Nat) (xs:List RationalWord) (i:Nat) (hi:i<q):
    (SemiprimeD1RecoveryScalarWeightBits.read q xs i).word=readWord xs i:=by
  have hp:i<2^(q+1):=hi.trans_le
    ((SemiprimeD1HermiteDenominatorBits.self_le_two_power q).trans
      (Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)))
  change (SemiprimeSourceMemoryBits.readWord xs (SemiprimeEncodedRowSelection.digits (q+1) i).bits).word=_
  rw [SemiprimeSourceMemoryBits.readWord_word,SemiprimeEncodedRowSelection.digits_value _ _ hp]
  rfl
/-- Every scalar pair has the literal original multiplication/addition order and both fits. -/
def combine (width:List Bool) (inverse powers:List RationalWord) (j k:Nat) (suffix:RationalWord):RationalWord:=
  (executeOperation .add (executeOperation .mul (readWord inverse (k-j)) (readWord powers k) width).word suffix width).word
/-- Exact raw right-fold step, including the original lower-index skip. -/
def step (width:List Bool) (inverse powers:List RationalWord) (j k:Nat) (suffix:RationalWord):RationalWord:=
  if j≤k then combine width inverse powers j k suffix else suffix
/-- Native sum is this EXACT raw right fold, not merely an equal rational value. -/
theorem sum_fold (width:List Bool) (q j:Nat) (inverse powers:List RationalWord) (keys:List Nat)
    (hk:∀k∈keys,k<q):
    (SemiprimeD1RecoveryScalarWeightBits.sum width q j inverse powers keys).word=
      keys.foldr (step width inverse powers j) zeroWord:=by
  induction keys with
  | nil=>rfl
  | cons k ks ih=>
    have hkt:=hk k List.mem_cons_self
    have ht:=ih (fun i hi=>hk i (List.mem_cons_of_mem k hi))
    by_cases hj:j≤k
    · simp only [SemiprimeD1RecoveryScalarWeightBits.sum,hj,ite_true,List.foldr_cons,step]
      rw [ht,read_native q inverse (k-j) (by omega),read_native q powers k hkt]
      rfl
    · simp only [SemiprimeD1RecoveryScalarWeightBits.sum,hj,ite_false,List.foldr_cons,step]
      exact ht
/-- Actual decreasing count describes the same complete suffix accumulator. -/
def dotLoop (width:List Bool) (inverse powers:List RationalWord) (j:Nat):Nat→RationalWord→RationalWord
  | 0,acc=>acc
  | n+1,acc=>dotLoop width inverse powers j n (combine width inverse powers j (j+n) acc)
/-- Descending physical k executes product-FIRST/suffix-SECOND in the exact native right-fold order. -/
theorem dotLoop_fold (width:List Bool) (inverse powers:List RationalWord) (j n:Nat) (acc:RationalWord):
    dotLoop width inverse powers j n acc=
      (List.range' j n).reverse.foldl (fun suffix k=>combine width inverse powers j k suffix) acc:=by
  induction n generalizing acc with
  | zero=>rfl
  | succ n ih=>
    rw [dotLoop,ih]
    simp only [List.range'_1_concat,List.reverse_append,List.reverse_singleton,List.foldl_append,List.foldl_cons,List.foldl_nil]
/-- All lower indices are skipped WITHOUT executing any scalar operation, exactly as in the native sum. -/
theorem skip_fold (width:List Bool) (inverse powers:List RationalWord) (j:Nat) (keys:List Nat)
    (hk:∀k∈keys,k<j) (acc:RationalWord):keys.foldr (step width inverse powers j) acc=acc:=by
  induction keys with
  | nil=>rfl
  | cons k ks ih=>
    have hkj:=hk k List.mem_cons_self
    have ht:=ih (fun i hi=>hk i (List.mem_cons_of_mem k hi))
    simp only [List.foldr_cons,step,show ¬j≤k by omega,ite_false,ht]
/-- Actual visited indices retain EVERY product/add operation, including zero-valued fields. -/
theorem keep_fold (width:List Bool) (inverse powers:List RationalWord) (j:Nat) (keys:List Nat)
    (hk:∀k∈keys,j≤k) (acc:RationalWord):
    keys.foldr (step width inverse powers j) acc=keys.foldr (combine width inverse powers j) acc:=by
  induction keys with
  | nil=>rfl
  | cons k ks ih=>
    have hkj:=hk k List.mem_cons_self
    have ht:=ih (fun i hi=>hk i (List.mem_cons_of_mem k hi))
    simp only [List.foldr_cons,step,hkj,ite_true,ht]
/-- The complete descending paid pair loop is byte-identical to native sum on ALL original ascending indices. -/
theorem sum_original (width:List Bool) (q j:Nat) (inverse powers:List RationalWord) (hj:j≤q):
    dotLoop width inverse powers j (q-j) zeroWord=
      (SemiprimeD1RecoveryScalarWeightBits.sum width q j inverse powers (SemiprimeD1RecoveryScalarRun.indices q).value).word:=by
  rw [SemiprimeD1RecoveryScalarRun.indices_value,sum_fold width q j inverse powers (List.range q)
    (fun k hk=>List.mem_range.mp hk)]
  have hr:List.range q=List.range j++List.range' j (q-j):=by
    conv_lhs=>rw [show q=j+(q-j) by omega]
    rw [List.range_add,←List.range'_eq_map_range]
  rw [hr,List.foldr_append,skip_fold width inverse powers j (List.range j) (fun k hk=>List.mem_range.mp hk)]
  have hkeep:∀k∈List.range' j (q-j),j≤k:=by
    intro k hk
    rw [List.range'_eq_map_range] at hk
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp hk
    omega
  rw [keep_fold width inverse powers j _ hkeep,dotLoop_fold,List.foldl_reverse]
/-- Final actual normalized multiplication uses acquired Ezero FIRST and entire actual sum SECOND. -/
def weight (width:List Bool) (q j:Nat) (scalar:RationalWord) (inverse powers:List RationalWord):RationalWord:=
  (executeOperation .mul scalar (dotLoop width inverse powers j (q-j) zeroWord) width).word
/-- Full raw weight equality to the authoritative constructor has no Valid/Fits or normalized-answer premise. -/
theorem weight_original (width:List Bool) (q j:Nat) (scalar:RationalWord) (inverse powers:List RationalWord) (hj:j≤q):
    weight width q j scalar inverse powers=
      (SemiprimeD1RecoveryScalarWeightBits.weight width q j scalar inverse powers (SemiprimeD1RecoveryScalarRun.indices q).value).word:=by
  rw [weight,sum_original width q j inverse powers hj]
  rfl
/-- Whole original ascending array; physical descending j/prepend will acquire this order. -/
def array (width:List Bool) (q:Nat) (scalar:RationalWord) (inverse powers:List RationalWord):List RationalWord:=
  (List.range q).map (fun j=>weight width q j scalar inverse powers)
/-- Exact entire native weights report word list, with its report clock deliberately absent. -/
theorem weights_words (width:List Bool) (q:Nat) (scalar:RationalWord) (inverse powers:List RationalWord) (keys js:List Nat):
    (SemiprimeD1RecoveryNodeBits.weights width q scalar inverse powers keys js).words=
      js.map (fun j=>(SemiprimeD1RecoveryScalarWeightBits.weight width q j scalar inverse powers keys).word):=by
  induction js with
  | nil=>rfl
  | cons j js ih=>simp only [SemiprimeD1RecoveryNodeBits.weights,List.map_cons,ih]
/-- Complete array identity preserves ALL raw bytes and every original index, including q0/W0/invalid fields. -/
theorem array_original (width:List Bool) (q:Nat) (scalar:RationalWord) (inverse powers:List RationalWord):
    array width q scalar inverse powers=
      (SemiprimeD1RecoveryNodeBits.weights width q scalar inverse powers (SemiprimeD1RecoveryScalarRun.indices q).value
        (SemiprimeD1RecoveryScalarRun.indices q).value).words:=by
  rw [weights_words,SemiprimeD1RecoveryScalarRun.indices_value]
  apply List.map_congr_left
  intro j hj
  simpa only [SemiprimeD1RecoveryScalarRun.indices_value] using weight_original width q j scalar inverse powers (List.mem_range.mp hj).le
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsSpec
