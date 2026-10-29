/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEdgeCatalogueClear

/-! # Closed actual scan of the original descriptor tape
Every record is physically parsed/tested; selected records produce exactly two
half-edge records, and every cache is physically cleared before continuation.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackEdgeCatalogueScan
open SemiprimeD1StackEdgeCatalogue SemiprimeD1StackEdgeCatalogueView
open SemiprimeD1StackEdgeCatalogueParse SemiprimeD1StackEdgeCatalogueEmit
open SemiprimeD1StackEdgeCatalogueDispatch SemiprimeD1StackEdgeCatalogueClear
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeD1EdgeCatalogueEncoding (Record record half selected tape output)
open SemiprimeSourceHistogramKeyBits (frame frame_length)

/-- Exact physical reverse accumulator after this one actual record. -/
def afterRaw (words:Record) (raw:List Bool) : List Bool :=
  if selected words then (half false words (half true words [])).reverse++raw else raw
/-- Exact accounted copy/parse/test/emit/clear transition sum. -/
def recordTime (words:Record) : ℕ :=
  1+(8*wordMass words+40)+tagTime (words 0)+(if selected words then 20*wordMass words+132 else 0)+(wordMass words+5)
/-- A real reader peek starts the first field even when its encoded tag is empty. -/
theorem record_head (base:Cat.Stack→List Bool) (words:Record) (tail raw:List Bool) :
    Runs program 1 (.inl .parse) (clean base (record words tail) (fun _=>[]) raw [])
      (.inl (.field 0)) (clean base (record words tail) (fun _=>[]) raw []) := by
  apply one_base program _ _ (.peek reader (.inl .finalReverse) (.inl (.field 0)) (.inl (.field 0))) _ _ rfl
  · have hr:clean base (record words tail) (fun _=>[]) raw [] reader=record words tail:=store_reader _ _ _ _
    change some (SemiprimeD1StackBytecode.choose (Sum.inl Control.finalReverse:Label)
      (.inl (.field 0)) (.inl (.field 0)) (clean base (record words tail) (fun _=>[]) raw [] reader).head?)=
        some (.inl (.field 0))
    rw [hr]
    cases hw:words 0 with
    | nil => simp [SemiprimeD1StackBytecode.choose,record,frame,hw]
    | cons b word => simp [SemiprimeD1StackBytecode.choose,record,frame,hw]
  · rfl
/-- Whole actual one-record trace, all branch decisions derived by its physical test. -/
theorem record_run (base:Cat.Stack→List Bool) (words:Record) (tail raw:List Bool) :
    Runs program (recordTime words) (.inl .parse) (clean base (record words tail) (fun _=>[]) raw [])
      (.inl .parse) (clean base tail (fun _=>[]) (afterRaw words raw) []) := by
  have h0:=record_head base words tail raw
  have h1:=fields_run base words tail raw []
  have h2:=tag_run base tail words raw []
  by_cases hs:selected words
  · change 10≤(words 0).length at hs
    rw [afterTest,ite_eq_left hs] at h2
    have h3:=pair_run base tail words raw
    have h4:=caches_run base tail words ((half false words (half true words [])).reverse++raw) []
    have h:=h0.trans (h1.trans (h2.trans (h3.trans h4)))
    unfold recordTime afterRaw
    simp only [ite_eq_left hs]
    convert h using 1;omega
  · change ¬10≤(words 0).length at hs
    rw [afterTest,ite_eq_right hs] at h2
    have h3:=caches_run base tail words raw []
    have h:=h0.trans (h1.trans (h2.trans h3))
    unfold recordTime afterRaw
    simp only [ite_eq_right hs]
    convert h using 1;omega
/-- Exact actual five-field byte count, independent of any catalogue-size advice. -/
theorem record_length (words:Record) (tail:List Bool) :
    (record words tail).length=2*wordMass words+tail.length+5 := by
  unfold record
  simp only [frame_length]
  unfold wordMass
  omega
/-- Uniform transition cap for a record comes from its actual bytes. -/
theorem recordTime_le (words:Record) : recordTime words≤50*(record words []).length := by
  have ht:=tagTime_le (words 0)
  have hm:(words 0).length≤wordMass words:=by unfold wordMass;omega
  have he:(if selected words then 20*wordMass words+132 else 0)≤20*wordMass words+132:=by split <;> omega
  rw [record_length,List.length_nil]
  unfold recordTime
  omega
/-- A side-plus-descriptor preserves an actual appended tape suffix. -/
theorem half_tail (side:Bool) (words:Record) (xs ys:List Bool) :
    half side words (xs++ys)=half side words xs++ys := by
  calc
    _=half side words []++(xs++ys):=half_append side words (xs++ys)
    _=(half side words []++xs)++ys:=(List.append_assoc _ _ _).symm
    _= _:=congrArg (fun t=>t++ys) (half_append side words xs).symm

/-- The actual two edge records preserve their following catalogue suffix. -/
theorem pair_append (words:Record) (tail:List Bool) :
    half false words (half true words tail)=half false words (half true words [])++tail := by
  rw [half_append true words tail,half_tail]
/-- Accumulation equals the reverse of the original-order output, not reversed records. -/
theorem afterRaw_output (words:Record) (rest:List Record) (raw:List Bool) :
    (output rest []).reverse++afterRaw words raw=(output (words::rest) []).reverse++raw := by
  change (output rest []).reverse++afterRaw words raw=
    (if selected words then half false words (half true words (output rest [])) else output rest []).reverse++raw
  by_cases hs:selected words
  · simp only [afterRaw,ite_eq_left hs]
    rw [pair_append words (output rest []),List.reverse_append,List.append_assoc]
  · simp only [afterRaw,ite_eq_right hs]

/-- Every actual finite tape scan is closed; the runtime has no descriptor/count callback. -/
theorem scan_run (base:Cat.Stack→List Bool) (records:List Record) (raw:List Bool) :
    ∃time≤50*(tape records []).length,Runs program time (.inl .parse)
      (clean base (tape records []) (fun _=>[]) raw []) (.inl .parse)
      (clean base [] (fun _=>[]) ((output records []).reverse++raw) []) := by
  induction records generalizing raw with
  | nil =>
    refine ⟨0,by simp [tape],?_⟩
    simpa only [tape,output,List.foldr_nil,List.reverse_nil,List.nil_append] using
      Runs.refl program (.inl .parse) (clean base [] (fun _=>[]) raw [])
  | cons words rest ih =>
    have h0:=record_run base words (tape rest []) raw
    obtain ⟨time,ht,h1⟩:=ih (afterRaw words raw)
    refine ⟨recordTime words+time,?_,?_⟩
    · have hr:=recordTime_le words
      change recordTime words+time≤50*(record words (tape rest [])).length
      rw [record_append,List.length_append,mul_add]
      exact Nat.add_le_add hr ht
    · have h:=h0.trans h1
      rw [afterRaw_output] at h
      exact h
end RiemannGaussian.SemiprimeD1StackEdgeCatalogueScan
