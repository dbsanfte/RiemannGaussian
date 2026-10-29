/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEdgeCatalogueParse

/-! # Actual fixed ten-marker constructor dispatch -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackEdgeCatalogueDispatch
open SemiprimeD1StackEdgeCatalogue SemiprimeD1StackEdgeCatalogueComponents
open SemiprimeD1StackEdgeCatalogueView
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeD1EdgeCatalogueEncoding (Record)

/-- Static test-stage label; index ten is its success continuation. -/
def testLabel (i:ℕ) : Label := if h:i<10 then .inl (.test ⟨i,h⟩) else .inl (.clearTest true)
/-- Exact actual scan cost, including the first encountered EOF. -/
def testTime : ℕ→List Bool→ℕ
  | 0,_ => 0
  | _+1,[] => 1
  | n+1,_::word => 1+testTime n word
/-- The bounded static tag scan cannot exceed eleven real pops. -/
theorem testTime_le (n:ℕ) (word:List Bool) : testTime n word≤n+1 := by
  induction n generalizing word with
  | zero => simp [testTime]
  | succ n ih => cases word with
    | nil => simp [testTime]
    | cons b word => simp only [testTime];have h:=ih word;omega
/-- The literal next-label expression is exactly the next static test stage. -/
theorem next_test (i:ℕ) (hi:i<10) :
    (if h:i<9 then Sum.inl (Control.test ⟨i+1,by omega⟩) else .inl (.clearTest true):Label)=testLabel (i+1) := by
  by_cases h:i<9
  · have hn:i+1<10:=by omega
    simp [testLabel,h,hn]
  · have hn:¬i+1<10:=by omega
    simp [testLabel,h,hn]
/-- Actual tag classification, not a decoded tag/count supplied by the caller. -/
theorem test_run (n i:ℕ) (hi:i+n=10) (word:List Bool) (data:Stack→List Bool) :
    Runs program (testTime n word) (testLabel i) (Function.update data (aux .tagReader) word)
      (.inl (.clearTest (decide (n≤word.length))))
      (Function.update data (aux .tagReader) (word.drop n)) := by
  induction n generalizing i word with
  | zero =>
    have he:i=10:=by omega
    subst i
    simpa [testLabel,testTime] using Runs.refl program (.inl (.clearTest true)) (Function.update data (aux .tagReader) word)
  | succ n ih =>
    have hit:i<10:=by omega
    have hc:program (.inl (.test ⟨i,hit⟩))=
        .base (.pop (aux .tagReader) (.inl (.clearTest false)) (testLabel (i+1)) (testLabel (i+1))):=by
      simpa only [program] using congrArg (fun next:Label=>(.base
        (.pop (aux .tagReader) (.inl (.clearTest false)) next next):C.Instruction Stack Label)) (next_test i hit)
    cases word with
    | nil =>
      have h:Runs program 1 (.inl (.test ⟨i,hit⟩)) (Function.update data (aux .tagReader) [])
          (.inl (.clearTest false)) (Function.update data (aux .tagReader) []):=by
        apply one_base program _ _ (.pop (aux .tagReader) (.inl (.clearTest false)) (testLabel (i+1)) (testLabel (i+1))) _ _ hc
        · simp [B.execute,SemiprimeD1StackBytecode.choose,Function.update_self]
        · change Function.update (Function.update data (aux .tagReader) []) (aux .tagReader) []=_
          rw [Function.update_idem]
      simpa [testLabel,hit,testTime] using h
    | cons bit word =>
      have h0:Runs program 1 (.inl (.test ⟨i,hit⟩)) (Function.update data (aux .tagReader) (bit::word))
          (testLabel (i+1)) (Function.update data (aux .tagReader) word):=by
        apply one_base program _ _ (.pop (aux .tagReader) (.inl (.clearTest false)) (testLabel (i+1)) (testLabel (i+1))) _ _ hc
        · cases bit <;> simp [B.execute,SemiprimeD1StackBytecode.choose,Function.update_self]
        · change Function.update (Function.update data (aux .tagReader) (bit::word)) (aux .tagReader) word=_
          rw [Function.update_idem]
      have h1:=ih (i+1) (by omega) word
      simpa [testTime,testLabel,hit] using h0.trans h1

/-- Exact static destination after clearing the physical tag-test buffer. -/
def afterTest (tag:List Bool) : Label :=
  if 10≤tag.length then .inl (.emitFrame false 0) else .inl (.clearCache 0)
/-- Actual tag acquisition/test/cleanup time. -/
def tagTime (tag:List Bool) : ℕ := 5*tag.length+4+testTime 10 tag+(tag.drop 10).length+1
/-- The actual tag path has a closed linear bound. -/
theorem tagTime_le (tag:List Bool) : tagTime tag≤6*tag.length+16 := by
  have h:=testTime_le 10 tag
  have hd: (tag.drop 10).length≤tag.length:=by simp only [List.length_drop];omega
  unfold tagTime
  omega
/-- Closed actual copy/test/clear trace on the fields just physically read. -/
theorem tag_run (base:Cat.Stack→List Bool) (tape:List Bool) (words:Record) (raw side:List Bool) :
    Runs program (tagTime (words 0)) (.inl .copyTag) (clean base tape words raw side)
      (afterTest (words 0)) (clean base tape words raw side) := by
  let before:=clean base tape words raw side
  have h0:=copy_call before rfl
  change Runs program (5*(words 0).length+4) _ before _
    (Function.update before (aux .tagReader) ((words 0)++[])) at h0
  rw [List.append_nil] at h0
  have h1:=test_run 10 0 rfl (words 0) before
  have h2:=clear_run ((words 0).drop 10)
    (.inl (.clearTest (decide (10≤(words 0).length)))) (afterTest (words 0)) (aux .tagReader)
    (Function.update before (aux .tagReader) ((words 0).drop 10)) (Function.update_self _ _ _)
    (by by_cases h:10≤(words 0).length <;> simp [program,afterTest,h])
  rw [Function.update_idem] at h2
  have he:Function.update before (aux .tagReader) []=before:=by
    have hh:before (aux .tagReader)=[]:=rfl
    rw [←hh]
    exact Function.update_eq_self _ _
  rw [he] at h2
  have h:=h0.trans (h1.trans h2)
  change Runs program _ _ before _ before at h
  unfold tagTime
  convert h using 1;omega
end RiemannGaussian.SemiprimeD1StackEdgeCatalogueDispatch
