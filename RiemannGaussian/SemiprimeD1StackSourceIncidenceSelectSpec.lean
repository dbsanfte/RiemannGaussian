/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1IncidenceSearch
import RiemannGaussian.SemiprimeD1StackWordLessExecution
/-! # Exact forward candidate order, strict improvement and original ties
This module contains mathematical refinement facts only. Score functions below
are not runtime data/control or evaluator instructions. The physical controller
will instantiate them with its actual closed incidence source and stored words.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectSpec
open SemiprimeBitArithmetic (bitValue)
/-- Left-biased minimum: the incumbent is retained on EVERY equality. -/
def pick {α:Type} (score:α→Nat) (a b:α) :α :=if score a ≤ score b then a else b
/-- Left-biased minimum is associative, so each actual candidate score is acquired only once. -/
theorem pick_assoc {α:Type} (score:α→Nat) (a b c:α) :
    pick score (pick score a b) c=pick score a (pick score b c) :=by
  by_cases hab:score a ≤ score b <;> by_cases hbc:score b ≤ score c <;> by_cases hac:score a ≤ score c <;>
    simp only [pick,hab,hbc,hac,ite_true,ite_false]
  all_goals omega
/-- Mathematical exact old tail-first candidate order, used only in refinement. -/
def tailChoice {α:Type} (score:α→Nat) (a:α) :List α→α
  | []=>a
  | b::bs=>pick score a (tailChoice score b bs)
/-- A forward scan retaining the actual incumbent on ties returns the exact same literal ID as the old choice. -/
theorem forward_choice {α:Type} (score:α→Nat) (a:α) (rest:List α) :
    rest.foldl (pick score) a=tailChoice score a rest :=by
  let inst:Std.Associative (pick score):=⟨pick_assoc score⟩
  induction rest generalizing a with
  | nil=>rfl
  | cons b rest ih=>rw [List.foldl_cons,List.foldl_assoc,ih];rfl
/-- Mathematical pair of an actual copied candidate ID and its actual acquired binary score. -/
abbrev Scored :=List Bool×List Bool
/-- Actual strict-improvement rule on stored words; no incumbent score is recomputed. -/
def scoredPick (best candidate:Scored) :Scored :=
  if bitValue candidate.2 < bitValue best.2 then candidate else best
/-- Physical numeric comparison accepts arbitrary high-zero score padding and produces EXACTstrict improvement. -/
theorem real_less_pick (best candidate:Scored) :
    (if SemiprimeD1StackWordLessExecution.answer candidate.2 best.2 then candidate else best)=scoredPick best candidate :=by
  by_cases h:SemiprimeD1StackWordLessExecution.answer candidate.2 best.2=true
  · have hn:bitValue candidate.2 < bitValue best.2:=(SemiprimeD1StackWordLessExecution.answer_true _ _).mp h
    simp only [h,ite_true,scoredPick,hn]
  · have hn:¬bitValue candidate.2 < bitValue best.2:=fun hn=>h ((SemiprimeD1StackWordLessExecution.answer_true _ _).mpr hn)
    simp only [h,ite_false,scoredPick,hn,Bool.false_eq_true]
/-- Tied numeric scores retain BOTHthe first actual ID and its actual copied score word. -/
theorem scoredPick_tie (a b:Scored) (h:bitValue a.2=bitValue b.2) :scoredPick a b=a :=by
  simp only [scoredPick,h,Nat.lt_irrefl,ite_false]
/-- Actual cached score-pair update is the exact left-biased semantic candidate update. -/
theorem scoredPick_scored (score:List Bool→List Bool) (a b:List Bool) :
    scoredPick (a,score a) (b,score b)=
      (pick (fun id=>bitValue (score id)) a b,score (pick (fun id=>bitValue (score id)) a b)) :=by
  by_cases h:bitValue (score a) ≤ bitValue (score b)
  · have hn:¬bitValue (score b) < bitValue (score a):=by omega
    simp only [scoredPick,pick,h,hn,ite_true,ite_false]
  · have hn:bitValue (score b) < bitValue (score a):=by omega
    simp only [scoredPick,pick,h,hn,ite_true,ite_false]
/-- Forward retained-score scan refines exact old order while copying only actually acquired score words. -/
theorem scored_forward (score:List Bool→List Bool) (a:List Bool) (rest:List (List Bool)) :
    (rest.map (fun id=>(id,score id))).foldl scoredPick (a,score a)=
      (rest.foldl (pick (fun id=>bitValue (score id))) a,
        score (rest.foldl (pick (fun id=>bitValue (score id))) a)) :=by
  induction rest generalizing a with
  | nil=>rfl
  | cons b rest ih=>rw [List.map_cons,List.foldl_cons,scoredPick_scored,ih,List.foldl_cons]
/-- Whole exact choice includes all original ties, rather than merely returning some minimizer. -/
theorem scored_choice (score:List Bool→List Bool) (a:List Bool) (rest:List (List Bool)) :
    ((rest.map (fun id=>(id,score id))).foldl scoredPick (a,score a)).1=
      tailChoice (fun id=>bitValue (score id)) a rest :=by
  rw [scored_forward,forward_choice]
/-- Every exact tail-first minimum is one of the actual supplied candidates, including duplicate IDs. -/
theorem tailChoice_mem {α:Type} (score:α→Nat) (a:α) (rest:List α) :tailChoice score a rest∈a::rest :=by
  induction rest generalizing a with
  | nil=>exact List.mem_cons_self
  | cons b rest ih=>
    change pick score a (tailChoice score b rest)∈a::b::rest
    unfold pick
    split
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (ih b)
/-- Integer score equality at the actual menu entries preserves the literal original rational-report choice. -/
theorem tailChoice_reports (score:List Bool→Nat)
    (report:List Bool→SemiprimeRationalBits.RationalReport) (a:List Bool) (rest:List (List Bool))
    (hv:∀x∈a::rest,(report x).word.Valid)
    (hs:∀x∈a::rest,(report x).word.value=(score x:Rat)) :
    tailChoice score a rest=(SemiprimeSourceChoiceBits.choose report a rest).value :=by
  induction rest generalizing a with
  | nil=>simp only [tailChoice,SemiprimeSourceChoiceBits.choose,SemiprimeSourceChoiceBits.copyID_value]
  | cons b rest ih=>
    have ht:=ih b (fun x hx=>hv x (List.mem_cons_of_mem a hx))
      (fun x hx=>hs x (List.mem_cons_of_mem a hx))
    have hm:=SemiprimeSourceChoiceBits.choose_mem report b rest
    have hvb:=hv _ (List.mem_cons_of_mem a hm)
    have hsb:=hs _ (List.mem_cons_of_mem a hm)
    simp only [tailChoice,SemiprimeSourceChoiceBits.choose,SemiprimeSourceChoiceBits.copyID_value]
    rw [SemiprimeSourceComparisonBits.compare_branch _ _ (hv a List.mem_cons_self) hvb,
      hs a List.mem_cons_self,hsb]
    simp only [Nat.cast_le,←ht,pick]
/-- Equality of actual numeric scores on the consumed menu preserves its exact left-biased choice. -/
theorem tailChoice_congr {α:Type} (left right:α→Nat) (a:α) (rest:List α)
    (h:∀x∈a::rest,left x=right x) :tailChoice left a rest=tailChoice right a rest :=by
  induction rest generalizing a with
  | nil=>rfl
  | cons b rest ih=>
    have ht:=ih b (fun x hx=>h x (List.mem_cons_of_mem a hx))
    have hm:=tailChoice_mem right b rest
    simp only [tailChoice,ht,pick,h a List.mem_cons_self,h _ (List.mem_cons_of_mem a hm)]
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectSpec
