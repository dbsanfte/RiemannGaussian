/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshArithmetic
/-! # Actual allocator primitive fragments, preserving the complete acquired context cache -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshPrimitives
open SemiprimeD1StackPhaseChildContextFresh SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Physical width-empty interpretation; no precision-value payload enters finite control. -/
def positive (ph : H.Stack→List Bool) : Bool :=!(ph (H.childStack H.J.widthCache)).isEmpty
/-- Exact chronological fragment composition preserves arbitrary actual caller return cells. -/
theorem join {m n : Nat} {pc mid next : Label} {d e f : Stack→List Bool}
    (h : Runs program m pc d mid e) (g : Runs program n mid e next f) :
    Runs program (m+n) pc d next f :=runs_trans program m n pc mid next d e f h g
/-- Literal history-bit push, with all85 other cache/work views accounted. -/
theorem push_history (pc next : Label) (b : Bool) (hc : program pc=.base (.push (aux .history) b next))
    (ph : H.Stack→List Bool) (rem sk hist out scratch : List Bool) :
    Runs program 1 pc (store ph rem sk hist out scratch) next (store ph rem sk (b::hist) out scratch) :=by
  apply one_base program pc next (.push (aux .history) b next) _ _ hc
  · rfl
  · funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Actual remaining-rank pop; no numerical decrement opcode is used. -/
theorem pop_remaining (pc empty next : Label) (hc : program pc=.base (.pop (aux .remaining) empty next next))
    (ph : H.Stack→List Bool) (rem sk hist out scratch : List Bool) (b : Bool) :
    Runs program 1 pc (store ph (b::rem) sk hist out scratch) next (store ph rem sk hist out scratch) :=by
  apply one_base program pc next (.pop (aux .remaining) empty next next) _ _ hc
  · cases b <;> rfl
  · funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Actual empty remaining-rank pop selects the physical end-of-allocation branch. -/
theorem empty_remaining (pc empty next : Label) (hc : program pc=.base (.pop (aux .remaining) empty next next))
    (ph : H.Stack→List Bool) (sk hist out scratch : List Bool) :
    Runs program 1 pc (store ph [] sk hist out scratch) empty (store ph [] sk hist out scratch) :=by
  apply one_base program pc empty (.pop (aux .remaining) empty next next) _ _ hc
  · rfl
  · funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Actual old-rank skip counter pop, including the later cleanup drain. -/
theorem pop_skip (pc empty next : Label) (hc : program pc=.base (.pop (aux .skip) empty next next))
    (ph : H.Stack→List Bool) (rem sk hist out scratch : List Bool) (b : Bool) :
    Runs program 1 pc (store ph rem (b::sk) hist out scratch) next (store ph rem sk hist out scratch) :=by
  apply one_base program pc next (.pop (aux .skip) empty next next) _ _ hc
  · cases b <;> rfl
  · funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- An actual empty skip pop detects exactly dense index oldrank. -/
theorem empty_skip (pc empty next : Label) (hc : program pc=.base (.pop (aux .skip) empty next next))
    (ph : H.Stack→List Bool) (rem hist out scratch : List Bool) :
    Runs program 1 pc (store ph rem [] hist out scratch) empty (store ph rem [] hist out scratch) :=by
  apply one_base program pc empty (.pop (aux .skip) empty next next) _ _ hc
  · rfl
  · funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- The reduced scalar unit is determined by physically peeking the ACQUIRED width cache. -/
theorem unit_peek (ph : H.Stack→List Bool) (rem hist out scratch : List Bool) :
    Runs program 1 .unit (store ph rem [] hist out scratch)
      (if positive ph then .one0 else .zeroAfter0) (store ph rem [] hist out scratch) :=by
  apply one_base program .unit _ (.peek width .zeroAfter0 .one0 .one0) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose Label.zeroAfter0 Label.one0 Label.one0
      ((ph (H.childStack H.J.widthCache)).head?))=some _
    cases hw:ph (H.childStack H.J.widthCache) with
    | nil=>simp only [positive,hw,List.isEmpty_nil,Bool.not_true];rfl
    | cons b bs=>cases b <;> simp only [positive,hw,List.isEmpty_cons,Bool.not_false,ite_true] <;> rfl
  · rfl
/-- Two physical pushes emit the empty coefficient's actual reverse byte chunk. -/
theorem zero_before (ph : H.Stack→List Bool) (rem sk hist out scratch : List Bool) :
    Runs program 2 .zeroBefore0 (store ph rem sk hist out scratch) .before
      (store ph rem sk ([false,true]++hist) out scratch) :=
  join (push_history .zeroBefore0 .zeroBefore1 true rfl ph rem sk hist out scratch)
    (push_history .zeroBefore1 .before false rfl ph rem sk (true::hist) out scratch)
/-- Two physical pushes emit an empty coefficient after the unit index. -/
theorem zero_after (ph : H.Stack→List Bool) (rem sk hist out scratch : List Bool) :
    Runs program 2 .zeroAfter0 (store ph rem sk hist out scratch) .after
      (store ph rem sk ([false,true]++hist) out scratch) :=
  join (push_history .zeroAfter0 .zeroAfter1 true rfl ph rem sk hist out scratch)
    (push_history .zeroAfter1 .after false rfl ph rem sk (true::hist) out scratch)
/-- Four physical pushes emit the nonzero reduced unit's actual reverse byte chunk. -/
theorem one (ph : H.Stack→List Bool) (rem sk hist out scratch : List Bool) :
    Runs program 4 .one0 (store ph rem sk hist out scratch) .after
      (store ph rem sk ([false,true,true,true]++hist) out scratch) :=
  join (join (join (push_history .one0 .one1 true rfl ph rem sk hist out scratch)
    (push_history .one1 .one2 true rfl ph rem sk (true::hist) out scratch))
    (push_history .one2 .one3 true rfl ph rem sk (true::true::hist) out scratch))
    (push_history .one3 .after false rfl ph rem sk (true::true::true::hist) out scratch)
/-- Real rank preserving copies, including both physical restoration loops and actual return. -/
theorem copy_call (old : Bool) (pc next : Label) (hc : program pc=.call (.copy old 0) next)
    (d : Stack→List Bool) (hs : d (aux .scratch)=[]) (ht : d (if old then aux .skip else aux .remaining)=[]) :
    Runs program (5*(d (if old then oldRank else newRank)).length+4) pc d next
      (Function.update d (if old then aux .skip else aux .remaining) (d (if old then oldRank else newRank))) :=by
  let xs:=d (if old then oldRank else newRank)
  have hi:Link.DataRel (copyStack old) d (SemiprimeD1StackCopy.state 0 none xs [] []).store d:=by
    constructor
    · intro k;fin_cases k
      · rfl
      · exact ht
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (copyStack old) (copy_injective old) _ _ _ hi (1:Fin 3) xs
  have he:Function.update (SemiprimeD1StackCopy.state 0 none xs [] []).store 1 xs=(SemiprimeD1StackCopy.done xs xs).store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  have hr:=SemiprimeD1StackCopy.copy_words xs [] none
  rw [List.append_nil] at hr
  exact included_call program (copyStack old) (Label.copy old) (copy_injective old)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc (5*xs.length+3)
    (SemiprimeD1StackCopy.state 0 none xs [] []) (SemiprimeD1StackCopy.done xs xs) d _ rfl rfl hr hi ho
/-- Real history reversal, with all actual context/rank/width originals retained. -/
theorem reverse_call (ph : H.Stack→List Bool) (hist out : List Bool) :
    Runs program (2*hist.length+3) .reverse (store ph [] [] hist out []) .done
      (store ph [] [] [] (hist.reverse++out) []) :=by
  apply included_call program reverseStack Label.reversal reverse_injective SemiprimeD1StackReverseWord.code 0 (fun _=>rfl)
    .reverse .done rfl (2*hist.length+2) (SemiprimeD1StackReverseWord.state none hist out)
    (SemiprimeD1StackReverseWord.done (hist.reverse++out)) _ _ rfl rfl (SemiprimeD1StackReverseWord.reverse_run hist out none)
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk;rcases k with k|k
      · rfl
      · cases k with
        | remaining=>rfl
        | skip=>rfl
        | history=>exact (hk 0 rfl).elim
        | output=>exact (hk 1 rfl).elim
        | scratch=>rfl
end RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshPrimitives
