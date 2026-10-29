/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCarryEquation
import RiemannGaussian.SemiprimeD1StackAdderExecution
/-! # Actual four-field parse, INTEGER shift, sums and comparison -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackCarryEquationExecution
open SemiprimeD1StackCarryEquation SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeBitArithmetic (addBits)
open SemiprimeBitFermatArithmetic (shiftTemplateBits)
/-- Actual shifted byte specification; not an executing supplier. -/
def shifted (cached next : List Bool) : List Bool := List.replicate cached.length false++next
/-- Exact old integer-shift bytes, including all physical template cells. -/
theorem shifted_original (cached next : List Bool) : shifted cached next=(shiftTemplateBits cached next).bits := by
  induction cached with
  | nil=>rfl
  | cons b bs ih=>simpa only [shifted,List.length_cons,List.replicate_succ,List.cons_append,shiftTemplateBits] using congrArg (List.cons false) ih
/-- Exact original integer carry Boolean, used solely in the output theorem. -/
def answer (cached coefficient previous target next : List Bool) : Bool :=
  (SemiprimeMacroEntryBitPrimitives.carryEquationBits cached coefficient previous target next).accepted
/-- Final complete cleared store, retaining original suffix and cached template. -/
def finalData (cached coefficient previous target next tail : List Bool) : Stack→List Bool :=
  store tail cached [] [] [] [] [] [] [] [] [] [answer cached coefficient previous target next]
/-- Actual whole clean halt. -/
def done (cached coefficient previous target next tail : List Bool) : C.State Stack Label :=
  ⟨none,none,none,finalData cached coefficient previous target next tail,[]⟩
/-- Actual executed adder transition count. -/
def addTime (a b : List Bool) : ℕ := 3*(max a.length b.length+1)+2*(addBits a b false).bits.length+2
/-- Each framed source cell is parsed by actual included finite code and its
PHYSICALLY PRODUCED true validity cell is consumed by a real pop. -/
theorem field_call (k : Fin 4) (word tail : List Bool) (data result : Stack→List Bool)
    (hi : SemiprimeD1StackMultiplierLink.DataRel (fieldStack k) data
      (F.initial (frame word tail) []).store data)
    (ho : SemiprimeD1StackMultiplierLink.DataRel (fieldStack k) data
      (Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true]))
      (Function.update result .valid [true]))
    (hresult : result .valid=[]) :
    Runs program (8*word.length+8) (.read k) data (afterField k) result := by
  have h0 : Runs program (8*word.length+7) (.read k) data (.check k) (Function.update result .valid [true]) := by
    apply included_call program (fieldStack k) (Label.field k) (field_injective k) F.code
      (F.active .tagPop (none,false)) (fun _=>rfl) (.read k) (.check k) rfl
      (8*word.length+6) (F.initial (frame word tail) [])
      (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩:
        SemiprimeD1StackBytecode.State F.Stack F.Label) data (Function.update result .valid [true])
      rfl rfl (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hi ho
  have h1 : Runs program 1 (.check k) (Function.update result .valid [true]) (afterField k) result := by
    apply one_base program (.check k) (afterField k) (.pop .valid .bad .bad (afterField k)) _ _ rfl
    · rfl
    · change Function.update (Function.update result .valid [true]) .valid []=result
      rw [Function.update_idem,←hresult]
      exact Function.update_eq_self _ _
  have h:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
  simpa only [show 8*word.length+7+1=8*word.length+8 by omega] using h

/-- Actual original field 1, with earlier payloads physically retained. -/
theorem read_coefficient (cached coefficient previous target next tail : List Bool) :
    Runs program (8*coefficient.length+8) (.read 0) (store (frame coefficient (frame previous (frame target (frame next (tail))))) cached [] [] [] [] [] [] [] [] [] [])
      (.read 1) (store (frame previous (frame target (frame next (tail)))) cached [] [] [] coefficient [] [] [] [] [] []) := by
  apply field_call 0 coefficient (frame previous (frame target (frame next (tail)))) _ _
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk (.inl .input) rfl).elim | exact (hk (.inl .output) rfl).elim | exact (hk (.inr ()) rfl).elim
  · rfl

/-- Actual original field 2, with earlier payloads physically retained. -/
theorem read_previous (cached coefficient previous target next tail : List Bool) :
    Runs program (8*previous.length+8) (.read 1) (store (frame previous (frame target (frame next (tail)))) cached [] [] [] coefficient [] [] [] [] [] [])
      (.read 2) (store (frame target (frame next (tail))) cached [] [] [] coefficient previous [] [] [] [] []) := by
  apply field_call 1 previous (frame target (frame next (tail))) _ _
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk (.inl .input) rfl).elim | exact (hk (.inl .output) rfl).elim | exact (hk (.inr ()) rfl).elim
  · rfl

/-- Actual original field 3, with earlier payloads physically retained. -/
theorem read_target (cached coefficient previous target next tail : List Bool) :
    Runs program (8*target.length+8) (.read 2) (store (frame target (frame next (tail))) cached [] [] [] coefficient previous [] [] [] [] [])
      (.read 3) (store (frame next (tail)) cached [] [] [] coefficient previous target [] [] [] []) := by
  apply field_call 2 target (frame next (tail)) _ _
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk (.inl .input) rfl).elim | exact (hk (.inl .output) rfl).elim | exact (hk (.inr ()) rfl).elim
  · rfl

/-- Actual original field 4, with earlier payloads physically retained. -/
theorem read_next (cached coefficient previous target next tail : List Bool) :
    Runs program (8*next.length+8) (.read 3) (store (frame next (tail)) cached [] [] [] coefficient previous target [] [] [] [])
      .copyCache (store (tail) cached [] [] [] coefficient previous target next [] [] []) := by
  apply field_call 3 next (tail) _ _
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk (.inl .input) rfl).elim | exact (hk (.inl .output) rfl).elim | exact (hk (.inr ()) rfl).elim
  · rfl

/-- The retained raw template is ACTUALLY copied before it is consumed. -/
theorem copy_cache (cached coefficient previous target next tail : List Bool) :
    Runs program (5*cached.length+4) .copyCache
      (store tail cached [] [] [] coefficient previous target next [] [] []) .shift
      (store tail cached cached [] [] coefficient previous target next [] [] []) := by
  apply included_call program copyStack Label.copy copy_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) .copyCache .shift rfl (5*cached.length+3)
    (SemiprimeD1StackCopy.state 0 none cached [] []) (SemiprimeD1StackCopy.done cached cached)
    _ _ rfl rfl (by simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words cached [] none)
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk;cases k <;> first | rfl | exact (hk 1 rfl).elim
/-- Every copied template cell becomes one real false push on the actual next
word. Template CONTENTS do not determine the shift, only visited physical cells. -/
theorem shift_run (count cached coefficient previous target next tail : List Bool) :
    Runs program (2*count.length+1) .shift
      (store tail cached count [] [] coefficient previous target next [] [] []) .addLeft
      (store tail cached [] [] [] coefficient previous target (List.replicate count.length false++next) [] [] []) := by
  induction count generalizing next with
  | nil=>
    apply one_base program .shift .addLeft (.pop .count .addLeft .prepend .prepend) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  | cons b bs ih=>
    have h0 : Runs program 1 .shift (store tail cached (b::bs) [] [] coefficient previous target next [] [] [])
        .prepend (store tail cached bs [] [] coefficient previous target next [] [] []) := by
      apply one_base program .shift .prepend (.pop .count .addLeft .prepend .prepend) _ _ rfl
      · cases b <;> rfl
      · funext k;cases k <;> rfl
    have h1 : Runs program 1 .prepend (store tail cached bs [] [] coefficient previous target next [] [] [])
        .shift (store tail cached bs [] [] coefficient previous target (false::next) [] [] []) := by
      apply one_base program .prepend .shift (.push .next false .shift) _ _ rfl
      · rfl
      · funext k;cases k <;> rfl
    have h:=runs_trans program 2 (2*bs.length+1) _ _ _ _ _ _
      (runs_trans program 1 1 _ _ _ _ _ _ h0 h1) (ih (false::next))
    have hb : List.replicate bs.length false++false::next=false::(List.replicate bs.length false++next) := by
      have hh : ∀n : ℕ,List.replicate n false++false::next=false::(List.replicate n false++next) := by
        intro n;induction n with
        | zero=>rfl
        | succ n hn=>simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons false) hn
      exact hh bs.length
    simpa only [List.length_cons,List.replicate_succ,List.cons_append,hb,
      show 2+(2*bs.length+1)=2*(bs.length+1)+1 by omega] using h

/-- Complete actual left INTEGER ripple sum, with all arithmetic scratch cleared. -/
theorem add_left (cached coefficient previous target next tail : List Bool) :
    Runs program (addTime coefficient previous+1) .addLeft (store tail cached [] [] [] coefficient previous target next [] [] []) .addRight (store tail cached [] [] [] [] [] target next (addBits coefficient previous false).bits [] []) := by
  apply included_call program (addStack false) (Label.add false) (add_injective false) A.code
    (.start false) (fun _=>rfl) .addLeft .addRight rfl (addTime coefficient previous)
    (A.state (some (.start false)) none coefficient previous [] [])
    (A.state none none [] [] [] (addBits coefficient previous false).bits) _ _ rfl rfl
    (SemiprimeD1StackAdderExecution.source_run coefficient previous false)
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk;cases k <;> first | rfl | exact (hk .left rfl).elim | exact (hk .right rfl).elim | exact (hk .output rfl).elim

/-- Complete actual right INTEGER ripple sum, with all arithmetic scratch cleared. -/
theorem add_right (cached target next left tail : List Bool) :
    Runs program (addTime target next+1) .addRight (store tail cached [] [] [] [] [] target next left [] []) .compare (store tail cached [] [] [] [] [] [] [] left (addBits target next false).bits []) := by
  apply included_call program (addStack true) (Label.add true) (add_injective true) A.code
    (.start false) (fun _=>rfl) .addRight .compare rfl (addTime target next)
    (A.state (some (.start false)) none target next [] [])
    (A.state none none [] [] [] (addBits target next false).bits) _ _ rfl rfl
    (SemiprimeD1StackAdderExecution.source_run target next false)
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk;cases k <;> first | rfl | exact (hk .left rfl).elim | exact (hk .right rfl).elim | exact (hk .output rfl).elim

/-- The final actual comparator consumes both computed integer sums. -/
theorem compare_sums (cached left right tail : List Bool) :
    Runs program (SemiprimeD1StackWordEqualExecution.executionTime left right+1) .compare
      (store tail cached [] [] [] [] [] [] [] left right []) .done
      (store tail cached [] [] [] [] [] [] [] [] [] [(SemiprimeMacroEntryBitPrimitives.equalBits left right).accepted]) := by
  have hr:=SemiprimeD1StackWordEqualExecution.source_run left right none
  rw [SemiprimeD1StackWordEqualBounds.original_answer] at hr
  apply included_call program equalStack Label.equal equal_injective SemiprimeD1StackWordEqual.code .loop
    (fun _=>rfl) .compare .done rfl (SemiprimeD1StackWordEqualExecution.executionTime left right)
    (SemiprimeD1StackWordEqual.state (some .loop) none left right [])
    (SemiprimeD1StackWordEqual.state none none [] [] [(SemiprimeMacroEntryBitPrimitives.equalBits left right).accepted])
    _ _ rfl rfl hr
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk;cases k <;> first | rfl | exact (hk .left rfl).elim | exact (hk .right rfl).elim | exact (hk .output rfl).elim
/-- Complete actual transition count of the closed pipeline. -/
def totalTime (cached coefficient previous target next : List Bool) : ℕ :=
  (8*coefficient.length+8)+(8*previous.length+8)+(8*target.length+8)+(8*next.length+8)+
    (5*cached.length+4)+(2*cached.length+1)+(addTime coefficient previous+1)+
    (addTime target (shifted cached next)+1)+
    (SemiprimeD1StackWordEqualExecution.executionTime (addBits coefficient previous false).bits
      (addBits target (shifted cached next) false).bits+1)+1
/-- CLOSED exact actual integer carry checker, for ALL raw operands/templates.
No positivity, canonicality, expected intermediate or verdict premise occurs. -/
theorem source_run (cached coefficient previous target next tail : List Bool) :
    C.run program (totalTime cached coefficient previous target next)
      (initial (record coefficient previous target next tail) cached)=
      some (done cached coefficient previous target next tail) := by
  have h0:=runs_trans program _ _ _ _ _ _ _ _ (read_coefficient cached coefficient previous target next tail)
    (read_previous cached coefficient previous target next tail)
  have h1:=runs_trans program _ _ _ _ _ _ _ _ h0 (read_target cached coefficient previous target next tail)
  have h2:=runs_trans program _ _ _ _ _ _ _ _ h1 (read_next cached coefficient previous target next tail)
  have h3:=runs_trans program _ _ _ _ _ _ _ _ h2 (copy_cache cached coefficient previous target next tail)
  have h4:=runs_trans program _ _ _ _ _ _ _ _ h3 (shift_run cached cached coefficient previous target next tail)
  have h5:=runs_trans program _ _ _ _ _ _ _ _ h4 (add_left cached coefficient previous target (shifted cached next) tail)
  have h6:=runs_trans program _ _ _ _ _ _ _ _ h5 (add_right cached target (shifted cached next) (addBits coefficient previous false).bits tail)
  have h7:=runs_trans program _ _ _ _ _ _ _ _ h6
    (compare_sums cached (addBits coefficient previous false).bits (addBits target (shifted cached next) false).bits tail)
  have he : (SemiprimeMacroEntryBitPrimitives.equalBits (addBits coefficient previous false).bits
      (addBits target (shifted cached next) false).bits).accepted=answer cached coefficient previous target next := by
    rw [shifted_original];rfl
  rw [he] at h7
  obtain ⟨finish,hfinish,hout⟩:=h7 [] (initial (record coefficient previous target next tail) cached) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (finalData cached coefficient previous target next tail) [] finish hout
  rw [totalTime,SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
  rfl
end RiemannGaussian.SemiprimeD1StackCarryEquationExecution
