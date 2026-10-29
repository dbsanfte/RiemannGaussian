/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprDotTerm

/-! # Whole physical dot-expression source construction
All term calls are the proved closed literal pipeline. The decreasing counter,
zero constructor, second count copy and final addition tags execute physically.
No abstract loop body, chosen word, exponent or syntax producer is a premise.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackExprDotExecution
open SemiprimeD1StackExprDot SemiprimeD1StackExprDotComponents SemiprimeD1StackExprDotTerm
open SemiprimeD1StackExprDotSpec (terms addTags addTags_push)
open SemiprimeD1StackProcedureTrace
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => SemiprimeD1StackExprDot.Label.control

/-- A real preserving count copy initializes each physical construction pass. -/
theorem count_copy (c : Cache) (out : List Bool) (pc next : Label)
    (hcall : program pc=.call (.copy .count 0) next) :
    Runs program (5*c.count.length+4) pc (bank c {output:=out}) next (bank c {remaining:=c.count,output:=out}) := by
  have h:=copy_call .count (bank c {output:=out}) rfl pc next hcall
  have he : Function.update (bank c {output:=out}) .remaining c.count=bank c {remaining:=c.count,output:=out} := by
    funext k;cases k <;> simp [Function.update,bank]
  simpa only [copyInput,copyOutput,bank,List.append_nil,he] using h

/-- All three literal-zero source cells are actually pushed. -/
theorem zero_run (c : Cache) (out : List Bool) :
    Runs program 3 (ctl .zero0) (bank c {output:=out}) (ctl .copyAgain)
      (bank c {output:=false::false::false::out}) := by
  have h0:=push_run c {output:=out} .zero0 .zero1 false rfl
  have h1:=push_run c {output:=false::out} .zero1 .zero2 false rfl
  have h2:=push_run c {output:=false::false::out} .zero2 .copyAgain false rfl
  exact runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2

/-- Counted actual addition-constructor loop, with no supplied constructor count. -/
theorem add_loop (count : List Bool) (c : Cache) (out : List Bool) :
    Runs program (3*count.length+1) (ctl .addLoop) (bank c {remaining:=count,output:=out})
      (ctl .done) (bank c {output:=addTags count.length out}) := by
  induction count generalizing out with
  | nil =>
    apply one_base program (ctl .addLoop) (ctl .done) (.pop .remaining (ctl .done) (ctl .add0) (ctl .add0)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  | cons bit count ih =>
    have h0 : Runs program 1 (ctl .addLoop) (bank c {remaining:=bit::count,output:=out})
        (ctl .add0) (bank c {remaining:=count,output:=out}) := by
      apply one_base program (ctl .addLoop) (ctl .add0) (.pop .remaining (ctl .done) (ctl .add0) (ctl .add0)) _ _ rfl
      · cases bit <;> rfl
      · funext k;cases k <;> rfl
    have h1:=push_run c {remaining:=count,output:=out} .add0 .add1 true rfl
    have h2:=push_run c {remaining:=count,output:=true::out} .add1 .addLoop false rfl
    have h3:=ih (false::true::out)
    rw [addTags_push] at h3
    have h:=runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3
    simpa only [List.length_cons,addTags,
      show (1+1)+1+(3*count.length+1)=3*(count.length+1)+1 by omega] using h

/-- Retains the actual closed pipeline cost for every counted term visit. -/
def loopBudget (c : Cache) (words : List (List Bool)) (stride frequency : ℕ) : ℕ→ℕ
  | 0 => 1
  | n+1 => 1+SemiprimeD1StackExprDotTerm.budget c words stride frequency n+
      loopBudget c words stride frequency n

/-- Complete decreasing-index term construction, including all zero/default
word cases. Its numeric indices arise from the ACTUAL popped counter. -/
theorem loop_run (c : Cache) (words : List (List Bool)) (stride frequency n : ℕ)
    (hs : c.stride=unary stride) (hf : c.frequency=unary frequency) (hc : c.words=vectorBits words)
    (out : List Bool) :
    ∃t ≤ loopBudget c words stride frequency n,Runs program t (ctl .loop)
      (bank c {remaining:=unary n,output:=out}) (ctl .zero0)
      (bank c {output:=terms n c.base words stride frequency out}) := by
  induction n generalizing out with
  | zero =>
    refine ⟨1,le_refl _,?_⟩
    apply one_base program (ctl .loop) (ctl .zero0) (.pop .remaining (ctl .zero0) (ctl .copyProduct) (ctl .copyProduct)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  | succ n ih =>
    have h0 : Runs program 1 (ctl .loop) (bank c {remaining:=unary (n+1),output:=out})
        (ctl .copyProduct) (bank c {remaining:=unary n,output:=out}) := by
      apply one_base program (ctl .loop) (ctl .copyProduct)
        (.pop .remaining (ctl .zero0) (ctl .copyProduct) (ctl .copyProduct)) _ _ rfl
      · rfl
      · funext k;cases k <;> rfl
    obtain ⟨m,hm,h1⟩:=term_run c words stride frequency n hs hf hc out
    obtain ⟨k,hk,h2⟩:=ih (SemiprimeD1StackExprDotSpec.term c.base words stride frequency n out)
    have h:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
    refine ⟨1+m+k,?_,h⟩
    unfold loopBudget
    omega

/-- Whole own budget: count copies, every actual term, zero, add tags and halt. -/
def timeBound (c : Cache) (words : List (List Bool)) (stride frequency n : ℕ) : ℕ :=
  (5*n+4)+loopBudget c words stride frequency n+3+(5*n+4)+(3*n+1)+1
/-- Exact final data, including all retained argument caches and physical suffix. -/
def done (c : Cache) (words : List (List Bool)) (stride frequency n : ℕ) (tail : List Bool) : C.State Stack Label :=
  ⟨none,none,none,bank c {output:=SemiprimeD1StackExprDotSpec.result n c.base words stride frequency tail},[]⟩

/-- COMPLETE actual dot-expression source acquisition. Only original physical
cache representations are identified; no producer/body/value/clock is supplied. -/
theorem source_run (c : Cache) (words : List (List Bool)) (stride frequency n : ℕ)
    (hs : c.stride=unary stride) (hf : c.frequency=unary frequency) (hn : c.count=unary n)
    (hc : c.words=vectorBits words) (tail : List Bool) :
    ∃t ≤ timeBound c words stride frequency n,
      C.run program t (initial c tail)=some (done c words stride frequency n tail) := by
  have h0:=count_copy c tail (ctl .start) (ctl .loop) rfl
  rw [hn] at h0
  simp only [unary,List.length_replicate] at h0
  obtain ⟨m,hm,h1⟩:=loop_run c words stride frequency n hs hf hc tail
  have h2:=zero_run c (terms n c.base words stride frequency tail)
  have h3:=count_copy c (false::false::false::terms n c.base words stride frequency tail)
    (ctl .copyAgain) (ctl .addLoop) rfl
  rw [hn] at h3
  simp only [unary,List.length_replicate] at h3
  have h4:=add_loop (unary n) c (false::false::false::terms n c.base words stride frequency tail)
  simp only [unary,List.length_replicate] at h4
  have h:=runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3) h4
  obtain ⟨finish,hr,ho⟩:=h [] (initial c tail) ⟨rfl,rfl,rfl⟩
  have he:=halt_run program (ctl .done) rfl
    (bank c {output:=SemiprimeD1StackExprDotSpec.result n c.base words stride frequency tail}) [] finish ho
  refine ⟨(5*n+4)+m+3+(5*n+4)+(3*n+1)+1,?_,?_⟩
  · unfold timeBound
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,he]
    rfl

end RiemannGaussian.SemiprimeD1StackExprDotExecution
