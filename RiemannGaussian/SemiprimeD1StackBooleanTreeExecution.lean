/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanTreeParts

/-! # Whole actual recursive Boolean tree framing
Both child calls, every marker restore, every entry read/codec push, the real
history reverse and final halt are retained. The physical depth bytes are
preserved exactly, not replaced by a normalized unary answer.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackBooleanTreeExecution
open SemiprimeD1StackBooleanTree SemiprimeD1StackBooleanTreeParts SemiprimeD1StackProcedureTrace
open SemiprimeD1BooleanTreeStream (bytes leafBytes bytes_zero bytes_succ)

/-- Own exact body trace count; pure specification, never a code/initial operand. -/
def bodyTime : List Bool→List Bool→ℕ
  | [],raw=>2+(leafBytes (raw.head?.getD false)).length
  | _::depth,raw=>bodyTime depth raw+bodyTime depth (raw.drop (2^depth.length))+7
/-- Actual sequential source trace connector, preserving all outer frames. -/
theorem chain {m n : ℕ} {pc mid next : Label} {input middle output : Stack→List Bool}
    (h : Runs program m pc input mid middle) (g : Runs program n mid middle next output) :
    Runs program (m+n) pc input next output := runs_trans program _ _ _ _ _ _ _ _ h g
/-- Two physically consumed equal subtrees expose exactly the original next tail. -/
theorem drop_two (raw : List Bool) (n : ℕ) :
    (raw.drop (2^n)).drop (2^n)=raw.drop (2^(n+1)) := by
  rw [List.drop_drop]
  congr 1
  rw [pow_succ]
  omega
/-- Reverse logging preserves the required old preorder and both child orders. -/
theorem log_fork (low high hist : List Bool) :
    high.reverse++(low.reverse++true::hist)=(true::(low++high)).reverse++hist := by
  simp only [List.reverse_cons,List.reverse_append,List.append_assoc,List.singleton_append]

/-- Complete SAME actual recursive body for all entry streams and every actual
depth-marker bit pattern. The source tail and every outer return frame survive. -/
theorem visit_run (depth raw hist out : List Bool) :
    Runs program (bodyTime depth raw) .visit (store raw depth hist out) .returnPC
      (store (raw.drop (2^depth.length)) depth ((bytes depth.length raw).reverse++hist) out) := by
  induction depth generalizing raw hist out with
  | nil=>
    have h:=chain (visit_leaf raw hist out) (chain (read_leaf raw hist out)
      (emit_run (raw.head?.getD false) raw.tail [] hist out))
    rw [show 1+(1+(leafBytes (raw.head?.getD false)).length)=2+(leafBytes (raw.head?.getD false)).length by omega] at h
    simpa only [bodyTime,List.length_nil,pow_zero,List.drop_one,bytes_zero] using h
  | cons b depth ih=>
    have h0:=visit_node b raw depth hist out
    have h1:=push_node b raw depth hist out
    have h2:=SemiprimeD1StackRecursiveCallTrace.invoke program (.left b) .visit .returnPC (.afterLeft b)
      rfl rfl (bodyTime depth raw) _ _ (ih raw (true::hist) out)
    have h3:=SemiprimeD1StackRecursiveCallTrace.invoke program (.afterLeft b) .visit .returnPC (.restore b)
      rfl rfl (bodyTime depth (raw.drop (2^depth.length))) _ _
      (ih (raw.drop (2^depth.length)) ((bytes depth.length raw).reverse++true::hist) out)
    have h4:=restore_node b ((raw.drop (2^depth.length)).drop (2^depth.length)) depth
      ((bytes depth.length (raw.drop (2^depth.length))).reverse++((bytes depth.length raw).reverse++true::hist)) out
    have h:=chain h0 (chain h1 (chain h2 (chain h3 h4)))
    rw [drop_two,log_fork,←bytes_succ] at h
    have ht : 1+(1+((bodyTime depth raw+2)+(bodyTime depth (raw.drop (2^depth.length))+2+1)))=
        bodyTime depth raw+bodyTime depth (raw.drop (2^depth.length))+7 := by omega
    rw [ht] at h
    exact h

/-- Real final reversal reads and moves every physical history byte once. -/
theorem reverse_run (hist raw depth out : List Bool) :
    Runs program (2*hist.length+1) .reverse (store raw depth hist out)
      .done (store raw depth [] (hist.reverse++out)) := by
  induction hist generalizing out with
  | nil=>
    apply one_base program .reverse .done (.pop .history .done (.write false) (.write true)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  | cons b hist ih=>
    have h0 : Runs program 1 .reverse (store raw depth (b::hist) out) (.write b) (store raw depth hist out) := by
      apply one_base program .reverse (.write b) (.pop .history .done (.write false) (.write true)) _ _ rfl
      · cases b <;> rfl
      · funext k;cases k <;> rfl
    have h1 : Runs program 1 (.write b) (store raw depth hist out) .reverse (store raw depth hist (b::out)) := by
      apply one_base program (.write b) .reverse (.push .output b .reverse) _ _ rfl
      · rfl
      · funext k;cases k <;> rfl
    have h:=chain h0 (chain h1 (ih (b::out)))
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,
      show 1+(1+(2*hist.length+1))=2*(hist.length+1)+1 by omega] using h

/-- Exact source count includes top call/return, physical reverse and halt. -/
def totalTime (raw depth : List Bool) : ℕ := bodyTime depth raw+2*(bytes depth.length raw).length+4
/-- Only unread input, original depth and complete old-codec bytes remain. -/
def done (raw depth : List Bool) : C.State Stack Label :=
  ⟨none,none,none,store (raw.drop (2^depth.length)) depth [] (bytes depth.length raw),[]⟩
/-- COMPLETE actual writer with no table, entry callback, size/count or clock
advice. Entry-stream/metadata acquisition remains the enclosing caller's cost. -/
theorem source_run (raw depth : List Bool) :
    C.run program (totalTime raw depth) (initial raw depth)=some (done raw depth) := by
  have hb:=SemiprimeD1StackRecursiveCallTrace.invoke program .start .visit .returnPC .reverse rfl rfl
    (bodyTime depth raw) _ _ (visit_run depth raw [] [])
  simp only [List.append_nil] at hb
  have hr:=reverse_run (bytes depth.length raw).reverse (raw.drop (2^depth.length)) depth []
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hr
  have h:=chain hb hr
  obtain ⟨finish,hfinish,hout⟩:=h [] (initial raw depth) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (done raw depth).data [] finish hout
  rw [totalTime,show bodyTime depth raw+2*(bytes depth.length raw).length+4=
    ((bodyTime depth raw+2)+(2*(bytes depth.length raw).length+1))+1 by omega,
    SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
  rfl
end RiemannGaussian.SemiprimeD1StackBooleanTreeExecution
