/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceOccurrencesView
/-! # Actual binary initialization and factor-key counter successors
Every n marker drives one real fixed-width increment/carry-pop/double-reversal.
The complete n+F+1 width was physically allocated by the source prescan.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceOccurrencesCounter
open SemiprimeD1StackSourceOccurrences SemiprimeD1StackSourceOccurrencesPrimitives
open SemiprimeD1StackSourceOccurrencesView SemiprimeD1StackSourceOccurrencesEncoding
open SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Fixed next loop after an actual initialized/per-factor counter successor. -/
def counterNext :Counter→Label | .initialize=>ctl .initLoop | .factor=>ctl .factorTag
/-- Actual Increment call, false-carry pop and TWO real reversals transfer the owner without changing bit order. -/
theorem counter_transfer (part:Counter) (before:Stack→List Bool) (n F v:Nat) (hv:v<n+F)
    (ho:before .counter=counterWord n F v) (hn:before .next=[]) (hs:before .incrementScratch=[]) :
    ∃q≤ 14*(n+F+1)+24,Runs program q (ctl (.increment part)) before (counterNext part)
      (Function.update before .counter (counterWord n F (v+1))) :=by
  let word:=counterWord n F v
  let next:=SemiprimeD1StackIncrement.wrapped word
  let b1:=Function.update (Function.update before .counter []) .next (false::next)
  let b2:=Function.update b1 .next next
  let b3:=Function.update (Function.update b2 .next []) .incrementScratch next.reverse
  let b4:=Function.update (Function.update b3 .incrementScratch []) .counter next
  obtain ⟨b,hb,h0⟩:=increment_call part before word ho hs hn
  rw [counter_no_overflow n F v (by omega)] at h0
  have h1:=pop_run (.carry part) (ctl .abort) (ctl (.counterFirst part)) (ctl .abort) .next b1 (false::next) rfl (by simp [b1])
  have h2:=reverse_call .counterFirst (.counterFirst part) (.counterSecond part) rfl b2 next []
    (by simp [b2,reverseStack]) (by simpa [b2,b1,reverseStack,Function.update] using hs)
  simp only [List.append_nil] at h2
  have h3:=reverse_call .counterSecond (.counterSecond part) (.afterIncrement part) rfl b3 next.reverse []
    (by simp [b3,reverseStack]) (by simp [b3,b2,b1,reverseStack,Function.update])
  simp only [List.reverse_reverse,List.append_nil] at h3
  have h4:Runs program 1 (ctl (.afterIncrement part)) b4 (counterNext part) b4:=by
    apply one_base program (ctl (.afterIncrement part)) (counterNext part) (.jump (counterNext part)) _ _
      (by cases part <;> rfl)
    · rfl
    · rfl
  have hh0:=join (join (join (join h0 h1) h2) h3) h4
  have hnext:next=counterWord n F (v+1):=counter_succ n F v hv
  have he:b4=Function.update before .counter (counterWord n F (v+1)):=by
    funext k
    cases k <;> simp [b4,b3,b2,b1,Function.update,hn,hs,hnext]
  change Runs program (b+1+(2*next.length+3)+(2*next.reverse.length+3)+1) (ctl (.increment part)) before (counterNext part) b4 at hh0
  rw [he] at hh0
  refine ⟨b+1+(2*next.length+3)+(2*next.reverse.length+3)+1,?_,hh0⟩
  rw [List.length_reverse]
  have hlen:next.length=n+F+1:=by rw [SemiprimeD1StackIncrement.wrapped_length,counter_length n F v (by omega)]
  have hword:word.length=n+F+1:=counter_length n F v (by omega)
  rw [hlen]
  rw [hword] at hb
  omega
/-- One actual initialization marker is popped before the real binary successor call. -/
theorem init_step (source number factors:List Bool) (n F v m:Nat) (hv:v<n+F) :
    ∃q≤14*(n+F+1)+25,Runs program q (ctl .initLoop)
      (data source number [] [] [] (List.replicate (m+1) true) (counterWord n F v) [] [] [] factors [])
      (ctl .initLoop) (data source number [] [] [] (List.replicate m true) (counterWord n F (v+1)) [] [] [] factors []) :=by
  let b0:=data source number [] [] [] (List.replicate (m+1) true) (counterWord n F v) [] [] [] factors []
  let b1:=data source number [] [] [] (List.replicate m true) (counterWord n F v) [] [] [] factors []
  have h0:Runs program 1 (ctl .initLoop) b0 (ctl (.increment .initialize)) b1:=by
    apply one_base program (ctl .initLoop) (ctl (.increment .initialize))
      (.pop .todo (ctl .mainCopy) (ctl .abort) (ctl (.increment .initialize))) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  obtain ⟨q,hq,h1⟩:=counter_transfer .initialize b1 n F v hv rfl rfl rfl
  have he:Function.update b1 .counter (counterWord n F (v+1))=
      data source number [] [] [] (List.replicate m true) (counterWord n F (v+1)) [] [] [] factors []:=
    data_counter _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [he] at h1
  exact ⟨1+q,by omega,join h0 h1⟩
/-- Exactly the actual remaining n markers initialize the binary factor namespace offset. -/
theorem init_loop (source number factors:List Bool) (n F m v:Nat) (hv:v+m≤n+F) :
    ∃q≤(14*(n+F+1)+25)*m+1,Runs program q (ctl .initLoop)
      (data source number [] [] [] (List.replicate m true) (counterWord n F v) [] [] [] factors [])
      (ctl .mainCopy) (data source number [] [] [] [] (counterWord n F (v+m)) [] [] [] factors []) :=by
  induction m generalizing v with
  | zero=>
    refine ⟨1,by omega,?_⟩
    apply one_base program (ctl .initLoop) (ctl .mainCopy)
      (.pop .todo (ctl .mainCopy) (ctl .abort) (ctl (.increment .initialize))) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  | succ m ih=>
    obtain ⟨a,ha,h0⟩:=init_step source number factors n F v m (by omega)
    obtain ⟨b,hb,h1⟩:=ih (v+1) (by omega)
    have he:v+1+m=v+(m+1):=by omega
    rw [he] at h1
    refine ⟨a+b,?_,join h0 h1⟩
    nlinarith
/-- A second preserving copy reads actual n markers; no binary n offset is supplied. -/
theorem initialize_run (source:List Bool) (n F:Nat) :
    ∃q≤100*(n+F+2)^2,Runs program q (ctl .copyInit)
      (data source (List.replicate n true) [] [] [] [] (List.replicate (n+F+1) false) [] [] [] (List.replicate F true) [])
      (ctl .mainCopy) (data source (List.replicate n true) [] [] [] [] (counterWord n F n) [] [] [] (List.replicate F true) []) :=by
  let number:=List.replicate n true
  let factors:=List.replicate F true
  let b0:=data source number [] [] [] [] (counterWord n F 0) [] [] [] factors []
  have h0:=copy_call .number .copyInit .initLoop rfl b0 number [] rfl rfl rfl
  simp only [List.append_nil] at h0
  change Runs program (5*number.length+4) _ b0 _ (Function.update b0 .todo number) at h0
  have he:Function.update b0 .todo number=data source number [] [] [] number (counterWord n F 0) [] [] [] factors []:=
    data_todo _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [he] at h0
  obtain ⟨q,hq,h1⟩:=init_loop source number factors n F n 0 (by omega)
  have h:=join h0 h1
  have hb0:b0=data source number [] [] [] [] (List.replicate (n+F+1) false) [] [] [] factors []:=by dsimp only [b0];rw [counter_zero]
  rw [hb0] at h
  simp only [Nat.zero_add] at h
  refine ⟨(5*number.length+4)+q,?_,h⟩
  have hn:number.length=n:=List.length_replicate
  rw [hn]
  nlinarith
end RiemannGaussian.SemiprimeD1StackSourceOccurrencesCounter
