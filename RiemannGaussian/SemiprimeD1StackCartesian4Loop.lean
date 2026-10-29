/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCartesian4Body

/-! # Exact actual local-loop composition
The predicate below composes traces of the fixed lower-level procedure already
present in Cartesian4.program. F is a mathematical output specification, not
an instruction, runtime callback or supplied table. The closed four-level
assembly instantiates it with the actual physical record body.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackCartesian4Loop
open SemiprimeD1StackCartesian4 SemiprimeD1StackCartesian4Components
open SemiprimeD1StackProcedureFragments (Runs one_base)

/-- Ascending mathematical fold specified by descending physical emissions. -/
def rangeFold : ℕ→(ℕ→List Bool→List Bool)→List Bool→List Bool
  | 0,_,output => output
  | n+1,F,output => rangeFold n F (F n output)

/-- A literal nonempty-index pop changes exactly the actual current-index word. -/
theorem pop_index (level:Fin 4) (pc:Label) (limits indices:Fin 4→List Bool) (tag output tail:List Bool)
    (hi:indices level=true::tail)
    (hcode:program pc=.base (.pop (indexStack level) (.inl .ret) (.inl (.child level)) (.inl (.child level)))) :
    Runs program 1 pc (store limits indices tag output) (.inl (.child level))
      (store limits (Function.update indices level tail) tag output) := by
  apply one_base program _ _ (.pop (indexStack level) (.inl .ret) (.inl (.child level)) (.inl (.child level))) _ _ hcode
  · simp [B.execute,SemiprimeD1StackBytecode.choose,store,indexStack,hi]
  · change Function.update (store limits indices tag output) (indexStack level) (indices level).tail=_
    rw [hi,List.tail_cons,store_index]

/-- The empty-index EOF test retains every actual payload and returns to its caller. -/
theorem pop_empty (level:Fin 4) (pc:Label) (limits indices:Fin 4→List Bool) (tag output:List Bool)
    (hi:indices level=[])
    (hcode:program pc=.base (.pop (indexStack level) (.inl .ret) (.inl (.child level)) (.inl (.child level)))) :
    Runs program 1 pc (store limits indices tag output) (.inl .ret) (store limits indices tag output) := by
  apply one_base program _ _ (.pop (indexStack level) (.inl .ret) (.inl (.child level)) (.inl (.child level))) _ _ hcode
  · simp [B.execute,SemiprimeD1StackBytecode.choose,store,indexStack,hi]
  · change Function.update (store limits indices tag output) (indexStack level) (indices level).tail=_
    have he:Function.update indices level []=indices:=by
      simpa only [hi] using Function.update_eq_self level indices
    rw [hi,List.tail_nil,store_index,he]

/-- Every actual child call, counter pop and record prefix is included in the loop.
The sole proof premise is a trace of the specific fixed lower procedure, never
an executable evaluator parameter. -/
theorem inner_run (n:ℕ) (level:Fin 4) (limits indices:Fin 4→List Bool) (tag:List Bool)
    (F:ℕ→List Bool→List Bool) (B:ℕ)
    (hchild:∀i≤n,∀output,∃m≤B,Runs program m (childEntry level)
      (store limits (Function.update indices level (List.replicate i true)) tag output)
      (.inl .ret) (store limits (Function.update indices level (List.replicate i true)) tag (F i output)))
    (output:List Bool) :
    ∃m≤(n+1)*(B+3),Runs program m (.inl (.child level))
      (store limits (Function.update indices level (List.replicate n true)) tag output)
      (.inl .ret) (store limits (Function.update indices level []) tag (rangeFold (n+1) F output)) := by
  induction n generalizing output with
  | zero =>
    obtain ⟨m,hm,hsub⟩:=hchild 0 (le_refl _) output
    have h0:=SemiprimeD1StackLocalCall.call_run program (.inl (.child level)) (childEntry level)
      (.inl .ret) (.inl (.after level)) _ _ m rfl rfl hsub
    have h1:=pop_empty level (.inl (.after level)) limits (Function.update indices level []) tag
      (F 0 output) (by simp) rfl
    refine ⟨(m+2)+1,by omega,?_⟩
    exact h0.trans h1
  | succ n ih =>
    obtain ⟨m,hm,hsub⟩:=hchild (n+1) (le_refl _) output
    have h0:=SemiprimeD1StackLocalCall.call_run program (.inl (.child level)) (childEntry level)
      (.inl .ret) (.inl (.after level)) _ _ m rfl rfl hsub
    have h1:=pop_index level (.inl (.after level)) limits
      (Function.update indices level (List.replicate (n+1) true)) tag (F (n+1) output)
      (List.replicate n true) (by simp [List.replicate_succ]) rfl
    rw [Function.update_idem] at h1
    obtain ⟨t,ht,hr⟩:=ih (fun i hi out=>hchild i (by omega) out) (F (n+1) output)
    refine ⟨(m+2)+(1+t),?_,?_⟩
    · calc
        (m+2)+(1+t)≤(B+2)+(1+(n+1)*(B+3)):=Nat.add_le_add (by omega) (by omega)
        _=(n+2)*(B+3):=by ring
    · exact h0.trans (h1.trans hr)

/-- An actual acquired limit, empty current counter, all included Copy work and
all child calls yield the exact finite fold. The final assembly discharges the
lower-procedure trace from actual fields, not from an answer/cost oracle. -/
theorem entry_run (n:ℕ) (level:Fin 4) (limits indices:Fin 4→List Bool) (tag:List Bool)
    (hl:limits level=List.replicate n true) (hi:indices level=[])
    (F:ℕ→List Bool→List Bool) (B:ℕ)
    (hchild:∀i<n,∀output,∃m≤B,Runs program m (childEntry level)
      (store limits (Function.update indices level (List.replicate i true)) tag output)
      (.inl .ret) (store limits (Function.update indices level (List.replicate i true)) tag (F i output)))
    (output:List Bool) :
    ∃m≤n*(B+8)+5,Runs program m (.inl (.entry level)) (store limits indices tag output)
      (.inl .ret) (store limits indices tag (rangeFold n F output)) := by
  have h0:=copy_empty level limits indices tag output hi
  have he:Function.update indices level []=indices:=by
    simpa only [hi] using Function.update_eq_self level indices
  rw [hl,List.length_replicate] at h0
  cases n with
  | zero =>
    rw [List.replicate_zero,he] at h0
    have h1:=pop_empty level (.inl (.drop level)) limits indices tag output hi rfl
    exact ⟨5,by omega,h0.trans h1⟩
  | succ n =>
    have h1:=pop_index level (.inl (.drop level)) limits
      (Function.update indices level (List.replicate (n+1) true)) tag output (List.replicate n true)
      (by simp [List.replicate_succ]) rfl
    rw [Function.update_idem] at h1
    obtain ⟨m,hm,hsub⟩:=inner_run n level limits indices tag F B
      (fun i hi out=>hchild i (by omega) out) output
    rw [he] at hsub
    refine ⟨(5*(n+1)+4)+(1+m),?_,h0.trans (h1.trans hsub)⟩
    calc
      (5*(n+1)+4)+(1+m)≤(5*(n+1)+4)+(1+(n+1)*(B+3)):=by omega
      _=(n+1)*(B+8)+5:=by ring
end RiemannGaussian.SemiprimeD1StackCartesian4Loop
