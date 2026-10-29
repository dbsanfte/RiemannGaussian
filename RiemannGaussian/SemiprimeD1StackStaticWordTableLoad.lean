/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticWordTableCleanup
/-! # Physical complete original-input template copying at every leaf -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackStaticWordTableLoad
open SemiprimeD1StackStaticWordTable SemiprimeD1StackStaticWordTablePrimitives
open SemiprimeD1StackStaticWordTableCleanup SemiprimeD1StackProcedureTrace SemiprimeD1StackProcedureReturns
variable {K L : Type} [DecidableEq K] (s : Static K L)
/-- Proof view of physically loaded template roles; the static list is never
an input-data argument or runtime table interpreter. -/
def loadPrefix (d : Stack K→List Bool) (n : Nat) : Stack K→List Bool
  | .inl k=>if k∈s.roles.take n then d (template k) else d (checker k)
  | .inr k=>d (.inr k)
/-- Complete literal template delivery, preserving every caller/scanner word. -/
def loaded (d : Stack K→List Bool) : Stack K→List Bool
  | .inl k=>d (template k) | .inr k=>d (.inr k)
/-- No role is supplied before its actual physical copy. -/
theorem loadPrefix_zero (d : Stack K→List Bool) : loadPrefix s d 0=d := by
  funext k;cases k <;> simp only [loadPrefix,List.take_zero,List.not_mem_nil,ite_false,checker]
/-- Literal full coverage supplies every actual checker input operand. -/
theorem loadPrefix_full (d : Stack K→List Bool) : loadPrefix s d s.roles.length=loaded d := by
  funext k
  cases k with
  | inl k=>simp only [loadPrefix,List.take_length,s.complete k,ite_true,loaded]
  | inr k=>rfl
/-- Actual source/temporary cleanup followed by copy advances exactly one static role. -/
theorem loadPrefix_step (d : Stack K→List Bool) (p : Fin s.roles.length) :
    Function.update (Function.update (loadPrefix s d p.val) (checker (role s p)) [])
      (checker (role s p)) (d (template (role s p)))=loadPrefix s d (p.val+1) := by
  funext k
  cases k with
  | inl k=>
    by_cases he:k=s.roles[p.val]
    · subst k
      change Function.update (Function.update (loadPrefix s d p.val) (Sum.inl s.roles[p.val]) [])
        (Sum.inl s.roles[p.val]) (d (template (role s p))) (Sum.inl s.roles[p.val])=_
      rw [Function.update_self]
      simp only [loadPrefix,List.take_succ_eq_append_getElem p.isLt,List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false,or_true,ite_true,role]
    · have hn:(Sum.inl k : Stack K)≠checker (role s p):=by intro h;exact he (Sum.inl.inj h)
      rw [Function.update_of_ne hn,Function.update_of_ne hn]
      simp only [loadPrefix,List.take_succ_eq_append_getElem p.isLt,List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false,he,or_false]
  | inr k=>
    have hn:(Sum.inr k : Stack K)≠checker (role s p):=by intro h;cases h
    rw [Function.update_of_ne hn,Function.update_of_ne hn]
    rfl
/-- Every template word, including empty private/shadow fields, is real data. -/
def templateInventory [Fintype K] (d : Stack K→List Bool) : Nat := ∑k:K,(d (template k)).length
omit [DecidableEq K] in
/-- One copied input field is counted in the full physical template inventory. -/
theorem template_cell_le [Fintype K] (d : Stack K→List Bool) (k : K) :
    (d (template k)).length≤ templateInventory d := by
  change (d (template k)).length≤∑j:K,(d (template j)).length
  exact Finset.single_le_sum (f:=fun j:K=>(d (template j)).length)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)
/-- No intermediate loaded field exceeds the original plus template byte inventories. -/
theorem loadPrefix_cell_le [Fintype K] (d : Stack K→List Bool) (n : Nat) (k : K) :
    (loadPrefix s d n (checker k)).length≤ inventory d+templateInventory d := by
  change (if k∈s.roles.take n then d (template k) else d (checker k)).length≤_
  split
  · exact (template_cell_le d k).trans (Nat.le_add_left _ _)
  · exact (cell_le_inventory d k).trans (Nat.le_add_right _ _)
/-- Own static per-role bound pays target drain, actual preserving copy and EOF. -/
def loadUnit [Fintype K] (d : Stack K→List Bool) : Nat :=6*(inventory d+templateInventory d)+5
/-- Every template role is copied by its actual literal preserving-copy procedure.
The read-only bank survives and ALL included input/private/shadow words are visited. -/
theorem load_runs [Fintype K] (d : Stack K→List Bool) (hs : d (aux .scratch)=[])
    (n left : Nat) (h : n+left=s.roles.length) :
    ∃t≤ left*loadUnit d,Runs (program s) t (.load ⟨n,by omega⟩)
      (loadPrefix s d n) (.load ⟨s.roles.length,by omega⟩) (loaded d) := by
  induction left generalizing n with
  | zero=>
    have hn:n=s.roles.length:=by omega
    subst n
    rw [loadPrefix_full]
    exact ⟨0,by omega,runs_refl (program s) _ _⟩
  | succ left ih=>
    have hn:n<s.roles.length:=by omega
    let p : Fin s.roles.length:=⟨n,hn⟩
    let before:=loadPrefix s d n
    let cleared:=Function.update before (checker (role s p)) []
    have h0:=drain s (.load ⟨n,by omega⟩) (.loadCopy p) (checker (role s p))
      (by simp only [program,dite_eq_left hn];rfl) before
    have h1:=copy_call s (some p) (.loadCopy p) (loadNext s p) rfl cleared
      (by exact Function.update_self _ _ _) (by
        change (Function.update before (checker (role s p)) []) (aux .scratch)=[]
        rw [Function.update_of_ne (by intro he;cases he)]
        exact hs)
    have hword:cleared (copyStack s (some p) 0)=d (template (role s p)) := by
      change (Function.update before (checker (role s p)) []) (template (role s p))=_
      rw [Function.update_of_ne (by intro he;cases he)]
      rfl
    change Runs (program s) (5*(cleared (copyStack s (some p) 0)).length+4)
      (.loadCopy p) cleared (loadNext s p)
      (Function.update cleared (checker (role s p)) (cleared (copyStack s (some p) 0))) at h1
    rw [hword] at h1
    have hstep:Function.update cleared (checker (role s p)) (d (template (role s p)))=
        loadPrefix s d (n+1):=loadPrefix_step s d p
    rw [hstep] at h1
    obtain ⟨t,ht,hr⟩:=ih (n+1) (by omega)
    have h01:=runs_trans (program s) _ _ _ _ _ _ _ _ h0 h1
    have hout:=runs_trans (program s) _ _ _ _ _ _ _ _ h01 hr
    refine ⟨_,?_,hout⟩
    have hb:=loadPrefix_cell_le s d n (role s p)
    have hw:=template_cell_le d (role s p)
    change (before (checker (role s p))).length+1+(5*(d (template (role s p))).length+4)+t≤_
    change (before (checker (role s p))).length≤ inventory d+templateInventory d at hb
    rw [Nat.succ_mul left (loadUnit d)]
    unfold loadUnit at *
    omega
/-- One actual return after the whole template load, with all outer frames retained. -/
theorem load_returns [Fintype K] (d : Stack K→List Bool) (hs : d (aux .scratch)=[]) :
    ∃t≤ s.roles.length*loadUnit d+1,Returns (program s) t (.load 0) d (loaded d) := by
  obtain ⟨t,ht,hr⟩:=load_runs s d hs 0 s.roles.length (by omega)
  rw [loadPrefix_zero] at hr
  refine ⟨t+1,by omega,?_⟩
  exact of_runs (program s) t (.load 0) (.load ⟨s.roles.length,by omega⟩) _ _ hr
    (by simp only [program,dite_eq_right (Nat.lt_irrefl _)])
end RiemannGaussian.SemiprimeD1StackStaticWordTableLoad
