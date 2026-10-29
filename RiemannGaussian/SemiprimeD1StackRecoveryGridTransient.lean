/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridCleanup
/-! # Complete physical transient-cache cleanup in the original grid fold -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridTransient
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackRecoveryGridCleanup SemiprimeD1StackProcedureTrace
/-- Exactly eight actual transient rational caches, each with both physical fields. -/
def caches :List Reg:=[.index,.negative,.numBase,.denBase,.numPower,.denPower,.reciprocal,.slope]
/-- The fixed drain list is an explicit finite list of actual cache fields. -/
theorem role_list :roles transientRole=[reg .index false,reg .index true,reg .negative false,reg .negative true,reg .numBase false,reg .numBase true,reg .denBase false,reg .denBase true,reg .numPower false,reg .numPower true,reg .denPower false,reg .denPower true,reg .reciprocal false,reg .reciprocal true,reg .slope false,reg .slope true]:=by rfl
/-- Fixed physical cache inventory agrees with the sixteen already compiled drain loops. -/
theorem mem_reg (r:Reg) (b:Bool) :reg r b∈roles transientRole↔r∈caches:=by
  rw [role_list]
  cases r <;> cases b <;> simp [reg,caches]
/-- Every allocated transient role is one of those signed/denominator cache fields. -/
theorem role_cache (i:Fin 16) :∃r b,r∈caches ∧transientRole i=reg r b:=by
  fin_cases i
  · exact ⟨.index,false,by decide,rfl⟩
  · exact ⟨.index,true,by decide,rfl⟩
  · exact ⟨.negative,false,by decide,rfl⟩
  · exact ⟨.negative,true,by decide,rfl⟩
  · exact ⟨.numBase,false,by decide,rfl⟩
  · exact ⟨.numBase,true,by decide,rfl⟩
  · exact ⟨.denBase,false,by decide,rfl⟩
  · exact ⟨.denBase,true,by decide,rfl⟩
  · exact ⟨.numPower,false,by decide,rfl⟩
  · exact ⟨.numPower,true,by decide,rfl⟩
  · exact ⟨.denPower,false,by decide,rfl⟩
  · exact ⟨.denPower,true,by decide,rfl⟩
  · exact ⟨.reciprocal,false,by decide,rfl⟩
  · exact ⟨.reciprocal,true,by decide,rfl⟩
  · exact ⟨.slope,false,by decide,rfl⟩
  · exact ⟨.slope,true,by decide,rfl⟩
/-- No original, arithmetic, geometry or auxiliary role belongs to the transient-cache drain inventory. -/
theorem mem_iff (k:Stack) :k∈roles transientRole↔∃r b,r∈caches ∧k=reg r b:=by
  constructor
  · intro hk
    obtain ⟨i,_,hi⟩:=List.mem_map.mp hk
    obtain ⟨r,b,hr,he⟩:=role_cache i
    exact ⟨r,b,hr,hi.symm.trans he⟩
  · rintro ⟨r,b,hr,rfl⟩
    exact (mem_reg r b).mpr hr
/-- Exact stopped full bank after all sixteen actual transient drains. -/
def result (w:Words) :Words:=
  {w with registers:=fun k=>if k.1∈caches then [] else w.registers k}
/-- Entire physical cleanup preserves every external word and all retained grid/final caches. -/
theorem cleared_result (w:Words) :cleared transientRole (bank w) 16=bank (result w):=by
  classical
  funext k
  rw [cleared_full]
  rcases k with k|k
  · have hn:¬Sum.inl k∈roles transientRole:=by
      rw [mem_iff]
      rintro ⟨r,b,_,h⟩;cases h
    rw [ite_eq_right hn]
    rfl
  · rcases k with k|k
    · have hn:¬Sum.inr (Sum.inl k)∈roles transientRole:=by
        rw [mem_iff]
        rintro ⟨r,b,_,h⟩;cases h
      rw [ite_eq_right hn]
      rfl
    · rcases k with k|k
      · have hn:¬Sum.inr (Sum.inr (Sum.inl k))∈roles transientRole:=by
          rw [mem_iff]
          rintro ⟨r,b,_,h⟩;cases h
        rw [ite_eq_right hn]
        rfl
      · rcases k with k|k
        · have hn:¬Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))∈roles transientRole:=by
            rw [mem_iff]
            rintro ⟨r,b,_,h⟩;cases h
          rw [ite_eq_right hn]
          rfl
        · rcases k with k|k
          · rcases k with ⟨r,b⟩
            change (if reg r b∈roles transientRole then [] else w.registers (r,b))=_
            rw [mem_reg]
            by_cases hh:r∈caches <;> simp only [bank,result,Sum.elim_inr,Sum.elim_inl,hh,ite_true,ite_false]
          · have hn:¬aux k∈roles transientRole:=by
              rw [mem_iff]
              rintro ⟨r,b,_,h⟩;cases h
            change (if aux k∈roles transientRole then [] else w.auxiliary k)=w.auxiliary k
            exact ite_eq_right hn
/-- All sixteen actual EOF drains execute before the row/final continuation; no hidden cache fields remain. -/
theorem transient_run (finish:Bool) (w:Words) :
    ∃t≤16*(mass (bank w)+1),Runs program t (.local (.clearTransient finish 0)) (bank w)
      (if finish then .local .clearFinalQ else .local .clearMultiplicity) (bank (result w)):=by
  obtain ⟨t,ht,h⟩:=transient_cleanup finish (bank w)
  rw [cleared_result] at h
  exact ⟨t,ht,h⟩
end RiemannGaussian.SemiprimeD1StackRecoveryGridTransient
