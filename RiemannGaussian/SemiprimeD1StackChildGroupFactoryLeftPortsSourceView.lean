/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsSource
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPortConvertView
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsLoop
/-! # Full actual left-scope source reuse boundary for the complete vertex loop
The first old vertex may inherit the actual final bucket counter; its real
drain acquires freshness before any child parse. Every other work word stays
explicit, and all converter tapes are physically clear before old-port queries.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsSourceView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryLeftPortsSource
namespace Work
export SemiprimeD1StackChildGroupFactoryOldPortsLoop (Fresh freshRole headerFresh childFresh)
end Work
namespace LV
export SemiprimeD1StackChildGroupFactoryLeftPortsLoopView (result_clean result_headerClean result_outerReader result_other)
end LV
namespace PV
export SemiprimeD1StackChildGroupFactoryPortConvertView (result_other result_ordinal result_bank result_history)
end PV
namespace Reuse
export SemiprimeD1StackChildGroupFactoryPortReuse (role)
end Reuse
/-- Every fixed query/parser/buffer word except the actual saved-global counter is fresh. -/
def FreshExceptGlobal (before:Stack→List Bool):Prop:=∀j : Fin 20,j≠9→before (Work.freshRole j)=[]
/-- The real saved-global-word drain makes the same complete twenty-role bank fresh. -/
theorem drained_fresh (before:Stack→List Bool) (hf:FreshExceptGlobal before):Work.Fresh (drained before):=by
  intro j
  by_cases h:Work.freshRole j=aux .globalPosition
  · rw [h]
    exact Function.update_self _ _ _
  · have hn:j≠9:=by intro he;subst j;exact h rfl
    exact (Function.update_of_ne h _ _).trans (hf j hn)
/-- Full actual retained-word projection across the complete unary left-scope source. -/
theorem result_other (before:Stack→List Bool) (buckets:List Loop.Bucket) (target:List Bool) (k:Stack)
    (hf:∀j,Cleanup.role j≠k) (he:k≠aux .endpointReader) (ho:k≠aux .outerReader)
    (hp:k≠aux .portHistory) (hr:∀j,Reuse.role false j≠k) (hv:k≠aux .vertexHistory):
    result before buckets target k=before k:=by
  rw [result,PV.result_other _ _ _ k hr hv]
  have hbank:=Ne.symm (hr 0)
  change k≠aux .portBank at hbank
  simp only [prepared,Function.update_of_ne hbank,Function.update_of_ne hp]
  rw [filtered,LV.result_other _ _ _ k hf he ho hp]
  have hg:=Ne.symm (hf 5)
  change k≠aux .globalPosition at hg
  simp only [copied,drained,Function.update_of_ne ho,Function.update_of_ne hg]
/-- Actual nested-filter halt is fresh on every one of the twenty query/parser/buffer tapes. -/
theorem filtered_fresh (before:Stack→List Bool) (buckets:List Loop.Bucket) (target:List Bool)
    (hf:FreshExceptGlobal before):Work.Fresh (filtered before buckets target):=by
  have hd:=drained_fresh before hf
  have hh:∀k∈Header.cleanRoles,copied before buckets k=[]:=by
    simpa [copied,Header.cleanRoles,aux,field] using Work.headerFresh (drained before) hd
  have hz:∀k∈Parse.cleanRoles,copied before buckets k=[]:=by
    simpa [copied,Parse.cleanRoles,aux,field] using Work.childFresh (drained before) hd
  have hh':=LV.result_headerClean buckets (copied before buckets) target hh
  have hz':=LV.result_clean buckets (copied before buckets) target hz
  have hcopy (j:Fin 20) (hne:Work.freshRole j≠aux .outerReader):copied before buckets (Work.freshRole j)=[]:=
    (Function.update_of_ne hne _ _).trans (hd j)
  intro j
  fin_cases j
  · exact LV.result_outerReader _ _ _
  · exact hh' (aux .childReader) (by simp [Header.cleanRoles])
  · exact hh' (aux .endpointReader) (by simp [Header.cleanRoles])
  · exact hz' (aux .rowBuffer) (by simp [Parse.cleanRoles])
  · exact hz' (aux .ownerKey) (by simp [Parse.cleanRoles])
  · exact hz' (aux .sourceKey) (by simp [Parse.cleanRoles])
  · exact hz' (aux .slotWord) (by simp [Parse.cleanRoles])
  · exact hz' (aux .edgeWord) (by simp [Parse.cleanRoles])
  · exact hz' (aux .sideWord) (by simp [Parse.cleanRoles])
  · exact hz' (aux .globalPosition) (by simp [Parse.cleanRoles])
  · exact (LV.result_other _ _ _ (Work.freshRole 10) (by intro i;fin_cases i <;> decide) (by decide) (by decide) (by decide)).trans (hcopy 10 (by decide))
  · exact (LV.result_other _ _ _ (Work.freshRole 11) (by intro i;fin_cases i <;> decide) (by decide) (by decide) (by decide)).trans (hcopy 11 (by decide))
  · exact (LV.result_other _ _ _ (Work.freshRole 12) (by intro i;fin_cases i <;> decide) (by decide) (by decide) (by decide)).trans (hcopy 12 (by decide))
  · exact (LV.result_other _ _ _ (Work.freshRole 13) (by intro i;fin_cases i <;> decide) (by decide) (by decide) (by decide)).trans (hcopy 13 (by decide))
  · exact hh' (aux .packetKey) (by simp [Header.cleanRoles])
  · exact hh' (aux .paddingKey) (by simp [Header.cleanRoles])
  · exact hz' (field (.inl .scratch)) (by simp [Parse.cleanRoles])
  · exact hz' (field (.inr ())) (by simp [Parse.cleanRoles])
  · exact (LV.result_other _ _ _ (Work.freshRole 18) (by intro i;fin_cases i <;> decide) (by decide) (by decide) (by decide)).trans (hcopy 18 (by decide))
  · exact (LV.result_other _ _ _ (Work.freshRole 19) (by intro i;fin_cases i <;> decide) (by decide) (by decide) (by decide)).trans (hcopy 19 (by decide))
/-- The real reversal touches neither the twenty query words nor the context/header caches. -/
theorem prepared_fresh (before:Stack→List Bool) (buckets:List Loop.Bucket) (target:List Bool)
    (hf:FreshExceptGlobal before):Work.Fresh (prepared before buckets target):=by
  have h:=filtered_fresh before buckets target hf
  intro j
  have hb:Work.freshRole j≠aux .portBank:=by fin_cases j <;> decide
  have hp:Work.freshRole j≠aux .portHistory:=by fin_cases j <;> decide
  exact (Function.update_of_ne hb _ _).trans ((Function.update_of_ne hp _ _).trans (h j))
/-- Complete actual unary conversion/logging/cleanup retains the freshly acquired query bank. -/
theorem result_fresh (before:Stack→List Bool) (buckets:List Loop.Bucket) (target:List Bool)
    (hf:FreshExceptGlobal before):Work.Fresh (result before buckets target):=by
  have h:=prepared_fresh before buckets target hf
  intro j
  exact (PV.result_other false _ _ (Work.freshRole j)
    (by intro i;fin_cases i <;> fin_cases j <;> decide) (by fin_cases j <;> decide)).trans (h j)
/-- All twelve actual ordinal tapes have really been drained after the left-scope row. -/
theorem result_ordinal (before:Stack→List Bool) (buckets:List Loop.Bucket) (target:List Bool) (k:O.Stack):
    result before buckets target (ordinal k)=[]:=PV.result_ordinal _ _ _ _
/-- Actual binary port metadata bank has really been drained. -/
theorem result_portBank (before:Stack→List Bool) (buckets:List Loop.Bucket) (target:List Bool):
    result before buckets target (aux .portBank)=[]:=PV.result_bank _ _ _
/-- Actual binary port history has really been consumed by its paid reversal. -/
theorem result_portHistory (before:Stack→List Bool) (buckets:List Loop.Bucket) (target:List Bool):
    result before buckets target (aux .portHistory)=[]:=by
  rw [result,PV.result_other _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide)]
  rfl
/-- Exactly the real unary left-scope row is appended to the actual per-old-vertex log. -/
theorem result_vertexHistory (before:Stack→List Bool) (buckets:List Loop.Bucket) (target:List Bool):
    result before buckets target (aux .vertexHistory)=
      (SemiprimeD1StackChildGroupFactoryWordLog.row (SemiprimeD1StackPortOrdinalStream.result (Loop.portWords buckets target))).reverse++
        before (aux .vertexHistory):=by
  have h:=PV.result_history false (prepared before buckets target) (Loop.portWords buckets target)
  change SemiprimeD1StackChildGroupFactoryPortConvert.result false (prepared before buckets target)
    (Loop.portWords buckets target) (aux .vertexHistory)=
      (SemiprimeD1StackChildGroupFactoryWordLog.row (SemiprimeD1StackPortOrdinalStream.result (Loop.portWords buckets target))).reverse++
        prepared before buckets target (aux .vertexHistory) at h
  rw [result,h]
  change _++filtered before buckets target (aux .vertexHistory)=_
  rw [filtered,LV.result_other _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)]
  rfl
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsSourceView
