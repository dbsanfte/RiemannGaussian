/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOldVertexStreamOperands
/-! # Paid stream field reads with real validity consumption -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOldVertexStreamRead
open SemiprimeD1StackOldVertexStream SemiprimeD1StackOldVertexStreamRoles
open SemiprimeD1StackOldVertexStreamView SemiprimeD1StackProcedureTrace
namespace Q
export SemiprimeD1StackOldVertexStreamPrimitives (field_call pop_run join)
end Q
/-- Complete field read followed by one actual TRUE validity pop. -/
theorem field_read (site : Field) (pc checked next : Label)
    (hc : program pc=.call (.field site (P.active .tagPop (none,false))) checked)
    (hp : program checked=.base (.pop (fieldWork (.inr ())) (.local .abort) (.local .abort) next))
    (before : Stack→List Bool) (word tail : List Bool)
    (hi : before (fieldInput site)=SemiprimeSourceHistogramKeyBits.frame word tail)
    (ho : before (fieldOutput site)=[]) (hs : before (fieldWork (.inl .scratch))=[])
    (hv : before (fieldWork (.inr ()))=[]) :
    Runs program (8*word.length+8) pc before next
      (Function.update (Function.update before (fieldInput site) tail) (fieldOutput site) word):=by
  have h0:=Q.field_call site pc checked hc before word tail hi ho hs hv
  let after:=Function.update (Function.update (Function.update before (fieldInput site) tail) (fieldOutput site) word)
    (fieldWork (.inr ())) [true]
  have h1:=Q.pop_run checked (.local .abort) (.local .abort) next (fieldWork (.inr ())) after [true] hp (Function.update_self _ _ _)
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h1
  have hn0 : fieldInput site≠fieldWork (.inr ()):=by cases site <;> decide
  have hn1 : fieldOutput site≠fieldWork (.inr ()):=by cases site <;> decide
  have he : Function.update after (fieldWork (.inr ())) []=
      Function.update (Function.update before (fieldInput site) tail) (fieldOutput site) word:=by
    dsimp only [after]
    rw [Function.update_idem,Function.update_comm hn1,Function.update_comm hn0,←hv,Function.update_eq_self]
  rw [he] at h1
  convert Q.join h0 h1 using 1
/-- A non-header operand projects to its actual raw work value. -/
theorem project_plain (i : Inputs) (w : Words) (k : ChoiceStack) (hk : ¬Header k) :
    data i w (choice k)=w.source k:=by
  rw [project]
  have h0 : k≠axesRole false:=fun h=>hk (Or.inl h)
  have h1 : k≠precisionRole false:=fun h=>hk (Or.inr (Or.inl h))
  have h2 : k≠axesRole true:=fun h=>hk (Or.inr (Or.inr (Or.inl h)))
  have h3 : k≠precisionRole true:=fun h=>hk (Or.inr (Or.inr (Or.inr h)))
  simp only [materialize,h0,h1,h2,h3,ite_false]
/-- Old ports are acquired physically before disposal; their bytes are never free metadata. -/
theorem read_ports (i : Inputs) (w : Words) (word tail : List Bool)
    (hi : w.records=SemiprimeSourceHistogramKeyBits.frame word tail) (ho : w.oldPorts=[]) :
    Runs program (8*word.length+8) (.local .ports) (data i w) (.local .table)
      (data i {w with records:=tail,oldPorts:=word}):=by
  have h:=field_read .ports (.local .ports) (.local .portsValid) (.local .table) rfl rfl
    (data i w) word tail hi ho rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (data i w) (aux .recordsReader) tail) (aux .oldPorts) word) at h
  rw [update_records,update_ports] at h
  exact h
/-- Parsed parent table enters the actual source template without a dictionary lookup. -/
theorem read_table (i : Inputs) (w : Words) (word tail : List Bool)
    (hi : w.records=SemiprimeSourceHistogramKeyBits.frame word tail) (ho : w.source parentRole=[]) :
    Runs program (8*word.length+8) (.local .table) (data i w) (.local .scopeTag)
      (data i {w with records:=tail,source:=Function.update w.source parentRole word}):=by
  have hop : data i w (fieldOutput .table)=[]:=(project_plain i w parentRole operand_not_header.1).trans ho
  have h:=field_read .table (.local .table) (.local .tableValid) (.local .scopeTag) rfl rfl
    (data i w) word tail hi hop rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (data i w) (aux .recordsReader) tail) (choice parentRole) word) at h
  rw [update_records,update_source _ _ _ _ operand_not_header.1] at h
  exact h
/-- Canonical child scope enters its real physical dimension-counter input. -/
theorem read_scope (i : Inputs) (w : Words) (word tail : List Bool)
    (hi : w.scopes=SemiprimeSourceHistogramKeyBits.frame word tail) (ho : w.source scopeRole=[]) :
    Runs program (8*word.length+8) (.local .scope) (data i w) (.local .orderTag)
      (data i {w with scopes:=tail,source:=Function.update w.source scopeRole word}):=by
  have hop : data i w (fieldOutput .scope)=[]:=(project_plain i w scopeRole operand_not_header.2.2.1).trans ho
  have h:=field_read .scope (.local .scope) (.local .scopeValid) (.local .orderTag) rfl rfl
    (data i w) word tail hi hop rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (data i w) (aux .scopesReader) tail) (choice scopeRole) word) at h
  rw [update_scopes,update_source _ _ _ _ operand_not_header.2.2.1] at h
  exact h
/-- Canonical ordinal order enters the same retained parent-table template. -/
theorem read_order (i : Inputs) (w : Words) (word tail : List Bool)
    (hi : w.orders=SemiprimeSourceHistogramKeyBits.frame word tail) (ho : w.source orderRole=[]) :
    Runs program (8*word.length+8) (.local .order) (data i w) (.local .activity)
      (data i {w with orders:=tail,source:=Function.update w.source orderRole word}):=by
  have hop : data i w (fieldOutput .order)=[]:=(project_plain i w orderRole operand_not_header.2.1).trans ho
  have h:=field_read .order (.local .order) (.local .orderValid) (.local .activity) rfl rfl
    (data i w) word tail hi hop rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (data i w) (aux .ordersReader) tail) (choice orderRole) word) at h
  rw [update_orders,update_source _ _ _ _ operand_not_header.2.1] at h
  exact h
end RiemannGaussian.SemiprimeD1StackOldVertexStreamRead
