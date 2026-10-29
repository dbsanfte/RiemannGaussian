/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearBounds
/-! # All29 actual data words and real returns at every whole/ready machine prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearStorage
open SemiprimeD1StackKernelLinear SemiprimeD1StackKernelLinearExecution
open SemiprimeD1StackKernelLinearBounds SemiprimeD1StackKernelLinearAcquisitionBounds
namespace Acq
export SemiprimeD1StackKernelLinearAcquisition (readyWords)
end Acq
/-- All29 words are counted, including every allocated otherwise-unused private address. -/
theorem word_sum (data : Stack→List Bool) (cap : ℕ) (h : ∀role,(data role).length≤cap) :
    (∑role : Stack,(data role).length)≤29*cap := by
  classical
  calc
    _≤∑_k : Stack,cap:=Finset.sum_le_sum (fun role _=>h role)
    _=29*cap:=by rw [Finset.sum_const,Finset.card_univ,stack_card];rfl
/-- A prefix cannot continue past a proved true halt of the SAME program/state. -/
theorem prefix_fuel (start stop : C.State Stack Label) (bound : ℕ)
    (hstop : stop.pc=none) (h : ∃s≤bound,SemiprimeD1StackCalls.run program s start=some stop)
    (fuel : ℕ) (out : C.State Stack Label) (hr : SemiprimeD1StackCalls.run program fuel start=some out) :
    fuel≤bound := by
  obtain ⟨s,hs,hh⟩:=h
  have hbefore:fuel ≤ s :=by
    by_contra hn
    have he:fuel=s+(1+(fuel-(s+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have heof:SemiprimeD1StackCalls.run program 1 stop=none:=by
      cases stop with
      | mk pc focus flag data frames=>cases pc <;> first | rfl | cases hstop
    rw [heof,Option.bind_none] at hr
    cases hr
  exact hbefore.trans hs
/-- Generic SAME-source prefix capacity counts all29 tapes and the real none-label stack. -/
theorem prefix_cap (start stop : C.State Stack Label) (cap bound : ℕ)
    (hstop : stop.pc=none) (hframes : start.frames=[])
    (hstart : ∀role,(start.data role).length≤cap)
    (h : ∃s≤bound,SemiprimeD1StackCalls.run program s start=some stop)
    (fuel : ℕ) (out : C.State Stack Label) (hr : SemiprimeD1StackCalls.run program fuel start=some out) :
    (∑role : Stack,(out.data role).length)+out.frames.length≤30*(cap+bound) := by
  have hf:=prefix_fuel start stop bound hstop h fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel cap start out hstart hr
  have hm:=word_sum out.data (cap+fuel) hd
  have hret:=SemiprimeD1StackCalls.run_frame_bound program fuel start out hr
  rw [hframes,List.length_nil] at hret
  omega
/-- Every one of four original source words is charged by the actual input size. -/
theorem initial_bound (a t x y:List Bool) (role:Stack):
    ((initial a t x y).data role).length ≤ 2*inputSize a t x y:=by
  rcases role with role|role
  · simp [initial,input,aux]
  · cases role <;> simp [initial,input,aux,inputSize] <;> omega
/-- Every physically acquired cache word has a semantic input-byte cap, independent of elapsed time. -/
theorem ready_initial_bound (a t x y:List Bool) (role:Stack):
    ((ready a t x y).data role).length ≤ 2*inputSize a t x y:=by
  have hc:=ready_caps a t x y
  rcases role with role|role
  · exact Nat.zero_le _
  · cases role
    case a=>change a.length ≤ _;unfold inputSize;omega
    case t=>change t.length ≤ _;unfold inputSize;omega
    case x=>change x.length ≤ _;unfold inputSize;omega
    case y=>change y.length ≤ _;unfold inputSize;omega
    case k=>change (true::a).length ≤ _;simp only [List.length_cons];unfold inputSize;omega
    case center=>
      change (SemiprimeD1StackKernelLinearSpec.power a.length).length ≤ _
      rw [SemiprimeD1StackKernelLinearSpec.power_length]
      unfold inputSize;omega
    case j=>exact hc.1
    case displacement=>exact hc.2.1
    case alpha=>exact hc.2.2.1
    case buffer=>exact hc.2.2.2
    all_goals exact Nat.zero_le _
/-- Fixed physical-space coefficient/degree, counting all29 roles plus actual return cells. -/
def cellsPolynomial (a t x y:List Bool):Nat:=10000000000*(inputSize a t x y)^3
/-- SAME-source capacity pays all retained inputs/caches and all actual allocations. -/
theorem cells_le (a t x y:List Bool):30*(2*inputSize a t x y+polynomial a t x y) ≤ cellsPolynomial a t x y:=by
  have h:inputSize a t x y ≤ (inputSize a t x y)^3:=Nat.le_pow (by decide:0<3)
  unfold polynomial cellsPolynomial
  omega
/-- EVERY successful whole-source prefix counts all29 data tapes and real return frames. -/
theorem prefix_cells (a t x y:List Bool) (hx:SemiprimeBitArithmetic.bitValue x<2^a.length)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial a t x y)=some out):
    (∑role:Stack,(out.data role).length)+out.frames.length ≤ cellsPolynomial a t x y:=
  (prefix_cap _ _ _ _ rfl rfl (initial_bound a t x y) (source_run_bounded a t x y hx) fuel out hr).trans (cells_le a t x y)
/-- SAME actual acquired-cache entry preserves and counts the entire retained source/cache bank. -/
theorem ready_prefix_cells (a t x y:List Bool) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (ready a t x y)=some out):
    (∑role:Stack,(out.data role).length)+out.frames.length ≤ cellsPolynomial a t x y:=
  (prefix_cap _ _ _ _ rfl rfl (ready_initial_bound a t x y) (ready_run_bounded a t x y) fuel out hr).trans (cells_le a t x y)
/-- Exact compiled-state bridge includes both all29 alphabets and the real none-label return alphabet. -/
theorem machine_cap (start:C.State Stack Label) (bound:Nat)
    (h:∀fuel out,SemiprimeD1StackCalls.run program fuel start=some out→
      (∑role:Stack,(out.data role).length)+out.frames.length ≤ bound)
    (fuel:Nat) (cfg:machine.Cfg)
    (hp:(fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start))=some cfg):
    (∑role:Stack,(cfg.stk (some role)).length)+(cfg.stk none).length ≤ bound:=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .a) (aux .slope) (Label.local Control.start) program fuel start
  have hh:=he.trans hp
  cases hout:SemiprimeD1StackCalls.run program fuel start with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hc:cfg=SemiprimeD1StackCalls.configuration out:=(Option.some.inj hh).symm
    subst cfg
    exact h fuel out hout
/-- ALL29 allocated tapes and real returns at every genuine compiled whole-source prefix. -/
theorem machine_prefix_cells (a t x y:List Bool) (hx:SemiprimeBitArithmetic.bitValue x<2^a.length)
    (fuel:Nat) (cfg:machine.Cfg)
    (hp:(fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial a t x y)))=some cfg):
    (∑role:Stack,(cfg.stk (some role)).length)+(cfg.stk none).length ≤ cellsPolynomial a t x y:=
  machine_cap _ _ (prefix_cells a t x y hx) fuel cfg hp
/-- ALL29 allocated tapes and real returns at every genuine SAME-machine acquired-cache prefix. -/
theorem machine_ready_prefix_cells (a t x y:List Bool) (fuel:Nat) (cfg:machine.Cfg)
    (hp:(fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (ready a t x y)))=some cfg):
    (∑role:Stack,(cfg.stk (some role)).length)+(cfg.stk none).length ≤ cellsPolynomial a t x y:=
  machine_cap _ _ (ready_prefix_cells a t x y) fuel cfg hp
end RiemannGaussian.SemiprimeD1StackKernelLinearStorage
