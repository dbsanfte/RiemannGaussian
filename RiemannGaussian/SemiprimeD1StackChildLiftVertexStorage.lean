/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildLiftVertexBounds
/-! # Every136-word compiled prefix includes actual table, frame and return cells -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildLiftVertexStorage
open SemiprimeD1StackChildLiftVertex SemiprimeD1StackChildLiftVertexOriginal
open SemiprimeD1StackChildLiftVertexBounds
open SemiprimeD1TensorTapeCodec (tape vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
variable {d : ℕ}
/-- All initialized physical words, including every134 template/shadow word, have an input-byte bound. -/
theorem initial_length (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) (slot : Stack) :
    ((originalInitial old extra oldp newp parent order ports).data slot).length≤
      62*resource old extra oldp newp parent order ports := by
  rcases slot with slot|slot
  · have hi:=SemiprimeD1StackVectorTableBounds.initial_cell_le SemiprimeD1StackChildLiftTable.source
      (SemiprimeD1StackChildLiftTableOriginal.original old extra oldp newp parent order)
      (vectorBits (ports.map unary)) slot
    have ht:=R.template_bytes old extra oldp newp parent order (ports.map unary)
    have hs : (vectorBits (ports.map unary)).length≤resource old extra oldp newp parent order ports:=Nat.le_add_left _ _
    change ((originalInitial old extra oldp newp parent order ports).data (table slot)).length≤_ at hi
    change SemiprimeD1StackVectorTableSpec.inputBytes
      (SemiprimeD1StackChildLiftTableOriginal.original old extra oldp newp parent order)≤
        61*resource old extra oldp newp parent order ports at ht
    change ((originalInitial old extra oldp newp parent order ports).data (table slot)).length≤_
    omega
  · cases slot <;> exact Nat.zero_le _
/-- One fixed complete storage polynomial, before every scope and original operand. -/
def cellsPolynomial (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) : ℕ :=
  10^27*(resource old extra oldp newp parent order ports)^2*2^ports.length
/-- A stopped program has no longer successful source prefix. -/
theorem prefix_fuel (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order ports : List ℕ) (fuel : ℕ) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (originalInitial old extra oldp newp parent order ports)=some out) :
    fuel≤polynomial old extra oldp newp parent order ports := by
  obtain ⟨t,ht,hs⟩:=source_run_bounded old ho extra he oldp newp hp parent hg order ports
  have hf : fuel≤t := by
    by_contra hn
    have heq : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [heq,SemiprimeD1StackReturnLink.run_add,hs,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hh : SemiprimeD1StackCalls.run program 1 (done old extra oldp newp parent order ports)=none := rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Abstract finite data inventory avoids unfolding any concrete nested-role enumeration. -/
theorem finite_sum_bound {K : Type} [Fintype K] (data : K→List Bool) (cap : ℕ)
    (h : ∀k,(data k).length≤cap) : (∑k : K,(data k).length)≤Fintype.card K*cap := by
  calc
    _≤∑_k : K,cap:=Finset.sum_le_sum (fun k _=>h k)
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
/-- All136 source/template/scanner/DFS/framing words are counted. -/
theorem word_sum (data : Stack→List Bool) (cap : ℕ) (h : ∀k,(data k).length≤cap) :
    (∑k : Stack,(data k).length)≤136*cap := by
  have hs:=finite_sum_bound data cap h
  rw [stack_card] at hs
  exact hs
/-- Every genuine source prefix counts all136 data roles AND its actual nested return stack. -/
theorem prefix_cells (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order ports : List ℕ) (fuel : ℕ) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (originalInitial old extra oldp newp parent order ports)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤cellsPolynomial old extra oldp newp parent order ports := by
  have ht:=prefix_fuel old ho extra he oldp newp hp parent hg order ports fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel
    (62*resource old extra oldp newp parent order ports) _ out
    (initial_length old extra oldp newp parent order ports) hr
  have hm:=word_sum out.data (62*resource old extra oldp newp parent order ports+fuel) hd
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel
    (originalInitial old extra oldp newp parent order ports) out hr
  change out.frames.length≤0+fuel at hframes
  let r:=resource old extra oldp newp parent order ports
  have hp2 : r≤r^2:=Nat.le_pow (by decide : 0<2)
  have he2 : 1≤2^ports.length:=Nat.one_le_pow _ _ (by decide : 1≤(2:ℕ))
  have hscale : r^2≤r^2*2^ports.length:=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (r^2) he2
  have hpay:=hp2.trans hscale
  unfold polynomial cellsPolynomial at *
  rw [Nat.mul_assoc] at ht ⊢
  change fuel≤10^24*(r^2*2^ports.length) at ht
  change _≤10^27*(r^2*2^ports.length)
  omega
/-- Actual compiled136-word machine includes all source/template/scanner/framing shadows and the real return tape. -/
theorem machine_prefix_cells (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order ports : List ℕ) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (originalInitial old extra oldp newp parent order ports)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤cellsPolynomial old extra oldp newp parent order ports := by
  have heq:=SemiprimeD1StackCalls.run_correct scopeInput (aux .record) (.local .start) program fuel
    (originalInitial old extra oldp newp parent order ports)
  have hh:=heq.trans hr
  cases hout : SemiprimeD1StackCalls.run program fuel (originalInitial old extra oldp newp parent order ports) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg : cfg=SemiprimeD1StackCalls.configuration out:=(Option.some.inj hh).symm
    subst cfg
    exact prefix_cells old ho extra he oldp newp hp parent hg order ports fuel out hout
end RiemannGaussian.SemiprimeD1StackChildLiftVertexStorage
