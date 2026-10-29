/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildVertexChoiceBounds
/-! # Every physical169-role prefix and actual saved return cell
All four displaced inactive input/output shadows and both complete source banks
are counted. Prefix bounds come from this SAME source's actual whole halt.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildVertexChoiceStorage
open SemiprimeD1StackChildVertexChoice SemiprimeD1StackChildVertexChoiceSpec
open SemiprimeD1StackChildVertexChoiceBounds
variable {d : ℕ}
/-- All eight original inputs and every empty private/shadow allocation have an actual source-byte cap. -/
theorem initial_length (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) (bit : Bool) (k : Stack) :
    ((originalInitial old extra oldp newp parent order ports bit).data k).length≤
      62*resource old extra oldp newp parent order ports := by
  have hb:=resource_bounds old extra oldp newp parent order ports
  rcases k with k|k
  · exact (SemiprimeD1StackChildLiftVertexStorage.initial_length old extra oldp newp parent order ports k).trans
      (Nat.mul_le_mul_left 62 hb.2.1)
  · rcases k with k|k
    · change (if shared k then [] else ([] : List Bool)).length≤_
      split <;> exact Nat.zero_le _
    · cases k
      change 1≤62*resource old extra oldp newp parent order ports
      omega
/-- A successful source prefix never extends beyond this same actual whole halt. -/
theorem prefix_fuel (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order ports : List ℕ) (bit : Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (originalInitial old extra oldp newp parent order ports bit)=some out) :
    fuel≤polynomial old extra oldp newp parent order ports := by
  obtain ⟨t,ht,hs⟩:=source_run_bounded old ho extra he oldp newp hp parent hg order ports bit
  have hf : fuel≤t := by
    by_contra hn
    have heq : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [heq,SemiprimeD1StackReturnLink.run_add,hs,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hh : SemiprimeD1StackCalls.run program 1 (done old extra oldp newp parent order ports bit)=none := rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- One fixed whole-family cap, including all data allocations and real return cells. -/
def cellsPolynomial (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) : ℕ:=
  10^29*(resource old extra oldp newp parent order ports)^2*2^ports.length
/-- All169 roles plus the actual call-return stack at EVERY reached prefix of the SAME source. -/
theorem prefix_cells (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order ports : List ℕ) (bit : Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (originalInitial old extra oldp newp parent order ports bit)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤cellsPolynomial old extra oldp newp parent order ports := by
  have hf:=prefix_fuel old ho extra he oldp newp hp parent hg order ports bit fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel
    (62*resource old extra oldp newp parent order ports) _ out
    (initial_length old extra oldp newp parent order ports bit) hr
  have hm:=SemiprimeD1StackChildLiftVertexStorage.finite_sum_bound out.data
    (62*resource old extra oldp newp parent order ports+fuel) hd
  rw [stack_card] at hm
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel
    (originalInitial old extra oldp newp parent order ports bit) out hr
  change out.frames.length≤0+fuel at hframes
  let r:=resource old extra oldp newp parent order ports
  have hr2 : r≤r^2:=Nat.le_pow (by decide : 0<2)
  have he2 : 1≤2^ports.length:=Nat.one_le_pow _ _ (by decide : 1≤(2:ℕ))
  have hscale : r^2≤r^2*2^ports.length:=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (r^2) he2
  have hpay:=hr2.trans hscale
  unfold polynomial cellsPolynomial at *
  rw [Nat.mul_assoc] at hf ⊢
  change fuel≤10^26*(r^2*2^ports.length) at hf
  change _≤10^29*(r^2*2^ports.length)
  omega
/-- The genuine compiled169-role machine also counts its real none-label saved-return tape. -/
theorem machine_prefix_cells (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order ports : List ℕ) (bit : Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (originalInitial old extra oldp newp parent order ports bit)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤cellsPolynomial old extra oldp newp parent order ports := by
  have heq:=SemiprimeD1StackCalls.run_correct activity output (.local .start) program fuel
    (originalInitial old extra oldp newp parent order ports bit)
  have hh:=heq.trans hr
  cases hout : SemiprimeD1StackCalls.run program fuel (originalInitial old extra oldp newp parent order ports bit) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg : cfg=SemiprimeD1StackCalls.configuration out:=(Option.some.inj hh).symm
    subst cfg
    exact prefix_cells old ho extra he oldp newp hp parent hg order ports bit fuel out hout
end RiemannGaussian.SemiprimeD1StackChildVertexChoiceStorage
