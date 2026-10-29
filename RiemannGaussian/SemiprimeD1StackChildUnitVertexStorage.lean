/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildUnitVertexBounds
/-! # All32 actual data roles, displaced cache shadows and real return cells -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildUnitVertexStorage
open SemiprimeD1StackChildUnitVertex SemiprimeD1StackChildUnitVertexOriginal
open SemiprimeD1StackChildUnitVertexBounds
/-- Only the two context-header tapes are present before all acquired counters/unit/record bits. -/
theorem initial_length (axes : List ℕ) (precision : List Bool) (k : Stack) :
    ((originalInitial axes precision).data k).length≤resource axes precision := by
  rcases k with k|k
  · exact SemiprimeD1StackJetContextBounds.initial_length axes precision k
  · rcases k with k|k
    · change (if k=U.widthCache ∨ k=U.rankCache then [] else ([] : List Bool)).length≤_
      split <;> exact Nat.zero_le _
    · cases k <;> exact Nat.zero_le _
/-- No actual successful source prefix extends beyond this same source's whole proved halt. -/
theorem prefix_fuel (axes : List ℕ) (hp : ∀q∈axes,0<q) (precision : List Bool)
    (fuel : ℕ) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (originalInitial axes precision)=some out) :
    fuel≤polynomial axes precision := by
  obtain ⟨t,ht,hs⟩:=source_run_bounded axes hp precision
  have hf : fuel≤t := by
    by_contra hn
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hs,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hh : SemiprimeD1StackCalls.run program 1 (done axes precision)=none := rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- An abstract inventory bound, without concrete register-enumeration reduction. -/
theorem finite_sum_bound {K : Type} [Fintype K] (data : K→List Bool) (cap : ℕ)
    (h : ∀k,(data k).length≤cap) : (∑k : K,(data k).length)≤Fintype.card K*cap := by
  calc
    _≤∑_k : K,cap:=Finset.sum_le_sum (fun k _=>h k)
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
/-- Fixed coefficient/degree before every actual header and context. -/
def cellsPolynomial (axes : List ℕ) (precision : List Bool) : ℕ:=10^11*(resource axes precision+1)^2
/-- Every SAME-source prefix includes ALL32 source/shadow/frame words and actual saved return cells. -/
theorem prefix_cells (axes : List ℕ) (hp : ∀q∈axes,0<q) (precision : List Bool)
    (fuel : ℕ) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (originalInitial axes precision)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤cellsPolynomial axes precision := by
  have hf:=prefix_fuel axes hp precision fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (resource axes precision)
    _ out (initial_length axes precision) hr
  have hm:=finite_sum_bound out.data (resource axes precision+fuel) hd
  rw [stack_card] at hm
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel (originalInitial axes precision) out hr
  change out.frames.length≤0+fuel at hframes
  have hr' : resource axes precision≤(resource axes precision+1)^2:=by nlinarith [sq_nonneg (resource axes precision)]
  unfold cellsPolynomial polynomial at *
  omega
/-- The actual finite32-role compiled machine counts its real none-label return tape at every reached prefix. -/
theorem machine_prefix_cells (axes : List ℕ) (hp : ∀q∈axes,0<q) (precision : List Bool)
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (originalInitial axes precision)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤cellsPolynomial axes precision := by
  have heq:=SemiprimeD1StackCalls.run_correct (context J.axesCache) (aux .record) (.local .start) program fuel
    (originalInitial axes precision)
  have hh:=heq.trans hr
  cases hout : SemiprimeD1StackCalls.run program fuel (originalInitial axes precision) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg : cfg=SemiprimeD1StackCalls.configuration out:=(Option.some.inj hh).symm
    subst cfg
    exact prefix_cells axes hp precision fuel out hout
end RiemannGaussian.SemiprimeD1StackChildUnitVertexStorage
