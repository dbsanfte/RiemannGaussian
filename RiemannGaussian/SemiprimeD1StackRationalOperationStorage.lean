/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalOperationBounds
/-! # All36 allocated words and actual return cells at every compiled prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalOperationStorage
open SemiprimeD1StackRationalOperation SemiprimeD1StackRationalOperationEncoding
open SemiprimeD1StackRationalOperationExecution SemiprimeD1StackRationalOperationBounds
/-- Every initialized byte is charged to one of the five actual original input tapes. -/
theorem initial_role_bound (op:Op) (ls ld rs rd template:List Bool) (k:Stack) :
    ((initial op ls ld rs rd template).data k).length ≤ inputSize ls ld rs rd template:=by
  rcases k with k|k
  · simp [initial,input,inputSize]
  · rcases k with k|k
    · simp [initial,input,inputSize]
    · cases k <;> simp [initial,input,inputSize] <;> omega
/-- Every successful prefix ends no later than this SAME actual source's true halt. -/
theorem prefix_fuel (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial op (sx::xn) xd (sy::yn) yd template)=some out) :
    fuel ≤ runBound op sx xn xd sy yn yd template:=by
  let q:=runBound op sx xn xd sy yn yd template
  have hfinal:=source_run op sx xn xd sy yn yd template
  have ht:fuel ≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (done op sx xn xd sy yn yd template)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact ht
/-- Every literal finite physical inventory sum is bounded by its36 actual role caps. -/
theorem word_sum (words:Stack→List Bool) (cap:Nat) (h:∀k,(words k).length ≤ cap) :
    (∑k:Stack,(words k).length) ≤36*cap:=by
  calc
    _ ≤∑_k:Stack,cap:=Finset.sum_le_sum (fun k _=>h k)
    _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
attribute [local irreducible] runBound result
/-- Every actual role includes retained input/template, shared arithmetic/copy scratch, and actual return cells. -/
theorem prefix_cells (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial op (sx::xn) xd (sy::yn) yd template)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤37*(inputSize (sx::xn) xd (sy::yn) yd template+
      runBound op sx xn xd sy yn yd template+1):=by
  let s:=inputSize (sx::xn) xd (sy::yn) yd template
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel s _ _ (initial_role_bound op (sx::xn) xd (sy::yn) yd template) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤0+fuel at hf
  have hsum:=word_sum out.data (s+fuel) hd
  have ht:=prefix_fuel op sx xn xd sy yn yd template fuel out hr
  omega
/-- Fixed sixth-degree bound includes the actual VALUE-width template and all private shared banks. -/
theorem polynomial_space (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    37*(inputSize (sx::xn) xd (sy::yn) yd template+runBound op sx xn xd sy yn yd template+1) ≤
      100000000000000000000000*(inputSize (sx::xn) xd (sy::yn) yd template)^6:=by
  have ht:=runBound_le op sx xn xd sy yn yd template
  have hs:1 ≤ inputSize (sx::xn) xd (sy::yn) yd template:=by unfold inputSize;omega
  have hpow:inputSize (sx::xn) xd (sy::yn) yd template ≤(inputSize (sx::xn) xd (sy::yn) yd template)^6:=Nat.le_pow (by decide:0<6)
  unfold polynomial at ht
  nlinarith only [ht,hs,hpow]
/-- Genuine compiled prefixes count all36 data tapes and the none-labelled real finite return tape. -/
theorem machine_prefix_cells (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool)
    (fuel:Nat) (cfg:(machine op).Cfg)
    (hr:(fun c=>c.bind (machine op).step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial op (sx::xn) xd (sy::yn) yd template)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      100000000000000000000000*(inputSize (sx::xn) xd (sy::yn) yd template)^6:=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .leftSigned) (aux .numeratorOutput) (localLabel .start op false false) program fuel
    (initial op (sx::xn) xd (sy::yn) yd template)
  have hh:=he.trans hr
  cases hout:SemiprimeD1StackCalls.run program fuel (initial op (sx::xn) xd (sy::yn) yd template) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact (prefix_cells op sx xn xd sy yn yd template fuel out hout).trans (polynomial_space op sx xn xd sy yn yd template)
end RiemannGaussian.SemiprimeD1StackRationalOperationStorage
