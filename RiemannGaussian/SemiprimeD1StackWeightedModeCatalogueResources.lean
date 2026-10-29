/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueBounds
/-! # Genuine metadata frontend machine and all thirty-five-role prefixes
The prepared inputs are paid unary packet/tile counts and actual precision
WIDTH. This is a complete finite frontend, with packet acquisition explicit
upstream; it is not claimed to initialize from binary N alone.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueResources
open SemiprimeD1StackWeightedModeCatalogue SemiprimeD1StackWeightedModeCatalogueView
open SemiprimeD1StackWeightedModeCatalogueExecution SemiprimeD1StackWeightedModeCatalogueBounds
open SemiprimeD1StackWeightedModeCatalogueFinish (weights)
open SemiprimeD1StackWeightedModeView (unary)
open SemiprimeD1StackCalls (configuration)
local notation "main" => (Sum.inl Control.start :Label)
attribute [local irreducible] runBound polynomial
/-- Every successful prefix precedes the actual completed source halt. -/
theorem prefix_fuel (p t width fuel:Nat) (out:C.State Stack Label)
    (hr:C.run program fuel (initial (unary p) (unary t) (unary width))=some out):fuel ≤runBound p t width:=by
  obtain ⟨time,ht,he⟩:=source_run_bounded p t width
  have hh:C.run program 1 (done p t width)=none:=rfl
  have hf:fuel ≤time:=by
    by_contra hn
    have h:fuel=time+(1+(fuel-(time+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- All seventeen DFS roles, seven multiplier roles, eleven frontend roles and actual returns are counted. -/
theorem prefix_cells (p t width fuel:Nat) (out:C.State Stack Label)
    (hr:C.run program fuel (initial (unary p) (unary t) (unary width))=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤36*(p+t+width+runBound p t width):=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (p+t+width) _ _ (initial_length p t width) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ _ hr
  change out.frames.length ≤0+fuel at hf
  have hs:=SemiprimeD1StackWeightedModeResources.word_sum_le out.data (p+t+width+fuel) hd
  rw [stack_card] at hs
  have ht:=prefix_fuel p t width fuel out hr
  omega
/-- Whole actual catalogue-and-feasible-DFS finite-machine certificate. -/
noncomputable def modesInTime (p t width:Nat):StateTransition.EvalsToInTime machine.step
    (configuration (initial (unary p) (unary t) (unary width)))
    (some (configuration (done p t width))) (runBound p t width):=by
  apply SemiprimeD1StackCalls.evalsCorrect (weighted .width) (weighted .output) main program
  have h:=source_run_bounded p t width
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Every actual compiled prefix includes all acquired catalogue, metadata and activation/return bytes. -/
theorem machine_prefix_cells (p t width fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel]
      (some (configuration (initial (unary p) (unary t) (unary width))))=some cfg):
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤36*(p+t+width+runBound p t width):=by
  have he:=SemiprimeD1StackCalls.run_correct (weighted .width) (weighted .output) main program fuel
    (initial (unary p) (unary t) (unary width))
  have hh:=he.trans hr
  cases hout:C.run program fuel (initial (unary p) (unary t) (unary width)) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells p t width fuel out hout
/-- Fixed coefficient and degree precede every metadata input and every actual feasible traversal. -/
theorem source_run_monomial:∃A d:Nat,∀p t width,∃time ≤A*(p+t+width+1)^d*
    SemiprimeD1WeightedTuples.visits (weights p t width) (width-1),
      C.run program time (initial (unary p) (unary t) (unary width))=some (done p t width):=by
  obtain ⟨A,d,hp⟩:=polynomial_monomial
  refine ⟨A,d,?_⟩
  intro p t width
  obtain ⟨time,ht,hr⟩:=source_run_bounded p t width
  have hb:runBound p t width ≤A*(p+t+width+1)^d*
      SemiprimeD1WeightedTuples.visits (weights p t width) (width-1):=by
    unfold runBound
    exact Nat.mul_le_mul_right _ (hp (p+t+width))
  exact ⟨time,ht.trans hb,hr⟩
/-- Fixed monomial resource witnesses cover every real data/return prefix of the same source. -/
theorem prefix_monomial:∃A d:Nat,∀p t width fuel (out:C.State Stack Label),
    C.run program fuel (initial (unary p) (unary t) (unary width))=some out→
      (∑k:Stack,(out.data k).length)+out.frames.length ≤A*(p+t+width+1)^d*
        SemiprimeD1WeightedTuples.visits (weights p t width) (width-1):=by
  obtain ⟨A,d,hp⟩:=polynomial_monomial
  refine ⟨36*(1+A),d+1,?_⟩
  intro p t width fuel out hr
  let n:=p+t+width
  let v:=SemiprimeD1WeightedTuples.visits (weights p t width) (width-1)
  have hv:1 ≤v:=Nat.succ_le_of_lt (SemiprimeD1WeightedTuples.visits_positive _ _)
  have hs:1 ≤n+1:=by omega
  have hd:(n+1)^d ≤(n+1)^(d+1):=Nat.pow_le_pow_right hs (by omega)
  have hn:n ≤(n+1)^(d+1):=by
    have h:n+1 ≤(n+1)^(d+1):=by
      simpa only [pow_one] using Nat.pow_le_pow_right hs (by omega:1 ≤d+1)
    omega
  have hnv:n ≤(n+1)^(d+1)*v:=hn.trans
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((n+1)^(d+1)) hv)
  have hb:runBound p t width ≤A*(n+1)^(d+1)*v:=by
    unfold runBound
    exact Nat.mul_le_mul_right v ((hp n).trans (Nat.mul_le_mul_left A hd))
  have hcell:=prefix_cells p t width fuel out hr
  change _ ≤36*(1+A)*(n+1)^(d+1)*v
  calc
    _ ≤36*(n+runBound p t width):=hcell
    _ ≤36*((n+1)^(d+1)*v+A*(n+1)^(d+1)*v):=
      Nat.mul_le_mul_left 36 (Nat.add_le_add hnv hb)
    _= _:=by ring
end RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueResources
