/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputBounds
/-! # All66 actual data roles and genuine saved return labels at every prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputStorage
open SemiprimeD1StackMarkedPublicInput SemiprimeD1StackMarkedPublicInputEncoding
open SemiprimeD1StackMarkedPublicInputBounds SemiprimeD1StackMarkedPublicInputCost
/-- The source initializes only its four actual input words. -/
theorem initial_length (bits raw indexWord : List Bool) (side : Bool) (k : Stack) :
    ((initial bits raw indexWord [side]).data k).length ≤ inputSize bits raw indexWord := by
  rcases k with k | k
  · exact (SemiprimeD1StackPublicInputBounds.initial_length bits raw indexWord k).trans
      (by unfold inputSize;omega)
  · rcases k with k | k
    · exact Nat.zero_le _
    · rcases k with k | k
      · cases k <;> exact Nat.zero_le _
      · cases k <;> first | exact Nat.zero_le _ | change 1 ≤ inputSize bits raw indexWord;unfold inputSize;omega
/-- The same deterministic actual halt bounds every reached source prefix. -/
theorem prefix_fuel (bits raw indexWord : List Bool) (side : Bool) (hb : bits≠[])
    (fuel : Nat) (out : C.State Stack Label)
    (hp : SemiprimeD1StackCalls.run program fuel (initial bits raw indexWord [side])=some out) :
    fuel ≤ polynomial bits raw indexWord := by
  obtain ⟨t,ht,hstop⟩ := source_run_bounded bits raw indexWord side hb
  have hf : fuel ≤ t := by
    by_contra h
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hp
    have hz : SemiprimeD1StackCalls.run program 1 (done bits raw indexWord side)=none := rfl
    rw [hz,Option.bind_none] at hp
    cases hp
  exact hf.trans ht
/-- Generic physical sum counts every allocated role, including the alias shadow. -/
theorem word_sum (words : Stack → List Bool) (cap : Nat) (h : ∀ k, (words k).length ≤ cap) :
    (∑ k : Stack, (words k).length) ≤ 66*cap := by
  calc
    _ ≤ ∑ _k : Stack, cap := Finset.sum_le_sum (fun k _ => h k)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
/-- Physical prefix resource bound before concrete original family instantiation. -/
theorem prefix_cells_at (s fuel : Nat) (before out : C.State Stack Label)
    (hd : ∀ k, (before.data k).length ≤ s) (hf : before.frames=[])
    (ht : fuel ≤ 1000000000000000*s^2)
    (hp : SemiprimeD1StackCalls.run program fuel before=some out) :
    (∑ k : Stack, (out.data k).length)+out.frames.length ≤ 1000000000000000000*s^2 := by
  have hdata := SemiprimeD1StackReturnLink.run_data_bound program fuel s before out hd hp
  have hframes := SemiprimeD1StackCalls.run_frame_bound program fuel before out hp
  rw [hf,List.length_nil] at hframes
  have hs := word_sum out.data (s+fuel) hdata
  have h2 : s ≤ s^2 := Nat.le_pow (by decide : 0<(2:Nat))
  omega
/-- Every source prefix counts all66 physical roles and the actual none-labelled return stack. -/
theorem prefix_cells (bits raw indexWord : List Bool) (side : Bool) (hb : bits≠[])
    (fuel : Nat) (out : C.State Stack Label)
    (hp : SemiprimeD1StackCalls.run program fuel (initial bits raw indexWord [side])=some out) :
    (∑ k : Stack, (out.data k).length)+out.frames.length ≤
      1000000000000000000*(inputSize bits raw indexWord)^2 :=
  prefix_cells_at _ fuel _ out (initial_length bits raw indexWord side) rfl
    (prefix_fuel bits raw indexWord side hb fuel out hp) hp
/-- Generic exact compiled-bank projection includes every actual saved return cell. -/
theorem machine_cells_at (bound fuel : Nat) (before : C.State Stack Label) (cfg : machine.Cfg)
    (hp : (fun q => q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration before))=some cfg)
    (hc : ∀ out, SemiprimeD1StackCalls.run program fuel before=some out →
      (∑ k : Stack, (out.data k).length)+out.frames.length ≤ bound) :
    (∑ k : Stack, (cfg.stk (some k)).length)+(cfg.stk none).length ≤ bound := by
  have he := SemiprimeD1StackCalls.run_correct
    (checker (.inl SemiprimeD1StackPublicInputWidth.original)) (aux .output) (ctl .start) program fuel before
  have hh := he.trans hp
  cases hout : SemiprimeD1StackCalls.run program fuel before with
  | none => rw [hout] at hh;cases hh
  | some out =>
    rw [hout] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact hc out hout
/-- All genuine compiled prefixes of the SAME source include all66 roles and all real returns. -/
theorem machine_prefix_cells (bits raw indexWord : List Bool) (side : Bool) (hb : bits≠[])
    (fuel : Nat) (cfg : machine.Cfg)
    (hp : (fun q => q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits raw indexWord [side])))=some cfg) :
    (∑ k : Stack, (cfg.stk (some k)).length)+(cfg.stk none).length ≤
      1000000000000000000*(inputSize bits raw indexWord)^2 := by
  apply machine_cells_at _ fuel _ cfg hp
  intro out hr
  exact prefix_cells bits raw indexWord side hb fuel out hr
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputStorage

