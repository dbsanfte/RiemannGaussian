/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootMetadataExecution
/-! # Every actual metadata-source prefix counts all13 words and real returns -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPackedRootMetadataStorage
open scoped BigOperators
open SemiprimeD1StackPackedRootMetadata SemiprimeD1StackPackedRootMetadataEncoding
open SemiprimeD1StackPackedRootMetadataExecution
open SemiprimeD1StackCalls (run configuration)
local notation "ctl" => Label.local
/-- The only initial operand is the original physical binary N. -/
theorem input_single (bits : List Bool) : input bits=fun k => if k=boot .input then bits else [] := by
  funext k
  rcases k with k|k|k
  · cases k <;> rfl
  · rfl
  · rfl
/-- The source is genuinely initialized by Turing.initList. -/
theorem initial_eq (bits : List Bool) : Turing.initList machine bits=configuration (initial bits) := by
  have hs : SemiprimeD1StackCalls.initial (boot .input) (ctl .start) bits=initial bits := by
    apply congrArg (fun d => (⟨some (ctl .start),none,none,d,[]⟩ : C.State Stack Label))
    exact (input_single bits).symm
  exact (SemiprimeD1StackCalls.initial_correct (boot .input) (aux .precision) (ctl .start) program bits).symm.trans
    (congrArg configuration hs)
/-- All actual initial data words fit the physically supplied input length. -/
theorem initial_length (bits : List Bool) (k : Stack) : ((initial bits).data k).length ≤ bits.length+1 := by
  change (input bits k).length ≤ bits.length+1
  rw [input_single]
  change (if k=boot .input then bits else []).length ≤ bits.length+1
  split_ifs <;> simp
/-- The ready entry contains only the physically acquired bootstrap words. -/
theorem ready_length (bits : List Bool) (k : Stack) : ((ready bits).data k).length ≤ bits.length+1 := by
  rcases k with k|k|k
  · cases k <;> simp only [ready,bank,Sum.elim_inl,SemiprimeD1BinaryBootstrap.done,B.payload,
      List.length_nil,List.length_replicate,List.length_singleton] <;> omega
  · exact Nat.zero_le _
  · exact Nat.zero_le _
/-- ALL13 physical allocations include the unused adder-left shadow. -/
theorem word_sum (d : Stack→List Bool) (cap : ℕ) (h : ∀k,(d k).length ≤ cap) :
    (∑k : Stack,(d k).length) ≤ 13*cap := by
  calc
    _ ≤ ∑_k : Stack,cap := Finset.sum_le_sum (fun k _ => h k)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
/-- Same actual program, own halt and own clock control every prefix. -/
theorem prefix_cells_at (bits : List Bool) (before out : C.State Stack Label) (fuel : ℕ)
    (hw : ∀k,(before.data k).length ≤ bits.length+1) (hf : before.frames=[])
    (hs : ∃t ≤ polynomial bits,run program t before=some (done bits))
    (hr : run program fuel before=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ 100000*(bits.length+1)^2 := by
  obtain ⟨t,ht,hstop⟩ := hs
  have hh : run program 1 (done bits)=none := rfl
  have hft : fuel ≤ t := by
    by_contra hn
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  have hd := SemiprimeD1StackReturnLink.run_data_bound program fuel (bits.length+1) before out hw hr
  have hframes := SemiprimeD1StackCalls.run_frame_bound program fuel before out hr
  rw [hf,List.length_nil] at hframes
  have hs := word_sum out.data (bits.length+1+fuel) hd
  have h2 : bits.length+1 ≤ (bits.length+1)^2 := Nat.le_pow (by decide : 0<(2:ℕ))
  unfold polynomial at ht
  omega
/-- Whole original-N prefix space counts all13 words and every genuine saved return. -/
theorem prefix_cells (bits : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : run program fuel (initial bits)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ 100000*(bits.length+1)^2 :=
  prefix_cells_at bits (initial bits) out fuel (initial_length bits) rfl (source_run_bounded bits) hr
/-- SAME actual acquired-bootstrap continuation has the same all-role prefix cap. -/
theorem ready_prefix_cells (bits : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : run program fuel (ready bits)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ 100000*(bits.length+1)^2 :=
  prefix_cells_at bits (ready bits) out fuel (ready_length bits) rfl (ready_run_bounded bits) hr
/-- Generic exact compiler projection precedes original input instantiation. -/
theorem machine_cells_at (bits : List Bool) (before : C.State Stack Label) (fuel : ℕ) (cfg : machine.Cfg)
    (hp : (fun q => q.bind machine.step)^[fuel] (some (configuration before))=some cfg)
    (hc : ∀out,run program fuel before=some out→
      (∑k : Stack,(out.data k).length)+out.frames.length ≤ 100000*(bits.length+1)^2) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 100000*(bits.length+1)^2 := by
  have he := SemiprimeD1StackCalls.run_correct (boot .input) (aux .precision) (ctl .start) program fuel before
  have hh := he.trans hp
  cases hout : run program fuel before with
  | none => rw [hout] at hh;cases hh
  | some out =>
    rw [hout] at hh
    have hcfg : configuration out=cfg := Option.some.inj hh
    subst cfg
    exact hc out hout
/-- Every genuine compiled N-only prefix pays all13 data words plus the actual return stack. -/
theorem machine_prefix_cells (bits : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hp : (fun q => q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 100000*(bits.length+1)^2 := by
  rw [initial_eq] at hp
  exact machine_cells_at bits (initial bits) fuel cfg hp (fun out hr => prefix_cells bits fuel out hr)
end RiemannGaussian.SemiprimeD1StackPackedRootMetadataStorage
