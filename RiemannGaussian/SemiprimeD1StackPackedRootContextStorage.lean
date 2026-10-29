/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootContextExecution
/-! # All28 actual context-source words and saved returns at every prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackPackedRootContextStorage
open scoped BigOperators
open SemiprimeD1StackPackedRootContext SemiprimeD1StackPackedRootContextEncoding
open SemiprimeD1StackPackedRootContextExecution
open SemiprimeD1StackCalls (run configuration)
local notation "ctl" => (Sum.inl : Control→Label)
/-- Every non-input word is physically empty at the original-N front door. -/
theorem input_single (bits : List Bool) : input bits=fun k => if k=originalInput then bits else [] := by
  funext k
  rcases k with k|k
  · have h := congrFun (SemiprimeD1StackPackedRootMetadataStorage.input_single bits) k
    simpa only [input,data,originalInput,metadata,Sum.elim_inl,Sum.inl.injEq] using h
  · rfl
/-- Genuine Turing.initList starts before BOTH real acquisitions. -/
theorem initial_eq (bits : List Bool) : Turing.initList machine bits=configuration (initial bits) := by
  have hs : SemiprimeD1StackCalls.initial originalInput (ctl .start) bits=initial bits := by
    apply congrArg (fun d => (⟨some (ctl .start),none,none,d,[]⟩ : C.State Stack Label))
    exact (input_single bits).symm
  exact (SemiprimeD1StackCalls.initial_correct originalInput rank (ctl .start) program bits).symm.trans
    (congrArg configuration hs)
/-- Original input bytes, not a decoded metadata estimate, bound every initial word. -/
theorem initial_length (bits : List Bool) (k : Stack) : ((initial bits).data k).length ≤ 3*(bits.length+1) := by
  change (input bits k).length ≤ 3*(bits.length+1)
  rw [input_single]
  change (if k=originalInput then bits else []).length ≤ 3*(bits.length+1)
  split_ifs
  · omega
  · change 0 ≤ 3*(bits.length+1)
    omega
/-- Each actually acquired metadata word has a semantic linear physical-byte
bound; no polynomial of a previous runtime is raised in this cache invariant. -/
theorem metadata_length (bits : List Bool) (k : M.Stack) : (M.result bits k).length ≤ 3*(bits.length+1) := by
  rcases k with k|k|k
  · cases k with
    | input =>
      change bits.length ≤ 3*(bits.length+1)
      omega
    | reverse => exact Nat.zero_le _
    | width =>
      change (List.replicate bits.length true).length ≤ 3*(bits.length+1)
      simp only [List.length_replicate]
      omega
    | nonzero =>
      change 1 ≤ 3*(bits.length+1)
      omega
  · exact Nat.zero_le _
  · cases k with
    | reader | copyScratch => exact Nat.zero_le _
    | precision => exact (SemiprimeD1StackPackedRootMetadataEncoding.precision_length bits.length).trans (by omega)
    | base =>
      change (SemiprimeD1StackPackedRootMetadataEncoding.baseWord bits.length).length ≤ 3*(bits.length+1)
      rw [SemiprimeD1StackPackedRootMetadataEncoding.base_length]
      omega
    | template =>
      change (List.replicate (2*bits.length) false).length ≤ 3*(bits.length+1)
      simp only [List.length_replicate]
      omega
/-- Exact ready input is an ACTUALLY acquired metadata bank and empty context. -/
theorem ready_length (bits : List Bool) (k : Stack) : ((ready bits).data k).length ≤ 3*(bits.length+1) := by
  rcases k with k|k
  · exact metadata_length bits k
  · exact Nat.zero_le _
/-- Count ALL28 allocations, including every private and shadow word. -/
theorem word_sum (d : Stack→List Bool) (cap : ℕ) (h : ∀k,(d k).length ≤ cap) :
    (∑k : Stack,(d k).length) ≤ 28*cap := by
  calc
    _ ≤ ∑_k : Stack,cap := Finset.sum_le_sum (fun k _ => h k)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
/-- Same-program halt bounds prefixes, including all actual saved return cells. -/
theorem prefix_cost (before out final : C.State Stack Label) (fuel cap clock : ℕ)
    (hw : ∀k,(before.data k).length ≤ cap) (hf : before.frames=[])
    (hs : ∃t ≤ clock,run program t before=some final) (hh : run program 1 final=none)
    (hr : run program fuel before=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ 28*(cap+clock)+clock := by
  obtain ⟨t,ht,hstop⟩ := hs
  have hft : fuel ≤ t := by
    by_contra hn
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  have hd := SemiprimeD1StackReturnLink.run_data_bound program fuel cap before out hw hr
  have hframes := SemiprimeD1StackCalls.run_frame_bound program fuel before out hr
  rw [hf,List.length_nil] at hframes
  have hs := word_sum out.data (cap+fuel) hd
  omega
/-- All actual N-only prefixes have fixed quadratic total data/return storage. -/
theorem prefix_cells (bits : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : run program fuel (initial bits)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ 1000000*(bits.length+1)^2 := by
  have h := prefix_cost (initial bits) out (done bits) fuel (3*(bits.length+1)) (polynomial bits)
    (initial_length bits) rfl (source_run_bounded bits) rfl hr
  have h2 : bits.length+1 ≤ (bits.length+1)^2 := Nat.le_pow (by decide : 0<(2:ℕ))
  unfold polynomial at h
  omega
/-- SAME actually acquired metadata-ready continuation uses linear total space. -/
theorem ready_prefix_cells (bits : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : run program fuel (ready bits)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ 1000000*(bits.length+1) := by
  have h := prefix_cost (ready bits) out (done bits) fuel (3*(bits.length+1)) (readyPolynomial bits)
    (ready_length bits) rfl (ready_run_bounded bits) rfl hr
  unfold readyPolynomial at h
  omega
/-- Exact compiler projection, abstracted before original-data instantiation. -/
theorem machine_cells_at (before : C.State Stack Label) (fuel bound : ℕ) (cfg : machine.Cfg)
    (hp : (fun q => q.bind machine.step)^[fuel] (some (configuration before))=some cfg)
    (hc : ∀out,run program fuel before=some out→
      (∑k : Stack,(out.data k).length)+out.frames.length ≤ bound) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ bound := by
  have he := SemiprimeD1StackCalls.run_correct originalInput rank (ctl .start) program fuel before
  have hh := he.trans hp
  cases hout : run program fuel before with
  | none => rw [hout] at hh;cases hh
  | some out =>
    rw [hout] at hh
    have hcfg : configuration out=cfg := Option.some.inj hh
    subst cfg
    exact hc out hout
/-- Genuine compiled N-only prefixes count all28 words and actual none-stack return cells. -/
theorem machine_prefix_cells (bits : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hp : (fun q => q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 1000000*(bits.length+1)^2 := by
  rw [initial_eq] at hp
  exact machine_cells_at (initial bits) fuel _ cfg hp (fun out hr => prefix_cells bits fuel out hr)
/-- Same compiled program's actual ready prefixes have the fixed linear cache-space cap. -/
theorem machine_ready_prefix_cells (bits : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hp : (fun q => q.bind machine.step)^[fuel] (some (configuration (ready bits)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 1000000*(bits.length+1) :=
  machine_cells_at (ready bits) fuel _ cfg hp (fun out hr => ready_prefix_cells bits fuel out hr)
end RiemannGaussian.SemiprimeD1StackPackedRootContextStorage
