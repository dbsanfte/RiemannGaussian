/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedMomentReadoutCost
/-! # Every actual readout prefix pays all22 words and genuine saved returns
The scalar is an actual second physical input, separately charged by its byte
length. These are prepared-machine certificates; N-only scalar acquisition is
still a separate caller obligation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedMomentReadoutStorage
open scoped BigOperators
open SemiprimeD1StackPackedMomentReadout SemiprimeD1StackPackedMomentReadoutEncoding
open SemiprimeD1StackPackedMomentReadoutExecution SemiprimeD1StackPackedMomentReadoutCost
open SemiprimeD1StackCalls (run configuration)
/-- Actual two-word input bytes bound every initially allocated word. -/
theorem initial_length (bits scalar : List Bool) (k : Stack) :
    ((initial bits scalar).data k).length ≤ 3*(bits.length+scalar.length+1) := by
  rcases k with k|k|k
  · have h:=SemiprimeD1StackPackedRootMetadataStorage.initial_length bits k
    change (M.input bits k).length ≤ _
    exact h.trans (by omega)
  · exact Nat.zero_le _
  · cases k with
    | scalar => change scalar.length ≤ _;omega
    | count | sum => exact Nat.zero_le _
/-- Each actually acquired metadata word has a semantic linear physical-byte
bound; no polynomial of a previous runtime is raised in this cache invariant. -/
theorem metadata_length (bits : List Bool) (k : M.Stack) : (metadataResult bits k).length ≤ 3*(bits.length+1) := by
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
/-- SAME actually acquired metadata cache has a semantic byte bound, with scalar charged separately. -/
theorem ready_length (bits scalar : List Bool) (k : Stack) :
    ((ready bits scalar).data k).length ≤ 3*(bits.length+scalar.length+1) := by
  rcases k with k|k|k
  · exact (metadata_length bits k).trans (by omega)
  · exact Nat.zero_le _
  · cases k with
    | scalar => change scalar.length ≤ _;omega
    | count | sum => exact Nat.zero_le _
/-- Every one of22 actual allocations is included in total data storage. -/
theorem word_sum (d : Stack→List Bool) (cap : ℕ) (h : ∀k,(d k).length ≤ cap) :
    (∑k : Stack,(d k).length) ≤ 22*cap := by
  calc
    _ ≤ ∑_k : Stack,cap := Finset.sum_le_sum (fun k _ => h k)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
/-- SAME actual program halt bounds every prefix and its actual saved-return cells. -/
theorem prefix_cost (before out final : C.State Stack Label) (fuel cap clock : ℕ)
    (hw : ∀k,(before.data k).length ≤ cap) (hf : before.frames=[])
    (hs : ∃t ≤ clock,run program t before=some final) (hh : run program 1 final=none)
    (hr : run program fuel before=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ 22*(cap+clock)+clock := by
  obtain ⟨t,ht,hstop⟩:=hs
  have hft : fuel ≤ t := by
    by_contra hn
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel cap before out hw hr
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel before out hr
  rw [hf,List.length_nil] at hframes
  have hsum:=word_sum out.data (cap+fuel) hd
  omega
/-- Whole prepared input has fixed quadratic all22-data and real-return prefix storage. -/
theorem prefix_cells (bits scalar : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : run program fuel (initial bits scalar)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ 100000000*(bits.length+scalar.length+1)^2 := by
  have h:=prefix_cost (initial bits scalar) out (done bits scalar) fuel
    (3*(bits.length+scalar.length+1)) (polynomial bits scalar)
    (initial_length bits scalar) rfl (source_run_bounded bits scalar) rfl hr
  have h2 : bits.length+scalar.length+1 ≤ (bits.length+scalar.length+1)^2 := Nat.le_pow (by decide : 0<(2:ℕ))
  unfold polynomial at h
  omega
/-- SAME actual metadata-ready continuation has linear all22-word and real-return prefix storage. -/
theorem ready_prefix_cells (bits scalar : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : run program fuel (ready bits scalar)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ 10000*(bits.length+scalar.length+1) := by
  have h:=prefix_cost (ready bits scalar) out (done bits scalar) fuel
    (3*(bits.length+scalar.length+1)) (readyPolynomial bits scalar)
    (ready_length bits scalar) rfl (ready_run_bounded bits scalar) rfl hr
  unfold readyPolynomial at h
  omega
/-- Exact compiler projection retains all actual data and return words. -/
theorem machine_cells_at (before : C.State Stack Label) (fuel bound : ℕ) (cfg : machine.Cfg)
    (hp : (fun q => q.bind machine.step)^[fuel] (some (configuration before))=some cfg)
    (hc : ∀out,run program fuel before=some out→
      (∑k : Stack,(out.data k).length)+out.frames.length ≤ bound) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ bound := by
  have he:=SemiprimeD1StackCalls.run_correct originalInput (aux .sum) (ctl .start) program fuel before
  have hh:=he.trans hp
  cases hout : run program fuel before with
  | none => rw [hout] at hh;cases hh
  | some out =>
    rw [hout] at hh
    have hcfg : configuration out=cfg := Option.some.inj hh
    subst cfg
    exact hc out hout
/-- Genuine compiled prepared-machine prefixes count all22 words and actual saved returns. -/
theorem machine_prefix_cells (bits scalar : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hp : (fun q => q.bind machine.step)^[fuel] (some (configuration (initial bits scalar)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 100000000*(bits.length+scalar.length+1)^2 :=
  machine_cells_at (initial bits scalar) fuel _ cfg hp (fun out hr => prefix_cells bits scalar fuel out hr)
/-- SAME compiled ready continuation has the actual linear cache-space bound. -/
theorem machine_ready_prefix_cells (bits scalar : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hp : (fun q => q.bind machine.step)^[fuel] (some (configuration (ready bits scalar)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 10000*(bits.length+scalar.length+1) :=
  machine_cells_at (ready bits scalar) fuel _ cfg hp (fun out hr => ready_prefix_cells bits scalar fuel out hr)
end RiemannGaussian.SemiprimeD1StackPackedMomentReadoutStorage
