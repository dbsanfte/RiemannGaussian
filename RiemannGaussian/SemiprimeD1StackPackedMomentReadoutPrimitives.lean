/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedMomentReadoutEncoding
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
/-! # Actual metadata, preserving copies, radix calls, literal index and cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedMomentReadoutPrimitives
open SemiprimeD1StackPackedMomentReadout SemiprimeD1StackPackedMomentReadoutEncoding
open SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Actual trace concatenation preserves every real caller frame and data word. -/
theorem join {m n : ℕ} {pc mid next : Label} {before between after : Stack→List Bool}
    (h : Runs program m pc before mid between) (g : Runs program n mid between next after) :
    Runs program (m+n) pc before next after := runs_trans program m n pc mid next before between after h g
/-- Every actual preserving copy includes all reads, writes, scratch restoration and real return. -/
theorem copy_call (site : Copy) (pc next : Label) (hc : program pc=.call (copyLabel site 0) next)
    (before : Stack→List Bool) (xs ys : List Bool)
    (hx : before (copyStack site 0)=xs) (hy : before (copyStack site 1)=ys) (hs : before (copyStack site 2)=[]) :
    Runs program (5*xs.length+4) pc before next (Function.update before (copyStack site 1) (xs++ys)) := by
  let source:=SemiprimeD1StackCopy.state 0 none xs ys []
  let stop:=SemiprimeD1StackCopy.done xs (xs++ys)
  have hi : Link.DataRel (copyStack site) before source.store before := by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (copyStack site) (copy_injective site) before source.store before hi (1:Fin 3) (xs++ys)
  have he : Function.update source.store 1 (xs++ys)=stop.store := by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (copyStack site) (copyLabel site) (copy_injective site)
    SemiprimeD1StackCopy.code 0 (fun _ => rfl) pc next hc (5*xs.length+3) source stop before _ rfl rfl
    (SemiprimeD1StackCopy.copy_words xs ys none) hi ho
/-- Real width acquisition from binary N preserves the separately acquired scalar verbatim. -/
theorem metadata_call (bits scalar : List Bool) :
    ∃t ≤ SemiprimeD1StackPackedRootMetadataExecution.polynomial bits+1,
      Runs program t (ctl .start) (input bits scalar) (ctl (.copyWidth false)) (ready bits scalar).data := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPackedRootMetadataExecution.source_run_bounded bits
  have hi : Link.DataRel metadata (input bits scalar) (SemiprimeD1StackPackedRootMetadata.initial bits).data (input bits scalar) :=
    ⟨fun _ => rfl,fun _ _ => rfl⟩
  have ho : Link.DataRel metadata (input bits scalar) (SemiprimeD1StackPackedRootMetadataEncoding.done bits).data (ready bits scalar).data := by
    constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k|k
      · exact False.elim (hk k rfl)
      · rfl
      · rfl
  exact ⟨t+1,by omega,SemiprimeD1StackProcedureCallsTrace.included_call program metadata metadataLabel metadata_injective
    M.program (.local .start) (fun _ => rfl) (ctl .start) (ctl (.copyWidth false)) rfl t
    (SemiprimeD1StackPackedRootMetadata.initial bits) (SemiprimeD1StackPackedRootMetadataEncoding.done bits)
    (input bits scalar) (ready bits scalar).data rfl rfl rfl rfl hr hi ho⟩
/-- Exact own radix-call clock, including the actual return to output copying. -/
def digitTime (bits scalar : List Bool) (high : Bool) : ℕ :=
  SemiprimeD1StackRadixDigitExecution.totalTime scalar (width bits) (index high)+1
/-- Whole real radix source consumes its actual value/width/index and clears every helper. -/
theorem digit_call (bits scalar : List Bool) (high : Bool) (u : Aux→List Bool) :
    Runs program (digitTime bits scalar high) (ctl (.acquire high))
      (bank (metadataResult bits) (D.store scalar (width bits) (index high) [] [] []) u)
      (ctl (.copyOutput high)) (bank (metadataResult bits) (D.store [] [] [] [] [] (moment bits scalar high)) u) := by
  let source : C.State D.Stack D.Label := ⟨some .start,none,none,D.store scalar (width bits) (index high) [] [] [],[]⟩
  let stop : C.State D.Stack D.Label := ⟨none,none,none,D.store [] [] [] [] [] (moment bits scalar high),[]⟩
  let before:=bank (metadataResult bits) source.data u
  let after:=bank (metadataResult bits) stop.data u
  have hi : Link.DataRel digit before source.data before := ⟨fun _ => rfl,fun _ _ => rfl⟩
  have ho : Link.DataRel digit before stop.data after := by
    constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k|k
      · rfl
      · exact False.elim (hk k rfl)
      · rfl
  exact SemiprimeD1StackProcedureCallsTrace.included_call program digit digitLabel digit_injective
    D.program .start (fun _ => rfl) (ctl (.acquire high)) (ctl (.copyOutput high)) rfl _
    source stop before after rfl rfl rfl rfl
    (SemiprimeD1StackRadixDigitExecution.source_run scalar (width bits) (index high)) hi ho
/-- The high digit receives one literal TRUE index marker by one actual push. -/
theorem seed_index (before : Stack→List Bool) :
    Runs program 1 (ctl .seedIndex) before (ctl (.acquire true))
      (Function.update before (digit .index) (true::before (digit .index))) :=
  one_base program _ _ _ _ _ rfl rfl rfl
/-- Actual digit-output cleanup erases every produced cell before the next stage. -/
theorem clear_output (bits : List Bool) (u : Aux→List Bool) (out : List Bool) (high : Bool) :
    Runs program (out.length+1) (ctl (.clearOutput high))
      (bank (metadataResult bits) (D.store [] [] [] [] [] out) u)
      (afterClear high) (bank (metadataResult bits) (fun _ => []) u) := by
  let before:=bank (metadataResult bits) (D.store [] [] [] [] [] out) u
  have h:=SemiprimeD1StackPhysicalLoops.drain program (ctl (.clearOutput high)) (afterClear high)
    (digit .output) rfl before out
  have he : Function.update before (digit .output) out=before := Function.update_eq_self _ _
  rw [he] at h
  dsimp only [before] at h
  rw [bank_digit,digit_output,←empty_digit] at h
  exact h
end RiemannGaussian.SemiprimeD1StackPackedMomentReadoutPrimitives
