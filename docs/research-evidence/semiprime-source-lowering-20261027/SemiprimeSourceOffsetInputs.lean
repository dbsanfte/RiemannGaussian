/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceOffsetInputsScales

/-! # Acquired original offset register bank
All seven words are constructed. Natural dimensions are control inputs; their
representation on an external tape is not asserted by this scalar/cell report.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceOffsetInputs
open SemiprimeRationalBits SemiprimeSourceOffsetInputsCore
open SemiprimeSourceProgramBits SemiprimeSourceOffsetInputsScales

/-- Complete initializer result and its retained work. -/
structure InputRun where
  /-- Acquired seven physical registers. -/
  memory : List RationalWord
  /-- Target width of the existing twelve-operation offset block. -/
  width : ℕ
  /-- All executed initializer stages, scans, and templates. -/
  clock : ℕ

/-- Input words are materialized once, including their reports. -/
def dimensions (M n r Q lam U : ℕ) : List RationalReport :=
  [encodeNat M,encodeNat n,encodeNat r,encodeNat Q,encodeNat lam,encodeNat U]

/-- The final physical read and addition by zero normalizes to the offset width. -/
def normalize (W : ℕ) (memory : List RationalWord) (i : ℕ) : RationalReport :=
  let input := SemiprimeSourceMemoryBits.readWord memory (addr i)
  let out := executeOperation .add input.word zeroWord (List.replicate W false)
  ⟨out.word,input.clock+out.clock+W+2⟩

/-- No scales or bank are supplied: U is built by actual repeated cell replication. -/
def acquire (M n r Q lam : ℕ) : InputRun :=
  let bank := unaryPower r (2*Q)
  let U := bank.cells.length
  let d := r*lam*U*(2*r)
  let B := M*(2*r)+n*(r*lam)*U
  let W := SemiprimeSourceOffsetHeight.height d B M n r Q U+1
  let V := workingWidth M n r Q lam U W
  let inputs := dimensions M n r Q lam U
  let state := run (List.replicate V false) code (inputs.map RationalReport.word)
  let outputs := selection.map (normalize W state.memory)
  ⟨outputs.map RationalReport.word,W,
   bank.clock+U+1+(inputs.map RationalReport.clock).sum+state.clock+
    (outputs.map RationalReport.clock).sum+V+W+1000⟩

/-- The cached natural reports are correct and legal. -/
theorem dimensions_spec (M n r Q lam U : ℕ) :
    (dimensions M n r Q lam U).map (fun x => x.word.value)=inputValues M n r Q lam U ∧
    ∀ x∈dimensions M n r Q lam U,x.word.Valid := by
  have hM := encodeNat_spec M
  have hn := encodeNat_spec n
  have hr := encodeNat_spec r
  have hQ := encodeNat_spec Q
  have hl := encodeNat_spec lam
  have hU := encodeNat_spec U
  constructor
  · simp only [dimensions,List.map_cons,List.map_nil,inputValues,hM.1,hn.1,hr.1,hQ.1,hl.1,hU.1]
  · intro x hx
    simp only [dimensions,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
    · exact hM.2.1
    · exact hn.2.1
    · exact hr.2.1
    · exact hQ.2.1
    · exact hl.2.1
    · exact hU.2.1

/-- Exact seven-register acquisition. The physical normalization fits are all
proved from the original dimensions and the original scale representations. -/
theorem acquire_spec (M n r Q lam : ℕ) (hr : 0<r) (hlam : 0<lam) :
    let U := r^(2*Q)
    let d := r*lam*U*(2*r)
    let B := M*(2*r)+n*(r*lam)*U
    let x := (1/((r*lam:ℕ):ℚ))*(M:ℚ)/(U:ℚ)
    let y := (n:ℚ)/(2*(r:ℚ))
    let result := acquire M n r Q lam
    result.width=SemiprimeSourceOffsetProgramBits.width d B M n r Q ∧
    result.memory.map RationalWord.value=SemiprimeSourceOffsetProgramBits.initialValues M n r Q U x y ∧
    (∀ w∈result.memory,w.Valid) ∧
    (∀ w∈result.memory,Width w result.width) ∧ result.memory.length=7 := by
  let U := r^(2*Q)
  let d := r*lam*U*(2*r)
  let B := M*(2*r)+n*(r*lam)*U
  let x := (1/((r*lam:ℕ):ℚ))*(M:ℚ)/(U:ℚ)
  let y := (n:ℚ)/(2*(r:ℚ))
  let W := SemiprimeSourceOffsetHeight.height d B M n r Q U+1
  let V := workingWidth M n r Q lam U W
  let inputs := dimensions M n r Q lam U
  let state := run (List.replicate V false) code (inputs.map RationalReport.word)
  have hU : 0<U := pow_pos hr _
  have hd : 0<d := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hr hlam) hU) (Nat.mul_pos (by decide) hr)
  have hi := dimensions_spec M n r Q lam U
  have hv : ∀ w∈inputs.map RationalReport.word,w.Valid := by
    intro w hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    exact hi.2 a ha
  have hm : (inputs.map RationalReport.word).map RationalWord.value=inputValues M n r Q lam U := by
    simpa only [inputs,List.map_map,Function.comp_def] using hi.1
  have hs := run_correct (List.replicate V false) code (inputs.map RationalReport.word) hv (by
    rw [hm,List.length_replicate]
    exact code_safe M n r Q lam U W hr hlam hU)
  have hselected : selection.map (fun i => ((state.memory.map RationalWord.value)[i]?).getD 0)=
      SemiprimeSourceOffsetProgramBits.initialValues M n r Q U x y := by
    rw [show state.memory.map RationalWord.value=evaluate code (inputValues M n r Q lam U) from hs.1.trans (congrArg (evaluate code) hm)]
    exact evaluate_values M n r Q lam U
  have hsc := SemiprimeSourceScorePrefixHeight.scheduled_scale_representations M n r lam U hr hlam hU
  have hc := SemiprimeSourceOffsetHeight.scratch_bound d B M n r Q U x y hd hr hU hsc.1 hsc.2
  have hnorm (i : ℕ) (hi : i∈selection) :
      (normalize W state.memory i).word.value=((state.memory.map RationalWord.value)[i]?).getD 0 ∧
      (normalize W state.memory i).word.Valid ∧ Width (normalize W state.memory i).word W := by
    have ha : SemiprimeBitArithmetic.bitValue (addr i)=i := by
      simp only [selection,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    let q := ((state.memory.map RationalWord.value)[i]?).getD 0
    have hq : q∈SemiprimeSourceOffsetHeight.scratch M n r Q U x y := by
      have hmem : q∈selection.map (fun i => ((state.memory.map RationalWord.value)[i]?).getD 0) := List.mem_map.mpr ⟨i,hi,rfl⟩
      rw [hselected] at hmem
      simp only [SemiprimeSourceOffsetProgramBits.initialValues,List.mem_cons,List.not_mem_nil,or_false] at hmem
      simp only [SemiprimeSourceOffsetHeight.scratch,List.mem_cons,List.not_mem_nil,or_false]
      tauto
    have hcap := hc q hq
    have hf : Fits q W := SemiprimeSourceOffsetProgramBits.fits_of_cap q _ hcap.1 hcap.2
    have hin := SemiprimeSourceMemoryBits.readWord_valid state.memory (addr i) hs.2
    have hout := executeOperation_correct .add (SemiprimeSourceMemoryBits.readWord state.memory (addr i)).word
      zeroWord (List.replicate W false) hin SemiprimeDotBits.zeroWord_valid (by
        simpa only [Operation.value,SemiprimeDotBits.zeroWord_value,add_zero,List.length_replicate,
          readWord_value,ha] using hf)
    simpa only [normalize,Operation.value,SemiprimeDotBits.zeroWord_value,add_zero,
      List.length_replicate,readWord_value,ha] using hout
  simp only [acquire,unaryPower_length]
  change W=_ ∧ ((selection.map (normalize W state.memory)).map RationalReport.word).map RationalWord.value=_ ∧ _
  refine ⟨rfl,?_,?_,?_,?_⟩
  · simp only [List.map_map,Function.comp_def]
    rw [List.map_congr_left (fun i hi => (hnorm i hi).1)]
    exact hselected
  · intro w hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    exact (hnorm i hi).2.1
  · intro w hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    exact (hnorm i hi).2.2
  · simp only [List.length_map,selection,List.length_cons,List.length_nil]

/-- Actual initial acquisition followed by the existing twelve physical operations. -/
def runOffset (M n r Q lam : ℕ) : SemiprimeSourceProgramBits.Report :=
  let initial := acquire M n r Q lam
  let result := run (List.replicate initial.width false)
    SemiprimeSourceOffsetProgramBits.code initial.memory
  ⟨result.memory,initial.clock+result.clock+initial.width+4⟩

/-- End-to-end ORIGINAL-dimension execution, with no initial encoded-register premise. -/
theorem runOffset_correct (M n r Q lam : ℕ) (hr : 0<r) (hlam : 0<lam) :
    let U := r^(2*Q)
    let x := (1/((r*lam:ℕ):ℚ))*(M:ℚ)/(U:ℚ)
    let y := (n:ℚ)/(2*(r:ℚ))
    let result := runOffset M n r Q lam
    (result.memory.headD zeroWord).value=(SemiprimeMaterializedSourceWords.offsetRun M n r Q x y).value ∧
    (∀ w∈result.memory,w.Valid) ∧
    (∀ w∈result.memory,Width w (acquire M n r Q lam).width) ∧ result.memory.length=19 := by
  let U := r^(2*Q)
  have hU : 0<U := pow_pos hr _
  have hs := acquire_spec M n r Q lam hr hlam
  have hrep := SemiprimeSourceScorePrefixHeight.scheduled_scale_representations M n r lam U hr hlam hU
  have hc := SemiprimeSourceOffsetProgramBits.run_offset
    (r*lam*U*(2*r)) (M*(2*r)+n*(r*lam)*U) M n r Q
    ((1/((r*lam:ℕ):ℚ))*(M:ℚ)/(U:ℚ)) ((n:ℚ)/(2*(r:ℚ)))
    (by positivity) hr hrep.1 hrep.2 (acquire M n r Q lam).memory hs.2.2.1 hs.2.1
    (by simpa only [hs.1] using hs.2.2.2.1)
  simpa only [runOffset,hs.1] using ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1⟩

/-- The actual report retains the complete original input acquisition. -/
theorem runOffset_retains_acquisition (M n r Q lam : ℕ) :
    (acquire M n r Q lam).clock≤(runOffset M n r Q lam).clock := by
  simp only [runOffset];omega

end RiemannGaussian.SemiprimeSourceOffsetInputs
