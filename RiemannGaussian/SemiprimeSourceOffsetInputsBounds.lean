/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceOffsetInputs

/-! # Original-resource clock of the acquired physical offset inputs -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceOffsetInputsBounds
open SemiprimeRationalBits SemiprimeSourceOffsetInputsCore SemiprimeSourceOffsetInputs
open SemiprimeSourceProgramBits SemiprimeSourceOffsetInputsScales

/-- A fixed-size literal address is actually stored for each scan. -/
theorem addr_length (i : ℕ) : (addr i).length=4 := by
  unfold addr
  split <;> rfl

/-- Numeric bound for an actually traversed list, without any cached-answer premise. -/
theorem sum_map_le (xs : List ℕ) (f : ℕ→ℕ) (B : ℕ)
    (h : ∀ x∈xs,f x≤ B) : (xs.map f).sum≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simpa only [Nat.add_mul,Nat.one_mul,Nat.add_comm] using Nat.add_le_add hx ht

/-- Paid read and physical normalization clock, including its actual template. -/
theorem normalize_clock (W V : ℕ) (memory : List RationalWord) (i : ℕ)
    (hV : 1≤ V) (hWV : W≤ V) (hm : memory.length=14)
    (hw : ∀ w∈memory,Width w V) :
    (SemiprimeSourceOffsetInputs.normalize W memory i).clock≤15*(8*V+90)+20000*(V+1)^3+W+2 := by
  have hr := SemiprimeSourceMemoryBits.readWord_clock memory (addr i) V 4 (by decide)
    (by rw [addr_length]) hw
  have hin := SemiprimeSourceMemoryBits.readWord_width memory (addr i) V hV hw
  have hz : Width zeroWord V := by
    simp only [Width,zeroWord,List.length_nil,List.length_cons];omega
  have ho := executeOperation_cost .add (SemiprimeSourceMemoryBits.readWord memory (addr i)).word
    zeroWord (List.replicate W false) hin hz (by simpa only [List.length_replicate] using hWV)
  rw [hm] at hr
  simp only [SemiprimeSourceOffsetInputs.normalize]
  omega

/-- The budget has only original dimensions, the actual U bank, and their
constructor-derived widths; no execution-result magnitude occurs in it. -/
def inputBudget (M n r Q lam U W V : ℕ) : ℕ :=
  2+2*Q*(r*(3*U+3)+U+5)+U+1+
  6*(20*(parameterSum M n r Q lam U+1)^2+4)+
  (8*(stepBudget 14 V 4+3)+1)+
  7*(15*(8*V+90)+20000*(V+1)^3+W+2)+V+W+1000

/-- Pure scalar composition, isolated from executable report projections. -/
theorem combine_clock (bank U encoded stage copied V W bankBound encodedBound stageBound copiedBound : ℕ)
    (hbank : bank≤ bankBound) (hencoded : encoded≤ encodedBound)
    (hstage : stage≤ stageBound) (hcopied : copied≤ copiedBound) :
    bank+U+1+encoded+stage+copied+V+W+1000≤
      bankBound+U+1+encodedBound+stageBound+copiedBound+V+W+1000 := by omega

/-- Full initial-bank clock with all six encoders, eight arithmetic instructions,
seven scans/normalizations, the U construction and template allocation retained. -/
theorem acquire_clock (M n r Q lam : ℕ) (hr : 0< r) :
    let U := r^(2*Q)
    let W := SemiprimeSourceOffsetHeight.height (r*lam*U*(2*r))
      (M*(2*r)+n*(r*lam)*U) M n r Q U+1
    let V := workingWidth M n r Q lam U W
    (acquire M n r Q lam).clock≤ inputBudget M n r Q lam U W V := by
  let U := r^(2*Q)
  let W := SemiprimeSourceOffsetHeight.height (r*lam*U*(2*r))
    (M*(2*r)+n*(r*lam)*U) M n r Q U+1
  let V := workingWidth M n r Q lam U W
  let P := parameterSum M n r Q lam U
  let inputs := dimensions M n r Q lam U
  let state := run (List.replicate V false) code (inputs.map RationalReport.word)
  have hP : 1≤ P := by dsimp [P,parameterSum];omega
  have hPV : P+1≤ V := by dsimp [V,workingWidth];change P+1≤ W+P^2+P+3;omega
  have hV : 1≤ V := by omega
  have hw (c : ℕ) (hc : c≤ P) : Width (encodeNat c).word V := by
    have hh := (encodeNat_spec c).2.2
    exact ⟨hh.1.trans (by omega),hh.2.trans (by omega)⟩
  have hcaps : M≤ P ∧ n≤ P ∧ r≤ P ∧ Q≤ P ∧ lam≤ P ∧ U≤ P := by
    dsimp [P,parameterSum];omega
  have hm : ∀ w∈inputs.map RationalReport.word,Width w V := by
    intro w h
    simp only [inputs,dimensions,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl
    · exact hw M hcaps.1
    · exact hw n hcaps.2.1
    · exact hw r hcaps.2.2.1
    · exact hw Q hcaps.2.2.2.1
    · exact hw lam hcaps.2.2.2.2.1
    · exact hw U hcaps.2.2.2.2.2
  have hin : (inputs.map RationalReport.clock).sum≤6*(20*(P+1)^2+4) := by
    have hc (c : ℕ) (hh : c≤ P) : (encodeNat c).clock≤20*(P+1)^2+4 := by
      apply (encodeNat_clock c).trans
      gcongr
    have h1 := hc M hcaps.1
    have h2 := hc n hcaps.2.1
    have h3 := hc r hcaps.2.2.1
    have h4 := hc Q hcaps.2.2.2.1
    have h5 := hc lam hcaps.2.2.2.2.1
    have h6 := hc U hcaps.2.2.2.2.2
    simp only [inputs,dimensions,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    omega
  have hcode : ∀ i∈code,i.left.length≤4 ∧ i.right.length≤4 := by
    intro i hi
    simp only [code,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [addr_length,le_refl,and_self]
  have hrun := run_clock (List.replicate V false) code (inputs.map RationalReport.word) 4
    (by simpa only [List.length_replicate] using hV) (by decide) hcode
    (by simpa only [List.length_replicate] using hm)
  have hstate : state.memory.length=14 := by
    rw [run_length]
    simp only [inputs,dimensions,List.length_map,code,List.length_cons,List.length_nil]
  have hstateW : ∀ w∈state.memory,Width w V := by
    simpa only [List.length_replicate] using run_width (List.replicate V false) code
      (inputs.map RationalReport.word) (by simpa only [List.length_replicate] using hm)
  have hn := sum_map_le selection (fun i => (SemiprimeSourceOffsetInputs.normalize W state.memory i).clock)
    (15*(8*V+90)+20000*(V+1)^3+W+2) (fun i _ => normalize_clock W V state.memory i
      hV (by dsimp [V,workingWidth];omega) hstate hstateW)
  have hp := unaryPower_clock r Q hr (2*Q) (by rfl)
  have hcl : code.length=8 := rfl
  have hil : (inputs.map RationalReport.word).length=6 := rfl
  rw [List.length_replicate,hcl,hil,show 6+8=14 from rfl] at hrun
  rw [show selection.length=7 from rfl] at hn
  simp only [acquire,unaryPower_length,List.map_map,Function.comp_def,inputBudget]
  exact combine_clock _ _ _ _ _ _ _ _ _ _ _ hp hin hrun hn

/-- Original-resource majorant of the initializer's working width. -/
def workingEnvelope (S : ℕ) : ℕ :=
  workingWidth S S S S S S (SemiprimeSourceOffsetProgramBudget.widthEnvelope S)

/-- Fixed original-resource initializer envelope; U is an actual materialized
resource, not a binary-length assertion about an arbitrary exponent. -/
def inputEnvelope (S : ℕ) : ℕ := inputBudget S S S S S S
  (SemiprimeSourceOffsetProgramBudget.widthEnvelope S) (workingEnvelope S)

/-- Initializer plus the existing actual twelve-operation clock. -/
def totalEnvelope (S : ℕ) : ℕ := inputEnvelope S+
  SemiprimeSourceOffsetProgramBudget.clockEnvelope S+
  SemiprimeSourceOffsetProgramBudget.widthEnvelope S+4

/-- Every original dimension and the actual bank are charged in a single resource cap. -/
theorem acquire_clock_original (M n r Q lam S : ℕ) (hr : 0< r)
    (hM : M≤ S) (hn : n≤ S) (hrS : r≤ S) (hQ : Q≤ S) (hlam : lam≤ S)
    (hU : r^(2*Q)≤ S) : (acquire M n r Q lam).clock≤ inputEnvelope S := by
  have hc := acquire_clock M n r Q lam hr
  have hw := SemiprimeSourceOffsetProgramBudget.scheduled_width_le M n r Q lam S hM hn hrS hQ hlam hU
  have hv : workingWidth M n r Q lam (r^(2*Q))
      (SemiprimeSourceOffsetProgramBits.width (r*lam*r^(2*Q)*(2*r))
        (M*(2*r)+n*(r*lam)*r^(2*Q)) M n r Q)≤ workingEnvelope S := by
    unfold workingEnvelope workingWidth parameterSum
    gcongr
  apply hc.trans
  clear hc
  change inputBudget M n r Q lam (r^(2*Q))
    (SemiprimeSourceOffsetProgramBits.width (r*lam*r^(2*Q)*(2*r))
      (M*(2*r)+n*(r*lam)*r^(2*Q)) M n r Q) _≤ inputEnvelope S
  unfold inputEnvelope inputBudget parameterSum stepBudget
  gcongr <;> assumption

/-- Pure complete-run addition, independent of any executable projection. -/
theorem combine_run (a b w A B W : ℕ) (ha : a≤ A) (hb : b≤ B) (hw : w≤ W) :
    a+b+w+4≤ A+B+W+4 := by omega

/-- All actual work from original dimensions through the final physical offset,
including input encoding and the bank construction. -/
theorem runOffset_clock (M n r Q lam S : ℕ) (hr : 0< r) (hlam : 0< lam)
    (hM : M≤ S) (hn : n≤ S) (hrS : r≤ S) (hQ : Q≤ S) (hlamS : lam≤ S)
    (hU : r^(2*Q)≤ S) : (runOffset M n r Q lam).clock≤ totalEnvelope S := by
  have hs := acquire_spec M n r Q lam hr hlam
  have hi := acquire_clock_original M n r Q lam S hr hM hn hrS hQ hlamS hU
  have hw := SemiprimeSourceOffsetProgramBudget.scheduled_width_le M n r Q lam S hM hn hrS hQ hlamS hU
  have hc := run_clock (List.replicate (acquire M n r Q lam).width false)
    SemiprimeSourceOffsetProgramBits.code (acquire M n r Q lam).memory 4
    (by rw [List.length_replicate,hs.1];unfold SemiprimeSourceOffsetProgramBits.width;omega)
    (by decide) SemiprimeSourceOffsetProgramBits.code_addresses
    (by simpa only [List.length_replicate] using hs.2.2.2.1)
  rw [List.length_replicate,SemiprimeSourceOffsetProgramBits.code_length,hs.2.2.2.2] at hc
  have hwidth : (acquire M n r Q lam).width≤ SemiprimeSourceOffsetProgramBudget.widthEnvelope S := hs.1.trans_le hw
  have hclock : (run (List.replicate (acquire M n r Q lam).width false)
      SemiprimeSourceOffsetProgramBits.code (acquire M n r Q lam).memory).clock≤
      SemiprimeSourceOffsetProgramBudget.clockEnvelope S := by
    apply hc.trans
    clear hc hi hs
    unfold SemiprimeSourceOffsetProgramBudget.clockEnvelope stepBudget
    gcongr
  simpa only [runOffset,totalEnvelope] using combine_run _ _ _ _ _ _ hi hclock hwidth

/-- Uniform fixed polynomial overhead in ORIGINAL materialized resources. -/
theorem totalEnvelope_monomial : ∃ C k : ℕ,∀ S,totalEnvelope S≤ C*(S+1)^k := by
  have hwidth : SemiprimeReportPolynomialGrowth.Bound
      (fun S => SemiprimeSourceOffsetProgramBudget.widthEnvelope S) := by
    simp only [SemiprimeSourceOffsetProgramBudget.widthEnvelope,SemiprimeSourceOffsetHeight.height,
      SemiprimeSourceOffsetProgramBudget.denominatorEnvelope,SemiprimeSourceOffsetProgramBudget.numeratorEnvelope]
    boundArithmetic
  obtain ⟨C,k,hwidth⟩ := hwidth
  obtain ⟨D,l,hclock⟩ := SemiprimeSourceOffsetProgramBudget.clockEnvelope_monomial
  let f := fun S => inputBudget S S S S S S (C*(S+1)^k)
    (workingWidth S S S S S S (C*(S+1)^k))+D*(S+1)^l+C*(S+1)^k+4
  have hf : SemiprimeReportPolynomialGrowth.Bound f := by
    dsimp only [f,inputBudget,workingWidth,parameterSum,stepBudget]
    boundArithmetic
  obtain ⟨E,m,hf⟩ := hf
  refine ⟨E,m,fun S => (show totalEnvelope S≤ f S from ?_).trans (hf S)⟩
  dsimp only [totalEnvelope,inputEnvelope,workingEnvelope,f,inputBudget,stepBudget,workingWidth,parameterSum]
  gcongr <;> first | exact hwidth S | exact hclock S

/-- Actual original-source cardinalities discharge the acquired-bank resource cap. -/
theorem caller_run_clock {I E : Type} {n r Q : ℕ} [NeZero r]
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam S : ℕ)
    (hlam : 0< lam) (hM : en.incidences.values.length≤ S) (hn : n≤ S)
    (hr : r≤ S) (hQ : Q≤ S) (hlamS : lam≤ S) (hU : en.types.values.length≤ S) :
    (runOffset en.incidences.values.length n r Q lam).clock≤ totalEnvelope S := by
  apply runOffset_clock _ _ _ _ _ S (NeZero.pos r) hlam hM hn hr hQ hlamS
  simpa only [SemiprimeSourceOffsetHeight.caller_universal_length] using hU

/-- The actual source caller's original cardinalities, including its exact U,
produce the original offset without any encoded scale or bank input. -/
theorem caller_run_offset {I E : Type} {n r Q : ℕ} [NeZero r]
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam : ℕ) (hlam : 0< lam) :
    ((runOffset en.incidences.values.length n r Q lam).memory.headD zeroWord).value=
    (SemiprimeMaterializedSourceWords.offsetRun en.incidences.values.length n r Q
      ((1/((r*lam:ℕ):ℚ))*(en.incidences.values.length:ℚ)/(en.types.values.length:ℚ))
      ((n:ℚ)/(2*(r:ℚ)))).value := by
  simpa only [SemiprimeSourceOffsetHeight.caller_universal_length] using
    (runOffset_correct en.incidences.values.length n r Q lam (NeZero.pos r) hlam).1

end RiemannGaussian.SemiprimeSourceOffsetInputsBounds
