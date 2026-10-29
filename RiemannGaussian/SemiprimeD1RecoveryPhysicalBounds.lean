/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryPhysicalRun

/-! # Original-input physical recovery cache and arithmetic clocks -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1RecoveryPhysicalBounds
open SemiprimeBitArithmetic SemiprimeRationalBits
open SemiprimeD1RecoveryPhysicalRun SemiprimeD1RecoveryIntegerBits

/-- Original retained source rows carry bounded actual node/coordinate labels. -/
theorem row_labels (a M u : ℕ) (hM : u ≤ M)
    (r : SemiprimeD1RecoveryRowsBits.Row)
    (hr : r ∈ (SemiprimeD1RecoveryRowsBits.acquire a M u).rows) :
    r.node < SemiprimeD1WireKernelOriginal.size a ∧ r.index < 4*M := by
  have hm : SemiprimeD1RecoveryRowsRun.Row.mk r.node r.index
      r.word.numerator.value (bitValue r.word.denominator) ∈
      rowView (SemiprimeD1RecoveryRowsBits.acquire a M u).rows :=
    List.mem_map.mpr ⟨r,hr,rfl⟩
  rw [rowView_original a M u hM,SemiprimeD1RecoveryRowsRun.acquire_rows] at hm
  simp only [SemiprimeD1RecoveryRowsRun.originalRows,List.mem_flatMap] at hm
  obtain ⟨t,ht,hm⟩:=hm
  split_ifs at hm with hs
  · simp at hm
  · obtain ⟨j,hj,hjr⟩:=List.mem_map.mp hm
    have hn:=congrArg SemiprimeD1RecoveryRowsRun.Row.node hjr
    have hi:=congrArg SemiprimeD1RecoveryRowsRun.Row.index hjr
    change t=r.node at hn
    change j=r.index at hi
    have ht':t<SemiprimeD1WireKernelOriginal.size a:=List.mem_range.mp ht
    have hj':j<(SemiprimeD1JetRecoveryWeights.acquire a
      (SemiprimeD1TaperedLoss.height M u) u t).weights.size := List.mem_range.mp hj
    rw [SemiprimeD1JetRecoveryWeights.acquire_weights_size] at hj'
    exact ⟨hn ▸ ht',hi ▸ hj'.trans_le
      (SemiprimeD1WeightPrecision.nodeMultiplicity_le a M u t hM)⟩

/-- A literal cache read bound in its actual shape and address widths. -/
def readBudget (nodes rows P B : ℕ) : ℕ :=
  (nodes+1)*(rows*(4*P+4)+15*B+40)+(rows+1)*(4*P+15*B+30)+4

/-- Actual physical row/child assembly has one paid cache scan per source row. -/
theorem entries_clock (children : List (List (List Bool)))
    (rs : List SemiprimeD1RecoveryRowsBits.Row) (A P B : ℕ)
    (hB : 1 ≤ B)
    (hc : ∀ row ∈ children, row.length ≤ A ∧ ∀ x ∈ row, x.length ≤ P)
    (hr : ∀ r ∈ rs, r.node+1 ≤ B ∧ r.index+1 ≤ B) :
    (entries children rs).clock ≤ rs.length*(readBudget children.length A P B+4)+1 := by
  induction rs with
  | nil => simp [entries]
  | cons r rs ih =>
    have hh:=hr r (by simp)
    have hd:=SemiprimeD1RecoveryChildBits.read_clock children
      (SemiprimeEncodedRowSelection.digits (r.node+1) r.node).bits
      (SemiprimeEncodedRowSelection.digits (r.index+1) r.index).bits A P B hB
      (by simpa only [SemiprimeEncodedRowSelection.digits_length] using hh.1)
      (by simpa only [SemiprimeEncodedRowSelection.digits_length] using hh.2) hc
    have ht:=ih (fun r hr' => hr r (by simp [hr']))
    change _ + (entries children rs).clock + 4 ≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    dsimp only [readBudget] at *
    omega

/-- Physical assembly retains one child operand per actual source row. -/
theorem entries_length (children : List (List (List Bool)))
    (rs : List SemiprimeD1RecoveryRowsBits.Row) :
    (entries children rs).entries.length=rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [entries,List.length_cons,ih]

/-- Original source store widths and literal child precision bound every actual
operand before arithmetic, not merely the requested final answer. -/
theorem entries_width (children : List (List (List Bool)))
    (rs : List SemiprimeD1RecoveryRowsBits.Row) (W P : ℕ)
    (hr : ∀ r ∈ rs, Width r.word W) (hP : P ≤ W)
    (hc : ∀ row ∈ children, ∀ x ∈ row, x.length ≤ P) :
    ∀ e ∈ (entries children rs).entries,
      e.numerator.magnitude.length ≤ W ∧ e.denominator.length ≤ W ∧ e.child.length ≤ W := by
  induction rs with
  | nil => simp [entries]
  | cons r rs ih =>
    intro e he
    simp only [entries,List.mem_cons] at he
    rcases he with he|he
    · subst e
      exact ⟨(hr r (by simp)).1,(hr r (by simp)).2,
        (child_read_length children _ _ P hc).trans hP⟩
    · exact ih (fun r hr' => hr r (by simp [hr'])) e he

/-- A conservative closed original-parameter physical recovery report.
All original producers are counted again whenever this run is repeated. -/
def budget (a M p P : ℕ) : ℕ :=
  let N:=SemiprimeD1WireKernelOriginal.size a
  let m:=4*M
  let W:=width a M P
  let K:=N*m
  SemiprimeD1RecoveryRowsBits.budget a M+
    (K*(readBudget N m P (N+m+1)+4)+1)+
    (K*(40*(W+1)^2+23)+3)+(K*(300*(W+1)^2+100)+3)+
    SemiprimeD1RecoveryStripBits.budget p W+3*W+10

/-- The actual full original physical recovery report is bounded from original
parameters and actual child-cache dimensions. No source/callback/output-height
or Fits answer is admitted. Typed metadata remains separately scoped. -/
theorem run_clock (a M u p P : ℕ) (children : List (List (List Bool)))
    (hM : u ≤ M) (hn : children.length ≤ SemiprimeD1WireKernelOriginal.size a)
    (hc : ∀ row ∈ children, row.length ≤ 4*M ∧ ∀ x ∈ row, x.length ≤ P) :
    (run a M u p P children).clock ≤ budget a M p P := by
  let rows:=SemiprimeD1RecoveryRowsBits.acquire a M u
  let es:=(entries children rows.rows).entries
  let W:=width a M P
  let N:=SemiprimeD1WireKernelOriginal.size a
  let m:=4*M
  let K:=N*m
  let B:=N+m+1
  let template:=List.replicate W false
  have hWpos : 0 < W := by dsimp only [W,width]; omega
  have hP : P ≤ W := by dsimp only [W,width]; omega
  have hw : SemiprimeD1RecoveryNodeBits.width a M ≤ W := by dsimp only [W,width]; omega
  have hg:=SemiprimeD1RecoveryRowsBits.acquire_good a M u hM
  have hes : ∀ e ∈ es, e.numerator.magnitude.length ≤ W ∧
      e.denominator.length ≤ W ∧ e.child.length ≤ W := by
    apply entries_width children rows.rows W P _ hP (fun r hr x hx => (hc r hr).2 x hx)
    intro r hr
    exact ⟨(hg.2 r hr).1.trans hw,(hg.2 r hr).2.trans hw⟩
  have hl : es.length ≤ K := by
    rw [show es.length=rows.rows.length from entries_length _ _]
    exact SemiprimeD1RecoveryRowsBits.acquire_length a M u hM
  have hs:=SemiprimeD1RecoveryRowsBits.acquire_clock a M u hM
  have he:=entries_clock children rows.rows m P B (by dsimp only [B]; omega) hc
    (fun r hr => by
      have hh:=row_labels a M u hM r hr
      dsimp only [B,N,m]
      omega)
  have hread : readBudget children.length m P B ≤ readBudget N m P B := by
    unfold readBudget
    gcongr
  have hrows : rows.rows.length ≤ K := SemiprimeD1RecoveryRowsBits.acquire_length a M u hM
  have he' : (entries children rows.rows).clock ≤ K*(readBudget N m P B+4)+1 := by
    exact he.trans (Nat.add_le_add_right (Nat.mul_le_mul hrows (Nat.add_le_add_right hread 4)) 1)
  have hd:=denominator_clock template es (by simpa only [template,List.length_replicate] using hWpos)
    (fun e he => by simpa only [template,List.length_replicate] using (hes e he).2.1)
  have hdl:=denominator_length template es (by simpa only [template,List.length_replicate] using hWpos)
  have ha:=accumulate_clock template (denominator template es).bits es hdl
    (by simpa only [template,List.length_replicate] using hes)
  have hnl:=accumulate_length template (denominator template es).bits es
  have hf:=SemiprimeD1RecoveryStripBits.finish_clock p W
    (accumulate template (denominator template es).bits es).word
    (denominator template es).bits
    (by simpa only [template,List.length_replicate] using hnl)
    (by simpa only [template,List.length_replicate] using hdl)
  simp only [template,List.length_replicate] at hd ha
  have hd' : (denominator template es).clock ≤ K*(40*(W+1)^2+23)+3 :=
    hd.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) 3)
  have ha' : (accumulate template (denominator template es).bits es).clock ≤
      K*(300*(W+1)^2+100)+3 :=
    ha.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) 3)
  simp only [run,widthRun_value,runAt,budget]
  change rows.clock+(entries children rows.rows).clock+(denominator template es).clock+
    (accumulate template (denominator template es).bits es).clock+
    (SemiprimeD1RecoveryStripBits.finish p
      (accumulate template (denominator template es).bits es).word
      (denominator template es).bits).clock+3*W+10 ≤ _
  change rows.clock ≤ SemiprimeD1RecoveryRowsBits.budget a M at hs
  dsimp only [B,K,N,m,W] at he' hd' ha' hf ⊢
  omega

/-- The original physical replacement always returns compact precision-p data. -/
theorem run_good (a M u p P : ℕ) (children : List (List (List Bool))) :
    (run a M u p P children).bits.length ≤ p ∧
      SemiprimeSourceCompactBits.Compact (run a M u p P children).bits := by
  rw [run_bits]
  exact SemiprimeD1RecoveryStripBits.finish_good _ _ _

/-- The two actual source label-to-address acquisitions per retained row are
explicit native metadata stages; their ledger is not silently dropped. -/
theorem entries_metadataWork (children : List (List (List Bool)))
    (rs : List SemiprimeD1RecoveryRowsBits.Row) (B : ℕ)
    (hr : ∀ r ∈ rs, r.node+1 ≤ B ∧ r.index+1 ≤ B) :
    (entries children rs).metadataWork ≤ rs.length*(8*B+6)+1 := by
  induction rs with
  | nil => simp [entries]
  | cons r rs ih =>
    have hh:=hr r (by simp)
    have ht:=ih (fun r hr' => hr r (by simp [hr']))
    simp only [entries,SemiprimeEncodedRowSelection.digits_work,List.length_cons,
      Nat.add_mul,Nat.one_mul]
    omega

/-- Repeating the recovery for another old coordinate retains the entire
original physical coefficient producer each time. -/
theorem run_retains_source (a M u p P : ℕ) (children : List (List (List Bool))) :
    (SemiprimeD1RecoveryRowsBits.acquire a M u).clock ≤ (run a M u p P children).clock := by
  simp only [run,runAt]
  omega

end RiemannGaussian.SemiprimeD1RecoveryPhysicalBounds
