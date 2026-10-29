/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OrientationInverse

/-! # Actual physical inverse parser/copy report bounds
All widths are derived from the original key and slot lengths. No intermediate
Fits, inverse answer, semantic colour or externally chosen width controls execution.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1OrientationInverseBounds
open SemiprimeD1OrientationBits SemiprimeD1OrientationInverse
open SemiprimeBitIndexClipping SemiprimeSourceHistogramKeyBits

/-- Every actual parser output is an input slice/copy and every inspected cell is paid. -/
theorem split_metrics : (key : List Bool) →
    (split key).first.length≤key.length ∧ (split key).rest.length≤key.length ∧
      (split key).clock≤6*key.length+3
  | [] => by simp [split]
  | false::ys => by simp [split]
  | true::[] => by simp [split]
  | true::b::bs => by
    obtain ⟨hf,hr,hc⟩ := split_metrics bs
    simp only [split,List.length_cons]
    omega

/-- Every inverse padding temporary has only original high bits plus slot bits. -/
theorem index_length (key slots : List Bool) :
    (recover key slots).index.length≤key.length+slots.length := by
  induction slots generalizing key with
  | nil => simp [recover,SemiprimeSourceCompactBits.copy_bits]
  | cons bit slots ih =>
    let field := split key
    let colours := split field.first
    let tail := recover field.rest slots
    have hf : field.rest.length≤key.length := (split_metrics key).2.1
    have ht : tail.index.length≤field.rest.length+slots.length := ih field.rest
    have htrim := SemiprimeSourceCompactBits.trim_length (bit::tail.index)
    change (if equality (leSignedBits ⟨false,colours.first⟩ ⟨false,colours.rest⟩)
      then SemiprimeSourceCompactBits.trim (bit::tail.index)
      else SemiprimeSourceCompactBits.copy tail.index).bits.length≤_
    simp only [List.length_cons]
    split_ifs
    · simp only [List.length_cons] at htrim
      omega
    · rw [SemiprimeSourceCompactBits.copy_bits]
      omega

/-- Full inverse report bound from actual original key/slot lengths, valid or malformed.
The statement includes all recursive parses, borrows, zero scans, copies and trims;
it does not claim a complete external address/tape machine simulation. -/
theorem recover_clock (key slots : List Bool) :
    (recover key slots).clock≤200*(slots.length+1)*(key.length+slots.length+1) := by
  induction slots generalizing key with
  | nil => simp only [recover,SemiprimeSourceCompactBits.copy_clock,List.length_nil];omega
  | cons bit slots ih =>
    let field := split key
    let colours := split field.first
    let tail := recover field.rest slots
    let order := leSignedBits ⟨false,colours.first⟩ ⟨false,colours.rest⟩
    let eq := equality order
    have hf := split_metrics key
    have hc := split_metrics field.first
    have hcl : colours.first.length≤key.length := hc.1.trans hf.1
    have hcr : colours.rest.length≤key.length := hc.2.1.trans hf.1
    have ho : order.clock≤40*(key.length+1) := leSignedBits_cost hcl hcr
    have ht : tail.clock≤200*(slots.length+1)*(key.length+slots.length+1) :=
      (ih field.rest).trans (by gcongr;exact hf.2.1)
    have hj : tail.index.length≤key.length+slots.length :=
      (index_length field.rest slots).trans (Nat.add_le_add_right hf.2.1 _)
    have hleft : (if eq then colours.first else if bit then colours.rest else colours.first).length≤key.length := by
      split_ifs <;> assumption
    have hright : (if eq then colours.rest else if bit then colours.first else colours.rest).length≤key.length := by
      split_ifs <;> assumption
    have hi : (if eq then SemiprimeSourceCompactBits.trim (bit::tail.index)
        else SemiprimeSourceCompactBits.copy tail.index).clock≤6*(key.length+slots.length+1)+1 := by
      split_ifs <;> simp only [SemiprimeSourceCompactBits.trim_clock,
        SemiprimeSourceCompactBits.copy_clock,List.length_cons] <;> omega
    change field.clock+colours.clock+tail.clock+order.clock+
      (SemiprimeSourceCompactBits.copy (if eq then colours.first else if bit then colours.rest else colours.first)).clock+
      (SemiprimeSourceCompactBits.copy (if eq then colours.rest else if bit then colours.first else colours.rest)).clock+
      (if eq then SemiprimeSourceCompactBits.trim (bit::tail.index)
        else SemiprimeSourceCompactBits.copy tail.index).clock+30≤_
    rw [SemiprimeSourceCompactBits.copy_clock,SemiprimeSourceCompactBits.copy_clock]
    simp only [List.length_cons]
    nlinarith

end RiemannGaussian.SemiprimeD1OrientationInverseBounds
