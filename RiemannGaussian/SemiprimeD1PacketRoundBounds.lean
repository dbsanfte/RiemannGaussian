/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketRoundBits

/-! # Acquired packet rounding widths and reports
All output sizes and costs follow actual source words. The numeric padding
inequality later consumes the derived original load cap, not an encoded answer.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1PacketRoundBounds
open SemiprimeBitArithmetic SemiprimeD1PacketRoundBits

/-- One physical increment has the structural width bound, including empty zero. -/
theorem increment_shape (bits : List Bool) (W : ℕ) (hw : bits.length≤W) :
    (SemiprimeSourceCompactBits.increment bits).bits.length≤W+2 := by
  have ht := SemiprimeSourceCompactBits.trim_length (addBits bits [true] false).bits
  have ha := (addBits_counts bits [true] false).2.2.2.2
  have hm : max bits.length [true].length≤W+1 := by simp;omega
  change (SemiprimeSourceCompactBits.trim (addBits bits [true] false).bits).bits.length≤W+2
  omega

/-- The acquired padded word is short even though its numerical value may be large. -/
theorem round_length (a : ℕ) (bits : List Bool) (W : ℕ) (hw : bits.length≤W) :
    (round a bits).bits.length≤a+W+2 := by
  have hh : (cut a bits).high.length≤W := (cut_length a bits).trans hw
  have high :
      (if (cut a bits).low then SemiprimeSourceCompactBits.increment (cut a bits).high
        else (⟨(cut a bits).high,0⟩ : SemiprimeSourceCompactBits.Report)).bits.length≤W+2 := by
    split_ifs
    · exact increment_shape _ W hh
    · simpa only using hh.trans (Nat.le_add_right W 2)
  have ht := SemiprimeSourceCompactBits.trim_length
    (List.replicate a false++
      (if (cut a bits).low then SemiprimeSourceCompactBits.increment (cut a bits).high
        else (⟨(cut a bits).high,0⟩ : SemiprimeSourceCompactBits.Report)).bits)
  simp only [List.length_append,List.length_replicate] at ht
  change _≤_ at ht
  exact ht.trans (by omega)

/-- The exact scan/increment/zero-prefix/trim path has a linear physical report. -/
theorem round_clock (a : ℕ) (bits : List Bool) (W : ℕ) (hw : bits.length≤W) :
    (round a bits).clock≤40*(a+W+3) := by
  let data := cut a bits
  let high : SemiprimeSourceCompactBits.Report :=
    if data.low then SemiprimeSourceCompactBits.increment data.high else ⟨data.high,0⟩
  have hh : data.high.length≤W := (cut_length a bits).trans hw
  have hc : data.clock≤3*W+3 := (cut_clock a bits).trans (by omega)
  have hhigh : high.bits.length≤W+2 := by
    dsimp only [high]
    split_ifs
    · exact increment_shape _ W hh
    · simpa only using hh.trans (Nat.le_add_right W 2)
  have hclock : high.clock≤20*(W+2)+10 := by
    dsimp only [high]
    split_ifs
    · exact SemiprimeSourceCompactBits.increment_clock _ (W+1) (by omega) (by omega)
    · simp
  have ht := SemiprimeSourceCompactBits.trim_clock (List.replicate a false++high.bits)
  simp only [List.length_append,List.length_replicate] at ht
  change data.clock+high.clock+3*a+
    (SemiprimeSourceCompactBits.trim (List.replicate a false++high.bits)).clock+5≤_
  omega

/-- Every emitted padding count is genuinely divisible by the packet size. -/
theorem packet_dvd_round (a : ℕ) (bits : List Bool) : 2^a∣bitValue (round a bits).bits := by
  rw [round_value]
  exact dvd_mul_right _ _

/-- D.3's three-M total padding bound, using actual acquired maximum bits. -/
theorem round_scaled_le (a D M : ℕ) (bits : List Bool)
    (hload : D*bitValue bits≤2*M) (hsize : D*2^a≤M) :
    D*bitValue (round a bits).bits≤3*M := by
  calc
    _ ≤ D*(bitValue bits+2^a) := Nat.mul_le_mul_left D (round_le a bits)
    _ = D*bitValue bits+D*2^a := Nat.mul_add _ _ _
    _ ≤ 2*M+M := Nat.add_le_add hload hsize
    _ = 3*M := by omega

end RiemannGaussian.SemiprimeD1PacketRoundBounds
