/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildPortBijection
import RiemannGaussian.SemiprimeD1OrientationInverseBounds

/-! # Physical source/target acquisition from an actual packet key and tile
Only acquired packet bytes and a finite tile ordinal execute. No semantic word,
colour getter, source/target ownership function, or coefficient oracle is input.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace RiemannGaussian.SemiprimeD1ModeRoutingBits
open SemiprimeMaterializedWords SemiprimeBitArithmetic
open SemiprimeSourceCompactBits (Report)

/-- Acquire the literal all-zero orientation slot, paying its list constructors. -/
def zeros : ℕ→Report
  | 0 => ⟨[],2⟩
  | a+1 => let tail := zeros a; ⟨false::tail.bits,tail.clock+4⟩

/-- No semantic slot or padding answer supplies the zero-slot acquisition. -/
theorem zeros_bits (a : ℕ) : (zeros a).bits=List.replicate a false := by
  induction a with
  | zero => rfl
  | succ a ih => simp only [zeros,ih,List.replicate_succ]

/-- Every acquired zero-slot cell remains in the actual report. -/
theorem zeros_clock (a : ℕ) : (zeros a).clock=4*a+2 := by
  induction a with
  | zero => rfl
  | succ a ih => simp only [zeros,ih];omega

/-- Read one physical tile/slot bit with high zero padding and paid visited cells. -/
def readBit : List Bool→ℕ→Run Bool
  | [],_ => ⟨false,2⟩
  | b::_,0 => ⟨b,2⟩
  | _::bs,i+1 => let tail := readBit bs i; ⟨tail.value,tail.work+4⟩

/-- Exact physical bit getter, not a native colour/slot oracle. -/
theorem readBit_value (bits : List Bool) (i : ℕ) : (readBit bits i).value=(bits[i]?).getD false := by
  induction bits generalizing i with
  | nil => rfl
  | cons b bs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

/-- Every actual bit visit and finite index decrement is retained. -/
theorem readBit_work (bits : List Bool) (i : ℕ) : (readBit bits i).work≤4*i+2 := by
  induction bits generalizing i with
  | nil => simp [readBit]
  | cons b bs ih => cases i with
    | zero => simp [readBit]
    | succ i => have hh := ih i; simp only [readBit];omega

/-- Actually recovered class fields and one tile's acquired group colours. -/
structure Route where
  /-- The physical inverse's zero-slot row/column fields and parse flags. -/
  classes : SemiprimeD1OrientationInverse.Decoded
  /-- Read lower class colour at the chosen coordinate. -/
  low : List Bool
  /-- Read upper class colour at the chosen coordinate. -/
  high : List Bool
  /-- Actual compact encoding of the original tile ordinal. -/
  tile : List Bool
  /-- Actual physical ith tile bit. -/
  bit : Bool
  /-- Copied source colour: low for true tile bit, high for false. -/
  source : List Bool
  /-- Copied other target colour. -/
  target : List Bool
  /-- Acquired physical class-equality flag; equal classes have no crossing row. -/
  localClass : Bool
  /-- Actual class parser/order validity flag. -/
  valid : Bool
  /-- Every zero-slot, inverse, coordinate, tile, compare, copy and control report. -/
  clock : ℕ

/-- Acquire routing from bytes, with coordinate range enforced by Fin a. -/
def acquire (key : List Bool) (a : ℕ) (i : Fin a) (tile : Fin (2^(i.val+1))) : Route :=
  let slot := zeros a
  let classes := SemiprimeD1OrientationInverse.recover key slot.bits
  let low := SemiprimeD1ChildGraph.readCoordinate classes.left i.val
  let high := SemiprimeD1ChildGraph.readCoordinate classes.right i.val
  let tileBits := SemiprimeSourceHistogramPortKeys.encodeKey tile.val
  let bit := readBit tileBits.bits i.val
  let order := SemiprimeBitIndexClipping.leSignedBits ⟨false,low.bits⟩ ⟨false,high.bits⟩
  let source := SemiprimeSourceCompactBits.copy (if bit.value then low.bits else high.bits)
  let target := SemiprimeSourceCompactBits.copy (if bit.value then high.bits else low.bits)
  ⟨classes,low.bits,high.bits,tileBits.bits,bit.value,source.bits,target.bits,
    SemiprimeD1OrientationBits.equality order,classes.valid,
    slot.clock+classes.clock+low.clock+high.clock+tileBits.clock+bit.work+order.clock+
      source.clock+target.clock+20⟩

/-- Exact acquired source/target rule, with no supplied ownership function. -/
theorem acquire_colours (key : List Bool) (a : ℕ) (i : Fin a) (tile : Fin (2^(i.val+1))) :
    (acquire key a i tile).source=(if (acquire key a i tile).bit then
      (acquire key a i tile).low else (acquire key a i tile).high) ∧
    (acquire key a i tile).target=(if (acquire key a i tile).bit then
      (acquire key a i tile).high else (acquire key a i tile).low) := by
  simp only [acquire,SemiprimeSourceCompactBits.copy_bits]
  simp

/-- Zero-slot inverse is the sole acquired unordered-class source. -/
theorem acquire_classes (key : List Bool) (a : ℕ) (i : Fin a) (tile : Fin (2^(i.val+1))) :
    (acquire key a i tile).classes=
      SemiprimeD1OrientationInverse.recover key (List.replicate a false) := by
  simp only [acquire,zeros_bits]

/-- Query an actual observed packet without reacquiring its source or selector. -/
def fromReplay {n F a : ℕ} {inputArity : Fin F→ℕ}
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a inputArity)
    (packet : Fin source.state.packets.length) (i : Fin a) (tile : Fin (2^(i.val+1))) : Route :=
  let key := SemiprimeSourceCompactBits.copy source.state.packets[packet.val]
  let out := acquire key.bits a i tile
  {out with clock := source.state.clock+key.clock+out.clock+packet.val+6}

/-- The route's input packet is literally the retained observed packet key. -/
theorem fromReplay_data {n F a : ℕ} {inputArity : Fin F→ℕ}
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a inputArity)
    (packet : Fin source.state.packets.length) (i : Fin a) (tile : Fin (2^(i.val+1))) :
    (fromReplay source packet i tile).source=(acquire source.state.packets[packet.val] a i tile).source ∧
    (fromReplay source packet i tile).target=(acquire source.state.packets[packet.val] a i tile).target := by
  simp only [fromReplay,SemiprimeSourceCompactBits.copy_bits]
  simp

end RiemannGaussian.SemiprimeD1ModeRoutingBits
