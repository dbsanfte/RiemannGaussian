/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ModeRoutingColours

/-! # One physical source and one physical target per packet tile
The statements refer to actual inverse-read colour bytes and actual slot bits.
Original acquired-packet wrappers discharge the class hypotheses separately.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace RiemannGaussian.SemiprimeD1ModeRoutingWireColours
open SemiprimeD1OrientationBits SemiprimeD1OrientationInverse SemiprimeD1OrientationComplete
open SemiprimeD1ModeRoutingBits SemiprimeD1ModeRoutingColours

/-- A non-source row in a two-colour class necessarily has the tile bit and target colour. -/
theorem crossing_choice (low high : List Bool) (slot tile : Bool)
    (hc : (if slot then high else low)≠(if tile then low else high)) :
    slot=tile ∧ (if slot then high else low)=(if tile then high else low) := by
  cases slot <;> cases tile <;> simp_all

/-- Every inverse-realized column with this tile bit has the acquired source colour. -/
theorem column_source (a : ℕ) (lows highs : List (List Bool)) (high : List Bool)
    (hc : Canonical lows highs) (hl : lows.length=a) (hh : highs.length=a)
    (i : Fin a) (tile : Fin (2^(i.val+1))) (slots : List Bool) (hs : slots.length=a)
    (hb : (slots[i.val]?).getD false=(SemiprimeD1ModeRoutingBits.acquire (packetKey lows highs high) a i tile).bit) :
    ((recover (packetKey lows highs high) slots).right[i.val]?).getD []=
      (SemiprimeD1ModeRoutingBits.acquire (packetKey lows highs high) a i tile).source := by
  have hr := (recover_colours lows highs high slots hc (hs.trans hl.symm) i.val (by omega)).2
  have hf := acquire_fields a lows highs high hl hh i tile
  have hsource := (acquire_colours (packetKey lows highs high) a i tile).1
  rw [hf.1,hf.2] at hsource
  rw [hr,hb,hsource]

/-- Every crossing inverse-realized row has the unique acquired target colour and
exactly the same chosen slot bit as the column tile. -/
theorem row_target (a : ℕ) (lows highs : List (List Bool)) (high : List Bool)
    (hc : Canonical lows highs) (hl : lows.length=a) (hh : highs.length=a)
    (i : Fin a) (tile : Fin (2^(i.val+1))) (slots : List Bool) (hs : slots.length=a)
    (hcross : ((recover (packetKey lows highs high) slots).left[i.val]?).getD []≠
      (SemiprimeD1ModeRoutingBits.acquire (packetKey lows highs high) a i tile).source) :
    (slots[i.val]?).getD false=(SemiprimeD1ModeRoutingBits.acquire (packetKey lows highs high) a i tile).bit ∧
    ((recover (packetKey lows highs high) slots).left[i.val]?).getD []=
      (SemiprimeD1ModeRoutingBits.acquire (packetKey lows highs high) a i tile).target := by
  have hr := (recover_colours lows highs high slots hc (hs.trans hl.symm) i.val (by omega)).1
  have hf := acquire_fields a lows highs high hl hh i tile
  have hsource := (acquire_colours (packetKey lows highs high) a i tile).1
  have htarget := (acquire_colours (packetKey lows highs high) a i tile).2
  rw [hf.1,hf.2] at hsource htarget
  rw [hr,hsource] at hcross
  have hp := crossing_choice _ _ _ _ hcross
  refine ⟨hp.1,?_⟩
  rw [hr,htarget]
  exact hp.2

/-- Equal physical class fields are entirely local; a crossing mode may be zero. -/
theorem equal_class_local (a : ℕ) (lows highs : List (List Bool)) (high : List Bool)
    (hc : Canonical lows highs) (hl : lows.length=a) (hh : highs.length=a)
    (i : Fin a) (tile : Fin (2^(i.val+1))) (slots : List Bool) (hs : slots.length=a)
    (heq : (lows[i.val]?).getD []=(highs[i.val]?).getD []) :
    ((recover (packetKey lows highs high) slots).left[i.val]?).getD []=
      (SemiprimeD1ModeRoutingBits.acquire (packetKey lows highs high) a i tile).source ∧
    ((recover (packetKey lows highs high) slots).right[i.val]?).getD []=
      (SemiprimeD1ModeRoutingBits.acquire (packetKey lows highs high) a i tile).source := by
  have hr := recover_colours lows highs high slots hc (hs.trans hl.symm) i.val (by omega)
  have hf := acquire_fields a lows highs high hl hh i tile
  have hsource := (acquire_colours (packetKey lows highs high) a i tile).1
  rw [hf.1,hf.2] at hsource
  rw [hr.1,hr.2,hsource,heq]
  simp only [ite_self,and_self]

end RiemannGaussian.SemiprimeD1ModeRoutingWireColours
