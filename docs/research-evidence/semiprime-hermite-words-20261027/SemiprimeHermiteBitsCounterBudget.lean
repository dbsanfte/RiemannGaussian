/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeHermiteBitsCounter
import RiemannGaussian.SemiprimeWordPacketCounterBudget

/-! # Actual physical-Hermite counter budget
The original physical node reports are retained without decoding. The new
physical Hermite reconstruction and one FINAL scalar boundary are charged
separately; no old reconstruction report or unit rational clock is substituted.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeHermiteBitsCounterBudget
open scoped BigOperators
open SemiprimeRationalBits SemiprimeJetBits SemiprimeLocalBits
open SemiprimeHermiteBitsCounter
open SemiprimeNodeArrayExecution (RuntimeDesign)
open SemiprimeMaterializedSourceUniversal (Run)
open SemiprimeNativeBitsCounter (nodeWord inputControl inputAt_acquire inputWork_acquire nodeWord_work)
variable {n F : ℕ} {arity : Fin F → ℕ}

/-- Actual node widths fit the sum-derived common physical Hermite width. -/
theorem node_width_le (b Q J R : ℕ) (design : Fin Q → RuntimeDesign n F) (a : Fin Q) :
    SemiprimeWordPacketCounter.nodeWidth b R J arity (design a)≤countWidth b Q J R arity design := by
  have hs : SemiprimeWordPacketCounter.nodeWidth b R J arity (design a)≤
      ∑ t,SemiprimeWordPacketCounter.nodeWidth b R J arity (design t) :=
    Finset.single_le_sum (fun t _ => Nat.zero_le (SemiprimeWordPacketCounter.nodeWidth b R J arity (design t))) (Finset.mem_univ a)
  have hp : SemiprimeWordPacketCounter.nodeWidth b R J arity (design a)≤
      SemiprimeWordPacketHermiteInput.packetBits b R J arity design := by
    unfold SemiprimeWordPacketHermiteInput.packetBits
    omega
  exact hp.trans (SemiprimeHermiteWordWidth.input_width_le _ Q J)

/-- Physical packet words have their acquired storage bound; semantic heights are not needed. -/
theorem node_bounded (b Q J R : ℕ) (design : Fin Q → RuntimeDesign n F) (a : Fin Q)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord) :
    Bounded (SemiprimeWordPacketCounter.node b J R (design a) (nodeWord b a).word source entries).words
      (countWidth b Q J R arity design) := by
  have h := SemiprimeMaterializedWordFibreBounds.node_bounded
    (List.replicate (SemiprimeWordPacketCounter.nodeWidth b R J arity (design a)) false) J (design a)
    (SemiprimeWordPacketCounter.group b J R (design a) (nodeWord b a).word source entries)
  simp only [List.length_replicate] at h
  intro i hi
  exact ⟨(h i hi).1.trans (node_width_le b Q J R design a),
    (h i hi).2.trans (node_width_le b Q J R design a)⟩

/-- The real physical packet size is exactly J, including empty head fibres. -/
theorem node_size (b Q J R : ℕ) (design : Fin Q → RuntimeDesign n F) (a : Fin Q)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord) :
    (SemiprimeWordPacketCounter.node b J R (design a) (nodeWord b a).word source entries).words.size=J :=
  SemiprimeMaterializedWordFibreBounds.node_size
    (List.replicate (SemiprimeWordPacketCounter.nodeWidth b R J arity (design a)) false) J (design a)
    (SemiprimeWordPacketCounter.group b J R (design a) (nodeWord b a).word source entries)

/-- Structural output width pays the single final rational interpretation boundary. -/
theorem reconstruct_decode_work (template : List Bool) (Q J : ℕ)
    (acquire : Fin Q → JetReport) (ht : 0<template.length) :
    SemiprimeNativeGroupBits.decodeWork
      #[(SemiprimeAcquiredHermiteBits.reconstruct template Q J acquire).word]≤
        SemiprimeWordPacketCounterBudget.decodeBudget template.length 1 := by
  have h := SemiprimeAcquiredHermiteBits.reconstruct_width template Q J acquire ht
  have hb : Bounded #[(SemiprimeAcquiredHermiteBits.reconstruct template Q J acquire).word] template.length := by
    intro i hi
    have he : i=0 := by simpa using (show i<1 from hi)
    subst i
    exact h
  simpa [SemiprimeWordPacketCounterBudget.decodeBudget] using
    SemiprimeNativeGroupBitsBudget.decodeWork_bound
      #[(SemiprimeAcquiredHermiteBits.reconstruct template Q J acquire).word] template.length hb

/-- Actual physical packets, physical reconstruction and one final decode. -/
def reductionBudget (b Q J R H M C : ℕ) (arity : Fin F → ℕ)
    (design : Fin Q → RuntimeDesign n F) : ℕ :=
  (∑ a : Fin Q,SemiprimeWordPacketCounterBudget.nodeBudget b J R H M C arity (design a))+
    Q*SemiprimeHermiteNodeBitsBounds.budget (countWidth b Q J R arity design) J Q J+
    Q*(20000*(countWidth b Q J R arity design+1)^3+8*countWidth b Q J R arity design+8)+4+
    SemiprimeWordPacketCounterBudget.decodeBudget (countWidth b Q J R arity design) 1

/-- The complete actual query report, from original word/entry dimensions.
No per-node decode or scalar Hermite clock is inserted in place of the new execution. -/
theorem count_work (b Q J R H M w A E : ℕ) (design : Fin Q → RuntimeDesign n F)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Run (Array RationalWord))
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (hh : ∀ a g,(design a).h g≤H) (hm : ∀ a g,(design a).m g≤M)
    (harity : ∀ e,arity e≤w)
    (hsource : ∀ e i v,Bounded (source e i v).value (SemiprimeNativeGroupBits.groupWidth b R F (∑ e,arity e)))
    (hsize : ∀ e i v,(source e i v).value.size≤A)
    (hentry : ∀ e eta,(entries e eta).clock≤E)
    (hentryWidth : ∀ e eta,(entries e eta).bits.magnitude.length≤
      SemiprimeNativeGroupBits.groupWidth b R F (∑ e,arity e)) :
    (count b Q J R design source entries).work≤
      (∑ e,∑ i,∑ v,(source e i v).work)+Q*(4*(b+1)+4)+
        reductionBudget b Q J R H M
          (SemiprimeNativeBitsCounterBudget.groupBudget n F R J b (∑ e,arity e) w A E) arity design+
        inputControl n F (∑ e,arity e) R b+control b Q J R arity design+10*Q+10 := by
  let template := List.replicate (countWidth b Q J R arity design) false
  let acquire := fun a : Fin Q => SemiprimeWordPacketCounter.node b J R (design a)
    (nodeWord b a).word (fun e i v => (source e i v).value) entries
  have hW : Q+2≤template.length := by
    rw [List.length_replicate]
    exact SemiprimeHermiteWordWidth.node_input_width_le _ Q J
  have hr := SemiprimeAcquiredHermiteBits.reconstruct_clock template Q J acquire J hW
    (fun a => (node_size b Q J R design a _ entries).le)
    (fun a => by
      simpa only [template,List.length_replicate,acquire] using
        node_bounded b Q J R design a (fun e i v => (source e i v).value) entries)
  have hn (a : Fin Q) : (acquire a).clock≤
      SemiprimeWordPacketCounterBudget.nodeBudget b J R H M
        (SemiprimeNativeBitsCounterBudget.groupBudget n F R J b (∑ e,arity e) w A E) arity (design a) :=
    SemiprimeWordPacketCounterBudget.node_clock b Q J R H M w A E a (design a) _ entries
      (hh a) (hm a) harity hsource hsize hentry hentryWidth
  have hs : (∑ a : Fin Q,(acquire a).clock)≤
      ∑ a : Fin Q,SemiprimeWordPacketCounterBudget.nodeBudget b J R H M
        (SemiprimeNativeBitsCounterBudget.groupBudget n F R J b (∑ e,arity e) w A E) arity (design a) :=
    Finset.sum_le_sum (fun a _ => hn a)
  have hd := reconstruct_decode_work template Q J acquire (by omega)
  have hall : (SemiprimeAcquiredHermiteBits.reconstruct template Q J acquire).clock+
      SemiprimeNativeGroupBits.decodeWork #[(SemiprimeAcquiredHermiteBits.reconstruct template Q J acquire).word]≤
        reductionBudget b Q J R H M
          (SemiprimeNativeBitsCounterBudget.groupBudget n F R J b (∑ e,arity e) w A E) arity design := by
    simp only [template,List.length_replicate] at hr hd
    unfold reductionBudget
    dsimp only [template]
    omega
  simp only [count,Array.getElem_ofFn,inputAt_acquire,inputWork_acquire,
    Array.toList_ofFn,List.map_ofFn,Function.comp_def,List.sum_ofFn,nodeWord_work,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  simp only [Fin.eta]
  change (∑ e,∑ i,∑ v,(source e i v).work)+Q*(4*(b+1)+4)+
    (SemiprimeAcquiredHermiteBits.reconstruct template Q J acquire).clock+
    SemiprimeNativeGroupBits.decodeWork #[(SemiprimeAcquiredHermiteBits.reconstruct template Q J acquire).word]+
    inputControl n F (∑ e,arity e) R b+control b Q J R arity design+10*Q+10≤_
  omega

end RiemannGaussian.SemiprimeHermiteBitsCounterBudget
