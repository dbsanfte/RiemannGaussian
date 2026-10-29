/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeWordPacketCounter
import RiemannGaussian.SemiprimeMaterializedWordFibreBounds
import RiemannGaussian.SemiprimeNativeBitsCounterBudget

/-! # Retained cost of the actual word packet counter
The executed native group, head, summary and signed support reports are joined
to the real cached source getters and Hermite consumer. Only completed nodes
cross the rational boundary. This bound is not a complete address/tape clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeWordPacketCounterBudget
open scoped BigOperators
open SemiprimeRationalBits SemiprimeJetBits SemiprimeLocalBits
open SemiprimeWordPacketCounter
open SemiprimeNodeArrayExecution (RuntimeDesign)
open SemiprimeMaterializedSourceUniversal (Run)
open SemiprimeNativeBitsCounter (nodeWord inputControl inputAt_acquire inputWork_acquire nodeWord_work)
variable {n F : ℕ} {arity : Fin F → ℕ}

/-- The larger node template covers the actual emitted group words. -/
theorem group_bounded (b J R : ℕ) (d : RuntimeDesign n F) (tw : RationalWord)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (U : Finset (Fin n)) (g : Fin d.r) (a : (k : Fin d.r) → Fin (d.h k) → Bool) :
    Bounded (group b J R d tw source entries U g a).words (nodeWidth b R J arity d) := by
  have hw := SemiprimeNativeGroupBitsBudget.run_bounded b arity J R tw source d.grouping d.assigned
    (fun v => decide (v ∈ U)) entries g a
  have hW := SemiprimeWordPacketWidth.groupWidth_le b R n F (∑ e,arity e) J d.r (headCap d)
    (SemiprimePacketArrayExecution.summaryCount d.r d.h d.m d.W)
    (SemiprimeCounterEnumeration.weightedCount n (J-1))
  intro i hi
  exact ⟨(hw i hi).1.trans hW,(hw i hi).2.trans hW⟩

/-- Structural output size follows from the actual physical group execution. -/
theorem group_size (b J R : ℕ) (d : RuntimeDesign n F) (tw : RationalWord)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (U : Finset (Fin n)) (g : Fin d.r) (a : (k : Fin d.r) → Fin (d.h k) → Bool) :
    (group b J R d tw source entries U g a).words.size=J :=
  SemiprimeNativeGroupBits.run_size b arity J R tw source d.grouping d.assigned
    (fun v => decide (v ∈ U)) entries g a

/-- Complete node traversal plus its retained parameter and cache allowance. -/
def nodeBudget (b J R H M C : ℕ) (arity : Fin F → ℕ) (d : RuntimeDesign n F) : ℕ :=
  SemiprimeMaterializedWordFibreBounds.nodeBudget (nodeWidth b R J arity d) n J d.r H M C
    (SemiprimePacketArrayExecution.summaryCount d.r d.h d.m d.W)+nodeControl b R J arity d

/-- The original group budget pays every actual new group callback. Its old
nonnegative decoding allowance is harmless overestimation, not cost equality. -/
theorem node_clock (b Q J R H M w A E : ℕ) (a : Fin Q) (d : RuntimeDesign n F)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (hh : ∀ g,d.h g≤H) (hm : ∀ g,d.m g≤M) (harity : ∀ e,arity e≤w)
    (hsource : ∀ e i v,Bounded (source e i v) (SemiprimeNativeGroupBits.groupWidth b R F (∑ e,arity e)))
    (hsize : ∀ e i v,(source e i v).size≤A)
    (hentry : ∀ e eta,(entries e eta).clock≤E)
    (hentryWidth : ∀ e eta,(entries e eta).bits.magnitude.length≤
      SemiprimeNativeGroupBits.groupWidth b R F (∑ e,arity e)) :
    (node b J R d (nodeWord b a).word source entries).clock≤
      nodeBudget b J R H M
        (SemiprimeNativeBitsCounterBudget.groupBudget n F R J b (∑ e,arity e) w A E) arity d := by
  have hp : 0<(List.replicate (nodeWidth b R J arity d) false).length := by
    rw [List.length_replicate]
    exact SemiprimeWordPacketWidth.positive b R n F (∑ e,arity e) J d.r (headCap d)
      (SemiprimePacketArrayExecution.summaryCount d.r d.h d.m d.W)
      (SemiprimeCounterEnumeration.weightedCount n (J-1))
  have hg (U : Finset (Fin n)) (g : Fin d.r) (x : (k : Fin d.r) → Fin (d.h k) → Bool) :=
    (group_clock_le_legacy b J R d (nodeWord b a).word source entries U g x).trans
      (SemiprimeNativeBitsCounterBudget.group_work b Q J R w A E a d source entries
        harity hsource hsize hentry hentryWidth U g x)
  have hw := SemiprimeMaterializedWordFibreBounds.node_clock
    (List.replicate (nodeWidth b R J arity d) false) J d
    (group b J R d (nodeWord b a).word source entries) H M _ hp hh hm hg
    (by simpa only [List.length_replicate] using group_bounded b J R d (nodeWord b a).word source entries)
    (group_size b J R d (nodeWord b a).word source entries)
  simp only [List.length_replicate] at hw
  exact Nat.add_le_add_right hw _

/-- Polynomial allowance for the single rational boundary at a completed node. -/
def decodeBudget (W J : ℕ) : ℕ := J*(20000*(2*W+1)^3+5)+2*J+1

/-- Completed physical nodes have a structurally bounded final decode allowance. -/
theorem node_decode_work (b J R : ℕ) (d : RuntimeDesign n F) (tw : RationalWord)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord) :
    SemiprimeNativeGroupBits.decodeWork (node b J R d tw source entries).words≤
      decodeBudget (nodeWidth b R J arity d) J := by
  have hw := SemiprimeMaterializedWordFibreBounds.node_bounded
    (List.replicate (nodeWidth b R J arity d) false) J d (group b J R d tw source entries)
  simp only [List.length_replicate] at hw
  have hs := SemiprimeMaterializedWordFibreBounds.node_size
    (List.replicate (nodeWidth b R J arity d) false) J d (group b J R d tw source entries)
  have hb := SemiprimeNativeGroupBitsBudget.decodeWork_bound
    (node b J R d tw source entries).words (nodeWidth b R J arity d) hw
  change (node b J R d tw source entries).words.size=J at hs
  rw [hs] at hb
  exact hb

/-- All actual nodes, one decode per completed node, and the Hermite work. -/
def reductionBudget (b Q J R H M C : ℕ) (arity : Fin F → ℕ)
    (design : Fin Q → RuntimeDesign n F) : ℕ :=
  (∑ a : Fin Q,(nodeBudget b J R H M C arity (design a)+
    decodeBudget (nodeWidth b R J arity (design a)) J))+
    Q*(2*J+4+2*SemiprimeHermiteArrayHeight.nodeWork Q J)

/-- Original word sizes and entry reports discharge the full physical callback
budget. Cached source getters and node encoders are charged exactly once. -/
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
        inputControl n F (∑ e,arity e) R b+10*Q+10 := by
  let acquire := fun a : Fin Q => SemiprimeNativeGroupBits.toScalarRun
    (node b J R (design a) (nodeWord b a).word (fun e i v => (source e i v).value) entries)
  have hn (a : Fin Q) : (acquire a).work≤
      nodeBudget b J R H M
        (SemiprimeNativeBitsCounterBudget.groupBudget n F R J b (∑ e,arity e) w A E) arity (design a)+
      decodeBudget (nodeWidth b R J arity (design a)) J := by
    dsimp only [acquire]
    rw [SemiprimeNativeGroupBits.toScalarRun_work]
    exact Nat.add_le_add
      (node_clock b Q J R H M w A E a (design a) (fun e i v => (source e i v).value) entries
        (hh a) (hm a) harity hsource hsize hentry hentryWidth)
      (node_decode_work b J R (design a) (nodeWord b a).word (fun e i v => (source e i v).value) entries)
  have hr := (SemiprimeAcquiredHermite.reconstruct_work Q J acquire).trans
    (Nat.add_le_add_right (Finset.sum_le_sum (fun a _ => hn a)) _)
  change _≤reductionBudget b Q J R H M
    (SemiprimeNativeBitsCounterBudget.groupBudget n F R J b (∑ e,arity e) w A E) arity design at hr
  simp only [count,Array.getElem_ofFn,inputAt_acquire,inputWork_acquire,
    Array.toList_ofFn,List.map_ofFn,Function.comp_def,List.sum_ofFn,nodeWord_work,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add_left hr _) _) _) _

end RiemannGaussian.SemiprimeWordPacketCounterBudget
