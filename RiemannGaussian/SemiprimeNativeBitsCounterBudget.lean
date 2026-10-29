/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeNativeBitsCounter
import RiemannGaussian.SemiprimeNativeGroupBitsBudget

/-! # The actual physical group budget supplies the complete counter traversal
There is no group-work or arithmetic-fit oracle in the exported bound. Original
word lengths, original entry clocks and acquired design dimensions bound the
executed groups; all source getters and scalar outer reductions remain retained.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeNativeBitsCounterBudget
open scoped BigOperators
open SemiprimeRationalBits SemiprimeJetBits SemiprimeLocalBits
open SemiprimeNativeBitsCounter SemiprimeNativeGroupBitsBudget
open SemiprimeNodeArrayExecution (RuntimeDesign)
open SemiprimeMaterializedSourceUniversal (Run)
variable {n F : ℕ} {arity : Fin F → ℕ}

/-- Literal node words fit the polynomial width actually built by the group. -/
theorem nodeWord_width (b Q R F s : ℕ) (a : Fin Q) :
    Width (nodeWord b a).word (SemiprimeNativeGroupBits.groupWidth b R F s) := by
  have hw : b+1≤SemiprimeNativeGroupBits.groupWidth b R F s := by
    unfold SemiprimeNativeGroupBits.groupWidth SemiprimeNativeLocalBits.publicWidth
    omega
  constructor
  · change (SemiprimeEncodedRowSelection.digits (b+1) _).bits.length≤_
    rw [SemiprimeEncodedRowSelection.digits_length]
    exact hw
  · change 1≤_
    omega

/-- Physical groups, the scalar boundary and family-access allowance all stay paid. -/
def groupBudget (n F R J b s w A E : ℕ) : ℕ :=
  scalarGroupBudget n F R J b s w A E+
    inputControl n F s R (SemiprimeNativeGroupBits.groupWidth b R F s)

/-- The executed callback's cost follows from actual original words and entries. -/
theorem group_work (b Q J R w A E : ℕ) (a : Fin Q) (d : RuntimeDesign n F)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (harity : ∀ e,arity e≤w)
    (hsource : ∀ e i v,Bounded (source e i v) (SemiprimeNativeGroupBits.groupWidth b R F (∑ e,arity e)))
    (hsize : ∀ e i v,(source e i v).size≤A)
    (hentry : ∀ e eta,(entries e eta).clock≤E)
    (hentryWidth : ∀ e eta,(entries e eta).bits.magnitude.length≤
      SemiprimeNativeGroupBits.groupWidth b R F (∑ e,arity e))
    (U : Finset (Fin n)) (g : Fin d.r) (x : (k : Fin d.r) → Fin (d.h k) → Bool) :
    (group b J R d (nodeWord b a).word source entries U g x).work≤
      groupBudget n F R J b (∑ e,arity e) w A E := by
  have h := toScalarRun_clock b arity J R w A E (nodeWord b a).word source d.grouping d.assigned
    (fun v => decide (v ∈ U)) entries g x harity (nodeWord_width b Q R F (∑ e,arity e) a)
    hsource hsize hentry hentryWidth
  unfold group groupBudget
  rw [SemiprimePacketArrayExecution.bump_work]
  exact Nat.add_le_add_right h _

/-- Complete actual native counter bound with the physical callback budget
DISCHARGED. The same support/head/summary factors remain; no global truth sweep. -/
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
        reductionBudget Q J H M (groupBudget n F R J b (∑ e,arity e) w A E) design+
        inputControl n F (∑ e,arity e) R b+10*Q+10 :=
  SemiprimeNativeBitsCounter.count_work b Q J R H M _ design source entries hh hm
    (fun a U g x => group_work b Q J R w A E a (design a)
      (fun e i v => (source e i v).value) entries harity hsource hsize hentry hentryWidth U g x)

end RiemannGaussian.SemiprimeNativeBitsCounterBudget
