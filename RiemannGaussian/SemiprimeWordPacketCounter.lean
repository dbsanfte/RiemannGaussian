/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedWordFibre
import RiemannGaussian.SemiprimeWordPacketWidth
import RiemannGaussian.SemiprimeNativeBitsCounter

/-! # Original native groups remain words through the complete node packet

Source getters and interpolation nodes are cached once. Group, head, summary
and signed-support arithmetic execute on words. Only the completed node packet
is decoded at the existing scalar Hermite boundary. Source/parameter/control
and final Hermite refinements remain explicitly separate obligations.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeWordPacketCounter
open scoped BigOperators
open Polynomial SemiprimeJetArray SemiprimeJetArrayHeight
open SemiprimeRationalBits SemiprimeJetBits SemiprimeLocalBits
open SemiprimeLocalExecutionHeight
open SemiprimeNodeArrayExecution (RuntimeDesign runtimeDesign)
open SemiprimeIndexedNodeCertificate
open SemiprimeMaterializedSourceUniversal (Run)
open SemiprimeNativeBitsCounter (acquireInputs inputAt inputWork inputAt_acquire inputWork_acquire
  inputControl nodeInt nodeWord nodeWord_value nodeWord_valid nodeWord_work)
variable {n F : ℕ} {arity : Fin F → ℕ}

/-- The actual total cached head-word count, with one safe empty-family unit. -/
def headCap (d : RuntimeDesign n F) : ℕ := 1+∑ g,2^(d.h g)

/-- Each actual local head count is covered without inserting a global truth count. -/
theorem headCap_le (d : RuntimeDesign n F) (g : Fin d.r) : 2^(d.h g)≤headCap d := by
  have h := Finset.single_le_sum (f:=fun g => 2^(d.h g)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ g)
  unfold headCap
  omega

/-- The actual head-cap resource is bounded by the existing local head envelope. -/
theorem headCap_bound (d : RuntimeDesign n F) (H : ℕ) (hh : ∀ g,d.h g≤H) :
    headCap d≤1+d.r*2^H := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun g _ =>
    Nat.pow_le_pow_right (by decide : 0<2) (hh g))
  simpa only [headCap,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using
    Nat.add_le_add_left hs 1

/-- Width is computed from original dimensions and actual finite enumeration sizes. -/
def nodeWidth (b R J : ℕ) (arity : Fin F → ℕ) (d : RuntimeDesign n F) : ℕ :=
  SemiprimeWordPacketWidth.packetWidth b R n F (∑ e,arity e) J d.r (headCap d)
    (SemiprimePacketArrayExecution.summaryCount d.r d.h d.m d.W)
    (SemiprimeCounterEnumeration.weightedCount n (J-1))

/-- The physical group report is retained directly; no rational decode occurs here. -/
def group (b J R : ℕ) (d : RuntimeDesign n F) (tw : RationalWord)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord) :
    SemiprimeMaterializedWordFibre.GroupCall d :=
  fun U g a =>
    let result := SemiprimeNativeGroupBits.run b arity J R tw source d.grouping d.assigned
      (fun v => decide (v ∈ U)) entries g a
    ⟨result.words,result.clock+
      inputControl n F (∑ e,arity e) R (SemiprimeNativeGroupBits.groupWidth b R F (∑ e,arity e))⟩

/-- The exact same acquired native group supplies the outer fold, and its
common height follows entirely from original source representations. -/
theorem group_spec (b J R den B T : ℕ) (d : RuntimeDesign n F)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (tw : RationalWord) (t : ℤ)
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (hvalid : ∀ e i v,Valid (source e i v)) (htw : tw.Valid) (htval : tw.value=(t:ℚ))
    (hd : 0<den) (ht : t.natAbs≤T) (hdb : den≤2^b) (hBb : B≤2^b)
    (hTb : T≤2^b) (hJb : J≤2^b) (hnb : n≤2^b)
    (hsource : ∀ e i v k,k≤R → Representation (coefficient (decode (source e i v)) k) den B)
    (hentries : ∀ e eta,(entries e eta).bits.value.natAbs≤1)
    (U : Finset (Fin n)) (g : Fin d.r) (a : (k : Fin d.r) → Fin (d.h k) → Bool) :
    decode (group b J R d tw source entries U g a).words=
      (SemiprimeNativeBitsCounter.group b J R d tw source entries U g a).jet.coefficients ∧
    Valid (group b J R d tw source entries U g a).words ∧
    ArrayBound (decode (group b J R d tw source entries U g a).words) J
      (SemiprimeNativeGroupBitsHeight.denominator den (∑ e,arity e) F)
      (SemiprimeNativeGroupBitsHeight.numerator n J R den B T (∑ e,arity e) F) := by
  have hs := SemiprimeNativeGroupBits.run_spec b arity J R den B T source tw t d.grouping d.assigned
    (fun v => decide (v ∈ U)) entries g a hvalid htw htval hd ht hdb hBb hTb hJb hnb hsource hentries
  have hh := SemiprimeNativeGroupBitsHeight.run_height b arity J R den B T source tw t
    d.grouping d.assigned (fun v => decide (v ∈ U)) entries g a
    hvalid htw htval hd ht hdb hBb hTb hJb hnb hsource hentries
  exact ⟨rfl,hs.2,hh⟩

/-- Omitting per-group decoding preserves the actual physical report and can
only remove the previous nonnegative boundary allowance. -/
theorem group_clock_le_legacy (b J R : ℕ) (d : RuntimeDesign n F) (tw : RationalWord)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (U : Finset (Fin n)) (g : Fin d.r) (a : (k : Fin d.r) → Fin (d.h k) → Bool) :
    (group b J R d tw source entries U g a).clock≤
      (SemiprimeNativeBitsCounter.group b J R d tw source entries U g a).work := by
  simp only [group,SemiprimeNativeBitsCounter.group,SemiprimePacketArrayExecution.bump_work,
    SemiprimeNativeGroupBits.toScalarRun_work]
  omega

/-- Retained finite parameter/template/cache allowance. A literal address and
natural arithmetic trace refinement remains separate from this control ledger. -/
def nodeControl (b R J : ℕ) (arity : Fin F → ℕ) (d : RuntimeDesign n F) : ℕ :=
  40*(n+F+d.r+(∑ e,arity e)+(∑ g,d.m g)+b+R+J+nodeWidth b R J arity d+1)^2+20

/-- Complete word-valued node acquisition, including the actual width template. -/
def node (b J R : ℕ) (d : RuntimeDesign n F) (tw : RationalWord)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord) : JetReport :=
  let template := List.replicate (nodeWidth b R J arity d) false
  let result := SemiprimeMaterializedWordFibre.node template J d (group b J R d tw source entries)
  ⟨result.words,result.clock+nodeControl b R J arity d⟩

/-- The actual original-input node has exact decoded coefficients and a
single denominator throughout all outer arithmetic. No intermediate fit is supplied. -/
theorem node_spec (b J R den B T : ℕ) (d : RuntimeDesign n F)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (tw : RationalWord) (t : ℤ)
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (hvalid : ∀ e i v,Valid (source e i v)) (htw : tw.Valid) (htval : tw.value=(t:ℚ))
    (hd : 0<den) (ht : t.natAbs≤T) (hdb : den≤2^b) (hBb : B≤2^b)
    (hTb : T≤2^b) (hJb : J≤2^b) (hnb : n≤2^b)
    (hsource : ∀ e i v k,k≤R → Representation (coefficient (decode (source e i v)) k) den B)
    (hentries : ∀ e eta,(entries e eta).bits.value.natAbs≤1) :
    let DG := SemiprimeNativeGroupBitsHeight.denominator den (∑ e,arity e) F
    let BG := SemiprimeNativeGroupBitsHeight.numerator n J R den B T (∑ e,arity e) F
    decode (node b J R d tw source entries).words=
      (SemiprimeMaterializedGroupAdapter.node d J
        (SemiprimeNativeBitsCounter.group b J R d tw source entries)).jet.coefficients ∧
    Valid (node b J R d tw source entries).words ∧
    ArrayBound (decode (node b J R d tw source entries).words) J (DG^d.r)
      (SemiprimeCounterEnumeration.weightedCount n (J-1)*
        (SemiprimePacketArrayExecution.summaryCount d.r d.h d.m d.W*
          (SemiprimeWordPacketWidth.productBase J DG BG (headCap d))^(2*d.r))) := by
  let s := ∑ e,arity e
  let DG := SemiprimeNativeGroupBitsHeight.denominator den s F
  let BG := SemiprimeNativeGroupBitsHeight.numerator n J R den B T s F
  have h := SemiprimeMaterializedWordFibre.node_correct
    (List.replicate (nodeWidth b R J arity d) false) b R s J (headCap d)
    (SemiprimePacketArrayExecution.summaryCount d.r d.h d.m d.W)
    (SemiprimeCounterEnumeration.weightedCount n (J-1)) DG BG d
    (group b J R d tw source entries) (SemiprimeNativeBitsCounter.group b J R d tw source entries)
    (by simp only [List.length_replicate]; exact le_rfl)
    (SemiprimeNativeGroupBitsHeight.denominator_pos den s F hd)
    (SemiprimeNativeGroupBitsHeight.denominator_dyadic b R den s F hdb)
    (SemiprimeNativeGroupBitsHeight.numerator_dyadic b R J den B T n s F hdb hBb hTb hJb hnb)
    (headCap_le d) (le_refl _) (by rw [SemiprimeCounterEnumeration.callbacks_eq_weightedCount])
    (group_spec b J R den B T d source tw t entries hvalid htw htval hd ht hdb hBb hTb hJb hnb hsource hentries)
  exact h

/-- Acquire source and nodes once, execute word packets, then scalar Hermite reconstruction. -/
def count (b Q J R : ℕ) (design : Fin Q → RuntimeDesign n F)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Run (Array RationalWord))
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord) :
    SemiprimeAcquiredHermite.ScalarRun :=
  let inputs := acquireInputs source
  let nodes := Array.ofFn (fun a : Fin Q => nodeWord b a)
  let out := SemiprimeAcquiredHermite.reconstruct Q J (fun a =>
    SemiprimeNativeGroupBits.toScalarRun
      (node b J R (design a) (nodes[a.val]'(by simp [nodes])).word
        (fun e i v => (inputAt inputs e.val i.val v.val).value) entries))
  ⟨out.value,inputWork inputs+(nodes.toList.map (fun x => x.work)).sum+out.work+
    inputControl n F (∑ e,arity e) R b+10*Q+10⟩

/-- The Hermite consumer depends only on acquired packet coefficients, not the
component reports. This permits an executed word replacement with a new cost. -/
theorem reconstruct_value_congr (Q J : ℕ) (a c : Fin Q → SemiprimeFibreArrayExecution.Run)
    (h : ∀ t k,k<J → coefficient (a t).jet.coefficients k=coefficient (c t).jet.coefficients k) :
    (SemiprimeAcquiredHermite.reconstruct Q J a).value=
      (SemiprimeAcquiredHermite.reconstruct Q J c).value := by
  rw [SemiprimeAcquiredHermite.reconstruct_value,SemiprimeAcquiredHermite.reconstruct_value]
  have hp : (fun t => SemiprimeAcquiredHermite.packet J (a t))=
      (fun t => SemiprimeAcquiredHermite.packet J (c t)) := by
    funext t
    unfold SemiprimeAcquiredHermite.packet
    congr 1
    funext k
    exact h t k.val k.isLt
  rw [hp]

/-- Complete acquired word packets replace scalar outer folds with identical
count values. The new physical reports are never equated with the old reports. -/
theorem count_value_eq_native (b Q J R den B : ℕ) (design : Fin Q → RuntimeDesign n F)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Run (Array RationalWord))
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (hvalid : ∀ e i v,Valid (source e i v).value) (hd : 0<den)
    (hdb : den≤2^b) (hBb : B≤2^b) (hQb : Q≤2^b) (hJb : J≤2^b) (hnb : n≤2^b)
    (hsource : ∀ e i v k,k≤R → Representation (coefficient (decode (source e i v).value) k) den B)
    (hentries : ∀ e eta,(entries e eta).bits.value.natAbs≤1) :
    (count b Q J R design source entries).value=
      (SemiprimeNativeBitsCounter.count b Q J R design source entries).value := by
  simp only [count,SemiprimeNativeBitsCounter.count,Array.getElem_ofFn,inputAt_acquire,
    SemiprimeMaterializedGroupAdapter.count]
  apply reconstruct_value_congr
  intro a k _hk
  have h := node_spec b J R den B Q (design a) (fun e i v => (source e i v).value)
    (nodeWord b a).word (nodeInt a) entries hvalid (nodeWord_valid b Q a)
    (nodeWord_value b Q a hQb) hd (by change a.val+1≤Q; omega) hdb hBb hQb hJb hnb hsource hentries
  exact congrArg (fun arr => coefficient arr k) h.1

/-- Original-network contraction from actual acquired word packets and original
Boolean callbacks, with the original all-input mathematical guards. -/
theorem count_correct {rows : (e : Fin F) → Fin (arity e) → Fin n → Polynomial ℚ}
    (b Q J R den B : ℕ) (hJ : 0<J)
    (design : (a : Fin Q) → Data arity (fun e i v => (rows e i v).eval ((a.val:ℚ)+1)))
    (source : (e : Fin F) → Fin (arity e) → Fin n → Run (Array RationalWord))
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (hvalid : ∀ e i v,Valid (source e i v).value) (hd : 0<den)
    (hdb : den≤2^b) (hBb : B≤2^b) (hQb : Q≤2^b) (hJb : J≤2^b) (hnb : n≤2^b)
    (hsource : ∀ e i v k,k≤R → Representation (coefficient (decode (source e i v).value) k) den B)
    (hentries : ∀ e eta,(entries e eta).bits.value.natAbs≤1)
    (hrows : ∀ e i v,(rows e i v).natDegree≤R)
    (hcoeff : ∀ e i v k,k≤R → coefficient (decode (source e i v).value) k=(rows e i v).coeff k)
    (hdegree : (∑ e,arity e)*R<Q*J)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (hrestore : ∀ e i v,(rows e i v).eval 0=if v=coordinate e i then 1 else 0) :
    (count b Q J R (fun a => runtimeDesign (design a)) source entries).value=
      SemiprimeCounterNative.originalContraction arity
        (fun e eta => ((entries e eta).bits.value:ℚ)) coordinate :=
  (count_value_eq_native b Q J R den B (fun a => runtimeDesign (design a)) source entries
    hvalid hd hdb hBb hQb hJb hnb hsource hentries).trans
      (SemiprimeNativeBitsCounter.count_correct b Q J R den B hJ design source entries
        hvalid hd hdb hBb hQb hJb hnb hsource hentries hrows hcoeff hdegree coordinate hrestore)

end RiemannGaussian.SemiprimeWordPacketCounter
