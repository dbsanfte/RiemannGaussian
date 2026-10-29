/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeNativeGroupBits
import RiemannGaussian.SemiprimeMaterializedGroupAdapter
import RiemannGaussian.SemiprimeSourceWordAcquisition

/-! # Actual physical native groups inside the materialized counter

Original source getters execute once per incidence and column before counting.
The acquired reports are cached, their work retained, and integer nodes encoded
once. Every group call executes the physical corrected-port/local/product path.
Outer head tests, summary/support arithmetic and Hermite reconstruction remain
scalar. Word interpretation and finite-address control remain explicit boundaries.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeNativeBitsCounter
open scoped BigOperators
open Polynomial SemiprimeJetArray SemiprimeJetArrayHeight
open SemiprimeRationalBits SemiprimeJetBits SemiprimeLocalBits
open SemiprimeNodeArrayExecution (RuntimeDesign runtimeDesign)
open SemiprimeIndexedNodeCertificate
open SemiprimeMaterializedSourceUniversal (Run)
variable {n F : ℕ} {arity : Fin F → ℕ}

/-- Materialize every original word-row getter report once. -/
def acquireInputs (source : (e : Fin F) → Fin (arity e) → Fin n → Run (Array RationalWord)) :
    Array (Array (Array (Run (Array RationalWord)))) :=
  Array.ofFn (fun e => Array.ofFn (fun i => Array.ofFn (fun v => source e i v)))

/-- Total indexed cache read; the empty default is unreachable for the acquired family. -/
def inputAt (cache : Array (Array (Array (Run (Array RationalWord)))))
    (e i v : ℕ) : Run (Array RationalWord) :=
  (((cache[e]?.getD #[])[i]?.getD #[])[v]?).getD ⟨#[],0⟩

/-- Literal acquisition order preserves each original row report. -/
theorem inputAt_acquire (source : (e : Fin F) → Fin (arity e) → Fin n → Run (Array RationalWord))
    (e : Fin F) (i : Fin (arity e)) (v : Fin n) :
    inputAt (acquireInputs source) e.val i.val v.val=source e i v := by
  simp [inputAt,acquireInputs,e.isLt,i.isLt,v.isLt]

/-- Sum the actual cached getter reports, never invoke the source again. -/
def inputWork (cache : Array (Array (Array (Run (Array RationalWord))))) : ℕ :=
  (cache.toList.map (fun rows => (rows.toList.map
    (fun columns => (columns.toList.map Run.work).sum)).sum)).sum

/-- Every original read report occurs exactly once in the acquisition work. -/
theorem inputWork_acquire (source : (e : Fin F) → Fin (arity e) → Fin n → Run (Array RationalWord)) :
    inputWork (acquireInputs source)=∑ e,∑ i,∑ v,(source e i v).work := by
  simp [inputWork,acquireInputs,List.sum_ofFn,Function.comp_def]

/-- Conservative finite cache allocation and nested-index control allowance. -/
def inputControl (n F s R b : ℕ) : ℕ := 40*(n+1)^2*(F+1)^2*(s+1)^2*(R+1)*(b+1)+20

/-- Encode the actual positive integer interpolation node once. -/
def nodeInt {Q : ℕ} (a : Fin Q) : ℤ := Int.ofNat (a.val+1)

/-- Encode the actual positive integer interpolation node once. -/
def nodeWord (b : ℕ) {Q : ℕ} (a : Fin Q) : SemiprimeEncodedRowSelection.IntegerWordRun :=
  SemiprimeEncodedRowSelection.encode b (nodeInt a)

/-- The node encoder retains the original integer without a supplied word. -/
theorem nodeWord_value (b Q : ℕ) (a : Fin Q) (hQ : Q≤2^b) :
    (nodeWord b a).word.value=(nodeInt a:ℚ) := by
  apply SemiprimeEncodedRowSelection.encode_value
  have h : a.val+1≤2^b := (by omega : a.val+1≤Q).trans hQ
  change |((a.val+1 : ℕ) : ℤ)|≤(2^b : ℕ)
  rw [abs_of_nonneg (Int.natCast_nonneg _)]
  exact_mod_cast h

/-- Literal denominator one is legal at every acquired node. -/
theorem nodeWord_valid (b Q : ℕ) (a : Fin Q) : (nodeWord b a).word.Valid :=
  SemiprimeEncodedRowSelection.encode_valid b _

/-- Each node retains its actual scalar digit-construction ledger. -/
theorem nodeWord_work (b Q : ℕ) (a : Fin Q) : (nodeWord b a).work=4*(b+1)+4 :=
  (SemiprimeEncodedRowSelection.encode_work b _).1

/-- Execute and retain the physical group before returning to scalar outer folds. -/
def group (b J R : ℕ) (d : RuntimeDesign n F) (tw : RationalWord)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord) :
    SemiprimeMaterializedGroupAdapter.GroupCall d :=
  fun U g a => SemiprimePacketArrayExecution.bump
    (SemiprimeNativeGroupBits.toScalarRun (SemiprimeNativeGroupBits.run b arity J R tw source
      d.grouping d.assigned (fun v => decide (v ∈ U)) entries g a))
    (inputControl n F (∑ e,arity e) R (SemiprimeNativeGroupBits.groupWidth b R F (∑ e,arity e)))

/-- The original acquired rows and encoded nodes feed actual physical group calls. -/
def count (b Q J R : ℕ) (design : Fin Q → RuntimeDesign n F)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Run (Array RationalWord))
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord) :
    SemiprimeAcquiredHermite.ScalarRun :=
  let inputs := acquireInputs source
  let nodes := Array.ofFn (fun a : Fin Q => nodeWord b a)
  let out := SemiprimeMaterializedGroupAdapter.count Q J design (fun a =>
    group b J R (design a) (nodes[a.val]'(by simp [nodes])).word
      (fun e i v => (inputAt inputs e.val i.val v.val).value) entries)
  ⟨out.value,inputWork inputs+(nodes.toList.map (fun x => x.work)).sum+out.work+
    inputControl n F (∑ e,arity e) R b+10*Q+10⟩

/-- The actual physical group is the old native group coefficient array;
its independently acquired report is kept rather than equated with the old one. -/
theorem group_correct (b J R den B T : ℕ) (d : RuntimeDesign n F)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (tw : RationalWord) (t : ℤ)
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (hvalid : ∀ e i v,Valid (source e i v)) (htw : tw.Valid) (htval : tw.value=(t:ℚ))
    (hd : 0<den) (ht : t.natAbs≤T) (hdb : den≤2^b) (hBb : B≤2^b)
    (hTb : T≤2^b) (hJb : J≤2^b) (hnb : n≤2^b)
    (hsource : ∀ e i v k,k≤R → Representation (coefficient (decode (source e i v)) k) den B)
    (hentries : ∀ e eta,(entries e eta).bits.value.natAbs≤1)
    (U : Finset (Fin n)) (g : Fin d.r) (a : (k : Fin d.r) → Fin (d.h k) → Bool) :
    (group b J R d tw source entries U g a).jet.coefficients=
      (SemiprimeNativeGroupExecution.nativeGroup arity J R (t:ℚ)
        (fun e i v => decode (source e i v)) d.grouping d.assigned
        (fun v => decide (v ∈ U)) (fun e => table (entries e)) g a).jet.coefficients :=
  SemiprimeNativeGroupBits.run_correct b arity J R den B T source tw t d.grouping d.assigned
    (fun v => decide (v ∈ U)) entries g a hvalid htw htval hd ht hdb hBb hTb hJb hnb hsource hentries

/-- The actual cached physical-native counter returns the original contraction.
All word fits follow from original source representations and parameter bounds. -/
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
        (fun e eta => ((entries e eta).bits.value:ℚ)) coordinate := by
  let value := fun a : Fin Q => group b J R (runtimeDesign (design a)) (nodeWord b a).word
    (fun e i v => (source e i v).value) entries
  have hv (a : Fin Q) (U : Finset (Fin n)) (g) (x) (k : ℕ) (_hk : k<J) :
      coefficient (value a U g x).jet.coefficients k=
        coefficient (SemiprimeNativeGroupExecution.nativeGroup arity J R ((a.val:ℚ)+1)
          (fun e i v => decode (source e i v).value) (design a).grouping (design a).assigned
          (fun v => decide (v ∈ U)) (fun e => table (entries e)) g x).jet.coefficients k := by
    have h := group_correct b J R den B Q (runtimeDesign (design a))
      (fun e i v => (source e i v).value) (nodeWord b a).word (nodeInt a) entries
      hvalid (nodeWord_valid b Q a) (nodeWord_value b Q a hQb) hd
      (by change a.val+1≤Q; omega) hdb hBb hQb hJb hnb hsource hentries U g x
    have hcoeff' := congrArg (fun arr => coefficient arr k) h
    have ht : (nodeInt a:ℚ)=(a.val:ℚ)+1 := by
      change (((a.val+1:ℕ):ℤ):ℚ)=(a.val:ℚ)+1
      push_cast
      rfl
    simpa only [value,ht,runtimeDesign] using hcoeff'
  have h := SemiprimeMaterializedGroupAdapter.count_correct Q J R hJ design
    (fun e i v => decode (source e i v).value) (fun e => table (entries e)) hrows hcoeff hdegree
    coordinate hrestore value hv
  simpa only [count,Array.getElem_ofFn,inputAt_acquire,value,table] using h

/-- Cost of the unchanged outer reductions around an executed group bound. -/
def reductionBudget (Q J H M C : ℕ) (design : Fin Q → RuntimeDesign n F) : ℕ :=
  (∑ a : Fin Q,(SemiprimeCounterEnumeration.weightedCount n (J-1)*
    (SemiprimeMaterializedGroupAdapter.fibreBudget J (design a).r H M C
      (SemiprimePacketArrayExecution.summaryCount (design a).r (design a).h (design a).m (design a).W)+
      3*J+3*n+2+n*(8*J+3))+
      ((design a).r*(2^H*(H+M*(4*H+2)+3))+(design a).r+1)))+
    Q*(2*J+4+2*SemiprimeHermiteArrayHeight.nodeWork Q J)

/-- The real getter, node encoding, physical group and outer reduction costs
are all retained. C bounds the actual executed group report, not its value. -/
theorem count_work (b Q J R H M C : ℕ) (design : Fin Q → RuntimeDesign n F)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Run (Array RationalWord))
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (hh : ∀ a g,(design a).h g≤H) (hm : ∀ a g,(design a).m g≤M)
    (hg : ∀ a U g x,(group b J R (design a) (nodeWord b a).word
      (fun e i v => (source e i v).value) entries U g x).work≤C) :
    (count b Q J R design source entries).work ≤
      (∑ e,∑ i,∑ v,(source e i v).work)+Q*(4*(b+1)+4)+
        reductionBudget Q J H M C design+inputControl n F (∑ e,arity e) R b+10*Q+10 := by
  have h := SemiprimeMaterializedGroupAdapter.count_work Q J H M C design
    (fun a => group b J R (design a) (nodeWord b a).word
      (fun e i v => (source e i v).value) entries) hh hm hg
  change _≤reductionBudget Q J H M C design at h
  simp only [count,Array.getElem_ofFn,inputAt_acquire,inputWork_acquire,
    Array.toList_ofFn,List.map_ofFn,Function.comp_def,List.sum_ofFn,nodeWord_work,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  gcongr

end RiemannGaussian.SemiprimeNativeBitsCounter
