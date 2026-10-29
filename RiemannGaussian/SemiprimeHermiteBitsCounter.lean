/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeAcquiredHermiteBits
import RiemannGaussian.SemiprimeWordPacketHermiteInput

/-! # Actual original-source counter with physical Hermite reconstruction
The source getters and node encoders are cached once. Every node packet remains
physical through Hermite reconstruction. Only the final scalar count crosses
the existing rational/floor boundary, with its decode allowance retained.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeHermiteBitsCounter
open scoped BigOperators
open Polynomial SemiprimeJetArray SemiprimeJetArrayHeight
open SemiprimeRationalBits SemiprimeJetBits SemiprimeLocalBits
open SemiprimeNodeArrayExecution (RuntimeDesign runtimeDesign)
open SemiprimeIndexedNodeCertificate
open SemiprimeMaterializedSourceUniversal (Run)
open SemiprimeNativeBitsCounter (acquireInputs inputAt inputWork inputAt_acquire inputWork_acquire
  inputControl nodeWord nodeWord_work)
variable {n F : ℕ} {arity : Fin F → ℕ}

/-- Physical Hermite width derived from actual original node dimensions. -/
def countWidth (b Q J R : ℕ) (arity : Fin F → ℕ) (design : Fin Q → RuntimeDesign n F) : ℕ :=
  SemiprimeHermiteWordWidth.width (SemiprimeWordPacketHermiteInput.packetBits b R J arity design) Q J

/-- Retained width/frontend/control allowance; literal natural/address refinement remains. -/
def control (b Q J R : ℕ) (arity : Fin F → ℕ) (design : Fin Q → RuntimeDesign n F) : ℕ :=
  40*(n+F+(∑ e,arity e)+b+Q+J+R+countWidth b Q J R arity design+1)^2+20

/-- Complete acquired physical query with a single final scalar-count boundary. -/
def count (b Q J R : ℕ) (design : Fin Q → RuntimeDesign n F)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Run (Array RationalWord))
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord) :
    SemiprimeAcquiredHermite.ScalarRun :=
  let inputs := acquireInputs source
  let nodes := Array.ofFn (fun a : Fin Q => nodeWord b a)
  let template := List.replicate (countWidth b Q J R arity design) false
  let out := SemiprimeAcquiredHermiteBits.reconstruct template Q J (fun a =>
    SemiprimeWordPacketCounter.node b J R (design a) (nodes[a.val]'(by simp [nodes])).word
      (fun e i v => (inputAt inputs e.val i.val v.val).value) entries)
  ⟨out.word.value,inputWork inputs+(nodes.toList.map (fun x => x.work)).sum+out.clock+
    SemiprimeNativeGroupBits.decodeWork #[out.word]+inputControl n F (∑ e,arity e) R b+
    control b Q J R arity design+10*Q+10⟩

/-- Original source guards produce the common packet bounds internally and
justify the actual physical Hermite replacement. No work equality is asserted. -/
theorem count_value_eq_word_packet (b Q J R den B : ℕ) (hJ : 0<J)
    (design : Fin Q → RuntimeDesign n F)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Run (Array RationalWord))
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (hvalid : ∀ e i v,Valid (source e i v).value) (hd : 0<den)
    (hdb : den≤2^b) (hBb : B≤2^b) (hQb : Q≤2^b) (hJb : J≤2^b) (hnb : n≤2^b)
    (hsource : ∀ e i v k,k≤R → Representation (coefficient (decode (source e i v).value) k) den B)
    (hentries : ∀ e eta,(entries e eta).bits.value.natAbs≤1) :
    (count b Q J R design source entries).value=
      (SemiprimeWordPacketCounter.count b Q J R design source entries).value := by
  have ha := SemiprimeWordPacketHermiteInput.actual_nodes_bound b J R den B arity design
    (fun e i v => (source e i v).value) entries hvalid hd hdb hBb hQb hJb hnb hsource hentries
  have h := SemiprimeAcquiredHermiteBits.reconstruct_value_eq_acquired
    (List.replicate (countWidth b Q J R arity design) false)
    (SemiprimeWordPacketHermiteInput.packetBits b R J arity design) Q J
    (SemiprimeWordPacketHermiteInput.commonDenominator den arity design)
    (2^(SemiprimeWordPacketHermiteInput.packetBits b R J arity design))
    (fun a => SemiprimeWordPacketCounter.node b J R (design a) (nodeWord b a).word
      (fun e i v => (source e i v).value) entries)
    hJ ha.1 (fun a => (ha.2.2 a).1) (fun a => (ha.2.2 a).2.2) ha.2.1 le_rfl
    (by simp only [List.length_replicate]; exact le_rfl) (fun a => (ha.2.2 a).2.1)
  simpa only [count,SemiprimeWordPacketCounter.count,Array.getElem_ofFn,inputAt_acquire] using h

/-- Exact original-network contraction through the actual physical Hermite path. -/
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
  (count_value_eq_word_packet b Q J R den B hJ (fun a => runtimeDesign (design a)) source entries
    hvalid hd hdb hBb hQb hJb hnb hsource hentries).trans
      (SemiprimeWordPacketCounter.count_correct b Q J R den B hJ design source entries
        hvalid hd hdb hBb hQb hJb hnb hsource hentries hrows hcoeff hdegree coordinate hrestore)

end RiemannGaussian.SemiprimeHermiteBitsCounter
