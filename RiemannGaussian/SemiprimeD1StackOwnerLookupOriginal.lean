/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerLookupBounds
import RiemannGaussian.SemiprimeD1PortOwnerKeys
import RiemannGaussian.SemiprimeD1OrdinalBankSpec
import RiemannGaussian.SemiprimePublicAcquiredExecution
/-! # Original endpoint completeness licenses the physical prepared-map lookup
The catalogue below is a proof specification of forward emission in the exact
original E-wire order. Its physical acquisition remains a caller obligation.
The lookup itself is the actual finite machine with paid key/payload scans.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackOwnerLookupOriginal
open SemiprimeD1StackOwnerLookup SemiprimeD1StackOwnerLookupExecution
open SemiprimeD1PortOwnerKeys SemiprimeMacroGraph
open SemiprimeBitArithmetic (bitValue)
/-- Semantic first-match specification needs coverage and exact matching only. -/
theorem result_value (query:List Bool) (rows:List (List Bool×List Bool)) (tail value:List Bool)
    (hex:∃key,(key,value)∈rows ∧ bitValue key=bitValue query)
    (hall:∀key payload,(key,payload)∈rows→bitValue key=bitValue query→payload=value) :
    (result query rows tail).1=value := by
  induction rows with
  | nil=>obtain ⟨key,hk,_⟩:=hex;cases hk
  | cons row rows ih=>
    rcases row with ⟨key,payload⟩
    by_cases h:bitValue key=bitValue query
    · simp only [result,h,ite_true]
      exact hall key payload (by simp) h
    · simp only [result,h,ite_false]
      apply ih
      · obtain ⟨k,hk,he⟩:=hex
        rcases List.mem_cons.mp hk with hh|hh
        · cases hh
          exact (h he).elim
        · exact ⟨k,hh,he⟩
      · intro k v hk he
        exact hall k v (List.mem_cons_of_mem _ hk) he
/-- BOTH endpoints of each actual E-wire share its original owner word. -/
def forward {r t digits:ℕ} (hd:0<digits) (hc:digits≤r*t)
    (owner:Edge r t digits→List Bool) : List (List Bool×List Bool) :=
  ((SemiprimeMacroFiniteEnumerations.edges r t digits).values.product [false,true]).map
    (fun eh=>(key (endpoint hd hc eh.1 eh.2),owner eh.1))
/-- Original endpoint bijection discharges every match/coverage premise. -/
theorem forward_result {r t digits:ℕ} (hd:0<digits) (hc:digits≤r*t)
    (owner:Edge r t digits→List Bool) (p:Port r t digits) (tail:List Bool) :
    (result (key p) (forward hd hc owner) tail).1=
      owner ((subdividedOrderedEndpointEquiv r t digits hd hc).symm p).1 := by
  let eh:Edge r t digits×Bool:=(subdividedOrderedEndpointEquiv r t digits hd hc).symm p
  have he:key (endpoint hd hc eh.1 eh.2)=key p:=by
    change key ((subdividedOrderedEndpointEquiv r t digits hd hc)
      ((subdividedOrderedEndpointEquiv r t digits hd hc).symm p))=key p
    rw [Equiv.apply_symm_apply]
  apply result_value
  · refine ⟨key (endpoint hd hc eh.1 eh.2),?_,congrArg bitValue he⟩
    apply List.mem_map.mpr
    refine ⟨eh,List.mem_product.mpr ⟨(SemiprimeMacroFiniteEnumerations.edges r t digits).complete _,?_⟩,rfl⟩
    cases eh.2 <;> simp
  · intro k value hmem hmatch
    obtain ⟨candidate,hcand,hrow⟩:=List.mem_map.mp hmem
    have hk:key (endpoint hd hc candidate.1 candidate.2)=k:=congrArg Prod.fst hrow
    have hv:owner candidate.1=value:=congrArg Prod.snd hrow
    have hp:endpoint hd hc candidate.1 candidate.2=p:=(key_value_iff _ _).mp (by rw [hk];exact hmatch)
    have hsame:candidate=eh:=by
      apply (subdividedOrderedEndpointEquiv r t digits hd hc).injective
      change endpoint hd hc candidate.1 candidate.2=endpoint hd hc eh.1 eh.2
      exact hp.trans ((key_injective r t digits he).symm)
    rw [←hv,hsame]
/-- Endpoint inverse has the SAME wire as the original ordered graph scope. -/
theorem inverse_wire {r t digits:ℕ} (hd:0<digits) (hc:digits≤r*t) (p:Port r t digits) :
    ((subdividedOrderedEndpointEquiv r t digits hd hc).symm p).1=orderedEdgeAt hd hc p := rfl
/-- Every actual prepared forward map lookup returns its original coordinate's ID. -/
theorem original_output {r t digits:ℕ} (hd:0<digits) (hc:digits≤r*t)
    (owner:Edge r t digits→List Bool) (p:Port r t digits) (tail:List Bool) :
    (done (key p) (forward hd hc owner) tail).data (.inr .output)=owner (orderedEdgeAt hd hc p) := by
  change (result _ _ _).1=_
  rw [forward_result,inverse_wire]
namespace Public
open SemiprimePublicAcquiredExecution SemiprimeMacroParameters
/-- Actual M is the sum of original arities, distinct from the E-wire count. -/
def occurrences (N:ℕ) : ℕ := ∑factor:Fin (factorCount N),indexedArity N factor
/-- The complete graph supplies M=2E; E is never silently replaced by M. -/
theorem occurrences_eq (N:ℕ) (hN:0<N) : occurrences N=2*wireCount N :=
  indexed_incidence_count N hN
/-- Exact owner-ID bytes are the FIRST E entries in the physically acquired M bank. -/
def ownerWord (N:ℕ) (edge:PublicEdge N) : List Bool :=
  SemiprimeD1OrdinalBankSpec.idAt (occurrences N) ((edgeEnumeration N).equivFin.symm edge).val
/-- Owner IDs retain common physical M-bit width, while numeric value is < E. -/
theorem ownerWord_value (N:ℕ) (hN:0<N) (edge:PublicEdge N) :
    bitValue (ownerWord N edge)=((edgeEnumeration N).equivFin.symm edge).val := by
  apply SemiprimeD1OrdinalBankSpec.id_value
  have hi:=((edgeEnumeration N).equivFin.symm edge).isLt
  change _<wireCount N at hi
  rw [occurrences_eq N hN]
  omega
theorem ownerWord_length (N:ℕ) (hN:0<N) (edge:PublicEdge N) :
    (ownerWord N edge).length=occurrences N := by
  apply SemiprimeD1OrdinalBankSpec.id_length
  have hi:=((edgeEnumeration N).equivFin.symm edge).isLt
  change _<wireCount N at hi
  rw [occurrences_eq N hN]
  omega
/-- The original full forward catalogue specification, with acquired padded owner IDs. -/
def catalogue (N:ℕ) (hN:0<N) : List (List Bool×List Bool) :=
  forward (digitCount_bounds (bitLength_pos hN)).1
    (SemiprimeScheduledCounter.public_digit_capacity (bitLength_pos hN)) (ownerWord N)
/-- The physical map lookup computes the SAME wire ordinal as every actual
original factor/local-slot coordinate; no supplied permutation is used. -/
theorem indexed_output (N:ℕ) (hN:0<N) (factor:Fin (factorCount N))
    (slot:Fin (indexedArity N factor)) (tail:List Bool) :
    (done (key ⟨(vertexEnumeration N).equivFin factor,slot⟩) (catalogue N hN) tail).data (.inr .output)=
      SemiprimeD1OrdinalBankSpec.idAt (occurrences N) (indexedCoordinate N hN factor slot).val :=
  original_output _ _ _ _ _
/-- Numeric owner identity is EXACT original E-wire index, with no compactness premise. -/
theorem indexed_value (N:ℕ) (hN:0<N) (factor:Fin (factorCount N))
    (slot:Fin (indexedArity N factor)) (tail:List Bool) :
    bitValue ((done (key ⟨(vertexEnumeration N).equivFin factor,slot⟩) (catalogue N hN) tail).data (.inr .output))=
      (indexedCoordinate N hN factor slot).val := by
  rw [indexed_output]
  apply SemiprimeD1OrdinalBankSpec.id_value
  have hi: (indexedCoordinate N hN factor slot).val<wireCount N:=(indexedCoordinate N hN factor slot).isLt
  rw [occurrences_eq N hN]
  omega
/-- Concrete padded public wire encoding required by the original owner table. -/
def encode (N:ℕ) (wire:Fin (wireCount N)) : List Bool :=
  SemiprimeD1OrdinalBankSpec.idAt (occurrences N) wire.val
theorem encode_value (N:ℕ) (hN:0<N) (wire:Fin (wireCount N)) : bitValue (encode N wire)=wire.val := by
  apply SemiprimeD1OrdinalBankSpec.id_value
  rw [occurrences_eq N hN]
  have h:=wire.isLt
  omega
/-- Whole actual lookup trace specialized to EVERY original indexed port.
Only the actual physically prepared map/query bytes are initial operands. -/
theorem indexed_source_run (N:ℕ) (hN:0<N) (factor:Fin (factorCount N))
    (slot:Fin (indexedArity N factor)) (tail:List Bool) :
    ∃t≤SemiprimeD1StackOwnerLookupBounds.runBound
      (key ⟨(vertexEnumeration N).equivFin factor,slot⟩) (catalogue N hN),
      C.run program t (initial (key ⟨(vertexEnumeration N).equivFin factor,slot⟩)
        (records (catalogue N hN) tail))=
        some (done (key ⟨(vertexEnumeration N).equivFin factor,slot⟩) (catalogue N hN) tail) ∧
      (done (key ⟨(vertexEnumeration N).equivFin factor,slot⟩) (catalogue N hN) tail).data (.inr .output)=
        encode N (indexedCoordinate N hN factor slot) := by
  refine ⟨_,SemiprimeD1StackOwnerLookupBounds.time_le _ _,source_run _ _ _,?_⟩
  exact indexed_output N hN factor slot tail
end Public
end RiemannGaussian.SemiprimeD1StackOwnerLookupOriginal
