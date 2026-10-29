/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryForwardBucketsBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryFrontierView
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesSourceBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryFinishBounds
/-! # Whole literal thirteen-input child factory has one fixed twelfth-degree bound
All activation, endpoint emission, duplicate packet scans, generated unary
ordinals, all-vertex scope/order queries, final frames and115-role sweep are
charged to THIS SAME source. Recursive-child runtimes do not occur in the cap.
The prepared physical-input boundary remains explicit; no N-only claim is made.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBounds
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory
namespace E
export SemiprimeD1StackChildGroupFactoryExecution (timeBound done)
end E
namespace F
export SemiprimeD1StackChildGroupFactoryForwardBucketsSource (result endpoints)
end F
namespace Forward
export SemiprimeD1StackChildGroupFactoryForwardSource (rows)
end Forward
namespace Code
export SemiprimeD1StackChildGroupFactoryCatalogueCodecs (oldPoints buckets)
end Code
namespace V
export SemiprimeD1StackChildGroupFactoryVerticesSource (result timeBound)
end V
namespace Cap
export SemiprimeD1StackChildGroupFactoryForwardBounds (capacity)
export SemiprimeD1StackChildGroupFactoryInputCapacities (endpoints_count packets_count old_points vertices)
export SemiprimeD1StackChildGroupFactoryTraceBounds (Valid inputBytes cells)
end Cap
namespace P
export SemiprimeD1StackChildGroupFactoryEndpointParse (Fields)
end P
/-- Exact number of actual observed bucket records, retaining empty and duplicate packets. -/
theorem bucket_count (packets:List (List Bool)) (es:List SemiprimeD1StackChildGroupFactoryBucketParse.Endpoint)
    (position:List Bool):(Code.buckets packets es position).length=packets.length:=by
  induction packets generalizing position with
  | nil=>rfl
  | cons p ps ih=>simp only [Code.buckets,List.length_cons,ih]
/-- Same-program total monomial coefficient and degree are fixed BEFORE every input. -/
def runBound (i:Inputs):Nat:=10^60*(Cap.capacity i+1)^12
/-- Every complete source stage, including its physical cleanup, is paid by one fixed S12 cap. -/
theorem timeBound_le (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:Cap.Valid i a coordinate ids packets fields):E.timeBound i a coordinate ids packets fields≤runBound i:=by
  let S:=Cap.capacity i
  let before:=F.result i a coordinate ids packets fields
  let points:=Code.oldPoints (Forward.rows i a coordinate ids fields)
  let buckets:=Code.buckets packets (F.endpoints i a coordinate ids fields) []
  have hfront:=SemiprimeD1StackChildGroupFactoryForwardBucketsBounds.timeBound_le i a coordinate ids packets fields hv
  have hc:=SemiprimeD1StackChildGroupFactoryForwardBucketsBounds.result_word_le i a coordinate ids packets fields hv
  obtain ⟨hr,hp,hb,hkey⟩:=SemiprimeD1StackChildGroupFactoryFrontierView.actual_frontier i a coordinate ids packets fields
  have he: (F.endpoints i a coordinate ids fields).length≤S:=Cap.endpoints_count i a coordinate ids packets fields hv
  have hk:packets.length≤S:=Cap.packets_count i a coordinate ids packets fields hv
  have hJ:points.length≤S:=Cap.old_points i a coordinate ids packets fields hv
  have hV:i.owners.length+i.factors.length≤S:=Cap.vertices i
  have hK:buckets.length≤S:=by rw [bucket_count];exact hk
  have hm:packets.length*(F.endpoints i a coordinate ids fields).length≤S*S:=Nat.mul_le_mul hk he
  have hD:(buckets.flatMap (fun b=>b.children)).length≤S*S:=
    (SemiprimeD1StackChildGroupFactoryCounterBounds.catalogue_count packets (F.endpoints i a coordinate ids fields) []).trans hm
  have hG:∀p∈buckets.flatMap (fun b=>b.children),SemiprimeBitArithmetic.bitValue p.2≤S*S:=by
    intro p hp
    exact (SemiprimeD1StackChildGroupFactoryCounterBounds.generated_value packets (F.endpoints i a coordinate ids fields) p hp).trans hm
  have hrow:∀target,SemiprimeD1StackChildGroupFactoryVertexByteBounds.rowBytes points buckets target≤100*(S+1)^4:=by
    intro target
    exact SemiprimeD1StackChildGroupFactoryRowByteBounds.generated_rows_quartic packets
      (F.endpoints i a coordinate ids fields) points target S hk he hJ
  have hvertices:=SemiprimeD1StackChildGroupFactoryVerticesSourceBounds.timeBound_le before i.owners i.factors
    points buckets [] S hc hr hp hb hkey hV hK hJ hrow hD hG
  have hwords:=SemiprimeD1StackChildGroupFactoryVerticesSourceBounds.result_word_le before i.owners i.factors
    points buckets [] S hc hr hkey hV hrow
  have hfinish:=SemiprimeD1StackChildGroupFactoryFinishBounds.timeBound_le
    (V.result before i.owners i.factors points buckets [])
    (SemiprimeD1StackChildGroupFactoryRates.master S+1) hwords
  have hrate:10000000000000*(S+1)^4+10^44*(S+1)^10+
      1000000*(SemiprimeD1StackChildGroupFactoryRates.master S+2)≤10^60*(S+1)^12:=by
    dsimp only [SemiprimeD1StackChildGroupFactoryRates.master]
    ring_nf
    omega
  change _≤10^60*(S+1)^12
  dsimp only [E.timeBound,SemiprimeD1StackChildGroupFactorySuffix.timeBound]
  dsimp only [before,points,buckets,S] at hvertices hfinish
  dsimp only [S] at hrate ⊢
  omega
/-- Actual complete thirteen-input run, with the SAME own S12 clock and exact stopped output. -/
theorem source_run_bounded (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:Cap.Valid i a coordinate ids packets fields):
    ∃t≤runBound i,SemiprimeD1StackCalls.run program t (initial i)=some (E.done i a coordinate ids packets fields):=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackChildGroupFactoryTraceBounds.source_run i a coordinate ids packets fields hv
  exact ⟨t,ht.trans (timeBound_le i a coordinate ids packets fields hv),hr⟩
/-- Every ACTUAL successful prefix has the same fixed whole-source time cap. -/
theorem prefix_time (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:Cap.Valid i a coordinate ids packets fields) (fuel:Nat)
    (out:SemiprimeD1StackCalls.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial i)=some out):fuel≤runBound i:=
  (SemiprimeD1StackChildGroupFactoryTraceBounds.prefix_time i a coordinate ids packets fields hv fuel out hr).trans
    (timeBound_le i a coordinate ids packets fields hv)
/-- ALL115 data words AND real saved returns at every actual successful prefix. -/
theorem prefix_cells (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:Cap.Valid i a coordinate ids packets fields) (fuel:Nat)
    (out:SemiprimeD1StackCalls.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial i)=some out):
    Cap.cells out≤10^63*(Cap.capacity i+1)^12:=by
  have h:=SemiprimeD1StackChildGroupFactoryTraceBounds.prefix_cells i a coordinate ids packets fields hv fuel out hr
  have ht:=timeBound_le i a coordinate ids packets fields hv
  have hi:Cap.inputBytes i≤Cap.capacity i:=by dsimp only [Cap.capacity];omega
  have hp:Cap.capacity i+1≤(Cap.capacity i+1)^12:=Nat.le_pow (by decide:0<(12:Nat))
  dsimp only [runBound] at ht
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBounds
