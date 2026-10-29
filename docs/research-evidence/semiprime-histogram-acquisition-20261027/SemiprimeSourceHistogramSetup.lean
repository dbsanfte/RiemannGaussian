/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramHeadBits
import RiemannGaussian.SemiprimeSourceHistogramScales
import RiemannGaussian.SemiprimeSourceHistogramPortKeys

/-! # Once-acquired original inputs of the physical histogram query
Only actual sparse metadata, physical keys, compact rows/IDs and executed scale
words are stored. No score-pair list, native word function or supplied histogram
is a runtime field. All initializer reports remain in the aggregate clock.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramSetup
open SemiprimeBitArithmetic

/-- Concrete source inputs shared by every prefix/candidate score query. -/
structure Cache (n F Q : ℕ) (arity : Fin F → ℕ) where
  /-- Actual graph metadata and original encoded port records. -/
  data : SemiprimeSourceHistogramPortKeys.Acquired n F Q arity
  /-- One actually acquired bank, physical row dictionary and coordinate tags. -/
  rows : SemiprimeSourceHistogramRowKeys.QueryCache
  /-- Actual original vertex codes and physically acquired variable keys. -/
  vertices : List SemiprimeSourceHistogramHeadBits.Vertex
  /-- Actually counted and multiplied compact original score constants. -/
  scales : SemiprimeSourceHistogramScales.Cache
  /-- Coordinate count acquired by physical increments over the actual list. -/
  coordinateCount : List Bool
  /-- Every graph/key/bank/row/tag/scale/count initializer report, paid once. -/
  clock : ℕ

/-- Acquire the complete histogram-query input directly from original data. -/
def acquire (n F r Q lam : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) : Cache n F Q arity :=
  let data := SemiprimeSourceHistogramPortKeys.acquireOriginal n F Q arity owner
  let rows := SemiprimeSourceHistogramRowKeys.acquireCaches r Q
  let vertices := SemiprimeSourceHistogramHeadBits.verticesWith data.metadata.vertices
  let scales := SemiprimeSourceHistogramScales.acquire r Q lam data.records data.metadata.vertices
  let coordinates := SemiprimeSourceHistogramCountInput.count data.metadata.coordinates
  ⟨data,rows,vertices.value,scales,coordinates.bits,
    data.clock+rows.clock+vertices.work+scales.clock+coordinates.clock+8⟩

/-- The cached graph metadata is the actual new sparse original constructor. -/
theorem metadata_actual (n F r Q lam : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) :
    (acquire n F r Q lam arity owner).data.metadata=
      SemiprimeSourceHistogramMetadata.acquire n F Q arity := by
  exact SemiprimeSourceHistogramPortKeys.acquireOriginal_metadata n F Q arity owner

/-- Record contents come from actually acquired original ports, not label advice. -/
theorem records_actual (n F r Q lam : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) :
    (acquire n F r Q lam arity owner).data.records=
      (SemiprimeSourceHistogramPortKeys.acquirePorts owner
        (SemiprimeSourceHistogramMetadata.acquire n F Q arity).incidences).value := by
  change (SemiprimeSourceHistogramPortKeys.acquireOriginal n F Q arity owner).records=_
  rw [SemiprimeSourceHistogramPortKeys.acquirePorts_value]
  exact SemiprimeSourceHistogramPortKeys.acquireOriginal_records n F Q arity owner

/-- The selector and row dictionary share the same concrete original compact bank. -/
theorem bank_actual (n F r Q lam : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) :
    (acquire n F r Q lam arity owner).rows.source.bank=
      SemiprimeSourceCompactWordBank.acquire r Q :=
  SemiprimeSourceHistogramRowKeys.acquireCaches_bank r Q

/-- The original finite vertex cache is acquired once, in canonical order. -/
theorem vertices_actual (n F r Q lam : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) :
    (acquire n F r Q lam arity owner).vertices=
      (SemiprimeSourceHistogramHeadBits.verticesWith (List.finRange n)).value := by
  change (SemiprimeSourceHistogramHeadBits.verticesWith
    (SemiprimeSourceHistogramPortKeys.acquireOriginal n F Q arity owner).metadata.vertices).value=_
  rw [SemiprimeSourceHistogramPortKeys.acquireOriginal_metadata]
  simp only [SemiprimeSourceHistogramMetadata.acquire,
    SemiprimeSourceHistogramMetadata.finFast_value]

/-- The physical row and coordinate cache comes from the actual original bank. -/
theorem rows_actual (n F r Q lam : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) :
    (acquire n F r Q lam arity owner).rows=
      SemiprimeSourceHistogramRowKeys.acquireCaches r Q := rfl

/-- The coordinate magnitude is acquired from the original physical traversal. -/
theorem coordinate_value (n F r Q lam : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) :
    bitValue (acquire n F r Q lam arity owner).coordinateCount=Q := by
  change bitValue (SemiprimeSourceHistogramCountInput.count _).bits=Q
  rw [SemiprimeSourceHistogramCountInput.count_value,
    SemiprimeSourceHistogramPortKeys.acquireOriginal_metadata]
  exact (SemiprimeSourceHistogramMetadata.sizes n F Q arity).2.2.2.1

end RiemannGaussian.SemiprimeSourceHistogramSetup
