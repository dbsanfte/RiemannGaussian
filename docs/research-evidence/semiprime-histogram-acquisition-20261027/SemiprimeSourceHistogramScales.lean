/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramCountInput
import RiemannGaussian.SemiprimeSourceCountPowers

/-! # Actual compact scale/weight cache from original dimensions and lists
Record/vertex counts are acquired by inspecting their actual lists. Original r
and lambda use the paid native encoder and are trimmed BEFORE powers or weights.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramScales
open SemiprimeBitArithmetic SemiprimeSourceOffsetInputsCore
open SemiprimeSourceCompactBits (Compact Report)

/-- Original native parameter encoding is paid explicitly and compacted immediately. -/
def natural (n : ℕ) : Report :=
  let raw := natBits n
  let out := SemiprimeSourceCompactBits.trim raw.bits
  ⟨out.bits,raw.clock+out.clock+5⟩

/-- Physical power construction followed by actual compact normalization. -/
def power (base : List Bool) (k : ℕ) : Report :=
  let raw := SemiprimeSourceCountPowers.powerBits base k
  let out := SemiprimeSourceCompactBits.trim raw.bits
  ⟨out.bits,raw.clock+out.clock+5⟩

/-- Actual multiplication and compact output, without a numeric product answer. -/
def product (a b : List Bool) : Report :=
  let raw := mulBits a b
  let out := SemiprimeSourceCompactBits.trim raw.bits
  ⟨out.bits,bitCost raw+out.clock+5⟩

/-- Original seven-product weight constructor with both physical outputs trimmed. -/
def weights (M n lam U : List Bool) : SemiprimeSourceScoreWeightBits.Weights :=
  let raw := SemiprimeSourceScoreWeightBits.weights M n lam U
  let a := SemiprimeSourceCompactBits.trim raw.incidence
  let b := SemiprimeSourceCompactBits.trim raw.head
  ⟨a.bits,b.bits,raw.clock+a.clock+b.clock+5⟩

/-- Actual query constants and weights, without a native cardinality answer field. -/
structure Cache where
  /-- Alphabet size L acquired by physical power. -/
  alphabet : List Bool
  /-- Actual square L². -/
  square : List Bool
  /-- Actual fourth power L⁴. -/
  fourth : List Bool
  /-- Distinct-key head collision value r^(4Q−1), unused when Q=0. -/
  head : List Bool
  /-- Original integer weights with actual compact physical outputs. -/
  weights : SemiprimeSourceScoreWeightBits.Weights
  /-- All record counts, original encodings, powers, products, trims and weight work. -/
  clock : ℕ

/-- Original-input endpoint: actual metadata lists determine both count operands. -/
def acquire {A B : Type*} (r Q lam : ℕ) (records : List A) (vertices : List B) : Cache :=
  let M := SemiprimeSourceHistogramCountInput.count records
  let n := SemiprimeSourceHistogramCountInput.count vertices
  let base := natural r
  let lambda := natural lam
  let L := power base.bits Q
  let L2 := product L.bits L.bits
  let L4 := product L2.bits L2.bits
  let G := power base.bits (4*Q-1)
  let w := weights M.bits n.bits lambda.bits L2.bits
  ⟨L.bits,L2.bits,L4.bits,G.bits,w,
    M.clock+n.clock+base.clock+lambda.clock+L.clock+L2.clock+L4.clock+G.clock+w.clock+20⟩

/-- Actual natural encoder value. -/
theorem natural_value (n : ℕ) : bitValue (natural n).bits=n := by
  simp only [natural,SemiprimeSourceCompactBits.trim_value,natBits_value]

/-- Actual physical power value. -/
theorem power_value (base : List Bool) (k : ℕ) : bitValue (power base k).bits=bitValue base^k := by
  simp only [power,SemiprimeSourceCompactBits.trim_value,SemiprimeSourceCountPowers.powerBits_value]

/-- Actual physical product value. -/
theorem product_value (a b : List Bool) : bitValue (product a b).bits=bitValue a*bitValue b := by
  simp only [product,SemiprimeSourceCompactBits.trim_value,mulBits_correct]

/-- Trimming the actual weight reports preserves the original incidence coefficient. -/
theorem weights_incidence_value (M n lam U : List Bool) :
    bitValue (weights M n lam U).incidence=bitValue n^2*bitValue lam^2*bitValue U^2 := by
  simp only [weights,SemiprimeSourceCompactBits.trim_value]
  exact (SemiprimeSourceScoreWeightBits.weights_value M n lam U).1

/-- Trimming the actual weight reports preserves the original head coefficient. -/
theorem weights_head_value (M n lam U : List Bool) :
    bitValue (weights M n lam U).head=4*bitValue M^2 := by
  simp only [weights,SemiprimeSourceCompactBits.trim_value]
  exact (SemiprimeSourceScoreWeightBits.weights_value M n lam U).2

/-- All cached values follow actual list counting and executed arithmetic. -/
theorem acquire_values {A B : Type*} (r Q lam : ℕ) (records : List A) (vertices : List B) :
    bitValue (acquire r Q lam records vertices).alphabet=r^Q ∧
    bitValue (acquire r Q lam records vertices).square=(r^Q)^2 ∧
    bitValue (acquire r Q lam records vertices).fourth=(r^Q)^4 ∧
    bitValue (acquire r Q lam records vertices).head=r^(4*Q-1) ∧
    bitValue (acquire r Q lam records vertices).weights.incidence=
      vertices.length^2*lam^2*(r^Q)^4 ∧
    bitValue (acquire r Q lam records vertices).weights.head=4*records.length^2 := by
  simp only [acquire,power_value,product_value,natural_value,weights_incidence_value,
    weights_head_value,SemiprimeSourceHistogramCountInput.count_value]
  constructor
  · trivial
  constructor
  · ring
  constructor
  · ring
  constructor
  · trivial
  constructor
  · ring
  · trivial

/-- Every natural output is actual compact physical bits. -/
theorem natural_compact (n : ℕ) : Compact (natural n).bits := SemiprimeSourceCompactBits.trim_compact _

/-- Every power output is actual compact physical bits. -/
theorem power_compact (base : List Bool) (k : ℕ) : Compact (power base k).bits :=
  SemiprimeSourceCompactBits.trim_compact _

/-- Every product output is actual compact physical bits. -/
theorem product_compact (a b : List Bool) : Compact (product a b).bits :=
  SemiprimeSourceCompactBits.trim_compact _

/-- Both query weights are physically trimmed, not just numerically bounded. -/
theorem weights_compact (M n lam U : List Bool) :
    Compact (weights M n lam U).incidence ∧ Compact (weights M n lam U).head :=
  ⟨SemiprimeSourceCompactBits.trim_compact _,SemiprimeSourceCompactBits.trim_compact _⟩

/-- All six original cache outputs are canonical physical magnitudes. -/
theorem acquire_compact {A B : Type*} (r Q lam : ℕ) (records : List A) (vertices : List B) :
    Compact (acquire r Q lam records vertices).alphabet ∧
    Compact (acquire r Q lam records vertices).square ∧
    Compact (acquire r Q lam records vertices).fourth ∧
    Compact (acquire r Q lam records vertices).head ∧
    Compact (acquire r Q lam records vertices).weights.incidence ∧
    Compact (acquire r Q lam records vertices).weights.head :=
  ⟨power_compact _ _,product_compact _ _,product_compact _ _,power_compact _ _,
    (weights_compact _ _ _ _).1,(weights_compact _ _ _ _).2⟩

/-- Actual compact natural operands have logarithmic widths BEFORE their consumers. -/
theorem natural_length (n : ℕ) : (natural n).bits.length ≤ Nat.clog 2 (n+1) := by
  have h := SemiprimeSourceCompactBits.compact_length_clog _ (natural_compact n)
  simpa only [natural_value] using h

/-- All cache widths follow original values and actual compactness, with no Fits advice. -/
theorem acquire_lengths {A B : Type*} (r Q lam : ℕ) (records : List A) (vertices : List B) :
    (acquire r Q lam records vertices).alphabet.length ≤ Nat.clog 2 (r^Q+1) ∧
    (acquire r Q lam records vertices).square.length ≤ Nat.clog 2 ((r^Q)^2+1) ∧
    (acquire r Q lam records vertices).fourth.length ≤ Nat.clog 2 ((r^Q)^4+1) ∧
    (acquire r Q lam records vertices).head.length ≤ Nat.clog 2 (r^(4*Q-1)+1) ∧
    (acquire r Q lam records vertices).weights.incidence.length ≤
      Nat.clog 2 (vertices.length^2*lam^2*(r^Q)^4+1) ∧
    (acquire r Q lam records vertices).weights.head.length ≤ Nat.clog 2 (4*records.length^2+1) := by
  have hc := acquire_compact r Q lam records vertices
  have hv := acquire_values r Q lam records vertices
  exact ⟨by simpa only [hv.1] using SemiprimeSourceCompactBits.compact_length_clog _ hc.1,
    by simpa only [hv.2.1] using SemiprimeSourceCompactBits.compact_length_clog _ hc.2.1,
    by simpa only [hv.2.2.1] using SemiprimeSourceCompactBits.compact_length_clog _ hc.2.2.1,
    by simpa only [hv.2.2.2.1] using SemiprimeSourceCompactBits.compact_length_clog _ hc.2.2.2.1,
    by simpa only [hv.2.2.2.2.1] using SemiprimeSourceCompactBits.compact_length_clog _ hc.2.2.2.2.1,
    by simpa only [hv.2.2.2.2.2] using SemiprimeSourceCompactBits.compact_length_clog _ hc.2.2.2.2.2⟩

end RiemannGaussian.SemiprimeSourceHistogramScales
