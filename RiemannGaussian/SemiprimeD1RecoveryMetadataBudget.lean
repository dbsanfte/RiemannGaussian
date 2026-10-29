/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryPhysicalBounds

/-! # Actual original recovery metadata stage bounds
These are native scalar/index/valuation/control stage counts retained by the
physical producer, not primitive-bit costs for those host representations.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1RecoveryMetadataBudget
open SemiprimeD1RecoveryScalarRun SemiprimeD1RecoveryWeightRun
open SemiprimeD1WireKernelOriginal SemiprimeD1TaperedLoss
open SemiprimeD1RecoveryNodeBits

/-- Actual original geometry acquisition has a linear native stage count. -/
theorem geometry_work (a t : ℕ) : (geometry a t).work=3*a+8 := by
  simp only [geometry,intPower_work]

/-- Explicit native grid/index/valuation ledger, without scalar height advice. -/
def gridBudget (a N : ℕ) : ℕ :=
  (3*a+8)+(4*(a+2)+4)+(N*N+4*N+1)+N*(5*N+4*(a+2)+30)+1+20

/-- The actual original physical grid retains a derived metadata stage bound. -/
theorem grid_work (template : List Bool) (a M u : ℕ) (t : Fin (size a)) :
    (SemiprimeD1RecoveryGridBits.acquire template a M u t).metadataWork ≤ gridBudget a (size a) := by
  have hl:=SemiprimeD1RecoveryGridBitsBounds.loop_metadataWork template a (height M u) u t.val
    (geometry a t.val)
    (SemiprimeD1RecoveryPowerBits.power template SemiprimeD1RecoveryGridBits.twoWord a).word
    (SemiprimeD1RecoveryPowerBits.power template SemiprimeD1RecoveryGridBits.twoWord (a+1)).word
    (SemiprimeD1RecoveryGridBits.index a t.val).word
    (indices (geometry a t.val).size).value
  have hi:=(SemiprimeEncodedRowSelection.encode_work (a+1) (t.val:ℤ)).1
  change (SemiprimeD1RecoveryGridBits.index a t.val).work=4*(a+2)+4 at hi
  simp only [indices_value,List.length_range,geometry_size] at hl
  simp only [SemiprimeD1RecoveryGridBits.acquire,geometry_work,indices_work,
    geometry_size,hi,gridBudget,indices_value]
  omega

/-- Explicit local metadata polynomial at the original retained-count and width caps. -/
def nodeBodyBudget (a N m W : ℕ) : ℕ :=
  gridBudget a N+(3*a+8)+(5*N+8)+(m*m+4*m+1)+(3*m+1)+
    (m*(m*(8*(m+1)+12)+7)+1)+W+2*m+30

/-- Pure nonnegative scalar monotonicity, isolated from actual source terms. -/
theorem node_scalar_mono {q m : ℕ} (h : q ≤ m) :
    (q*q+4*q+1)+(3*q+1)+(q*(q*(8*(q+1)+12)+7)+1)+2*q ≤
    (m*m+4*m+1)+(3*m+1)+(m*(m*(8*(m+1)+12)+7)+1)+2*m := by
  gcongr

/-- Every executed original node metadata stage is bounded from original
multiplicity, grid size and public store width; no metadata budget is advised. -/
theorem node_body_work (template : List Bool) (a M u : ℕ) (t : Fin (size a))
    (hu : u ≤ M) :
    (acquireAt template a M u t).metadataWork ≤
      nodeBodyBudget a (size a) (4*M) template.length := by
  let q:=(multiplicityRun (geometry a t.val) (height M u) u t.val).value
  have hq : q ≤ 4*M :=
    (SemiprimeD1RecoveryWeightRunBounds.multiplicity_value_le _ _ _ _).trans (SemiprimeD1WeightPrecision.height_mul_le M u hu)
  have hg:=grid_work template a M u t
  have hm:=SemiprimeD1RecoveryWeightRunBounds.multiplicity_work (geometry a t.val) (height M u) u t.val
  have hp:=SemiprimeD1RecoveryScalarWeightBits.powers_metadataWork template
    (SemiprimeD1RecoveryGridBits.acquire template a M u t).argument (indices q).value
  have hw:=SemiprimeD1RecoveryNodeBitsBounds.weights_metadataWork template q
    (SemiprimeD1RecoveryGridBits.acquire template a M u t).scalar
    (SemiprimeSourceMemoryBits.copyMemory
      (SemiprimeNormalizedInverseBits.build template
        (SemiprimeAffineJetBits.build template q
          (SemiprimeD1RecoveryGridBits.acquire template a M u t).grid.slopes).words q).words.toList).words
    (SemiprimeD1RecoveryScalarWeightBits.powers template
      (SemiprimeD1RecoveryGridBits.acquire template a M u t).argument (indices q).value).words
    (indices q).value (indices q).value
  simp only [indices_value,List.length_range] at hp hw
  have hmono:=node_scalar_mono hq
  simp only [geometry_size] at hm
  simp only [acquireAt,nodeBodyBudget,geometry_work,indices_work,indices_value]
  change _+_+_+(q*q+4*q+1)+_+_+template.length+2*q+30 ≤ _
  dsimp only [q] at hp hw hmono ⊢
  omega

/-- Whole actual node metadata envelope, including original width acquisition. -/
def nodeBudget (a M : ℕ) : ℕ :=
  3*a+308+nodeBodyBudget a (size a) (4*M) (width a M)

/-- The original internally width-initialized physical node has a closed ledger. -/
theorem node_work (a M u : ℕ) (t : Fin (size a)) (hu : u ≤ M) :
    (SemiprimeD1RecoveryNodeBits.acquire a M u t).metadataWork ≤ nodeBudget a M := by
  have h:=node_body_work (List.replicate (widthRun a M).value false) a M u t hu
  simp only [List.length_replicate,widthRun_value] at h
  change (widthRun a M).work+
    (acquireAt (List.replicate (widthRun a M).value false) a M u t).metadataWork ≤ _
  rw [widthRun_value]
  simp only [nodeBudget,widthRun,geometry_work]
  omega

/-- Explicit metadata budget for the actual full original-grid row cache. -/
def rowsBudget (a M : ℕ) : ℕ :=
  (3*a+8+(size a*size a+4*size a+1)+4*size a+3)+
    size a*(nodeBudget a M+5*(4*M)+7)+4

/-- Every right-recursive original-grid metadata frame is bounded, including
nodes whose fully acquired coefficient data are subsequently filtered out. -/
theorem gather_work (a M u : ℕ) (ts : List (Fin (size a))) (hu : u ≤ M) :
    (SemiprimeD1RecoveryRowsBits.gather a M u ts).metadataWork ≤
      ts.length*(nodeBudget a M+5*(4*M)+7)+1 := by
  induction ts with
  | nil => simp [SemiprimeD1RecoveryRowsBits.gather]
  | cons t ts ih =>
    have hc:=node_work a M u t hu
    have hl : (SemiprimeD1RecoveryNodeBits.acquire a M u t).words.length ≤ 4*M := by
      rw [SemiprimeD1RecoveryRowsBits.node_length a M u t hu]
      exact SemiprimeD1WeightPrecision.nodeMultiplicity_le a M u t.val hu
    have hp:=SemiprimeD1RecoveryRowsBits.pack_metadataWork t.val 0
      (SemiprimeD1RecoveryNodeBits.acquire a M u t).words
    have hpl:=SemiprimeD1RecoveryRowsBits.pack_length t.val 0
      (SemiprimeD1RecoveryNodeBits.acquire a M u t).words
    simp only [SemiprimeD1RecoveryRowsBits.gather,List.length_cons,Nat.add_mul,Nat.one_mul]
    split_ifs <;> dsimp only <;> omega

/-- Complete actual row-cache metadata is polynomial in original grid/count/width. -/
theorem rows_work (a M u : ℕ) (hu : u ≤ M) :
    (SemiprimeD1RecoveryRowsBits.acquire a M u).metadataWork ≤ rowsBudget a M := by
  have h:=gather_work a M u (SemiprimeD1RecoveryRowsRun.nodeIndices a).value hu
  have hl : (SemiprimeD1RecoveryRowsRun.nodeIndices a).value.length=size a := by
    have hv:=congrArg List.length (SemiprimeD1RecoveryRowsRun.nodeIndices_values a)
    simpa only [List.length_map,List.length_range] using hv
  simp only [hl] at h
  simp only [SemiprimeD1RecoveryRowsBits.acquire,rowsBudget,
    SemiprimeD1RecoveryRowsRun.nodeIndices_work]
  omega

/-- Actual fixed original-width acquisition ledger, separate from physical bits. -/
theorem width_work (a M P : ℕ) :
    (SemiprimeD1RecoveryPhysicalRun.widthRun a M P).work=9*a+724 := by
  simp only [SemiprimeD1RecoveryPhysicalRun.widthRun,
    SemiprimeD1RecoveryNodeBits.widthRun,SemiprimeD1RecoveryFinishBits.widthRun,geometry_work]
  omega

/-- Full original scalar recovery metadata envelope, without any supplied
coefficient, word-width/Fits, child answer, or metadata-work advice. -/
def budget (a M : ℕ) : ℕ :=
  rowsBudget a M+size a*(4*M)*(8*(size a+4*M+1)+6)+1+9*a+744

/-- Original physical recovery retains a closed bound on every native
index/valuation/width/control stage, in addition to its separate bit clock. -/
theorem run_metadataWork (a M u p P : ℕ) (children : List (List (List Bool))) (hu : u ≤ M) :
    (SemiprimeD1RecoveryPhysicalRun.run a M u p P children).metadataWork ≤ budget a M := by
  have hr:=rows_work a M u hu
  have he:=SemiprimeD1RecoveryPhysicalBounds.entries_metadataWork children
    (SemiprimeD1RecoveryRowsBits.acquire a M u).rows (size a+4*M+1) (by
      intro r hr
      have h:=SemiprimeD1RecoveryPhysicalBounds.row_labels a M u hu r hr
      omega)
  have hl:=SemiprimeD1RecoveryRowsBits.acquire_length a M u hu
  have hm:=Nat.mul_le_mul_right (8*(size a+4*M+1)+6) hl
  simp only [SemiprimeD1RecoveryPhysicalRun.run,SemiprimeD1RecoveryPhysicalRun.runAt,
    width_work,budget]
  omega

end RiemannGaussian.SemiprimeD1RecoveryMetadataBudget
