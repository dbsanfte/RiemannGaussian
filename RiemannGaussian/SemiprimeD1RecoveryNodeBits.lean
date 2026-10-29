/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryScalarWeightBits
import RiemannGaussian.SemiprimeD1RecoveryAffineBits
import RiemannGaussian.SemiprimeNormalizedInverseBitsBounds

/-! # Actual original-input physical D.9 weight acquisition
Grid coefficients, local affine/inverse arrays, powers, scalar sums and canonical
row payloads are acquired on Boolean words. The typed original grid/multiplicity
and address-generation control remains separately retained native metadata.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1RecoveryNodeBits
open SemiprimeRationalBits SemiprimeJetBits SemiprimeJetArray SemiprimeJetArrayHeight
open SemiprimeD1RecoveryScalarRun SemiprimeD1RecoveryWeightRun
open SemiprimeD1WireKernelOriginal SemiprimeD1TaperedLoss SemiprimeD1JetRecoveryGrid
open SemiprimeD1HermiteDenominatorHeight SemiprimeD1HermiteDenominatorBits
open SemiprimeD1HermiteWeightHeight SemiprimeD1HermiteWeightBits
open SemiprimeLocalExecutionHeight

/-- Original upper bound for every retained local multiplicity. -/
def m (M : ℕ) : ℕ := 4*M
/-- Original upper bound on actual repeated slopes. -/
def slopeCount (a M : ℕ) : ℕ := size a*m M
/-- Slope common-denominator/numerator and degree input exponent. -/
def affineBits (a M : ℕ) : ℕ := (size a+1)*(slopeCount a M+1)+m M+1
/-- Exponent for actual local cardinal coefficients supplied to physical inversion. -/
def inverseBits (a M : ℕ) : ℕ := (a+1)*slopeCount a M+(m M+a+1)*slopeCount a M+1
/-- Original upper bound on the NEW right-recursive scalar-sum exponent. -/
def sumBits (a M : ℕ) : ℕ := m M+inverseEnvelope a M+(a+1)*m M+1

/-- Literal fixed polynomial in independent original grid dimensions. -/
def widthPolynomial (a M N : ℕ) : ℕ :=
  ((a+1)*(4*M)*N+(a+1)*(a+1)+a+10)+
  SemiprimeAffineJetBits.width ((N+1)*(N*(4*M)+1)+4*M+1) (N*(4*M))+
  SemiprimeNormalizedInverseBits.inverseWidth ((a+1)*(N*(4*M))+(4*M+a+1)*(N*(4*M))+1) (4*M)+
  weightPolynomial a M N+(4*M+inversePolynomial a M N+(a+1)*(4*M)+1)+
  (a+1)*(4*M)+inversePolynomial a M N+20

/-- Complete original-dimension physical rational template. -/
def width (a M : ℕ) : ℕ := widthPolynomial a M (size a)

/-- All original width components, with no source coefficient/height input. -/
theorem width_expanded (a M : ℕ) : width a M=
    SemiprimeD1RecoveryGridBits.gridWidth a (m M) 1+
    SemiprimeAffineJetBits.width (affineBits a M) (slopeCount a M)+
    SemiprimeNormalizedInverseBits.inverseWidth (inverseBits a M) (m M)+
    weightEnvelope a M+sumBits a M+(a+1)*m M+inverseEnvelope a M+20 := by
  simp only [width,widthPolynomial,SemiprimeD1RecoveryGridBits.gridWidth,m,affineBits,slopeCount,inverseBits,
    sumBits,weightEnvelope_eq,weightPolynomial,inversePolynomial,inverseEnvelope,Nat.mul_one]

/-- All actual later phases fit the internally computed common template. -/
theorem width_caps (a M : ℕ) :
    SemiprimeD1RecoveryGridBits.gridWidth a (m M) 1 ≤ width a M ∧
    SemiprimeAffineJetBits.width (affineBits a M) (slopeCount a M) ≤ width a M ∧
    SemiprimeNormalizedInverseBits.inverseWidth (inverseBits a M) (m M) ≤ width a M ∧
    weightEnvelope a M < width a M ∧ sumBits a M < width a M ∧
    (a+1)*m M+1 ≤ width a M ∧ inverseEnvelope a M+(a+1)*m M < width a M ∧ 0 < width a M := by
  rw [width_expanded]
  unfold sumBits
  omega

/-- Actual original-grid width acquisition, separate native scalar metadata. -/
def widthRun (a M : ℕ) : Run ℕ :=
  let geometry:=SemiprimeD1RecoveryWeightRun.geometry a 0
  ⟨widthPolynomial a M geometry.size,geometry.work+300⟩

/-- The width is acquired internally from original geometry. -/
theorem widthRun_value (a M : ℕ) : (widthRun a M).value=width a M := by
  simp only [widthRun,geometry_size,width]

/-- Actual computed local weight words and retained physical/native reports. -/
structure WeightsReport where
  /-- Canonical rational words in original retained-index order. -/
  words : List RationalWord
  /-- Actual arithmetic, normalization/GCD and coefficient scans. -/
  clock : ℕ
  /-- Native original index/address construction and loop stages. -/
  metadataWork : ℕ

/-- Each original local coefficient is computed once from the same acquired caches. -/
def weights (template : List Bool) (q : ℕ) (scalar : RationalWord)
    (inverse powers : List RationalWord) (keys : List ℕ) : List ℕ → WeightsReport
  | [] => ⟨[],1,1⟩
  | j::js =>
    let tail:=weights template q scalar inverse powers keys js
    let current:=SemiprimeD1RecoveryScalarWeightBits.weight template q j scalar inverse powers keys
    ⟨current.word::tail.words,current.clock+tail.clock+4,current.metadataWork+tail.metadataWork+4⟩

/-- Actual original physical node weights, with no scalar coefficient supplier. -/
structure Report where
  /-- Actual acquired retained multiplicity. -/
  retained : ℕ
  /-- Actual physical canonical weight rows. -/
  words : List RationalWord
  /-- Every coefficient-data Boolean arithmetic/normalization/read/copy report. -/
  clock : ℕ
  /-- All typed input/index/control/width-generation native stages retained apart. -/
  metadataWork : ℕ

/-- Original node producer: original inputs -> actual physical grid -> actual
physical local cardinal/inverse arrays -> cached physical powers -> canonical
weight words. No native rational coefficient, canonical field or Fits oracle. -/
def acquireAt (template : List Bool) (a M u : ℕ) (t : Fin (size a)) : Report :=
  let grid:=SemiprimeD1RecoveryGridBits.acquire template a M u t
  let g:=geometry a t.val
  let retained:=multiplicityRun g (height M u) u t.val
  let q:=retained.value
  let denominator:=SemiprimeAffineJetBits.build template q grid.grid.slopes
  let inverse:=SemiprimeNormalizedInverseBits.build template denominator.words q
  let memory:=SemiprimeSourceMemoryBits.copyMemory inverse.words.toList
  let keys:=indices q
  let powers:=SemiprimeD1RecoveryScalarWeightBits.powers template grid.argument keys.value
  let rows:=weights template q grid.scalar memory.words powers.words keys.value keys.value
  ⟨q,rows.words,
    grid.clock+denominator.clock+inverse.clock+memory.clock+powers.clock+rows.clock+3*template.length+30,
    grid.metadataWork+g.work+retained.work+keys.work+powers.metadataWork+rows.metadataWork+template.length+2*q+30⟩

/-- Original-input entry point ACTUALLY acquires its own numerical template. -/
def acquire (a M u : ℕ) (t : Fin (size a)) : Report :=
  let W:=widthRun a M
  let body:=acquireAt (List.replicate W.value false) a M u t
  ⟨body.retained,body.words,body.clock,W.work+body.metadataWork⟩

/-- The physical producer acquires the original multiplicity, not an advised count. -/
theorem acquire_retained (a M u : ℕ) (t : Fin (size a)) :
    (acquire a M u t).retained=nodeMultiplicity a (height M u) u t.val :=
  multiplicityRun_value a (height M u) u t.val t.val t.isLt

/-- Original taper bounds give the actual grid primitive its needed template. -/
theorem grid_width_le (a M u : ℕ) (hM : u ≤ M) :
    SemiprimeD1RecoveryGridBits.gridWidth a (height M u) u ≤ width a M := by
  apply le_trans _ (width_caps a M).1
  have hm:=SemiprimeD1WeightPrecision.height_mul_le M u hM
  unfold SemiprimeD1RecoveryGridBits.gridWidth m
  simp only [Nat.mul_one]
  gcongr

/-- Actual original slope cardinality is bounded before any coefficient is read. -/
theorem slopes_length_le (a M u t : ℕ) (hM : u ≤ M) :
    (SemiprimeD1JetRecoveryWeights.slopes a (height M u) u t).length ≤ slopeCount a M := by
  have hl:=original_slopes_length a (height M u) u t
  have hm:=Nat.mul_le_mul_left (size a) (SemiprimeD1WeightPrecision.height_mul_le M u hM)
  exact hl.trans (by simpa only [slopeCount,m,Nat.mul_assoc] using hm)

/-- The original retained scalar-sum/weight exponents fit the acquired template. -/
theorem scalar_caps (a M u t : ℕ) (hM : u ≤ M) :
    SemiprimeD1RecoveryWeightRunState.sumExponent a (height M u) u t < width a M ∧
    SemiprimeD1HermiteWeightBits.weightExponent a (height M u) u t < width a M ∧
    (a+1)*nodeMultiplicity a (height M u) u t+1 ≤ width a M := by
  have hs:=SemiprimeD1RecoveryWeightRunState.original_sumExponent_le a M u t hM
  have hw:=original_weightExponent_le a M u t hM
  have hq:=SemiprimeD1WeightPrecision.nodeMultiplicity_le a M u t hM
  have caps:=width_caps a M
  refine ⟨hs.trans_lt caps.2.2.2.2.1,hw.trans_lt caps.2.2.2.1,?_⟩
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left (a+1) hq) 1).trans caps.2.2.2.2.2.1

/-- Original canonical slope denominators/numerators supply the generalized
physical affine builder, including its constant-one guard d<=B. -/
theorem affine_parameters (a M u : ℕ) (t : Fin (size a)) (hM : u ≤ M) :
    let D:=sourceDenominator a (height M u) u t.val
    0 < D ∧ D ≤ D*size a ∧ D ≤ 2^affineBits a M ∧ D*size a ≤ 2^affineBits a M ∧
    nodeMultiplicity a (height M u) u t.val ≤ 2^affineBits a M ∧
    (∀c∈SemiprimeD1JetRecoveryWeights.slopes a (height M u) u t.val,
      Representation c D (D*size a)) := by
  dsimp only
  let N:=size a
  let cs:=SemiprimeD1JetRecoveryWeights.slopes a (height M u) u t.val
  let D:=sourceDenominator a (height M u) u t.val
  let T:=slopeCount a M
  have hN : 0 < N := by unfold N size; positivity
  have hd : 0 < D := sourceDenominator_pos _ _ _ _
  have hDB : D ≤ D*N := Nat.le_mul_of_pos_right _ hN
  have hl : cs.length ≤ T := slopes_length_le a M u t.val hM
  have hDc : D ≤ N^cs.length := commonDenominator_le N cs (by
    intro c hc
    exact (original_slope_bounds a (height M u) u t c hc).1)
  have hDT : D ≤ N^T := hDc.trans (Nat.pow_le_pow_right hN hl)
  have hp : N^T*N ≤ N^(T+1) := by rw [pow_succ]
  have hBT : D*N ≤ N^(T+1) := (Nat.mul_le_mul_right N hDT).trans hp
  have hBN : N^(T+1) ≤ 2^(N*(T+1)) := by
    simpa only [← pow_mul] using Nat.pow_le_pow_left (self_le_two_power N) (T+1)
  have hBex : N*(T+1) ≤ affineBits a M := by
    change N*(T+1) ≤ (N+1)*(T+1)+m M+1
    have hh:=Nat.mul_le_mul_right (T+1) (Nat.le_succ N)
    simp only [Nat.succ_eq_add_one] at hh
    omega
  have hB : D*N ≤ 2^affineBits a M := hBT.trans (hBN.trans (Nat.pow_le_pow_right (by decide) hBex))
  have hq:=SemiprimeD1WeightPrecision.nodeMultiplicity_le a M u t.val hM
  have hm : m M ≤ affineBits a M := by unfold affineBits; omega
  refine ⟨hd,hDB,hDB.trans hB,hB,hq.trans (hm.trans (self_le_two_power _)),?_⟩
  intro c hc
  exact SemiprimeD1RecoveryAffineBits.slope_common_representation cs N c hc
    (original_slope_bounds a (height M u) u t c hc).2

/-- Original source denominator and numerator exponents are bounded before
physical inverse execution, without an input array/height oracle. -/
theorem inverse_parameters (a M u : ℕ) (t : Fin (size a)) (hM : u ≤ M) :
    sourceDenominator a (height M u) u t.val ≤ 2^inverseBits a M ∧
    sourceNumerator a (height M u) u t.val ≤ 2^inverseBits a M := by
  have hd:=SemiprimeD1HermiteDenominatorBits.denominator_bound a (height M u) u t
  have hn:=SemiprimeD1HermiteDenominatorBits.numerator_bound a (height M u) u t.val
  have hl:=slopes_length_le a M u t.val hM
  have hq:=SemiprimeD1WeightPrecision.nodeMultiplicity_le a M u t.val hM
  have heD : denominatorExponent a (height M u) u t.val ≤ (a+1)*slopeCount a M := by
    exact Nat.mul_le_mul_left _ hl
  have heN : numeratorExponent a (height M u) u t.val ≤ (m M+a+1)*slopeCount a M := by
    unfold numeratorExponent
    exact Nat.mul_le_mul (by dsimp only [m]; omega) hl
  constructor
  · apply hd.trans
    apply Nat.pow_le_pow_right (by decide)
    unfold inverseBits
    omega
  · apply hn.trans
    apply Nat.pow_le_pow_right (by decide)
    unfold inverseBits
    omega

/-- Actual original physical local-cardinal array, with no supplied coefficient bank. -/
theorem denominator_correct (template : List Bool) (a M u : ℕ) (t : Fin (size a))
    (hM : u ≤ M) (hW : width a M ≤ template.length) :
    let grid:=SemiprimeD1RecoveryGridBits.acquire template a M u t
    let q:=nodeMultiplicity a (height M u) u t.val
    let den:=SemiprimeAffineJetBits.build template q grid.grid.slopes
    decode den.words=(SemiprimeD1JetRecoveryWeights.acquire a (height M u) u t.val).denominator.coefficients ∧
      Valid den.words ∧ Bounded den.words template.length := by
  dsimp only
  let q:=nodeMultiplicity a (height M u) u t.val
  let grid:=SemiprimeD1RecoveryGridBits.acquire template a M u t
  let cs:=grid.grid.slopes
  let D:=sourceDenominator a (height M u) u t.val
  have hw:= (grid_width_le a M u hM).trans hW
  have hg:=SemiprimeD1RecoveryGridBits.acquire_grid_correct template a M u t hw
  rcases hg with ⟨hn,hd,hs,hvn,hvd,hvs,hwn,hwd,hws⟩
  rw [fullGrid_slopes] at hs
  have hmap : cs.map RationalWord.value=SemiprimeD1JetRecoveryWeights.slopes a (height M u) u t.val := hs
  have hl : cs.length ≤ slopeCount a M := by
    have he:=congrArg List.length hmap
    have hh:=slopes_length_le a M u t.val hM
    simp only [List.length_map] at he
    omega
  have params:=affine_parameters a M u t hM
  have hinput : ∀c∈cs,c.Valid ∧ Representation c.value D (D*size a) := by
    intro c hc
    refine ⟨hvs c hc,?_⟩
    have hm : c.value∈cs.map RationalWord.value := List.mem_map.mpr ⟨c,hc,rfl⟩
    rw [hmap] at hm
    exact params.2.2.2.2.2 c.value hm
  have hwidth : SemiprimeAffineJetBits.width (affineBits a M) cs.length ≤ template.length := by
    apply le_trans _ ((width_caps a M).2.1.trans hW)
    unfold SemiprimeAffineJetBits.width
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right hl 1)) 1
  have hbuild:=SemiprimeD1RecoveryAffineBits.build_correct template (affineBits a M) q D (D*size a) cs
    params.1 params.2.1 params.2.2.1 params.2.2.2.1 params.2.2.2.2.1 hwidth hinput
  have heq : decode (SemiprimeAffineJetBits.build template q cs).words=
      (SemiprimeD1JetRecoveryWeights.acquire a (height M u) u t.val).denominator.coefficients := by
    rw [hbuild.1,hmap]
    rfl
  refine ⟨heq,hbuild.2.1,?_⟩
  exact SemiprimeAffineJetBits.build_bounded template q cs (lt_of_lt_of_le (width_caps a M).2.2.2.2.2.2.2 hW)

/-- Derived original input caps cover the actual physical inverse template. -/
theorem inverse_width_le (a M u t : ℕ) (hM : u ≤ M) :
    SemiprimeNormalizedInverseBits.inverseWidth (inverseBits a M) (nodeMultiplicity a (height M u) u t) ≤ width a M := by
  apply le_trans _ (width_caps a M).2.2.1
  have hq:=SemiprimeD1WeightPrecision.nodeMultiplicity_le a M u t hM
  unfold SemiprimeNormalizedInverseBits.inverseWidth
  dsimp only [m]
  gcongr

/-- The actual physical cached inverse agrees with the original array loop.
Original coefficients, constant1 and capacities are derived internally. -/
theorem inverse_correct (template : List Bool) (a M u : ℕ) (t : Fin (size a))
    (hM : u ≤ M) (hW : width a M ≤ template.length) :
    let grid:=SemiprimeD1RecoveryGridBits.acquire template a M u t
    let q:=nodeMultiplicity a (height M u) u t.val
    let den:=SemiprimeAffineJetBits.build template q grid.grid.slopes
    let inv:=SemiprimeNormalizedInverseBits.build template den.words q
    decode inv.words=(SemiprimeD1JetRecoveryWeights.acquire a (height M u) u t.val).inverse.coefficients ∧
      Valid inv.words ∧ Bounded inv.words template.length := by
  dsimp only
  let q:=nodeMultiplicity a (height M u) u t.val
  let grid:=SemiprimeD1RecoveryGridBits.acquire template a M u t
  let den:=SemiprimeAffineJetBits.build template q grid.grid.slopes
  let inv:=SemiprimeNormalizedInverseBits.build template den.words q
  let D:=sourceDenominator a (height M u) u t.val
  let B:=sourceNumerator a (height M u) u t.val
  have hd:=denominator_correct template a M u t hM hW
  have ht : 0 < template.length := lt_of_lt_of_le (width_caps a M).2.2.2.2.2.2.2 hW
  have bounded:=SemiprimeNormalizedInverseBits.build_bounded template ht den.words q
  by_cases hq : q=0
  · refine ⟨?_,?_,bounded⟩
    · change decode (SemiprimeNormalizedInverseBits.build template den.words q).words=_
      simp only [hq,SemiprimeNormalizedInverseBits.build,decode,Array.map_empty]
      change #[]=(SemiprimeJetArray.inverse _ q).coefficients
      rw [hq]
      rfl
    · change Valid (SemiprimeNormalizedInverseBits.build template den.words q).words
      simp only [hq,SemiprimeNormalizedInverseBits.build]
      intro i hi
      simp at hi
  · have hpos : 0 < q := by omega
    have hzero : coefficient (decode den.words) 0=1 := by
      rw [hd.1]
      exact SemiprimeD1JetRecoveryWeights.acquire_denominator_constant a (height M u) u t.val hpos
    have hrep : ∀i<q,Representation (coefficient (decode den.words) i) D B := by
      intro i hi
      rw [hd.1]
      exact original_denominator_representation a (height M u) u t i hi
    have hp:=inverse_parameters a M u t hM
    have hi:=SemiprimeNormalizedInverseBits.build_correct_of_width template den.words D B
      (inverseBits a M) q (sourceDenominator_pos _ _ _ _) hd.2.1 hzero hrep hp.1 hp.2
      ((inverse_width_le a M u t.val hM).trans hW)
    refine ⟨?_,hi.2,bounded⟩
    have heq : decode inv.words=(SemiprimeJetArray.inverse (decode den.words) q).coefficients := by
      rw [hi.1]
      simp only [SemiprimeJetArray.inverse,hzero,inv_one]
    rw [heq,hd.1]
    rfl

end RiemannGaussian.SemiprimeD1RecoveryNodeBits
