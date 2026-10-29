/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryNodeBitsCorrectness

/-! # Closed actual physical node-weight arithmetic clocks
The reports price executed Boolean rational arithmetic, normalization/GCD,
coefficient scans and payload copies. Typed input/valuation/control construction
remains distinctly retained native metadata, not a whole tape-machine clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1RecoveryNodeBitsBounds
open SemiprimeRationalBits SemiprimeJetBits SemiprimeJetArray
open SemiprimeD1RecoveryNodeBits SemiprimeD1RecoveryNodeBitsCorrectness
open SemiprimeD1RecoveryScalarRun SemiprimeD1RecoveryWeightRun
open SemiprimeD1WireKernelOriginal SemiprimeD1TaperedLoss
open SemiprimeD1JetRecoveryGrid

/-- Actual power-cache length is the number of original cache indices. -/
theorem powers_length (template : List Bool) (argument : RationalWord) (keys : List ℕ) :
    (SemiprimeD1RecoveryScalarWeightBits.powers template argument keys).words.length=keys.length := by
  induction keys with
  | nil => rfl
  | cons k ks ih => simp only [SemiprimeD1RecoveryScalarWeightBits.powers,List.length_cons,ih]

/-- Each acquired output weight is stored once. -/
theorem weights_length (template : List Bool) (q : ℕ) (scalar : RationalWord)
    (inverse powers : List RationalWord) (keys js : List ℕ) :
    (weights template q scalar inverse powers keys js).words.length=js.length := by
  induction js with
  | nil => rfl
  | cons j js ih => simp only [weights,List.length_cons,ih]

/-- Complete physical weight-list construction retains all local scans/GCDs. -/
theorem weights_clock (template : List Bool) (q : ℕ) (scalar : RationalWord)
    (inverse powers : List RationalWord) (keys js : List ℕ) (ht : 0 < template.length) (A : ℕ)
    (hi : inverse.length ≤ A) (hp : powers.length ≤ A)
    (hiw : ∀x∈inverse,Width x template.length) (hpw : ∀x∈powers,Width x template.length)
    (hs : Width scalar template.length) :
    (weights template q scalar inverse powers keys js).clock ≤
      js.length*(keys.length*SemiprimeD1RecoveryScalarWeightBits.sumStepBudget template.length q A+
        20000*(template.length+1)^3+10)+1 := by
  induction js with
  | nil => simp [weights]
  | cons j js ih =>
    have cur:=SemiprimeD1RecoveryScalarWeightBits.weight_clock template q j scalar inverse powers keys ht A hi hp hiw hpw hs
    simp only [weights,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Actual native address/index stages are retained for every physical weight. -/
theorem weights_metadataWork (template : List Bool) (q : ℕ) (scalar : RationalWord)
    (inverse powers : List RationalWord) (keys js : List ℕ) :
    (weights template q scalar inverse powers keys js).metadataWork ≤
      js.length*(keys.length*(8*(q+1)+12)+7)+1 := by
  induction js with
  | nil => simp [weights]
  | cons j js ih =>
    have cur:=SemiprimeD1RecoveryScalarWeightBits.sum_metadataWork template q j inverse powers keys
    simp only [weights,SemiprimeD1RecoveryScalarWeightBits.weight,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Pure monotonicity of the physical affine step budget. -/
theorem affine_step_mono (W J K : ℕ) (h : J ≤ K) :
    SemiprimeAffineJetBits.stepBudget W J ≤ SemiprimeAffineJetBits.stepBudget W K := by
  unfold SemiprimeAffineJetBits.stepBudget
  gcongr

/-- Pure monotonicity of actual scalar-scan step budgets. -/
theorem sum_step_mono (W q A m : ℕ) (hq : q ≤ m) (hA : A ≤ m) :
    SemiprimeD1RecoveryScalarWeightBits.sumStepBudget W q A ≤
      SemiprimeD1RecoveryScalarWeightBits.sumStepBudget W m m := by
  unfold SemiprimeD1RecoveryScalarWeightBits.sumStepBudget
  gcongr

/-- Pure original taper substitution in the actual grid arithmetic budget. -/
theorem grid_budget_le (a M u W : ℕ) (hM : u ≤ M) :
    SemiprimeD1RecoveryGridBitsBounds.budget a (height M u) u W ≤
      SemiprimeD1RecoveryGridBitsBounds.budget a (m M) 1 W := by
  have hm:=SemiprimeD1WeightPrecision.height_mul_le M u hM
  unfold SemiprimeD1RecoveryGridBitsBounds.budget SemiprimeD1RecoveryGridBits.frameBudget m
  simp only [Nat.mul_one]
  gcongr

/-- Literal closed physical arithmetic/read/copy node budget, entirely from
original dimensions and the internally derived common word width. -/
def budget (a M W : ℕ) : ℕ :=
  SemiprimeD1RecoveryGridBitsBounds.budget a (m M) 1 W+
  (4+slopeCount a M*SemiprimeAffineJetBits.stepBudget W (m M))+
  (1+m M*SemiprimeNormalizedInverseBitsBounds.stepBudget W (m M+1) (m M))+
  (m M*(8*W+9)+1)+(m M*(m M*(20000*(W+1)^3+4)+6)+1)+
  (m M*(m M*SemiprimeD1RecoveryScalarWeightBits.sumStepBudget W (m M) (m M)+20000*(W+1)^3+10)+1)+3*W+30

/-- Actual original node arithmetic clock has no callback, operation-count,
Fits, source array or weight advice premise. -/
theorem acquireAt_clock (template : List Bool) (a M u : ℕ) (t : Fin (size a))
    (hM : u ≤ M) (hW : width a M ≤ template.length) :
    (acquireAt template a M u t).clock ≤ budget a M template.length := by
  let q:=nodeMultiplicity a (height M u) u t.val
  let grid:=SemiprimeD1RecoveryGridBits.acquire template a M u t
  let den:=SemiprimeAffineJetBits.build template q grid.grid.slopes
  let inv:=SemiprimeNormalizedInverseBits.build template den.words q
  let memory:=SemiprimeSourceMemoryBits.copyMemory inv.words.toList
  let keys:=(indices q).value
  let powers:=SemiprimeD1RecoveryScalarWeightBits.powers template grid.argument keys
  let rows:=weights template q grid.scalar memory.words powers.words keys keys
  have ht : 0 < template.length := lt_of_lt_of_le (width_caps a M).2.2.2.2.2.2.2 hW
  have hq : q ≤ m M := SemiprimeD1WeightPrecision.nodeMultiplicity_le a M u t.val hM
  have gw:=(grid_width_le a M u hM).trans hW
  have cg:=SemiprimeD1RecoveryGridBitsBounds.acquire_clock template a M u t gw
  have cgMax:=(grid_budget_le a M u template.length hM)
  have hs:=SemiprimeD1RecoveryGridBits.acquire_grid_correct template a M u t gw
  have hl : grid.grid.slopes.length ≤ slopeCount a M := by
    have hm:=congrArg List.length hs.2.2.1
    rw [fullGrid_slopes] at hm
    have hb:=slopes_length_le a M u t.val hM
    simp only [List.length_map] at hm
    change grid.grid.slopes.length=_ at hm
    omega
  have hsw : ∀x∈grid.grid.slopes,Width x template.length := hs.2.2.2.2.2.2.2.2
  have cd:=SemiprimeAffineJetBits.build_clock template q grid.grid.slopes ht hsw
  have dstep:=affine_step_mono template.length q (m M) hq
  have dMax : grid.grid.slopes.length*SemiprimeAffineJetBits.stepBudget template.length q ≤
      slopeCount a M*SemiprimeAffineJetBits.stepBudget template.length (m M) := Nat.mul_le_mul hl dstep
  have dw:=SemiprimeAffineJetBits.build_bounded template q grid.grid.slopes ht
  have dsize : den.words.size ≤ m M+1 := by
    change (SemiprimeAffineJetBits.build template q grid.grid.slopes).words.size ≤ _
    rw [SemiprimeAffineJetBits.build_size]
    split_ifs <;> omega
  have ci:=SemiprimeNormalizedInverseBitsBounds.build_clock template ht den.words (m M+1) (m M) dsize dw q hq
  have iw:=SemiprimeNormalizedInverseBits.build_bounded template ht den.words q
  have imw : ∀x∈inv.words.toList,Width x template.length := toList_bounded inv.words template.length iw
  have cm:=SemiprimeSourceMemoryBits.copyMemory_clock inv.words.toList template.length imw
  have mlen : memory.words.length=q := by
    simp only [memory,SemiprimeSourceMemoryBits.copyMemory_words,Array.length_toList,inv,SemiprimeNormalizedInverseBits.build_size]
  have mw : ∀x∈memory.words,Width x template.length := by rw [SemiprimeSourceMemoryBits.copyMemory_words]; exact imw
  have xw:=(SemiprimeD1RecoveryGridBits.acquire_argument_correct template a M u t gw).2.2
  have sw:=(SemiprimeD1RecoveryGridBits.acquire_scalar_correct template a M u t gw).2.2
  have hk : ∀k∈keys,k ≤ q := by simp only [keys,indices_value,List.mem_range]; exact fun k h => h.le
  have cp:=SemiprimeD1RecoveryScalarWeightBits.powers_clock template grid.argument q ht xw keys hk
  have pw : ∀x∈powers.words,Width x template.length := by
    have hx:=SemiprimeD1RecoveryGridBits.acquire_argument_correct template a M u t gw
    have caps:=scalar_caps a M u t.val hM
    exact (SemiprimeD1RecoveryScalarWeightBits.powers_correct template a (height M u) u t
      grid.argument hx.1 hx.2.1 (caps.2.2.trans hW) keys hk).2.2
  have plen : powers.words.length=q := by rw [powers_length]; simp [keys,indices_value]
  have cw:=weights_clock template q grid.scalar memory.words powers.words keys keys ht q
    (by rw [mlen]) (by rw [plen]) mw pw sw
  have klen : keys.length=q := by simp [keys,indices_value]
  rw [klen] at cp cw
  have istep:=Nat.mul_le_mul_right (SemiprimeNormalizedInverseBitsBounds.stepBudget template.length (m M+1) (m M)) hq
  have mcopy:=Nat.mul_le_mul_right (8*template.length+9) hq
  have pMax : q*(q*(20000*(template.length+1)^3+4)+6) ≤
      m M*(m M*(20000*(template.length+1)^3+4)+6) := by gcongr
  have sstep:=sum_step_mono template.length q q (m M) hq hq
  have wMax : q*(q*SemiprimeD1RecoveryScalarWeightBits.sumStepBudget template.length q q+
      20000*(template.length+1)^3+10) ≤
      m M*(m M*SemiprimeD1RecoveryScalarWeightBits.sumStepBudget template.length (m M) (m M)+
        20000*(template.length+1)^3+10) := by gcongr
  change _ ≤ budget a M template.length
  simp only [acquireAt,multiplicityRun_value a (height M u) u t.val t.val t.isLt]
  change grid.clock+den.clock+inv.clock+memory.clock+powers.clock+rows.clock+3*template.length+30 ≤ _
  unfold budget
  have ilen : inv.words.toList.length=q := by simp [inv,SemiprimeNormalizedInverseBits.build_size]
  rw [ilen] at cm
  dsimp only [q,grid,den,inv,memory,keys,powers,rows] at *
  omega

/-- ORIGINAL public node entry acquires its own template; no width advice. -/
theorem acquire_clock (a M u : ℕ) (t : Fin (size a)) (hM : u ≤ M) :
    (SemiprimeD1RecoveryNodeBits.acquire a M u t).clock ≤ budget a M (width a M) := by
  have h:=acquireAt_clock (List.replicate (width a M) false) a M u t hM (by simp)
  simpa only [SemiprimeD1RecoveryNodeBits.acquire,widthRun_value,List.length_replicate] using h

end RiemannGaussian.SemiprimeD1RecoveryNodeBitsBounds
