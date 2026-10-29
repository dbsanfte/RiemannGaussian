/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryGridBits

/-! # Actual physical grid acquisition clocks
Every rational arithmetic stage invokes the Boolean/GCD/division primitive.
Native typed input/index/valuation stages are explicitly retained separately.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1RecoveryGridBitsBounds
open SemiprimeRationalBits SemiprimeJetBits SemiprimeBitArithmetic
open SemiprimeD1RecoveryGridBits SemiprimeD1RecoveryWeightRun SemiprimeD1RecoveryScalarRun
open SemiprimeD1RecoveryPowerBits SemiprimeSourceMemoryBits
open SemiprimeD1WireKernelOriginal SemiprimeD1TaperedLoss

/-- Actual physical grid traversal cost: no supplied arithmetic-operation budget. -/
theorem loop_clock (template : List Bool) (a h u t : ℕ) (g : Geometry)
    (center alpha node : RationalWord) (qs : List ℕ)
    (hW : a+2 ≤ template.length)
    (hc : Width center template.length) (ha : Width alpha template.length) (hn : Width node template.length) :
    (loop template a h u t g center alpha node qs).clock ≤ qs.length*frameBudget template.length (h*u)+4 := by
  have ht : 0 < template.length := by omega
  induction qs with
  | nil => simp [loop]
  | cons q qs ih =>
    by_cases hs : q=g.center.natAbs ∨ q=t
    · simp only [loop,hs,ite_true,List.length_cons,Nat.add_mul,Nat.one_mul]
      have hp : 4 ≤ frameBudget template.length (h*u) := by
        unfold frameBudget
        have ha : 8 ≤ 2*(h*u)+8 := by omega
        have hb : 1 ≤ 20000*(template.length+1)^3+8*template.length+50 := by omega
        have hh:=Nat.mul_le_mul ha hb
        norm_num only at hh
        omega
      omega
    · let tail:=loop template a h u t g center alpha node qs
      let m:=multiplicityRun g h u q
      let negative:=executeOperation .neg (index a q).word (index a q).word template
      let nb:=executeOperation .add center negative.word template
      let db:=executeOperation .add node negative.word template
      let np:=power template nb.word m.value
      let dp:=power template db.word m.value
      let inv:=executeOperation .inv db.word db.word template
      let slope:=executeOperation .mul alpha inv.word template
      let repeated:=copies slope.word m.value
      let numerator:=executeOperation .mul np.word tail.numerator template
      let denominator:=executeOperation .mul dp.word tail.denominator template
      have qw:=index_width a q template.length hW
      have nw:=operation_width .neg (index a q).word (index a q).word template
      have nbw:=operation_width .add center negative.word template
      have dbw:=operation_width .add node negative.word template
      have npw:=power_width template nb.word m.value ht
      have dpw:=power_width template db.word m.value ht
      have iw:=operation_width .inv db.word db.word template
      have sw:=operation_width .mul alpha inv.word template
      have tw:=loop_width template a h u t g center alpha node qs ht
      have cn:=executeOperation_cost .neg (index a q).word (index a q).word template qw qw le_rfl
      have cnb:=executeOperation_cost .add center negative.word template hc nw le_rfl
      have cdb:=executeOperation_cost .add node negative.word template hn nw le_rfl
      have cnp:=power_clock template nb.word m.value ht nbw
      have cdp:=power_clock template db.word m.value ht dbw
      have ci:=executeOperation_cost .inv db.word db.word template dbw dbw le_rfl
      have cs:=executeOperation_cost .mul alpha inv.word template ha iw le_rfl
      have cr:=copies_clock slope.word m.value template.length sw
      have cN:=executeOperation_cost .mul np.word tail.numerator template npw tw.1 le_rfl
      have cD:=executeOperation_cost .mul dp.word tail.denominator template dpw tw.2.1 le_rfl
      have hm:=SemiprimeD1RecoveryWeightRunBounds.multiplicity_value_le g h u q
      have hf:=frame_envelope template.length m.value (h*u) hm
      have hlen : repeated.words.length=m.value := by simp only [repeated,copies_words,List.length_replicate]
      have visit : negative.clock+nb.clock+db.clock+np.clock+dp.clock+inv.clock+slope.clock+
          repeated.clock+numerator.clock+denominator.clock+2*repeated.words.length+15 ≤
          frameBudget template.length (h*u) := by
        rw [hlen]
        dsimp only [tail,m,negative,nb,db,np,dp,inv,slope,repeated,numerator,denominator] at *
        simp only [Nat.mul_assoc] at hf
        omega
      simp only [loop,hs,ite_false]
      change tail.clock+negative.clock+nb.clock+db.clock+np.clock+dp.clock+inv.clock+slope.clock+
        repeated.clock+numerator.clock+denominator.clock+2*repeated.words.length+15 ≤ _
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      dsimp only [tail,m,negative,nb,db,np,dp,inv,slope,repeated,numerator,denominator] at *
      omega

/-- Every native index/valuation stage of the actual original grid is retained. -/
theorem loop_metadataWork (template : List Bool) (a h u t : ℕ) (g : Geometry)
    (center alpha node : RationalWord) (qs : List ℕ) :
    (loop template a h u t g center alpha node qs).metadataWork ≤
      qs.length*(5*g.size+4*(a+2)+30)+1 := by
  induction qs with
  | nil => simp [loop]
  | cons q qs ih =>
    have hm:=SemiprimeD1RecoveryWeightRunBounds.multiplicity_work g h u q
    have hi:=(SemiprimeEncodedRowSelection.encode_work (a+1) (q:ℤ)).1
    simp only [loop]
    split_ifs <;> dsimp only
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · change _+(multiplicityRun g h u q).work+(index a q).work+10 ≤ _
      change (index a q).work=4*(a+2)+4 at hi
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul,hi]
      omega

/-- Literal original-grid physical arithmetic budget. -/
def budget (a h u W : ℕ) : ℕ :=
  (2*a+1)*(20000*(W+1)^3+4)+size a*frameBudget W (h*u)+6*(20000*(W+1)^3)+40

/-- Actual original physical scalar/slopes/argument acquisition has a closed
bit-arithmetic clock, not a count of unit native rational operations. -/
theorem acquire_clock (template : List Bool) (a M u : ℕ) (t : Fin (size a))
    (hW : gridWidth a (height M u) u ≤ template.length) :
    (acquire template a M u t).clock ≤ budget a (height M u) u template.length := by
  let h:=height M u
  let g:=geometry a t.val
  let c:=power template twoWord a
  let alpha:=power template twoWord (a+1)
  let node:=index a t.val
  let keys:=indices g.size
  let grid:=loop template a h u t.val g c.word alpha.word node.word keys.value
  let inverse:=executeOperation .inv grid.denominator grid.denominator template
  let scalar:=executeOperation .mul grid.numerator inverse.word template
  let neg:=executeOperation .neg node.word node.word template
  let point:=executeOperation .add c.word neg.word template
  let invAlpha:=executeOperation .inv alpha.word alpha.word template
  let arg:=executeOperation .mul point.word invAlpha.word template
  have caps:=gridWidth_caps a h u template.length hW
  have two:=twoWord_width template.length (by omega)
  have cw:=power_width template twoWord a caps.1
  have aw:=power_width template twoWord (a+1) caps.1
  have nw:=index_width a t.val template.length caps.2.1
  have gw:=loop_width template a h u t.val g c.word alpha.word node.word keys.value caps.1
  have iw:=operation_width .inv grid.denominator grid.denominator template
  have negw:=operation_width .neg node.word node.word template
  have pw:=operation_width .add c.word neg.word template
  have iaw:=operation_width .inv alpha.word alpha.word template
  have cc:=power_clock template twoWord a caps.1 two
  have ca:=power_clock template twoWord (a+1) caps.1 two
  have cg:=loop_clock template a h u t.val g c.word alpha.word node.word keys.value caps.2.1 cw aw nw
  have ci:=executeOperation_cost .inv grid.denominator grid.denominator template gw.2.1 gw.2.1 le_rfl
  have cs:=executeOperation_cost .mul grid.numerator inverse.word template gw.1 iw le_rfl
  have cn:=executeOperation_cost .neg node.word node.word template nw nw le_rfl
  have cp:=executeOperation_cost .add c.word neg.word template cw negw le_rfl
  have cia:=executeOperation_cost .inv alpha.word alpha.word template aw aw le_rfl
  have carg:=executeOperation_cost .mul point.word invAlpha.word template pw iaw le_rfl
  have hlen : keys.value.length=size a := by simp [keys,indices_value,g,geometry_size]
  rw [hlen] at cg
  change c.clock+alpha.clock+grid.clock+inverse.clock+scalar.clock+neg.clock+point.clock+invAlpha.clock+arg.clock+30 ≤ _
  unfold budget
  simp only [Nat.add_mul,Nat.one_mul,Nat.mul_assoc]
  dsimp only [c,alpha,node,keys,grid,inverse,scalar,neg,point,invAlpha,arg,g,h] at *
  simp only [Nat.add_mul,Nat.one_mul] at *
  omega

end RiemannGaussian.SemiprimeD1RecoveryGridBitsBounds
