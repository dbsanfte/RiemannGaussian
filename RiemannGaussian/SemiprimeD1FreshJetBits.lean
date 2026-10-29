/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetPolynomialBitsBounds

/-! # Acquired fresh nilpotent generator, including the one-cell axis
The actual dense word table is constructed from dimensions and one reduced bit.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1FreshJetBits
open scoped BigOperators
open SemiprimeD1JetAxes SemiprimeD1JetBoxIndex SemiprimeD1JetInterpretation
open SemiprimeD1JetAffineCoefficient (JetRun)
open SemiprimeBitArithmetic

/-- Actual outer-axis context with explicitly selected current precision. -/
def context (old : Context) (q p : ℕ) : Context:=⟨q::old.axes,p⟩

/-- Physically allocate the fresh generator at dense index oldRank. -/
def acquireFresh (old : Context) (q p : ℕ) : JetRun :=
  let one:=SemiprimeD1JetScalarBits.reduce p [true]
  ⟨(List.range (q*old.rank)).map (fun i=>if i=old.rank then one.bits else []),
    one.clock+3*(q*old.rank)+5⟩

/-- Original positive axes make the first fresh-axis index the exact unit exponent. -/
theorem exponent_fresh (old : Context) (q : ℕ) (hpos : old.Positive) :
    exponent (q::old.axes) old.rank=Finsupp.single 0 1 := by
  have hn : 0<old.rank:=List.prod_pos hpos
  ext j
  refine Fin.cases ?_ (fun k=>?_) j
  · simp only [exponent_apply,digitFn,Fin.cases_zero,Finsupp.single_eq_same]
    simpa only [Context.rank] using Nat.div_self hn
  · change digitFn old.axes (old.axes.prod%old.axes.prod) k=(Finsupp.single (0:Fin (old.axes.length+1)) 1) k.succ
    rw [Nat.mod_self]
    have hz:=congrArg (fun e:Fin old.axes.length→₀ℕ=>e k)
      (SemiprimeD1JetAffineCoefficient.exponent_zero old.axes)
    simpa only [exponent_apply,Finsupp.zero_apply,Finsupp.single_apply,Ne.symm (Fin.succ_ne_zero k),ite_false] using hz

/-- The acquired fresh generator has exactly its actual dense context shape. -/
theorem acquireFresh_shape (old : Context) (q p : ℕ) :
    (acquireFresh old q p).words.length=(context old q p).rank := by
  simp [acquireFresh,context,Context.rank]

/-- Every actual fresh word has intrinsic current precision width. -/
theorem acquireFresh_bounded (old : Context) (q p : ℕ) :
    ∀w∈(acquireFresh old q p).words,w.length≤p := by
  intro w hw
  rcases List.mem_map.mp hw with ⟨i,_,rfl⟩
  split_ifs
  · exact SemiprimeD1JetScalarBits.reduce_length _ _
  · exact Nat.zero_le _

/-- Actual fresh allocation satisfies the backend's derived shape/width invariant. -/
theorem acquireFresh_good (old : Context) (q p : ℕ) :
    SemiprimeD1JetAffineCoefficientBounds.Good (context old q p) (acquireFresh old q p).words :=
  ⟨acquireFresh_shape old q p,acquireFresh_bounded old q p⟩

/-- Fresh generator words are canonically compact without a fit assumption. -/
theorem acquireFresh_compact (old : Context) (q p : ℕ) :
    ∀w∈(acquireFresh old q p).words,SemiprimeSourceCompactBits.Compact w := by
  intro w hw
  rcases List.mem_map.mp hw with ⟨i,_,rfl⟩
  split_ifs
  · exact SemiprimeD1JetScalarBits.reduce_compact _ _
  · trivial

/-- Source reduction and every actual dense cell allocation are paid. -/
theorem acquireFresh_clock (old : Context) (q p : ℕ) :
    (acquireFresh old q p).clock≤9*p+3*(q*old.rank)+10 := by
  have h:=SemiprimeD1JetScalarBits.reduce_clock p [true]
  change (SemiprimeD1JetScalarBits.reduce p [true]).clock+3*(q*old.rank)+5≤_
  omega

/-- Every actual acquired coefficient is the literal fresh-axis coordinate indicator. -/
theorem acquireFresh_coefficient (old : Context) (q p i : ℕ) (hi : i<q*old.rank) :
    SemiprimeD1JetRingBits.coefficient (context old q p) (acquireFresh old q p).words i=
      if i=old.rank then 1 else 0 := by
  simp only [acquireFresh,SemiprimeD1JetRingBits.coefficient,List.getElem?_map,
    List.getElem?_range hi,Option.map_some,Option.getD_some]
  split
  · exact SemiprimeD1JetAffineCoefficient.one_scalar (context old q p)
  · simp [bitValue]

/-- A one-cell fresh axis physically allocates only zero coefficient words. -/
theorem acquireFresh_one_words (old : Context) (p : ℕ) :
    (acquireFresh old 1 p).words=List.replicate old.rank [] := by
  have hm : (List.range old.rank).map (fun i=>
      if i=old.rank then (SemiprimeD1JetScalarBits.reduce p [true]).bits else [])=
      (List.range old.rank).map (fun _=>([]:List Bool)) := by
    apply List.map_congr_left
    intro i hi
    exact ite_eq_right (Nat.ne_of_lt (List.mem_range.mp hi))
  simpa only [acquireFresh,Nat.one_mul,List.map_const',List.length_range] using hm

/-- A one-cell fresh axis emits only actual zero words. -/
theorem acquireFresh_one_value (old : Context) (p : ℕ) :
    interpret (context old 1 p) (acquireFresh old 1 p).words=0 := by
  classical
  unfold interpret
  apply Finset.sum_eq_zero
  intro i _
  have hi : i.val<old.rank := by simpa [context,Context.rank] using i.isLt
  have hn : i.val≠old.rank := Nat.ne_of_lt hi
  rw [acquireFresh_coefficient old 1 p i.val (by simpa using hi),ite_eq_right hn]
  simp [basis]


/-- Actual acquired words equal the concrete quotient's fresh generator for every positive q.
At q=1 both sides are zero, since that generator satisfies X^1=0. -/
theorem fresh_value (old : Context) (q p : ℕ) (hpos : old.Positive) (hq : 0<q) :
    interpret (context old q p) (acquireFresh old q p).words=
      SemiprimeD1JetAlgebra.generator (dims (q::old.axes)) 0 := by
  classical
  by_cases heq : q=1
  · subst q
    rw [acquireFresh_one_value]
    have h:=SemiprimeD1JetAlgebra.generator_pow (R:=ZMod (2^p)) (dims (1::old.axes)) 0
    change (SemiprimeD1JetAlgebra.generator (dims (1::old.axes)) 0:Carrier (context old 1 p))^1=0 at h
    exact ((pow_one _).symm.trans h).symm
  · have hn : 0<old.rank:=List.prod_pos hpos
    have hq2 : 2≤q := by omega
    have hi : old.rank<(context old q p).rank := by
      change old.rank<q*old.rank
      nlinarith
    let z : Fin (context old q p).rank:=⟨old.rank,hi⟩
    unfold interpret
    rw [Finset.sum_eq_single z]
    · rw [acquireFresh_coefficient old q p old.rank (by simpa [context,Context.rank] using hi),ite_eq_left rfl]
      change SemiprimeD1JetAlgebra.project (dims (q::old.axes))
        (MvPowerSeries.monomial (exponent (q::old.axes) old.rank) 1)=_
      rw [exponent_fresh old q hpos]
      rfl
    · intro i _ hiz
      have hn : i.val≠old.rank := fun h=>hiz (Fin.ext h)
      rw [acquireFresh_coefficient old q p i.val (by simpa [context,Context.rank] using i.isLt),ite_eq_right hn]
      simp [basis]
    · intro h
      exact False.elim (h (Finset.mem_univ z))

/-- Actual dimension-list generator agrees with the abstract outer-axis generator.
The heterogeneous equality reflects only the proved equality of dimension functions. -/
theorem fresh_value_outer (old : Context) (q p : ℕ) (hpos : old.Positive) (hq : 0<q) :
    HEq (interpret (context old q p) (acquireFresh old q p).words)
      (SemiprimeD1JetAlgebra.fresh (R:=ZMod (2^p)) q (dims old.axes)) := by
  rw [fresh_value old q p hpos hq]
  unfold SemiprimeD1JetAlgebra.fresh SemiprimeD1JetAlgebra.generator
  exact SemiprimeD1JetEmbedding.project_heq _ _
    (SemiprimeD1JetEmbedding.dims_cons q old.axes) _

end RiemannGaussian.SemiprimeD1FreshJetBits
