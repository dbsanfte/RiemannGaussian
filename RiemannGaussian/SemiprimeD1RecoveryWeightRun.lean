/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryScalarRun

/-! # Actual original-grid scalar weight producer with retained native loops
Every scalar, slope, inverse packet and canonical integer row is acquired from
original grid parameters. Native rational normalization is an explicit scalar
boundary, not a unit physical-bit operation or a supplied coefficient answer.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1RecoveryWeightRun
open scoped BigOperators
open SemiprimeD1RecoveryScalarRun SemiprimeD1WireKernelOriginal
  SemiprimeD1TaperedLoss SemiprimeD1JetRecoveryGrid SemiprimeD1JetRecoveryWeights
  SemiprimeJetArray SemiprimeD1JetRecoveryScalarHeight

/-- Cached original grid geometry, acquired by actual repeated integer powers. -/
structure Geometry where
  /-- Actual2L grid size. -/
  size : ℕ
  /-- Actual grid centre as a signed integer. -/
  center : ℤ
  /-- Actual supplied node's signed grid point. -/
  point : ℤ
  /-- Actual alpha=2L, acquired once. -/
  alpha : ℤ
  /-- All original native power/point arithmetic retained. -/
  work : ℕ

/-- Original grid geometry from a and the actual node index, never supplied scalar values. -/
def geometry (a t : ℕ) : Geometry :=
  let center:=intPower 2 a
  let alpha:=center.value*2
  ⟨alpha.natAbs,center.value,(t:ℤ)-center.value,alpha,center.work+7⟩

/-- Actual acquired centre is the original signed grid centre. -/
theorem geometry_center (a t : ℕ) : (geometry a t).center=(center a:ℤ) := by
  simp [geometry,intPower_value,center]

/-- Actual acquired centre index is the original nonnegative centre. -/
theorem geometry_center_abs (a t : ℕ) : (geometry a t).center.natAbs=center a := by
  rw [geometry_center]
  simp

/-- Actual acquired grid size is the original2L. -/
theorem geometry_size (a t : ℕ) : (geometry a t).size=size a := by
  simp [geometry,intPower_value,size,pow_succ,Int.natAbs_mul,Int.natAbs_pow]

/-- The original local point is acquired by actual signed subtraction. -/
theorem geometry_point (a t : ℕ) : (geometry a t).point=point a t := by
  simp [geometry,intPower_value,point,center]

/-- The actual acquired alpha equals the original source scalar. -/
theorem geometry_alpha (a t : ℕ) : (geometry a t).alpha=(2:ℤ)^(a+1) := by
  simp only [geometry,intPower_value,pow_succ]

/-- Compute ORIGINAL multiplicity by explicit bounded dyadic modulo/division steps. -/
def multiplicityRun (g : Geometry) (h u q : ℕ) : Run ℕ :=
  let order:=orderFuel g.size ((q:ℤ)-g.center).natAbs
  ⟨h*(u-order.value),order.work+5⟩

/-- Actual original multiplicity is derived, not supplied as a valuation/count answer. -/
theorem multiplicityRun_value (a h u t q : ℕ) (hq : q<size a) :
    (multiplicityRun (geometry a t) h u q).value=nodeMultiplicity a h u q := by
  have hp : ((q:ℤ)-(geometry a t).center).natAbs≤(geometry a t).size := by
    rw [geometry_center,geometry_size]
    exact (point_abs_lt a q hq).le
  have hv : padicValNat 2 ((q:ℤ)-(geometry a t).center).natAbs≤(geometry a t).size :=
    (Nat.padicValNat_le_self _).trans hp
  dsimp only [multiplicityRun]
  rw [orderFuel_value _ _ (Or.inr hv)]
  simp only [geometry_center,nodeMultiplicity,SemiprimeD1TaperedLoss.multiplicity,padicValInt,point]

/-- Actual grid products, slope list and every retained native operation/cell report. -/
structure GridReport where
  /-- Signed original Ezero numerator product. -/
  numerator : ℤ
  /-- Signed original nonzero Ezero denominator product. -/
  denominator : ℤ
  /-- Original ordered slopes repeated by acquired multiplicities. -/
  slopes : List ℚ
  /-- All grid visits, powers, integer products, rational normalizations and copied cells. -/
  work : ℕ

/-- Traverse the ACTUAL acquired grid, caching each multiplicity and slope once. -/
def gridRows (g : Geometry) (h u t : ℕ) : List ℕ → GridReport
  | [] => ⟨1,1,[],1⟩
  | q::qs =>
    let tail:=gridRows g h u t qs
    if q=g.center.natAbs ∨ q=t then
      ⟨tail.numerator,tail.denominator,tail.slopes,tail.work+4⟩
    else
      let m:=multiplicityRun g h u q
      let x:=(q:ℤ)-g.center
      let d:=g.point-x
      let numerator:=intPower (-x) m.value
      let denominator:=intPower d m.value
      let slope:ℚ:=(g.alpha:ℚ)/(d:ℚ)
      let copies:=replicateRun m.value slope
      ⟨numerator.value*tail.numerator,denominator.value*tail.denominator,
        copies.value++tail.slopes,
        tail.work+m.work+numerator.work+denominator.work+copies.work+2*copies.value.length+15⟩

/-- The original numerator grid fold is the literal finite integer product. -/
theorem gridRows_numerator (a h u t : ℕ) (qs : List ℕ) (hq : ∀q∈qs,q<size a) :
    (gridRows (geometry a t) h u t qs).numerator=
      (qs.map fun q => if q=center a ∨ q=t then 1 else (-point a q)^nodeMultiplicity a h u q).prod := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    have hm:=multiplicityRun_value a h u t q (hq q List.mem_cons_self)
    have hi:=ih (fun q h => hq q (List.mem_cons_of_mem _ h))
    by_cases hs : q=center a ∨ q=t
    · simp only [gridRows,geometry_center_abs,hs,ite_true,List.map_cons,List.prod_cons,one_mul,hi]
    · simp only [gridRows,hs,ite_false,List.map_cons,List.prod_cons,
        intPower_value,hm,geometry_center,Int.natAbs_natCast,point,hi]

/-- The original denominator grid fold is the literal signed node-difference product. -/
theorem gridRows_denominator (a h u t : ℕ) (qs : List ℕ) (hq : ∀q∈qs,q<size a) :
    (gridRows (geometry a t) h u t qs).denominator=
      (qs.map fun q => if q=center a ∨ q=t then 1 else
        (point a t-point a q)^nodeMultiplicity a h u q).prod := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    have hm:=multiplicityRun_value a h u t q (hq q List.mem_cons_self)
    have hi:=ih (fun q h => hq q (List.mem_cons_of_mem _ h))
    by_cases hs : q=center a ∨ q=t
    · simp only [gridRows,geometry_center_abs,hs,ite_true,List.map_cons,List.prod_cons,one_mul,hi]
    · simp only [gridRows,hs,ite_false,List.map_cons,List.prod_cons,
        intPower_value,hm,geometry_center,Int.natAbs_natCast,geometry_point,point,hi]

/-- The actual acquired grid folds yield the exact original slope ordering. -/
theorem gridRows_slopes (a h u t : ℕ) (qs : List ℕ) (hq : ∀q∈qs,q<size a) :
    (gridRows (geometry a t) h u t qs).slopes=
      qs.flatMap (fun q => if q=center a ∨ q=t then [] else List.replicate (nodeMultiplicity a h u q)
        (((2:ℤ)^(a+1):ℚ)/((point a t:ℚ)-(point a q:ℚ)))) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    have hm:=multiplicityRun_value a h u t q (hq q List.mem_cons_self)
    have hi:=ih (fun q h => hq q (List.mem_cons_of_mem _ h))
    by_cases hs : q=center a ∨ q=t
    · simp only [gridRows,geometry_center_abs,hs,ite_true,List.flatMap_cons,List.nil_append,hi]
    · simp only [gridRows,hs,ite_false,List.flatMap_cons,repeat_value,hm,
        geometry_point,geometry_center,Int.natAbs_natCast,geometry_alpha,point,Int.cast_sub,Int.cast_pow,Int.cast_ofNat,hi]

/-- The literal masked grid product is exactly the original omitted-node product. -/
theorem original_product {K : Type*} [CommMonoid K] (a t : ℕ) (f : ℕ→K) :
    ((List.range (size a)).map fun q => if q=center a ∨ q=t then 1 else f q).prod=
      ∏q∈others a t,f q := by
  classical
  rw [← List.prod_toFinset _ List.nodup_range,List.toFinset_range]
  have hs : others a t=(Finset.range (size a)).filter (fun q => ¬(q=center a ∨ q=t)) := by
    ext q
    simp only [others,Finset.mem_erase,Finset.mem_range,Finset.mem_filter]
    tauto
  rw [hs,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro q _
  by_cases h : q=center a ∨ q=t <;> simp only [h,not_true_eq_false,not_false_eq_true,ite_true,ite_false]

/-- ACTUAL original-grid numerator acquisition, including signs and inactive multiplicities. -/
theorem fullGrid_numerator (a h u t : ℕ) :
    (gridRows (geometry a t) h u t (indices (geometry a t).size).value).numerator=
      SemiprimeD1JetRecoveryScalarHeight.numerator a h u t := by
  rw [geometry_size,indices_value,gridRows_numerator a h u t _ (fun q h => List.mem_range.mp h)]
  exact original_product a t _

/-- ACTUAL original-grid denominator acquisition, without a supplied clearing scalar. -/
theorem fullGrid_denominator (a h u t : ℕ) :
    (gridRows (geometry a t) h u t (indices (geometry a t).size).value).denominator=
      SemiprimeD1JetRecoveryScalarHeight.denominator a h u t := by
  rw [geometry_size,indices_value,gridRows_denominator a h u t _ (fun q h => List.mem_range.mp h)]
  exact original_product a t _

/-- ACTUAL original slope acquisition in precisely the frozen constructor's order. -/
theorem fullGrid_slopes (a h u t : ℕ) :
    (gridRows (geometry a t) h u t (indices (geometry a t).size).value).slopes=slopes a h u t := by
  rw [geometry_size,indices_value,gridRows_slopes a h u t _ (fun q h => List.mem_range.mp h)]
  rfl

/-- Cache actual scalar powers once for each retained coefficient index. -/
def powersRun (x : ℚ) (q : ℕ) : Run (Array ℚ) :=
  let keys:=indices q
  let reports:=keys.value.map (rationalPower x)
  ⟨(reports.map (fun r => r.value)).toArray,
    keys.work+(reports.map (fun r => r.work)).sum+4*keys.value.length+3⟩

/-- Every cached power is the actual original scalar power. -/
theorem powersRun_coefficient (x : ℚ) (q k : ℕ) (hk : k<q) :
    coefficient (powersRun x q).value k=x^k := by
  simp [powersRun,indices_value,coefficient,hk,rationalPower_value]

/-- Explicit right-recursive local coefficient sum with retained reads and normalizations. -/
def sumWeights (j : ℕ) (inv powers : Array ℚ) : List ℕ → Run ℚ
  | [] => ⟨0,1⟩
  | k::ks =>
    let tail:=sumWeights j inv powers ks
    if j≤k then
      let term:=coefficient inv (k-j)*coefficient powers k
      ⟨term+tail.value,tail.work+7⟩
    else ⟨tail.value,tail.work+3⟩

/-- The executed scalar suffix sum has its actual literal list meaning. -/
theorem sumWeights_value (j : ℕ) (inv powers : Array ℚ) (ks : List ℕ) :
    (sumWeights j inv powers ks).value=
      (ks.map fun k => if j≤k then coefficient inv (k-j)*coefficient powers k else 0).sum := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    by_cases h : j≤k <;> simp only [sumWeights,h,ite_true,ite_false,List.map_cons,List.sum_cons,zero_add,ih]

/-- One actual weight, retaining every suffix/read and the final Ezero multiplication. -/
def weightRun (E : ℚ) (j : ℕ) (inv powers : Array ℚ) (keys : List ℕ) : Run ℚ :=
  let total:=sumWeights j inv powers keys
  ⟨E*total.value,total.work+3⟩

/-- Explicit acquired scalar loops compute EXACTLY the original finite localWeight. -/
theorem weightRun_value (q j : ℕ) (E x : ℚ) (inv : Array ℚ) :
    (weightRun E j inv (powersRun x q).value (indices q).value).value=localWeight q E x inv j := by
  simp only [weightRun,sumWeights_value,indices_value,localWeight]
  congr 1
  rw [← List.sum_toFinset _ List.nodup_range,List.toFinset_range]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : j≤k
  · simp only [h,ite_true,powersRun_coefficient x q k (Finset.mem_range.mp hk)]
  · simp only [h,ite_false]

/-- Actual canonical integer data extracted ONCE from an already acquired scalar. -/
structure CanonicalRow where
  /-- Actual canonical signed numerator. -/
  numerator : ℤ
  /-- Actual canonical positive denominator. -/
  denominator : ℕ
  deriving Repr

/-- Traverse actual scalar reports, retaining their work and canonical field accesses. -/
def canonicalRows : List (Run ℚ) → Run (List CanonicalRow)
  | [] => ⟨[],1⟩
  | r::rs =>
    let tail:=canonicalRows rs
    ⟨⟨r.value.num,r.value.den⟩::tail.value,r.work+tail.work+4⟩

/-- Canonical-row acquisition uses the actual computed values, never supplied Int rows. -/
theorem canonicalRows_value (rs : List (Run ℚ)) :
    (canonicalRows rs).value=rs.map (fun r => CanonicalRow.mk r.value.num r.value.den) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [canonicalRows,List.map_cons,ih]

/-- All original scalar/packet data, cached canonical Int rows and their retained acquisition report. -/
structure NodeReport where
  /-- Actual acquired original weight data. -/
  data : WeightData
  /-- Canonical numerator/denominator rows, cached once. -/
  rows : List CanonicalRow
  /-- ALL executed native scalar, array, index and list stages retained. -/
  work : ℕ

/-- Full node producer from ORIGINAL a,M,u,t. No slopes, Ezero, coefficient,
inverse, canonical integer row, height or operation-count answer is supplied. -/
def acquire (a M u : ℕ) (t : Fin (size a)) : NodeReport :=
  let h:=height M u
  let g:=geometry a t.val
  let gridKeys:=indices g.size
  let grid:=gridRows g h u t.val gridKeys.value
  let multiplicity:=multiplicityRun g h u t.val
  let q:=multiplicity.value
  let E:ℚ:=(grid.numerator:ℚ)/(grid.denominator:ℚ)
  let x:ℚ:=-(g.point:ℚ)/(g.alpha:ℚ)
  let denominator:=SemiprimeHermiteArrayHeight.buildAffine q grid.slopes
  let inverse:=SemiprimeJetArray.inverse denominator.coefficients q
  let keys:=indices q
  let powers:=powersRun x q
  let reports:=keys.value.map (fun j => weightRun E j inverse.coefficients powers.value keys.value)
  let canonical:=canonicalRows reports
  ⟨⟨q,E,x,denominator,inverse,(reports.map (fun r => r.value)).toArray⟩,canonical.value,
    g.work+gridKeys.work+grid.work+multiplicity.work+denominator.arithmetic+denominator.reads+
      inverse.arithmetic+inverse.reads+keys.work+powers.work+canonical.work+4*keys.value.length+20⟩

/-- Actual scalar report values form the ORIGINAL stored weight array. -/
theorem weight_array (q : ℕ) (E x : ℚ) (inv : Array ℚ) :
    (((indices q).value.map (fun j => weightRun E j inv (powersRun x q).value (indices q).value)).map
      (fun r => r.value)).toArray=
      Array.ofFn (fun j : Fin q => localWeight q E x inv j.val) := by
  simp only [List.map_map,Function.comp_def,indices_value]
  apply Array.ext
  · simp
  · intro j hj hj'
    simp only [List.getElem_toArray,List.getElem_map,List.getElem_range,Array.getElem_ofFn]
    simpa only [indices_value] using weightRun_value q j E x inv

/-- Full original-input producer refines the FROZEN actual weight constructor,
including acquired denominator/inverse arrays and their retained reports. -/
theorem acquire_data (a M u : ℕ) (t : Fin (size a)) :
    (acquire a M u t).data=SemiprimeD1JetRecoveryWeights.acquire a (height M u) u t.val := by
  simp only [acquire,fullGrid_numerator,fullGrid_denominator,fullGrid_slopes,
    multiplicityRun_value a (height M u) u t.val t.val t.isLt,geometry_point,geometry_alpha,
    ← ratio_spec,weight_array,SemiprimeD1JetRecoveryWeights.acquire]
  simp only [Int.cast_pow,Int.cast_ofNat]

/-- Canonical numerators/denominators are extracted from ACTUAL producer values once. -/
theorem acquire_rows (a M u : ℕ) (t : Fin (size a)) :
    (acquire a M u t).rows=(acquire a M u t).data.weights.toList.map
      (fun q => CanonicalRow.mk q.num q.den) := by
  simp only [acquire,canonicalRows_value,List.toList_toArray,List.map_map,Function.comp_def]

/-- Cached canonical integer rows agree EXACTLY with the original acquired scalar rows. -/
theorem acquire_original_rows (a M u : ℕ) (t : Fin (size a)) :
    (acquire a M u t).rows=(SemiprimeD1JetRecoveryWeights.acquire a (height M u) u t.val).weights.toList.map
      (fun q => CanonicalRow.mk q.num q.den) := by
  rw [acquire_rows,acquire_data]

end RiemannGaussian.SemiprimeD1RecoveryWeightRun
