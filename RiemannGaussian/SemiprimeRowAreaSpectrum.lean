/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeAnchoredRowAreas

/-!
# Residue and center information in three-row areas

Keep the actual public packets before removing their common midpoint plane.
Their signed rounding errors retain the same-center area exactly. A common
residue contributes an integer factor m³ before reduction modulo N. Mixed
centers retain a separate signed direction and are not covered by the
same-center small-area obstruction.
-/

namespace RiemannGaussian.SemiprimeRowAreaSpectrum

open SemiprimeQuotientRows SemiprimeQuotientCentering SemiprimeEuclidRowFamily
open SemiprimeWeightedRows SemiprimeCompanionRows SemiprimeCompanionCenterSpectrum
open SemiprimeAffineRowRoots SemiprimeCenteredOffsetExtractor SemiprimeAnchoredRowAreas

/-- The complete centered coefficient rows remain upstream of their area. -/
def centeredCoefficientArea (m : ℕ) (u w v : FamilyPacket) : ℤ :=
  Matrix.det !![(centeredPacketRow m u).a,(centeredPacketRow m u).b,
      (centeredPacketRow m u).c;
    (centeredPacketRow m w).a,(centeredPacketRow m w).b,(centeredPacketRow m w).c;
    (centeredPacketRow m v).a,(centeredPacketRow m v).b,(centeredPacketRow m v).c]

/-- The actual common-residue coordinate change has determinant m³. -/
theorem quotient_area_coordinate {N m j : ℤ} (u w v : QuotientRow)
    (hu : quotientRelation N m j u.a u.b u.c u.t)
    (hw : quotientRelation N m j w.a w.b w.c w.t)
    (hv : quotientRelation N m j v.a v.b v.c v.t) :
    Matrix.det !![u.a,m*u.b-2*u.a*j,N*u.t;
      w.a,m*w.b-2*w.a*j,N*w.t;v.a,m*v.b-2*v.a*j,N*v.t]=
      m^3*Matrix.det !![u.a,u.b,u.c;w.a,w.b,w.c;v.a,v.b,v.c] := by
  unfold quotientRelation at hu hw hv
  rw [←hu,←hw,←hv]
  simp [Matrix.det_fin_three]
  ring

/-- Apply the coordinate change to original public packets, with all shifts
and both center orientations retained. -/
theorem publicPacket_same_residue_scaled_area {N m : ℕ} (hm : 0<m)
    {u w v : FamilyPacket} (hu : u∈publicPackets N m) (hw : w∈publicPackets N m)
    (hv : v∈publicPackets N m) (hwu : w.residue=u.residue) (hvu : v.residue=u.residue) :
    (N : ℤ)*rowArea m u w v=(m : ℤ)^3*centeredCoefficientArea m u w v := by
  have hur := publicPacket_relation hm hu
  have hwr := publicPacket_relation hm hw
  have hvr := publicPacket_relation hm hv
  rw [hwu] at hwr
  rw [hvu] at hvr
  have h := quotient_area_coordinate (centeredPacketRow m u) (centeredPacketRow m w)
    (centeredPacketRow m v) hur hwr hvr
  rw [←original_row_area N m u w v]
  simpa only [centeredCoefficientArea,packetOffset,centeredPacketRow,shiftRow,hwu,hvu]
    using h

/-- A public coprimality check removes N from the integer divisibility. -/
theorem publicPacket_same_residue_area_dvd {N m : ℕ} (hm : 0<m) (hcop : m.Coprime N)
    {u w v : FamilyPacket} (hu : u∈publicPackets N m) (hw : w∈publicPackets N m)
    (hv : v∈publicPackets N m) (hwu : w.residue=u.residue) (hvu : v.residue=u.residue) :
    (m : ℤ)^3∣rowArea m u w v := by
  have h := publicPacket_same_residue_scaled_area hm hu hw hv hwu hvu
  obtain ⟨x,y,hxy⟩ := (hcop.pow_left 3).isCoprime
  simp only [Nat.cast_pow] at hxy
  refine ⟨x*rowArea m u w v+y*centeredCoefficientArea m u w v,?_⟩
  linear_combination -rowArea m u w v*hxy+y*h

/-- The midpoint equation keeps its signed rounding error, before bounds. -/
theorem packet_center_equation {N m : ℕ} (w : FamilyPacket) (side : Bool)
    (hc : CenterChoice N m w side) :
    -2*packetOffset m w=w.original.a*centerA N side+w.original.t*centerB N side+
      packetCenterError N m w side := by
  unfold CenterChoice at hc
  simp only [packetOffset,centeredPacketRow,shiftRow,packetCenterError,
    roundingError,centerNumerator,hc]
  ring

/-- Signed error area, forked from the full public packets. -/
def errorArea (N m : ℕ) (u w v : FamilyPacket) (us ws vs : Bool) : ℤ :=
  Matrix.det !![u.original.a,packetCenterError N m u us,u.original.t;
    w.original.a,packetCenterError N m w ws,w.original.t;
    v.original.a,packetCenterError N m v vs,v.original.t]

/-- One common midpoint plane cancels exactly. No absolute value has been
taken in this identity. -/
theorem same_center_area {N m : ℕ} (u w v : FamilyPacket) (side : Bool)
    (hu : CenterChoice N m u side) (hw : CenterChoice N m w side)
    (hv : CenterChoice N m v side) :
    2*rowArea m u w v= -errorArea N m u w v side side side := by
  have hue := packet_center_equation u side hu
  have hwe := packet_center_equation w side hw
  have hve := packet_center_equation v side hv
  simp [rowArea,errorArea,Matrix.det_fin_three]
  linear_combination (w.original.a*v.original.t-v.original.a*w.original.t)*hue-
    (u.original.a*v.original.t-v.original.a*u.original.t)*hwe+
    (u.original.a*w.original.t-w.original.a*u.original.t)*hve

/-- Every original intermediate numerator stays below the starting modulus. -/
theorem euclidPairs_numerator_lt {r₀ r₁ x y : ℕ} {negative : Bool}
    (horder : r₁<r₀) {z : ℤ×ℕ} (hz : z∈euclidPairs r₀ r₁ x y negative) :
    z.1.natAbs<r₀ := by
  rw [euclidPairs] at hz
  split_ifs at hz with hr
  · simp only [List.not_mem_nil] at hz
  · have hrpos : 0<r₁ := by omega
    simp only [List.mem_cons,List.mem_append,List.mem_map] at hz
    rcases hz with hcur|hmid|htail
    · subst z
      simpa only [signed_natAbs] using horder
    · obtain ⟨k,_,rfl⟩ := hmid
      simp only [signed_natAbs]
      have hprod : 0<(k+1)*r₁ := by positivity
      omega
    · exact (euclidPairs_numerator_lt (Nat.mod_lt _ hrpos) htail).trans horder
termination_by r₁
decreasing_by exact Nat.mod_lt _ (by omega)

theorem publicPairs_numerator_lt {N m j : ℕ} (hm : 0<m) {z : ℤ×ℕ}
    (hz : z∈publicPairs N m j) : z.1.natAbs<m :=
  euclidPairs_numerator_lt (Nat.mod_lt _ hm) hz

/-- Public membership supplies coefficient bounds without a factor witness. -/
theorem publicPacket_coefficient_bounds {N m : ℕ} (hm : 0<m) {w : FamilyPacket}
    (hw : w∈publicPackets N m) : |w.original.a|≤(m : ℤ) ∧ |w.original.t|≤(m : ℤ) := by
  obtain ⟨j,_,hw⟩ := List.mem_flatMap.mp hw
  split_ifs at hw
  · obtain ⟨z,hz,hw⟩ := List.mem_flatMap.mp hw
    have ha := (publicPairs_numerator_lt hm hz).le
    have ht := publicPairs_denominator_le hm hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl
    all_goals
      change |z.1|≤(m : ℤ) ∧ |(z.2 : ℤ)|≤(m : ℤ)
      constructor
      · rw [Int.abs_eq_natAbs]
        exact_mod_cast ha
      · simpa only [abs_of_nonneg (Int.natCast_nonneg z.2)] using
          (show (z.2 : ℤ)≤m by exact_mod_cast ht)
  · simp only [List.not_mem_nil] at hw

/-- One error determinant term has the literal fourth-power envelope. -/
theorem error_product_abs_le {M a e t : ℤ} (ha : |a|≤M) (he : |e|≤M^2)
    (ht : |t|≤M) : |a*e*t|≤M^4 := by
  have hM : 0≤M := (abs_nonneg a).trans ha
  rw [abs_mul,abs_mul]
  calc
    _ ≤ (M*M^2)*M :=
      mul_le_mul (mul_le_mul ha he (abs_nonneg e) hM) ht (abs_nonneg t)
        (mul_nonneg hM (sq_nonneg M))
    _ = _ := by ring

/-- A bound is applied only downstream of the exact signed error identity. -/
theorem publicPacket_errorArea_abs_le {N m : ℕ} (hm : 0<m) {u w v : FamilyPacket}
    (hu : u∈publicPackets N m) (hw : w∈publicPackets N m) (hv : v∈publicPackets N m)
    (us ws vs : Bool) : |errorArea N m u w v us ws vs|≤6*(m : ℤ)^4 := by
  have hub := publicPacket_coefficient_bounds hm hu
  have hwb := publicPacket_coefficient_bounds hm hw
  have hvb := publicPacket_coefficient_bounds hm hv
  have hue := packetCenterError_abs_le (N:=N) hm u us
  have hwe := packetCenterError_abs_le (N:=N) hm w ws
  have hve := packetCenterError_abs_le (N:=N) hm v vs
  have h₁ := abs_le.mp (error_product_abs_le hub.1 hwe hvb.2)
  have h₂ := abs_le.mp (error_product_abs_le hub.1 hve hwb.2)
  have h₃ := abs_le.mp (error_product_abs_le hwb.1 hue hvb.2)
  have h₄ := abs_le.mp (error_product_abs_le hvb.1 hue hwb.2)
  have h₅ := abs_le.mp (error_product_abs_le hwb.1 hve hub.2)
  have h₆ := abs_le.mp (error_product_abs_le hvb.1 hwe hub.2)
  apply abs_le.mpr
  simp [errorArea,Matrix.det_fin_three]
  constructor <;> nlinarith only [h₁.1,h₁.2,h₂.1,h₂.2,h₃.1,h₃.2,h₄.1,h₄.2,
    h₅.1,h₅.2,h₆.1,h₆.2]

/-- Same-center triples have no unbounded midpoint contribution. -/
theorem publicPacket_same_center_area_abs_le {N m : ℕ} (hm : 0<m)
    {u w v : FamilyPacket} (hu : u∈publicPackets N m) (hw : w∈publicPackets N m)
    (hv : v∈publicPackets N m) (side : Bool) (huc : CenterChoice N m u side)
    (hwc : CenterChoice N m w side) (hvc : CenterChoice N m v side) :
    |rowArea m u w v|≤3*(m : ℤ)^4 := by
  have he := same_center_area u w v side huc hwc hvc
  have hb := publicPacket_errorArea_abs_le hm hu hw hv side side side
  have habs := congrArg abs he
  rw [abs_mul,abs_neg] at habs
  norm_num at habs
  nlinarith only [habs,hb]

/-- Divide the known residue factor before applying a size bound. -/
def residueArea (m : ℕ) (u w v : FamilyPacket) : ℤ := rowArea m u w v/(m : ℤ)^3

theorem publicPacket_residueArea_exact {N m : ℕ} (hm : 0<m) (hcop : m.Coprime N)
    {u w v : FamilyPacket} (hu : u∈publicPackets N m) (hw : w∈publicPackets N m)
    (hv : v∈publicPackets N m) (hwu : w.residue=u.residue) (hvu : v.residue=u.residue) :
    rowArea m u w v=(m : ℤ)^3*residueArea m u w v :=
  (Int.mul_ediv_cancel' (publicPacket_same_residue_area_dvd hm hcop hu hw hv hwu hvu)).symm

/-- The literal normalized area is at most 3m for one residue and center. -/
theorem publicPacket_same_residue_center_residueArea_abs_le {N m : ℕ}
    (hm : 0<m) (hcop : m.Coprime N) {u w v : FamilyPacket}
    (hu : u∈publicPackets N m) (hw : w∈publicPackets N m) (hv : v∈publicPackets N m)
    (hwu : w.residue=u.residue) (hvu : v.residue=u.residue) (side : Bool)
    (huc : CenterChoice N m u side) (hwc : CenterChoice N m w side)
    (hvc : CenterChoice N m v side) : |residueArea m u w v|≤3*(m : ℤ) := by
  have he := publicPacket_residueArea_exact hm hcop hu hw hv hwu hvu
  have hb := publicPacket_same_center_area_abs_le hm hu hw hv side huc hwc hvc
  rw [he,abs_mul,abs_of_pos (by positivity : (0 : ℤ)<(m : ℤ)^3)] at hb
  have hpow : (0 : ℤ)<(m : ℤ)^3 := by positivity
  apply (mul_le_mul_iff_right₀ hpow).mp
  nlinarith only [hb]

/-- A small nonzero integer is a unit for two sufficiently large primes.
The primes may coincide. -/
theorem small_int_isUnit {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpm : 3*m<p) (hqm : 3*m<q) {k : ℤ} (hk : k≠0) (hb : |k|≤3*(m : ℤ)) :
    IsUnit (k : ZMod (p*q)) := by
  have hab : k.natAbs≤3*m := by
    rw [Int.abs_eq_natAbs] at hb
    exact_mod_cast hb
  have hpos : 0<k.natAbs := Int.natAbs_pos.mpr hk
  have hpc := (hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hpos (hab.trans_lt hpm))).symm
  have hqc := (hq.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hpos (hab.trans_lt hqm))).symm
  have hu := (ZMod.isUnit_iff_coprime k.natAbs (p*q)).mpr (hpc.mul_right hqc)
  have habsu : IsUnit ((|k| : ℤ) : ZMod (p*q)) := by
    simpa only [Int.abs_eq_natAbs,Int.cast_natCast] using hu
  by_cases hnonneg : 0≤k
  · simpa only [abs_of_nonneg hnonneg] using habsu
  · rw [abs_of_neg (lt_of_not_ge hnonneg),Int.cast_neg] at habsu
    simpa only [neg_neg] using habsu.neg

/-- Same-residue, same-center triples cannot give a proper area divisor once
both primes exceed 3m. This is a restriction on triples, not on factoring. -/
theorem publicPacket_same_residue_center_zero_or_unit {p q m : ℕ} (hm : 0<m)
    (hp : p.Prime) (hq : q.Prime) (hcop : m.Coprime (p*q))
    (hpm : 3*m<p) (hqm : 3*m<q) {u w v : FamilyPacket}
    (hu : u∈publicPackets (p*q) m) (hw : w∈publicPackets (p*q) m)
    (hv : v∈publicPackets (p*q) m) (hwu : w.residue=u.residue)
    (hvu : v.residue=u.residue) (side : Bool) (huc : CenterChoice (p*q) m u side)
    (hwc : CenterChoice (p*q) m w side) (hvc : CenterChoice (p*q) m v side) :
    rowArea m u w v=0 ∨ IsUnit (rowArea m u w v : ZMod (p*q)) := by
  have he := publicPacket_residueArea_exact hm hcop hu hw hv hwu hvu
  by_cases hk : residueArea m u w v=0
  · exact Or.inl (by rw [he,hk,mul_zero])
  · apply Or.inr
    have hkunit := small_int_isUnit hp hq hpm hqm hk
      (publicPacket_same_residue_center_residueArea_abs_le hm hcop hu hw hv hwu hvu
        side huc hwc hvc)
    have hmunit := (ZMod.isUnit_iff_coprime m (p*q)).mpr hcop
    rw [he]
    push_cast
    exact (hmunit.pow 3).mul hkunit

theorem publicPacket_same_residue_center_gcd {p q m : ℕ} (hm : 0<m)
    (hp : p.Prime) (hq : q.Prime) (hcop : m.Coprime (p*q))
    (hpm : 3*m<p) (hqm : 3*m<q) {u w v : FamilyPacket}
    (hu : u∈publicPackets (p*q) m) (hw : w∈publicPackets (p*q) m)
    (hv : v∈publicPackets (p*q) m) (hwu : w.residue=u.residue)
    (hvu : v.residue=u.residue) (side : Bool) (huc : CenterChoice (p*q) m u side)
    (hwc : CenterChoice (p*q) m w side) (hvc : CenterChoice (p*q) m v side) :
    (p*q).gcd (rowArea m u w v : ZMod (p*q)).val=p*q ∨
      (p*q).gcd (rowArea m u w v : ZMod (p*q)).val=1 := by
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  rcases publicPacket_same_residue_center_zero_or_unit hm hp hq hcop hpm hqm
      hu hw hv hwu hvu side huc hwc hvc with hz|hunit
  · exact Or.inl (by simp only [hz,Int.cast_zero,ZMod.val_zero,Nat.gcd_zero_right])
  · exact Or.inr ((SemiprimeBulkNorm.gcd_one_iff_unit _).mpr hunit)

theorem publicPacket_same_residue_center_no_proper_gcd {p q m : ℕ} (hm : 0<m)
    (hp : p.Prime) (hq : q.Prime) (hcop : m.Coprime (p*q))
    (hpm : 3*m<p) (hqm : 3*m<q) {u w v : FamilyPacket}
    (hu : u∈publicPackets (p*q) m) (hw : w∈publicPackets (p*q) m)
    (hv : v∈publicPackets (p*q) m) (hwu : w.residue=u.residue)
    (hvu : v.residue=u.residue) (side : Bool) (huc : CenterChoice (p*q) m u side)
    (hwc : CenterChoice (p*q) m w side) (hvc : CenterChoice (p*q) m v side) :
    ¬SemiprimeGroupSelection.ProperDivisor (p*q)
      ((p*q).gcd (rowArea m u w v : ZMod (p*q)).val) := by
  have hg := publicPacket_same_residue_center_gcd hm hp hq hcop hpm hqm
    hu hw hv hwu hvu side huc hwc hvc
  unfold SemiprimeGroupSelection.ProperDivisor
  omega

/-- The public center orientation remains a separate signed coordinate. -/
def centerFlag (side : Bool) : ℤ := if side then 1 else 0

/-- Difference of the two original public midpoint coordinates. -/
def centerDifference (N : ℕ) : ℤ := centerA N true-centerA N false

theorem centerA_split (N : ℕ) (side : Bool) :
    centerA N side=centerA N false+centerFlag side*centerDifference N := by
  cases side <;> simp only [centerFlag,centerDifference,Bool.false_eq_true,if_false,if_true]
  · ring
  · ring

theorem centerB_split (N : ℕ) (side : Bool) :
    centerB N side=centerB N false-centerFlag side*centerDifference N := by
  cases side <;> simp only [centerFlag,centerDifference,centerB,Bool.not_false,
    Bool.not_true,Bool.false_eq_true,if_false,if_true]
  · ring
  · ring

/-- Mixed-center direction, kept apart from the signed rounding errors. -/
def mixedArea (u w v : FamilyPacket) (us ws vs : Bool) : ℤ :=
  Matrix.det !![u.original.a,centerFlag us*(u.original.a-u.original.t),u.original.t;
    w.original.a,centerFlag ws*(w.original.a-w.original.t),w.original.t;
    v.original.a,centerFlag vs*(v.original.a-v.original.t),v.original.t]

/-- The two information channels add before any norm or modular projection. -/
theorem mixed_center_area {N m : ℕ} (u w v : FamilyPacket) (us ws vs : Bool)
    (hu : CenterChoice N m u us) (hw : CenterChoice N m w ws)
    (hv : CenterChoice N m v vs) :
    2*rowArea m u w v= -errorArea N m u w v us ws vs-
      centerDifference N*mixedArea u w v us ws vs := by
  have hue := packet_center_equation u us hu
  have hwe := packet_center_equation w ws hw
  have hve := packet_center_equation v vs hv
  rw [centerA_split N us,centerB_split N us] at hue
  rw [centerA_split N ws,centerB_split N ws] at hwe
  rw [centerA_split N vs,centerB_split N vs] at hve
  simp [rowArea,errorArea,mixedArea,Matrix.det_fin_three]
  linear_combination (w.original.a*v.original.t-v.original.a*w.original.t)*hue-
    (u.original.a*v.original.t-v.original.a*u.original.t)*hwe+
    (u.original.a*w.original.t-w.original.a*u.original.t)*hve

theorem mixedArea_same_center (u w v : FamilyPacket) (side : Bool) :
    mixedArea u w v side side side=0 := by
  simp [mixedArea,Matrix.det_fin_three]
  ring

/-- When two centers agree, the third center channel is a retained minor. -/
theorem mixedArea_first_center (u w v : FamilyPacket) (us ws : Bool) :
    mixedArea u w v us ws ws= -(centerFlag us-centerFlag ws)*
      (u.original.a-u.original.t)*denominatorMinor w v := by
  simp [mixedArea,denominatorMinor,Matrix.det_fin_three]
  ring

theorem mixedArea_last_center (u w v : FamilyPacket) (us vs : Bool) :
    mixedArea u w v us us vs= -(centerFlag vs-centerFlag us)*
      (v.original.a-v.original.t)*denominatorMinor u w := by
  simp [mixedArea,denominatorMinor,Matrix.det_fin_three]
  ring

/-- Residue reduction keeps the exact projective coordinate of every packet. -/
theorem packetOffset_residue_reduction (m : ℕ) (w : FamilyPacket) :
    (packetOffset m w : ZMod m)= -2*(w.original.a : ZMod m)*(w.residue : ZMod m) := by
  unfold packetOffset
  push_cast
  simp only [ZMod.natCast_self,zero_mul,zero_sub,neg_mul]

theorem publicPacket_denominator_residue_reduction {N m : ℕ} (hm : 0<m)
    {w : FamilyPacket} (hw : w∈publicPackets N m) :
    (N : ZMod m)*(w.original.t : ZMod m)=
      (w.original.a : ZMod m)*(w.residue : ZMod m)^2 := by
  have hr := publicPacket_original_relation hm hw
  unfold quotientRelation at hr
  have hc := congrArg (fun z : ℤ => (z : ZMod m)) hr
  push_cast at hc
  simp at hc
  simpa only [mul_comm] using hc.symm

/-- The retained residue coordinates give an exact Vandermonde signature.
This is modulo the auxiliary m, not modulo an unknown prime factor of N. -/
theorem publicPacket_area_residue_reduction {N m : ℕ} (hm : 0<m)
    {u w v : FamilyPacket} (hu : u∈publicPackets N m) (hw : w∈publicPackets N m)
    (hv : v∈publicPackets N m) :
    (N : ZMod m)*(rowArea m u w v : ZMod m)=
      -2*(u.original.a : ZMod m)*(w.original.a : ZMod m)*(v.original.a : ZMod m)*
        ((w.residue : ZMod m)-(u.residue : ZMod m))*
        ((v.residue : ZMod m)-(u.residue : ZMod m))*
        ((v.residue : ZMod m)-(w.residue : ZMod m)) := by
  have hue := publicPacket_denominator_residue_reduction hm hu
  have hwe := publicPacket_denominator_residue_reduction hm hw
  have hve := publicPacket_denominator_residue_reduction hm hv
  simp [rowArea,Matrix.det_fin_three]
  rw [packetOffset_residue_reduction,packetOffset_residue_reduction,
    packetOffset_residue_reduction]
  linear_combination
    (-2*(w.original.a : ZMod m)*(v.original.a : ZMod m)*
      ((v.residue : ZMod m)-(w.residue : ZMod m)))*hue+
    (2*(u.original.a : ZMod m)*(v.original.a : ZMod m)*
      ((v.residue : ZMod m)-(u.residue : ZMod m)))*hwe-
    (2*(u.original.a : ZMod m)*(w.original.a : ZMod m)*
      ((w.residue : ZMod m)-(u.residue : ZMod m)))*hve

set_option maxRecDepth 32768 in
theorem control_center_choices :
    CenterChoice 6396434398051 19 controlAnchor true ∧
      CenterChoice 6396434398051 19 controlSecond false ∧
      CenterChoice 6396434398051 19 controlThird false := by
  unfold CenterChoice
  decide +kernel

set_option maxRecDepth 32768 in
theorem control_signed_center_channels :
    centerDifference 6396434398051=1788356 ∧
      packetCenterError 6396434398051 19 controlAnchor true=200 ∧
      packetCenterError 6396434398051 19 controlSecond false=276 ∧
      packetCenterError 6396434398051 19 controlThird false=125 ∧
      errorArea 6396434398051 19 controlAnchor controlSecond controlThird true false false=12480 ∧
      mixedArea controlAnchor controlSecond controlThird true false false= -146 := by
  decide +kernel

/-- The previously successful actual triple uses a mixed-center direction. -/
theorem control_mixed_center_equation :
    2*rowArea 19 controlAnchor controlSecond controlThird=
      146*centerDifference 6396434398051-12480 := by
  rw [mixed_center_area controlAnchor controlSecond controlThird true false false
    control_center_choices.1 control_center_choices.2.1 control_center_choices.2.2,
    control_signed_center_channels.2.2.2.2.1,control_signed_center_channels.2.2.2.2.2]
  ring

end RiemannGaussian.SemiprimeRowAreaSpectrum
