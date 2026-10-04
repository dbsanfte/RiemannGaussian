/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSameResidueAreas

/-!
# All row areas in a public affine point carrier

Remove one common public midpoint plane over the integers, retaining the
signed error and the mixed-center direction separately upstream. Two
unit-guarded coordinates per packet preserve every three-row area GCD,
not just triples through a selected anchor. One anchored root axis is the
secant equation through one point of this carrier. No efficient complete
incidence extractor or universal sixth-root coverage is asserted.
-/

namespace RiemannGaussian.SemiprimeAffinePointAreas

open SemiprimeQuotientRows SemiprimeQuotientCentering SemiprimeEuclidRowFamily
open SemiprimeWeightedRows SemiprimeCompanionRows SemiprimeCompanionCenterSpectrum
open SemiprimeAffineRowRoots SemiprimeCenteredOffsetExtractor SemiprimeAnchoredRowAreas
open SemiprimeRowAreaSpectrum SemiprimeSameResidueAreas

/-- Integer residual after one common public center plane is removed. -/
def pointResidual (N m : ℕ) (w : FamilyPacket) : ℤ :=
  -2*packetOffset m w-w.original.a*centerA N false-w.original.t*centerB N false

/-- Both signed source channels commute with the common-plane removal. -/
theorem pointResidual_center_channels {N m : ℕ} (w : FamilyPacket) (side : Bool)
    (hc : CenterChoice N m w side) :
    pointResidual N m w=packetCenterError N m w side+
      centerFlag side*(w.original.a-w.original.t)*centerDifference N := by
  have h := packet_center_equation w side hc
  rw [centerA_split N side,centerB_split N side] at h
  unfold pointResidual
  linear_combination h

/-- The residual is independent of overlapping admissible center choices. -/
theorem pointResidual_center_choice {N m : ℕ} (w : FamilyPacket) (us ws : Bool)
    (hu : CenterChoice N m w us) (hw : CenterChoice N m w ws) :
    packetCenterError N m w us+centerFlag us*(w.original.a-w.original.t)*centerDifference N=
      packetCenterError N m w ws+centerFlag ws*(w.original.a-w.original.t)*centerDifference N :=
  (pointResidual_center_channels w us hu).symm.trans (pointResidual_center_channels w ws hw)

/-- A literal integer determinant, with the common plane removed before reduction. -/
theorem pointResidual_area (N m : ℕ) (u w v : FamilyPacket) :
    Matrix.det !![u.original.a,u.original.t,pointResidual N m u;
      w.original.a,w.original.t,pointResidual N m w;
      v.original.a,v.original.t,pointResidual N m v]=2*rowArea m u w v := by
  simp [pointResidual,rowArea,Matrix.det_fin_three]
  ring

/-- The original denominator ratio remains a separate coordinate. -/
def pointX (N : ℕ) (w : FamilyPacket) : ZMod N :=
  (w.original.t : ZMod N)*(w.original.a : ZMod N)⁻¹

/-- The signed residual ratio retains the second affine coordinate. -/
def pointY (N m : ℕ) (w : FamilyPacket) : ZMod N :=
  (pointResidual N m w : ZMod N)*(w.original.a : ZMod N)⁻¹

/-- One pair per full original packet; use only after its leading unit check. -/
def packetPoint (N m : ℕ) (w : FamilyPacket) : ZMod N×ZMod N :=
  (pointX N w,pointY N m w)

theorem pointX_coefficient {N : ℕ} (w : FamilyPacket)
    (hu : IsUnit (w.original.a : ZMod N)) :
    (w.original.a : ZMod N)*pointX N w=(w.original.t : ZMod N) := by
  unfold pointX
  rw [mul_left_comm,ZMod.mul_inv_of_unit _ hu,mul_one]

theorem pointY_coefficient {N m : ℕ} (w : FamilyPacket)
    (hu : IsUnit (w.original.a : ZMod N)) :
    (w.original.a : ZMod N)*pointY N m w=(pointResidual N m w : ZMod N) := by
  unfold pointY
  rw [mul_left_comm,ZMod.mul_inv_of_unit _ hu,mul_one]

/-- Constant-size incidence evaluation; no list of all triples is built. -/
def affineArea {N : ℕ} (u w v : ZMod N×ZMod N) : ZMod N :=
  Matrix.det !![1,u.1,u.2;1,w.1,w.2;1,v.1,v.2]

/-- Every triple, with arbitrary residues and centers, survives normalization. -/
theorem packetPoint_area {N m : ℕ} (u w v : FamilyPacket)
    (hu : IsUnit (u.original.a : ZMod N)) (hw : IsUnit (w.original.a : ZMod N))
    (hv : IsUnit (v.original.a : ZMod N)) :
    (u.original.a : ZMod N)*(w.original.a : ZMod N)*(v.original.a : ZMod N)*
        affineArea (packetPoint N m u) (packetPoint N m w) (packetPoint N m v)=
      2*(rowArea m u w v : ZMod N) := by
  have h := congrArg (fun z : ℤ => (z : ZMod N)) (pointResidual_area N m u w v)
  simp [Matrix.det_fin_three] at h
  rw [←pointX_coefficient u hu,←pointY_coefficient u hu,
    ←pointX_coefficient w hw,←pointY_coefficient w hw,
    ←pointX_coefficient v hv,←pointY_coefficient v hv] at h
  simp [affineArea,packetPoint,Matrix.det_fin_three]
  linear_combination h

/-- Exact GCD transport includes prime powers, zeros and whole-N saturation. -/
theorem packetPoint_area_gcd {N m : ℕ} (u w v : FamilyPacket)
    (h2 : IsUnit (2 : ZMod N)) (hu : IsUnit (u.original.a : ZMod N))
    (hw : IsUnit (w.original.a : ZMod N)) (hv : IsUnit (v.original.a : ZMod N)) :
    N.gcd (affineArea (packetPoint N m u) (packetPoint N m w) (packetPoint N m v)).val=
      N.gcd (rowArea m u w v : ZMod N).val := by
  have hp := SemiprimeRHCancellation.unit_mul_gcd_eq ((hu.mul hw).mul hv).unit
    (affineArea (packetPoint N m u) (packetPoint N m w) (packetPoint N m v))
  have htwo := SemiprimeRHCancellation.unit_mul_gcd_eq h2.unit (rowArea m u w v : ZMod N)
  rw [((hu.mul hw).mul hv).unit_spec,packetPoint_area u w v hu hw hv] at hp
  rw [h2.unit_spec] at htwo
  exact hp.symm.trans htwo

/-- Original affine roots and both residual coordinates commute with the plane removal. -/
theorem packetPoint_original_root {N m : ℕ} (w : FamilyPacket)
    (hu : IsUnit (w.original.a : ZMod N)) :
    2*packetRoot N m w false=(centerA N false : ZMod N)+
      (centerB N false : ZMod N)*pointX N w+pointY N m w := by
  have hx := pointX_coefficient w hu
  have hy := pointY_coefficient (m:=m) w hu
  have hr := packetRoot_coefficient (m:=m) w false hu
  simp only [packetScale,Bool.false_eq_true,if_false] at hr
  unfold pointResidual at hy
  push_cast at hy
  have hprod : (w.original.a : ZMod N)*
      (2*packetRoot N m w false-(centerA N false : ZMod N)-
        (centerB N false : ZMod N)*pointX N w-pointY N m w)=0 := by
    linear_combination 2*hr-hy-(centerB N false : ZMod N)*hx
  have h := congrArg (fun z => (w.original.a : ZMod N)⁻¹*z) hprod
  rw [←mul_assoc,ZMod.inv_mul_of_unit _ hu,one_mul,mul_zero] at h
  linear_combination h

/-- The two-point denominator minor is one coordinate difference with unit phases. -/
theorem pointX_minor {N : ℕ} (u w : FamilyPacket)
    (hu : IsUnit (u.original.a : ZMod N)) (hw : IsUnit (w.original.a : ZMod N)) :
    (u.original.a : ZMod N)*(w.original.a : ZMod N)*(pointX N w-pointX N u)=
      (denominatorMinor u w : ZMod N) := by
  have hx := pointX_coefficient u hu
  have hy := pointX_coefficient w hw
  simp only [denominatorMinor,Int.cast_sub,Int.cast_mul]
  linear_combination (u.original.a : ZMod N)*hy-(w.original.a : ZMod N)*hx

theorem pointY_minor {N m : ℕ} (u w : FamilyPacket)
    (hu : IsUnit (u.original.a : ZMod N)) (hw : IsUnit (w.original.a : ZMod N)) :
    (u.original.a : ZMod N)*(w.original.a : ZMod N)*(pointY N m w-pointY N m u)=
      -2*(offsetMinor m u w : ZMod N)-
        (centerB N false : ZMod N)*(denominatorMinor u w : ZMod N) := by
  have hx := pointY_coefficient (m:=m) u hu
  have hy := pointY_coefficient (m:=m) w hw
  simp only [pointResidual,Int.cast_sub,Int.cast_mul,Int.cast_neg,Int.cast_ofNat] at hx hy
  simp only [offsetMinor,denominatorMinor,Int.cast_sub,Int.cast_mul]
  linear_combination (u.original.a : ZMod N)*hy-(w.original.a : ZMod N)*hx

/-- The residual scalar channel retains a new signed two-row functional. -/
theorem pointY_difference_gcd {N m : ℕ} (u w : FamilyPacket)
    (hu : IsUnit (u.original.a : ZMod N)) (hw : IsUnit (w.original.a : ZMod N)) :
    N.gcd (pointY N m w-pointY N m u).val=
      N.gcd (-2*(offsetMinor m u w : ZMod N)-
        (centerB N false : ZMod N)*(denominatorMinor u w : ZMod N)).val := by
  have h := SemiprimeRHCancellation.unit_mul_gcd_eq (hu.mul hw).unit
    (pointY N m w-pointY N m u)
  rw [(hu.mul hw).unit_spec,pointY_minor u w hu hw] at h
  exact h.symm

/-- One old root axis is the secant equation through one retained point. -/
theorem anchorSlope_secant {N m : ℕ} (u w : FamilyPacket)
    (hu : IsUnit (u.original.a : ZMod N)) (hw : IsUnit (w.original.a : ZMod N))
    (hd : IsUnit (denominatorMinor u w : ZMod N)) :
    (pointX N w-pointX N u)*(2*anchorSlope N m u w+(centerB N false : ZMod N))+
      (pointY N m w-pointY N m u)=0 := by
  have hx := pointX_minor u w hu hw
  have hy := pointY_minor (m:=m) u w hu hw
  have hs := anchorSlope_coefficient (m:=m) u w hd
  have hprod : ((u.original.a : ZMod N)*(w.original.a : ZMod N))*
      ((pointX N w-pointX N u)*(2*anchorSlope N m u w+(centerB N false : ZMod N))+
        (pointY N m w-pointY N m u))=0 := by
    linear_combination (2*anchorSlope N m u w+(centerB N false : ZMod N))*hx+hy+2*hs
  have h := congrArg (fun z => ((u.original.a : ZMod N)*(w.original.a : ZMod N))⁻¹*z) hprod
  rw [←mul_assoc,ZMod.inv_mul_of_unit _ (hu.mul hw),one_mul,mul_zero] at h
  exact h

/-- The source list remains available before its complete two-coordinate fork. -/
def publicPoints (N m : ℕ) : List (ZMod N×ZMod N) :=
  (publicPackets N m).map (packetPoint N m)

theorem publicPoints_length (N m : ℕ) : (publicPoints N m).length=(publicPackets N m).length :=
  List.length_map _

/-- This is a stored-coordinate count, not a full incidence bit-complexity theorem. -/
theorem publicPoints_length_prime_le (N : ℕ) {m : ℕ} (hm : m.Prime) :
    (publicPoints N m).length≤8*m*(Nat.log2 m+1)^2 := by
  rw [publicPoints_length]
  exact SemiprimeEuclidRowBudget.publicPackets_length_le N hm

theorem publicPacket_numerator_ne_zero {N m : ℕ} (hm : 0<m) {w : FamilyPacket}
    (hw : w∈publicPackets N m) : w.original.a≠0 := by
  obtain ⟨j,_,hw⟩ := List.mem_flatMap.mp hw
  split_ifs at hw
  · obtain ⟨z,hz,hw⟩ := List.mem_flatMap.mp hw
    have ha := (publicPairs_correct hm hz).1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl <;> exact ha
  · simp only [List.not_mem_nil] at hw

/-- Large-factor membership discharges the leading-coordinate unit guard. -/
theorem publicPacket_leading_unit {p q m : ℕ} (hm : 0<m) (hp : p.Prime) (hq : q.Prime)
    (hmp : m<p) (hmq : m<q) {w : FamilyPacket} (hw : w∈publicPackets (p*q) m) :
    IsUnit (w.original.a : ZMod (p*q)) := by
  have hb := (publicPacket_coefficient_bounds hm hw).1
  exact bounded_int_isUnit hp hq (publicPacket_numerator_ne_zero hm hw)
    (hb.trans_lt (by exact_mod_cast hmp)) (hb.trans_lt (by exact_mod_cast hmq))

theorem two_isUnit_of_large_primes {p q m : ℕ} (hm : 2≤m) (hp : p.Prime) (hq : q.Prime)
    (hmp : m<p) (hmq : m<q) : IsUnit (2 : ZMod (p*q)) := by
  have h := bounded_int_isUnit hp hq (by norm_num : (2 : ℤ)≠0)
    (by norm_num; exact_mod_cast hm.trans_lt hmp)
    (by norm_num; exact_mod_cast hm.trans_lt hmq)
  simpa using h

/-- All actual public triples survive the full point fork in the hard branch.
No balanced-ratio restriction or distinct-prime assumption is needed. -/
theorem publicPacket_point_area_gcd {p q m : ℕ} (hm : 2≤m)
    (hp : p.Prime) (hq : q.Prime) (hmp : m<p) (hmq : m<q) {u w v : FamilyPacket}
    (hu : u∈publicPackets (p*q) m) (hw : w∈publicPackets (p*q) m)
    (hv : v∈publicPackets (p*q) m) :
    (p*q).gcd (affineArea (packetPoint (p*q) m u) (packetPoint (p*q) m w)
      (packetPoint (p*q) m v)).val=(p*q).gcd (rowArea m u w v : ZMod (p*q)).val := by
  have hmpos : 0<m := by omega
  exact packetPoint_area_gcd u w v (two_isUnit_of_large_primes hm hp hq hmp hmq)
    (publicPacket_leading_unit hmpos hp hq hmp hmq hu)
    (publicPacket_leading_unit hmpos hp hq hmp hmq hw)
    (publicPacket_leading_unit hmpos hp hq hmp hmq hv)

end RiemannGaussian.SemiprimeAffinePointAreas
