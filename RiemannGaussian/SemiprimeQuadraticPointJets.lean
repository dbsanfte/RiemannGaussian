/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeAffinePointAreas
import RiemannGaussian.SemiprimeStrassenPrefix

/-!
# Auxiliary conic constraints before factor-field projection

The quotient relation retains an exact discriminant multiple of m².
After unit normalization, the original packets lie on a public conic
modulo m², with one tangent equation for each residue. This is a separate
modulus from the whole input N: no factor-field conic or useful incidence
coverage is inferred from the auxiliary constraint.
-/

namespace RiemannGaussian.SemiprimeQuadraticPointJets

open SemiprimeQuotientRows SemiprimeQuotientCentering SemiprimeEuclidRowFamily
open SemiprimeWeightedRows
open SemiprimeCompanionRows SemiprimeCompanionCenterSpectrum SemiprimeAffineRowRoots
open SemiprimeCenteredOffsetExtractor SemiprimeRowAreaSpectrum
open SemiprimeSameResidueAreas SemiprimeAffinePointAreas
open SemiprimeAnchoredRowAreas

/-- The full original quotient relation gives an exact integer discriminant. -/
theorem quotient_discriminant {N m j a b c t : ℤ}
    (hq : quotientRelation N m j a b c t) :
    (m*b-2*a*j)^2-4*N*a*t=m^2*(b^2-4*a*c) := by
  unfold quotientRelation at hq
  linear_combination 4*a*hq

/-- Recentring retains the discriminant before any modular reduction. -/
theorem publicPacket_discriminant {N m : ℕ} (hm : 0<m) {w : FamilyPacket}
    (hw : w∈publicPackets N m) :
    (packetOffset m w)^2-4*(N : ℤ)*w.original.a*w.original.t=
      (m : ℤ)^2*((centeredPacketRow m w).b^2-
        4*w.original.a*(centeredPacketRow m w).c) := by
  have h := quotient_discriminant (publicPacket_relation hm hw)
  simpa only [packetOffset,centeredPacketRow,shiftRow] using h

theorem publicPacket_discriminant_dvd {N m : ℕ} (hm : 0<m) {w : FamilyPacket}
    (hw : w∈publicPackets N m) :
    (m : ℤ)^2∣(packetOffset m w)^2-4*(N : ℤ)*w.original.a*w.original.t := by
  rw [publicPacket_discriminant hm hw]
  exact dvd_mul_right _ _

/-- Keep the physical-input midpoint plane while clearing the normalization. -/
theorem publicPacket_residual_conic_integer {N m : ℕ} (hm : 0<m)
    {w : FamilyPacket} (hw : w∈publicPackets N m) :
    (pointResidual N m w+w.original.a*centerA N false+
      w.original.t*centerB N false)^2-16*(N : ℤ)*w.original.a*w.original.t=
      4*(m : ℤ)^2*((centeredPacketRow m w).b^2-
        4*w.original.a*(centeredPacketRow m w).c) := by
  have h := publicPacket_discriminant hm hw
  unfold pointResidual
  linear_combination 4*h

/-- The strict numerator bound discharges the auxiliary-m² unit guard. -/
theorem publicPacket_auxiliary_leading_unit {N m : ℕ} (hm : m.Prime)
    {w : FamilyPacket} (hw : w∈publicPackets N m) :
    IsUnit (w.original.a : ZMod (m^2)) := by
  have hnonzero := publicPacket_numerator_ne_zero hm.pos hw
  have ha : |w.original.a|<(m : ℤ) := by
    obtain ⟨j,_,hw⟩ := List.mem_flatMap.mp hw
    split_ifs at hw
    · obtain ⟨z,hz,hw⟩ := List.mem_flatMap.mp hw
      have hb := publicPairs_numerator_lt hm.pos hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl
      all_goals
        change |z.1|<(m : ℤ)
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hb
    · simp only [List.not_mem_nil] at hw
  rw [pow_two]
  exact bounded_int_isUnit hm hm hnonzero ha ha

/-- Denominator ratio in the auxiliary ring, distinct from the factor carrier. -/
def jetX (m : ℕ) (w : FamilyPacket) : ZMod (m^2) := pointX (m^2) w

/-- The physical midpoint residual, reduced in the auxiliary ring only. -/
def jetY (N m : ℕ) (w : FamilyPacket) : ZMod (m^2) :=
  (pointResidual N m w : ZMod (m^2))*(w.original.a : ZMod (m^2))⁻¹

theorem jetY_coefficient {N m : ℕ} (w : FamilyPacket)
    (hu : IsUnit (w.original.a : ZMod (m^2))) :
    (w.original.a : ZMod (m^2))*jetY N m w=(pointResidual N m w : ZMod (m^2)) := by
  unfold jetY
  rw [mul_left_comm,ZMod.mul_inv_of_unit _ hu,mul_one]

/-- Remove the common plane without replacing the physical input by m². -/
theorem jetY_affine {N m : ℕ} (w : FamilyPacket)
    (hu : IsUnit (w.original.a : ZMod (m^2))) :
    jetY N m w+(centerA N false : ZMod (m^2))+
      (centerB N false : ZMod (m^2))*jetX m w=2*packetRoot (m^2) m w false := by
  have hx := pointX_coefficient w hu
  have hy := jetY_coefficient (N:=N) w hu
  have hr := packetRoot_coefficient (m:=m) w false hu
  simp only [packetScale,Bool.false_eq_true,if_false] at hr
  unfold pointResidual at hy
  push_cast at hy
  have hprod : (w.original.a : ZMod (m^2))*
      (jetY N m w+(centerA N false : ZMod (m^2))+
        (centerB N false : ZMod (m^2))*jetX m w-2*packetRoot (m^2) m w false)=0 := by
    unfold jetX
    linear_combination hy+(centerB N false : ZMod (m^2))*hx-2*hr
  have h := congrArg (fun z => (w.original.a : ZMod (m^2))⁻¹*z) hprod
  rw [←mul_assoc,ZMod.inv_mul_of_unit _ hu,one_mul,mul_zero] at h
  linear_combination h

/-- Original packets satisfy the conic modulo m², not modulo either factor. -/
theorem publicPacket_auxiliary_conic {N m : ℕ} (hm : 0<m) {w : FamilyPacket}
    (hw : w∈publicPackets N m) (hu : IsUnit (w.original.a : ZMod (m^2))) :
    (2*packetRoot (m^2) m w false)^2=16*(N : ZMod (m^2))*jetX m w := by
  have hz : (((packetOffset m w)^2-4*(N : ℤ)*w.original.a*w.original.t : ℤ) : ZMod (m^2))=0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    simpa only [Nat.cast_pow] using publicPacket_discriminant_dvd hm hw
  push_cast at hz
  have hx := pointX_coefficient w hu
  have hr := packetRoot_coefficient (m:=m) w false hu
  simp only [packetScale,Bool.false_eq_true,if_false] at hr
  have hprod : (w.original.a : ZMod (m^2))^2*
      ((2*packetRoot (m^2) m w false)^2-16*(N : ZMod (m^2))*jetX m w)=0 := by
    unfold jetX
    linear_combination 4*hz+
      4*((w.original.a : ZMod (m^2))*packetRoot (m^2) m w false-
        (packetOffset m w : ZMod (m^2)))*hr-16*(N : ZMod (m^2))*
        (w.original.a : ZMod (m^2))*hx
  have h := congrArg (fun z => ((w.original.a : ZMod (m^2))^2)⁻¹*z) hprod
  rw [←mul_assoc,ZMod.inv_mul_of_unit _ (hu.pow 2),one_mul,mul_zero] at h
  exact sub_eq_zero.mp h

/-- All actual public packets, with their physical centers, lie on the auxiliary conic. -/
theorem publicPacket_jet_conic {N m : ℕ} (hm : m.Prime) {w : FamilyPacket}
    (hw : w∈publicPackets N m) :
    (jetY N m w+(centerA N false : ZMod (m^2))+
      (centerB N false : ZMod (m^2))*jetX m w)^2=
      16*(N : ZMod (m^2))*jetX m w := by
  have hu := publicPacket_auxiliary_leading_unit hm hw
  rw [jetY_affine w hu]
  exact publicPacket_auxiliary_conic hm.pos hw hu

/-- One residue supplies a literal tangent equation over the integers. -/
theorem publicPacket_tangent_integer {N m : ℕ} (hm : 0<m) {w : FamilyPacket}
    (hw : w∈publicPackets N m) :
    (w.residue : ℤ)*packetOffset m w+w.original.a*w.residue^2+
      (N : ℤ)*w.original.t=(m : ℤ)^2*(centeredPacketRow m w).c := by
  have h := publicPacket_relation hm hw
  simp only [quotientRelation,centeredPacketRow,shiftRow] at h
  simp only [packetOffset,centeredPacketRow,shiftRow]
  linear_combination -h

/-- Every packet lies on the auxiliary tangent belonging to its own residue. -/
theorem publicPacket_auxiliary_tangent {N m : ℕ} (hm : 0<m) {w : FamilyPacket}
    (hw : w∈publicPackets N m) (hu : IsUnit (w.original.a : ZMod (m^2))) :
    (w.residue : ZMod (m^2))*(2*packetRoot (m^2) m w false)=
      2*(w.residue : ZMod (m^2))^2+2*(N : ZMod (m^2))*jetX m w := by
  have hz : (((w.residue : ℤ)*packetOffset m w+w.original.a*w.residue^2+
      (N : ℤ)*w.original.t : ℤ) : ZMod (m^2))=0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    rw [publicPacket_tangent_integer hm hw,Nat.cast_pow]
    exact dvd_mul_right _ _
  push_cast at hz
  have hx := pointX_coefficient w hu
  have hr := packetRoot_coefficient (m:=m) w false hu
  simp only [packetScale,Bool.false_eq_true,if_false] at hr
  have hprod : (w.original.a : ZMod (m^2))*
      ((w.residue : ZMod (m^2))*(2*packetRoot (m^2) m w false)-
        2*(w.residue : ZMod (m^2))^2-2*(N : ZMod (m^2))*jetX m w)=0 := by
    unfold jetX
    linear_combination -2*hz+2*(w.residue : ZMod (m^2))*hr-2*(N : ZMod (m^2))*hx
  have h := congrArg (fun z => (w.original.a : ZMod (m^2))⁻¹*z) hprod
  rw [←mul_assoc,ZMod.inv_mul_of_unit _ hu,one_mul,mul_zero] at h
  linear_combination h

/-- The tangent displacement is square-zero in the auxiliary ring. -/
theorem publicPacket_auxiliary_nilpotent {N m : ℕ} (hm : 0<m) {w : FamilyPacket}
    (hw : w∈publicPackets N m) (hu : IsUnit (w.original.a : ZMod (m^2))) :
    (2*packetRoot (m^2) m w false-4*(w.residue : ZMod (m^2)))^2=0 := by
  have hc := publicPacket_auxiliary_conic hm hw hu
  have ht := publicPacket_auxiliary_tangent hm hw hu
  linear_combination hc-8*ht

/-- Signed midpoint channels retain the same nilpotent without changing moduli. -/
theorem publicPacket_jet_nilpotent {N m : ℕ} (hm : m.Prime) {w : FamilyPacket}
    (hw : w∈publicPackets N m) :
    (jetY N m w+(centerA N false : ZMod (m^2))+
      (centerB N false : ZMod (m^2))*jetX m w-4*(w.residue : ZMod (m^2)))^2=0 := by
  have hu := publicPacket_auxiliary_leading_unit hm hw
  rw [jetY_affine w hu]
  exact publicPacket_auxiliary_nilpotent hm.pos hw hu

/-- The first affine coordinate transports exactly the original two-row minor. -/
theorem pointX_difference_gcd {N : ℕ} (u w : FamilyPacket)
    (hu : IsUnit (u.original.a : ZMod N)) (hw : IsUnit (w.original.a : ZMod N)) :
    N.gcd (pointX N w-pointX N u).val=N.gcd (denominatorMinor u w : ZMod N).val := by
  have h := SemiprimeRHCancellation.unit_mul_gcd_eq (hu.mul hw).unit
    (pointX N w-pointX N u)
  rw [(hu.mul hw).unit_spec,pointX_minor u w hu hw] at h
  exact h.symm

/-- Large prime factors make every nonzero original coefficient minor a unit. -/
theorem publicPacket_minor_zero_or_unit {p q m : ℕ} (hm : 0<m)
    (hp : p.Prime) (hq : q.Prime) (hmp : m^2<p) (hmq : m^2<q)
    {u w : FamilyPacket} (hu : u∈publicPackets (p*q) m)
    (hw : w∈publicPackets (p*q) m) :
    denominatorMinor u w=0 ∨ IsUnit (denominatorMinor u w : ZMod (p*q)) := by
  by_cases hz : denominatorMinor u w=0
  · exact Or.inl hz
  · have hb := publicPacket_minor_abs_le hm hu hw
    exact Or.inr (bounded_int_isUnit hp hq hz
      (hb.trans_lt (by exact_mod_cast hmp)) (hb.trans_lt (by exact_mod_cast hmq)))

/-- No pair in the first coordinate alone has a proper GCD in the large-factor branch. -/
theorem publicPacket_pointX_no_proper_gcd {p q m : ℕ} (hm : 0<m)
    (hp : p.Prime) (hq : q.Prime) (hmp : m^2<p) (hmq : m^2<q)
    {u w : FamilyPacket} (hu : u∈publicPackets (p*q) m)
    (hw : w∈publicPackets (p*q) m) :
    ¬SemiprimeGroupSelection.ProperDivisor (p*q)
      ((p*q).gcd (pointX (p*q) w-pointX (p*q) u).val) := by
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  have hsmall : m≤m^2 := by simpa only [pow_two] using Nat.le_mul_self m
  have hau := publicPacket_leading_unit hm hp hq (hsmall.trans_lt hmp)
    (hsmall.trans_lt hmq) hu
  have haw := publicPacket_leading_unit hm hp hq (hsmall.trans_lt hmp)
    (hsmall.trans_lt hmq) hw
  rw [pointX_difference_gcd u w hau haw]
  rcases publicPacket_minor_zero_or_unit hm hp hq hmp hmq hu hw with hz|hunit
  · simp only [hz,Int.cast_zero,ZMod.val_zero,Nat.gcd_zero_right,
      SemiprimeGroupSelection.ProperDivisor,lt_self_iff_false,and_false,false_and,not_false_eq_true]
  · rw [(SemiprimeBulkNorm.gcd_one_iff_unit _).mpr hunit]
    simp only [SemiprimeGroupSelection.ProperDivisor,lt_self_iff_false,false_and,not_false_eq_true]

/-- The existing compressed prefix supplies signed bounded units without factor labels. -/
theorem prefix_none_bounded_int_unit {N m : ℕ} (hcover : m^2<N)
    (hnone : SemiprimeStrassenPrefix.factorPrefix N m=none) {k : ℤ}
    (hk : k≠0) (hbound : |k|≤(m : ℤ)^2) : IsUnit (k : ZMod N) := by
  have hkpos := Int.natAbs_pos.mpr hk
  have hkbound : k.natAbs≤m^2 := by
    rw [Int.abs_eq_natAbs] at hbound
    exact_mod_cast hbound
  have hcop := SemiprimeStrassenPrefix.prefix_none_coprime_integer hcover hnone hkpos hkbound
  have hu := (ZMod.isUnit_iff_coprime k.natAbs N).mpr hcop.symm
  have habsu : IsUnit ((|k| : ℤ) : ZMod N) := by
    simpa only [Int.abs_eq_natAbs,Int.cast_natCast] using hu
  by_cases hnonneg : 0≤k
  · simpa only [abs_of_nonneg hnonneg] using habsu
  · rw [abs_of_neg (lt_of_not_ge hnonneg),Int.cast_neg] at habsu
    simpa only [neg_neg] using habsu.neg

/-- Actual original leading coefficients are units after the N-only prefix fails. -/
theorem prefix_none_publicPacket_leading_unit {N m : ℕ} (hm : 0<m)
    (hcover : m^2<N) (hnone : SemiprimeStrassenPrefix.factorPrefix N m=none)
    {w : FamilyPacket} (hw : w∈publicPackets N m) : IsUnit (w.original.a : ZMod N) := by
  apply prefix_none_bounded_int_unit hcover hnone (publicPacket_numerator_ne_zero hm hw)
  exact (publicPacket_coefficient_bounds hm hw).1.trans
    (by exact_mod_cast (show m≤m^2 by simpa only [pow_two] using Nat.le_mul_self m))

/-- Every possible two-row minor is zero or unit after one public prefix stage. -/
theorem prefix_none_publicPacket_minor_zero_or_unit {N m : ℕ} (hm : 0<m)
    (hcover : m^2<N) (hnone : SemiprimeStrassenPrefix.factorPrefix N m=none)
    {u w : FamilyPacket} (hu : u∈publicPackets N m) (hw : w∈publicPackets N m) :
    denominatorMinor u w=0 ∨ IsUnit (denominatorMinor u w : ZMod N) := by
  by_cases hz : denominatorMinor u w=0
  · exact Or.inl hz
  · exact Or.inr (prefix_none_bounded_int_unit hcover hnone hz
      (publicPacket_minor_abs_le hm hu hw))

/-- A failed public prefix transports all triple GCDs without supplied prime factors. -/
theorem prefix_none_publicPacket_point_area_gcd {N m : ℕ} (hm : 2≤m)
    (hcover : m^2<N) (hnone : SemiprimeStrassenPrefix.factorPrefix N m=none)
    {u w v : FamilyPacket} (hu : u∈publicPackets N m) (hw : w∈publicPackets N m)
    (hv : v∈publicPackets N m) :
    N.gcd (affineArea (packetPoint N m u) (packetPoint N m w) (packetPoint N m v)).val=
      N.gcd (rowArea m u w v : ZMod N).val := by
  have hmpos : 0<m := by omega
  have h2int := prefix_none_bounded_int_unit hcover hnone (by norm_num : (2 : ℤ)≠0)
    (by
      norm_num
      have hmz : (2 : ℤ)≤m := by exact_mod_cast hm
      nlinarith only [hmz])
  have h2 : IsUnit (2 : ZMod N) := by simpa using h2int
  exact packetPoint_area_gcd u w v h2
    (prefix_none_publicPacket_leading_unit hmpos hcover hnone hu)
    (prefix_none_publicPacket_leading_unit hmpos hcover hnone hw)
    (prefix_none_publicPacket_leading_unit hmpos hcover hnone hv)

end RiemannGaussian.SemiprimeQuadraticPointJets
