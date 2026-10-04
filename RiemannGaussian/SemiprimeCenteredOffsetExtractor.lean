/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeAffineRowRoots

/-!
# Extract the centered offset before constructing the large constant term

The original packet remains the source. A second constructor uses its public
Euclidean coordinates, the residue modulo m² and the two exact integer
midpoints. The commuting identities below preserve the signed offset, both
affine coordinates and each primitive companion. They reduce intermediate
integer sizes; they do not supply universal coverage or a bit clock.
-/

namespace RiemannGaussian.SemiprimeCenteredOffsetExtractor

open SemiprimeQuotientRows SemiprimeQuotientCentering SemiprimeEuclidRowFamily
open SemiprimeWeightedRows SemiprimeCompanionRows SemiprimeCompanionCenterSpectrum
open SemiprimeAffineRowRoots

/-- Center an offset with the original signed floor division and tie rule. -/
def recenter (S d L : ℤ) : ℤ := L-((S+2*L+d)/(2*d))*d

/-- Translating by an integer period changes the selected shift equally. -/
theorem recenter_periodic (S L k : ℤ) {d : ℤ} (hd : d≠0) :
    recenter S d (L+d*k)=recenter S d L := by
  unfold recenter
  have he : S+2*(L+d*k)+d=(S+2*L+d)+k*(2*d) := by ring
  rw [he,Int.add_mul_ediv_right _ _ (by omega : 2*d≠0)]
  ring

/-- The residue is sufficient, including negative offsets and exact ties. -/
theorem recenter_emod (S L : ℤ) {d : ℤ} (hd : d≠0) :
    recenter S d (L%d)=recenter S d L := by
  have h := recenter_periodic S (L%d) (L/d) hd
  rw [Int.emod_add_mul_ediv] at h
  exact h.symm

theorem recenter_of_modEq (S : ℤ) {d L K : ℤ} (hd : d≠0)
    (h : L ≡ K [ZMOD d]) : recenter S d L=recenter S d K := by
  rw [←recenter_emod S L hd,←recenter_emod S K hd,h]

/-- The exact quotient relation determines the linear offset modulo m².
No constant coefficient is used on the right side. -/
theorem quotient_offset_modEq {N m j a b c t u : ℤ}
    (hq : quotientRelation N m j a b c t) (hu : j*u ≡ 1 [ZMOD m^2]) :
    m*b-2*a*j ≡ -a*j-N*t*u [ZMOD m^2] := by
  let L := m*b-2*a*j
  have hz : N*t+a*j^2+j*L ≡ 0 [ZMOD m^2] := by
    apply Int.modEq_zero_iff_dvd.mpr
    refine ⟨c,?_⟩
    dsimp [L]
    unfold quotientRelation at hq
    linear_combination -hq
  have h := ((hu.mul_right (a*j+L)).sub (hz.mul_left u)).sub (Int.ModEq.refl (a*j))
  have he : -a*j-N*t*u ≡ L [ZMOD m^2] := by
    convert h using 1 <;> ring
  exact he.symm

/-- Only N modulo m² enters the residue extractor. The inverse is public
Bezout data for j modulo m², rather than an inverse in either private field. -/
def residueOffset (N m j : ℕ) (a t : ℤ) : ℤ :=
  (-a*j-((N : ℤ)%(m : ℤ)^2)*t*publicInverse (m^2) j)%(m : ℤ)^2

theorem quotient_residueOffset {N m j : ℕ} {a b c t : ℤ}
    (hj : j.Coprime m) (hq : quotientRelation N m j a b c t) :
    (m : ℤ)*b-2*a*j ≡ residueOffset N m j a t [ZMOD (m : ℤ)^2] := by
  have hu : (j : ℤ)*publicInverse (m^2) j ≡ 1 [ZMOD (m : ℤ)^2] := by
    simpa only [Nat.cast_pow] using publicInverse_correct (hj.pow_right 2)
  have h := quotient_offset_modEq hq hu
  have hN := (Int.mod_modEq (N : ℤ) ((m : ℤ)^2)).mul_right
    (t*publicInverse (m^2) j)
  have he : (-a*(j : ℤ)-((N : ℤ)%(m : ℤ)^2)*t*publicInverse (m^2) j) ≡
      -a*(j : ℤ)-(N : ℤ)*t*publicInverse (m^2) j [ZMOD (m : ℤ)^2] := by
    convert (Int.ModEq.refl (-a*(j : ℤ))).sub hN using 1 <;> ring
  exact h.trans (he.symm.trans (Int.mod_modEq _ _).symm)

/-- Membership also supplies the unshifted source relation. -/
theorem publicPacket_original_relation {N m : ℕ} (hm : 0<m) {w : FamilyPacket}
    (hw : w∈publicPackets N m) :
    quotientRelation N m w.residue w.original.a w.original.b w.original.c w.original.t := by
  have h := publicPacket_relation hm hw
  simp only [centeredPacketRow,shiftRow,quotientRelation] at h ⊢
  linear_combination h

theorem publicPacket_residue_coprime {N m : ℕ} {w : FamilyPacket}
    (hw : w∈publicPackets N m) : w.residue.Coprime m := by
  obtain ⟨j,_,hw⟩ := List.mem_flatMap.mp hw
  split_ifs at hw with hj
  · obtain ⟨v,_,hw⟩ := List.mem_flatMap.mp hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl <;> exact hj
  · simp only [List.not_mem_nil] at hw

/-- The original signed midpoint acts on its linear offset alone. -/
theorem packetOffset_recenter {N m : ℕ} (w : FamilyPacket) (side : Bool)
    (hc : CenterChoice N m w side) :
    packetOffset m w=recenter
      (w.original.a*centerA N side+w.original.t*centerB N side) ((m : ℤ)^2)
      ((m : ℤ)*w.original.b-2*w.original.a*w.residue) := by
  unfold CenterChoice centerNumerator roundedShift at hc
  rw [mul_comm w.original.b (m : ℤ)] at hc
  simp only [packetOffset,centeredPacketRow,shiftRow,recenter,hc]
  ring

/-- Direct offset construction; no lifted constant coefficient is evaluated. -/
def reducedPacketOffset (N m : ℕ) (j : ℕ) (a t : ℤ) (side : Bool) : ℤ :=
  recenter (a*centerA N side+t*centerB N side) ((m : ℤ)^2) (residueOffset N m j a t)

/-- The direct construction agrees as an integer, before reducing modulo N. -/
theorem publicPacket_reduced_offset {N m : ℕ} (hm : 0<m) {w : FamilyPacket}
    (hw : w∈publicPackets N m) (side : Bool) (hc : CenterChoice N m w side) :
    reducedPacketOffset N m w.residue w.original.a w.original.t side=packetOffset m w := by
  have hr := quotient_residueOffset (publicPacket_residue_coprime hw)
    (publicPacket_original_relation hm hw)
  rw [packetOffset_recenter w side hc]
  unfold reducedPacketOffset
  exact (recenter_of_modEq _ (by positivity : (m : ℤ)^2≠0) hr).symm

/-- Every literal residue packet supplies its public orientation. -/
theorem residuePacket_center_choice {N m j : ℕ} {w : FamilyPacket}
    (hw : w∈residuePackets N m j) : ∃ side : Bool, CenterChoice N m w side := by
  obtain ⟨v,_,hw⟩ := List.mem_flatMap.mp hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl
  · refine ⟨false,?_⟩
    simpa only [CenterChoice,centerA,centerB,Bool.not_false,Bool.false_eq_true,if_false,if_true]
      using publicShift_midpoint N m j (liftRow N m j (publicInverse m j) v.1 v.2)
  · refine ⟨true,?_⟩
    simpa only [CenterChoice,centerA,centerB,Bool.not_true,Bool.false_eq_true,if_false,if_true]
      using reflectedShift_midpoint N m j (liftRow N m j (publicInverse m j) v.1 v.2)

theorem publicPacket_center_choice {N m : ℕ} {w : FamilyPacket}
    (hw : w∈publicPackets N m) : ∃ side : Bool, CenterChoice N m w side := by
  obtain ⟨j,_,hw⟩ := List.mem_flatMap.mp hw
  split_ifs at hw
  · exact residuePacket_center_choice hw
  · simp only [List.not_mem_nil] at hw

/-- Both affine channels use exactly the same signed integer offset. -/
theorem publicPacket_reduced_root {N m : ℕ} (hm : 0<m) {w : FamilyPacket}
    (hw : w∈publicPackets N m) (center channel : Bool) (hc : CenterChoice N m w center) :
    -(reducedPacketOffset N m w.residue w.original.a w.original.t center : ZMod N)*
      (packetScale w channel : ZMod N)⁻¹=packetRoot N m w channel := by
  rw [publicPacket_reduced_offset hm hw center hc]
  rfl

/-- The weighted companion is recovered directly from the two offsets.
The original packet and primitive checks remain upstream. -/
theorem publicPacket_companion_offset {N m : ℕ} {w : WeightedPacket}
    (hw : w∈publicWeightedPackets N m) (hp : PrimitivePacket m w) :
    rowDet w.left.original w.right.original*packetCompanion m w=
      -(w.right.original.t*packetOffset m w.left-w.left.original.t*packetOffset m w.right) := by
  have hf := publicPacket_coordinate_factorization hw hp 1
  have hs : w.right.residue=w.left.residue := by
    obtain ⟨j,_,hw⟩ := List.mem_flatMap.mp hw
    split_ifs at hw with hj
    · have h := weightedResiduePacket_relations hp.1 hj hw
      exact h.2.1.trans h.1.symm
    · simp only [List.not_mem_nil] at hw
  have hdet : rowDet w.left.original w.right.original=(m : ℤ)*packetOrientation m w := by
    have hd : (m : ℤ)∣rowDet w.left.original w.right.original := by
      rw [←dvd_abs,hp.2.1]
    exact (Int.mul_ediv_cancel' hd).symm
  simp only [centeredPacketRow,shiftRow,one_pow,mul_one] at hf
  simp only [packetOffset,centeredPacketRow,shiftRow,rowDet] at hdet ⊢
  rw [hs]
  linear_combination hf+(packetCompanion m w-1)*hdet

/-- Exact integer division by the checked nonzero determinant, without
forming the large Nt-containing exponents. -/
theorem publicPacket_companion_div {N m : ℕ} {w : WeightedPacket}
    (hw : w∈publicWeightedPackets N m) (hp : PrimitivePacket m w) :
    -(w.right.original.t*packetOffset m w.left-w.left.original.t*packetOffset m w.right)/
      rowDet w.left.original w.right.original=packetCompanion m w := by
  rw [←publicPacket_companion_offset hw hp,Int.mul_ediv_cancel_left]
  intro hz
  have h := hp.2.1
  rw [hz,abs_zero] at h
  have hm := hp.1
  omega

end RiemannGaussian.SemiprimeCenteredOffsetExtractor
