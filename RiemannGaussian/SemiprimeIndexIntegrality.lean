/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePartnerRecoveryObstruction
import Mathlib.RingTheory.Int.Basic

/-!
# Exact residue information in the original row's integral index

For an actual public packet and prime auxiliary modulus, m² divides the
factor sum exactly when the factor has the packet's residue modulo m.
Every same-residue row therefore has the same bare index-integrality
condition, and rows of distinct residues cannot simultaneously have
integral indices for one factor orientation. The factor pair is integral
and satisfies N=p*q throughout; this does not rule out using integrality
to search for that pair, or using bounds on the actual index values.
-/

namespace RiemannGaussian.SemiprimeIndexIntegrality

open SemiprimeQuotientRows SemiprimeQuotientCentering SemiprimeEuclidRowFamily
open SemiprimeCompanionRows SemiprimeCompanionCenterSpectrum SemiprimeAffineRowRoots
open SemiprimeCenteredOffsetExtractor SemiprimeQuadraticPointJets
open SemiprimeLiteralQuadraticRoots SemiprimePartnerRecoveryObstruction

/-- The auxiliary leading unit descends from m² to the prime modulus m. -/
theorem publicPacket_leading_auxiliary_unit {N m : ℕ} (hm : m.Prime)
    {w : FamilyPacket} (hw : w∈publicPackets N m) : IsUnit (w.original.a : ZMod m) := by
  have hd : m∣m^2 := by rw [pow_two]; exact dvd_mul_right m m
  simpa only [map_intCast] using
    (publicPacket_auxiliary_leading_unit hm hw).map (ZMod.castHom hd (ZMod m))

/-- The actual numerator cannot absorb a factor of the auxiliary prime. -/
theorem publicPacket_leading_not_auxiliary_dvd {N m : ℕ} (hm : m.Prime)
    {w : FamilyPacket} (hw : w∈publicPackets N m) : ¬(m : ℤ)∣w.original.a := by
  let : Fact m.Prime := ⟨hm⟩
  intro hd
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd w.original.a m).mpr hd
  exact (publicPacket_leading_auxiliary_unit hm hw).ne_zero hz

/-- Keep the square displacement and the entire centered quadratic before
testing index integrality; N=p*q is used as an integer identity. -/
theorem publicPacket_factor_sum_square {p q m : ℕ} (hm : 0<m)
    {w : FamilyPacket} (hw : w∈publicPackets (p*q) m) :
    (p : ℤ)*factorSum m w p q=
      w.original.a*((p : ℤ)-w.residue)^2+
        (m : ℤ)*(centeredPacketRow m w).b*((p : ℤ)-w.residue)+
          (m : ℤ)^2*(centeredPacketRow m w).c := by
  have he := publicPacket_relation hm hw
  simp only [quotientRelation,centeredPacketRow,shiftRow,Nat.cast_mul] at he
  simp only [factorSum,packetOffset,centeredPacketRow,shiftRow]
  linear_combination -he

/-- The m² denominator supplies precisely the original m-residue condition
on integral factor pairs, rather than an additional residue digit. -/
theorem publicPacket_index_integrality_iff_residue {p q m : ℕ}
    (hm : m.Prime) (hp : 0<p) {w : FamilyPacket}
    (hw : w∈publicPackets (p*q) m) :
    (m : ℤ)^2∣factorSum m w p q ↔ p%m=w.residue := by
  constructor
  · intro hd
    obtain ⟨z,hz⟩ := hd
    have he := publicPacket_factor_sum_square hm.pos hw
    have hda : (m : ℤ)∣w.original.a*((p : ℤ)-w.residue)^2 := by
      refine ⟨(m : ℤ)*p*z-(centeredPacketRow m w).b*((p : ℤ)-w.residue)-
        (m : ℤ)*(centeredPacketRow m w).c,?_⟩
      linear_combination -he+(p : ℤ)*hz
    have hdp : (m : ℤ)∣(p : ℤ)-w.residue := by
      rcases Int.Prime.dvd_mul' hm hda with ha|hsquare
      · exact False.elim (publicPacket_leading_not_auxiliary_dvd hm hw ha)
      · exact Int.Prime.dvd_pow' hm hsquare
    have hmod : w.residue ≡ p [MOD m] :=
      Int.natCast_modEq_iff.mp (Int.modEq_of_dvd hdp)
    change w.residue%m=p%m at hmod
    rw [Nat.mod_eq_of_lt (publicPacket_residue_lt hw)] at hmod
    exact hmod.symm
  · intro hj
    obtain ⟨i,hi,_⟩ := publicPacket_factor_index hm.pos hp hw hj.symm
    exact ⟨i,hi.symm⟩

/-- An integral collision index exists exactly in the factor's residue class.
No index bound or public acquisition of the factor is asserted. -/
theorem publicPacket_integer_index_iff_residue {p q m : ℕ}
    (hm : m.Prime) (hp : 0<p) {w : FamilyPacket}
    (hw : w∈publicPackets (p*q) m) :
    (∃ i : ℤ, (m : ℤ)^2*i=factorSum m w p q) ↔ p%m=w.residue := by
  constructor
  · rintro ⟨i,hi⟩
    exact (publicPacket_index_integrality_iff_residue hm hp hw).mp ⟨i,hi.symm⟩
  · intro hj
    obtain ⟨i,hi,_⟩ := publicPacket_factor_index hm.pos hp hw hj.symm
    exact ⟨i,hi⟩

/-- Adding other original rows and centers at the same residue supplies
the same bare integrality test, independently of their coefficient values. -/
theorem publicPacket_same_residue_integrality_iff {p q m : ℕ}
    (hm : m.Prime) (hp : 0<p) {u v : FamilyPacket}
    (hu : u∈publicPackets (p*q) m) (hv : v∈publicPackets (p*q) m)
    (hres : u.residue=v.residue) :
    (m : ℤ)^2∣factorSum m u p q ↔ (m : ℤ)^2∣factorSum m v p q := by
  rw [publicPacket_index_integrality_iff_residue hm hp hu,
    publicPacket_index_integrality_iff_residue hm hp hv,hres]

/-- A useful cross-residue incidence cannot be explained by assigning
integral physical indices to both rows in this one factor orientation. -/
theorem publicPacket_distinct_residue_no_joint_integer_indices {p q m : ℕ}
    (hm : m.Prime) (hp : 0<p) {u v : FamilyPacket}
    (hu : u∈publicPackets (p*q) m) (hv : v∈publicPackets (p*q) m)
    (hres : u.residue≠v.residue) :
    ¬∃ i k : ℤ, (m : ℤ)^2*i=factorSum m u p q ∧
      (m : ℤ)^2*k=factorSum m v p q := by
  rintro ⟨i,k,hi,hk⟩
  have hju := (publicPacket_integer_index_iff_residue hm hp hu).mp ⟨i,hi⟩
  have hjv := (publicPacket_integer_index_iff_residue hm hp hv).mp ⟨k,hk⟩
  exact hres (hju.symm.trans hjv)

end RiemannGaussian.SemiprimeIndexIntegrality
