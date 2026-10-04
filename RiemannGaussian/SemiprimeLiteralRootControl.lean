/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeLiteralQuadraticRoots

/-!
# A literal shifted-root repair of the canonical 119-bit control

The private reference search supplies two candidate packets. Their public
Euclidean membership, original offsets, normalized roots and proper GCD
are checked below in the kernel. The recovery program receives only N,m;
the final theorem also checks the canonical N-only modulus selector.
This single control supplies neither universal coverage nor a bit clock.
-/

namespace RiemannGaussian.SemiprimeLiteralRootControl

open SemiprimeEuclidRowFamily SemiprimeCompanionRows SemiprimeAffineRowRoots
open SemiprimeAnchoredRowAreas SemiprimeLiteralQuadraticRoots
open SemiprimeCompanionCoverage SemiprimeEuclidRowBudget
open SemiprimeQuotientCentering

/-- The canonical input previously missed by the full old joined family. -/
abbrev controlN : ℕ := 344480927244364494083113546915969253

/-- The public least prime above the input's ceiling sixth root. -/
abbrev controlM : ℕ := 837271

/-- First larger-center packet, retaining its negative numerator. -/
def firstPacket : FamilyPacket := largerPacket controlN controlM 250176 (-229343,126195)

/-- Second larger-center packet, whose signed root supplies the other endpoint. -/
def secondPacket : FamilyPacket := largerPacket controlN controlM 704514 (-32129,2647)

set_option maxRecDepth 32768 in
/-- Both exact vectors belong to the original public Euclidean stream. -/
theorem control_vectors :
    ((-229343 : ℤ),126195)∈publicPairs controlN controlM 250176 ∧
      ((-32129 : ℤ),2647)∈publicPairs controlN controlM 704514 := by
  decide +kernel

/-- The witnesses are members of the complete source, with no private labels. -/
theorem control_membership :
    firstPacket∈publicPackets controlN controlM ∧ secondPacket∈publicPackets controlN controlM := by
  exact ⟨largerPacket_mem_of_pair (by norm_num) (by norm_num [Nat.Coprime]) control_vectors.1,
    largerPacket_mem_of_pair (by norm_num) (by norm_num [Nat.Coprime]) control_vectors.2⟩

set_option maxRecDepth 32768 in
/-- Full original integer offsets, before reduction or inversion. -/
theorem control_offsets :
    packetOffset controlM firstPacket=99265048431547030603129 ∧
      packetOffset controlM secondPacket=21436717488731681518960 := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- Literal linear and constant coefficients of the two centered quadratics. -/
theorem control_coefficients :
    (centeredPacketRow controlM firstPacket).b=118557848571647983 ∧
      (centeredPacketRow controlM firstPacket).c=62011927590872743553719379631 ∧
      (centeredPacketRow controlM secondPacket).b=25603081306633588 ∧
      (centeredPacketRow controlM secondPacket).c=1300729603674195185119186367 := by
  decide +kernel

/-- The genuine original Sylvester resultants, with and without X reflection. -/
theorem control_resultants :
    Polynomial.resultant
      (quadraticPolynomial firstPacket.original.a (centeredPacketRow controlM firstPacket).b
        (centeredPacketRow controlM firstPacket).c)
      (quadraticPolynomial secondPacket.original.a (centeredPacketRow controlM secondPacket).b
        (centeredPacketRow controlM secondPacket).c) 2 2=
      -87043293115889056066098613071002919789714414386318646081579361835 ∧
    Polynomial.resultant
      (quadraticPolynomial firstPacket.original.a (centeredPacketRow controlM firstPacket).b
        (centeredPacketRow controlM firstPacket).c)
      (quadraticPolynomial secondPacket.original.a (-(centeredPacketRow controlM secondPacket).b)
        (centeredPacketRow controlM secondPacket).c) 2 2=
      -13993602994103838270600348845169132584140446838681875069502064092075 := by
  have ha : firstPacket.original.a=-229343 := rfl
  have hd : secondPacket.original.a=-32129 := rfl
  constructor <;>
    rw [quadratic_resultant,control_coefficients.1,control_coefficients.2.1,
      control_coefficients.2.2.1,control_coefficients.2.2.2,ha,hd] <;> norm_num

set_option maxRecDepth 32768 in
/-- Reflection exposes a proper original-quadratic resultant on this input. -/
theorem control_resultant_gcds :
    controlN.gcd (Polynomial.resultant
      (quadraticPolynomial firstPacket.original.a (centeredPacketRow controlM firstPacket).b
        (centeredPacketRow controlM firstPacket).c)
      (quadraticPolynomial secondPacket.original.a (centeredPacketRow controlM secondPacket).b
        (centeredPacketRow controlM secondPacket).c) 2 2).natAbs=1 ∧
    controlN.gcd (Polynomial.resultant
      (quadraticPolynomial firstPacket.original.a (centeredPacketRow controlM firstPacket).b
        (centeredPacketRow controlM firstPacket).c)
      (quadraticPolynomial secondPacket.original.a (-(centeredPacketRow controlM secondPacket).b)
        (centeredPacketRow controlM secondPacket).c) 2 2).natAbs=526706927522612147 := by
  rw [control_resultants.1,control_resultants.2]
  decide +kernel

/-- Each negative leading coefficient is a unit modulo the whole input. -/
theorem control_units :
    IsUnit (packetScale firstPacket false : ZMod controlN) ∧
      IsUnit (packetScale secondPacket false : ZMod controlN) := by
  constructor
  · change IsUnit (-229343 : ZMod controlN)
    exact ((ZMod.isUnit_iff_coprime 229343 controlN).mpr (by norm_num [Nat.Coprime])).neg
  · change IsUnit (-32129 : ZMod controlN)
    exact ((ZMod.isUnit_iff_coprime 32129 controlN).mpr (by norm_num [Nat.Coprime])).neg

/-- The common-coordinate scaling is also a whole-input unit. -/
theorem control_modulus_unit : IsUnit (controlM : ZMod controlN) := by
  exact (ZMod.isUnit_iff_coprime controlM controlN).mpr (by norm_num [Nat.Coprime])

/-- Verify the affine coordinates by coefficient equations rather than inverse evaluation. -/
theorem control_affine_roots :
    packetRoot controlN controlM firstPacket false=
      (217662715360117150581605711716660055 : ZMod controlN) ∧
      packetRoot controlN controlM secondPacket false=
      (131063365017121964490295293542671408 : ZMod controlN) := by
  constructor
  · apply packetRoot_eq_of_coefficient _ _ control_units.1
    rw [control_offsets.1]
    change (-229343 : ZMod controlN)*217662715360117150581605711716660055=
      -(99265048431547030603129 : ℤ)
    reduce_mod_char
  · apply packetRoot_eq_of_coefficient _ _ control_units.2
    rw [control_offsets.2]
    change (-32129 : ZMod controlN)*131063365017121964490295293542671408=
      -(21436717488731681518960 : ℤ)
    reduce_mod_char

/-- Retain each actual residue before identifying the two literal shifted roots. -/
theorem control_shifted_roots :
    shiftedRoot controlN controlM firstPacket=
      (217662715360117150581605711716409879 : ZMod controlN) ∧
      shiftedRoot controlN controlM secondPacket=
      (131063365017121964490295293541966894 : ZMod controlN) := by
  unfold shiftedRoot
  rw [control_affine_roots.1,control_affine_roots.2]
  change (217662715360117150581605711716660055 : ZMod controlN)-250176=_ ∧
    (131063365017121964490295293542671408 : ZMod controlN)-704514=_
  constructor <;> reduce_mod_char

set_option maxRecDepth 32768 in
/-- The signed source pair has an exact proper GCD, checked without private fields. -/
theorem control_gcd :
    controlN.gcd (shiftedRoot controlN controlM firstPacket+
      shiftedRoot controlN controlM secondPacket).val=526706927522612147 := by
  rw [control_shifted_roots.1,control_shifted_roots.2]
  norm_num [ZMod.val]
  decide +kernel

/-- This GCD is a proper divisor of the complete input. -/
theorem control_proper_sum : SemiprimeGroupSelection.ProperDivisor controlN
    (controlN.gcd (shiftedRoot controlN controlM firstPacket+
      shiftedRoot controlN controlM secondPacket).val) := by
  rw [control_gcd]
  norm_num [SemiprimeGroupSelection.ProperDivisor]

/-- The amended N,m-only detector recovers the formerly missed input. -/
theorem control_recovers : ∃ d, recoverLiteralQuadratics controlN controlM=some d := by
  apply recoverLiteralQuadratics_of_proper_pair
    (signedRoots_neg_mem (Finset.mem_union_right _ (literalRoots_shifted_mem control_membership.1)))
    (signedRoots_mem (Finset.mem_union_right _ (literalRoots_shifted_mem control_membership.2)))
  simpa only [sub_neg_eq_add,add_comm] using control_proper_sum

/-- Evaluate the public sixth-root width by its exact defining inequalities. -/
theorem control_sixthWidth : SemiprimeLehmanCoverage.sixthWidth controlN=837262 := by
  unfold SemiprimeLehmanCoverage.sixthWidth
  apply (Nat.find_eq_iff _).mpr
  constructor
  · norm_num
  · intro k hk hkn
    have hle : k≤837261 := by omega
    have hp := Nat.pow_le_pow_left hle 6
    have hl : (837261 : ℕ)^6<controlN := by norm_num
    omega

/-- Verify the exact canonical least-prime modulus, with no factor input. -/
theorem control_public_modulus : publicRowModulus controlN=controlM := by
  simp only [publicRowModulus,control_sixthWidth,show max 1 837262=837262 by decide]
  have hB : (0 : ℕ)<837262 := by norm_num
  have hp := publicPrimeAtLeast_prime 837262 hB
  have hlo := publicPrimeAtLeast_ge 837262 hB
  have hhi := publicPrimeAtLeast_minimal 837262 hB
    (by norm_num : Nat.Prime 837271) (by norm_num : 837262≤837271)
  have hcases : publicPrimeAtLeast 837262 hB=837262 ∨
      publicPrimeAtLeast 837262 hB=837263 ∨ publicPrimeAtLeast 837262 hB=837264 ∨
      publicPrimeAtLeast 837262 hB=837265 ∨ publicPrimeAtLeast 837262 hB=837266 ∨
      publicPrimeAtLeast 837262 hB=837267 ∨ publicPrimeAtLeast 837262 hB=837268 ∨
      publicPrimeAtLeast 837262 hB=837269 ∨ publicPrimeAtLeast 837262 hB=837270 ∨
      publicPrimeAtLeast 837262 hB=837271 := by omega
  rcases hcases with h|h|h|h|h|h|h|h|h|h
  all_goals first | exact h | (rw [h] at hp; norm_num at hp)

/-- The amended detector at the literal N-only public modulus succeeds. -/
theorem control_public_recovers :
    ∃ d, recoverLiteralQuadratics controlN (publicRowModulus controlN)=some d := by
  rw [control_public_modulus]
  exact control_recovers

end RiemannGaussian.SemiprimeLiteralRootControl
