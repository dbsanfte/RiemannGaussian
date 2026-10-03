/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRowPeriods

/-!
# Integer companions retained before the group-power projection

A primitive weighted quadratic has a public integer companion in the
original factor coordinate. Retaining this integer before exponentiation
allows additive local coincidences and zero endpoints to be recovered by
one root polynomial and its derivative. No group base or giant power is
an input or an operation in this constructor. Universal useful collisions
and the complete construction-inclusive sixth-root bit bound remain open.
-/

namespace RiemannGaussian.SemiprimeCompanionRows

open SemiprimeWeightedRows SemiprimeEuclidRowFamily SemiprimeCartesianCompletion
open SemiprimeQuotientRows

/-- The integer root of the surviving factor-coordinate linear companion. -/
def coefficientCompanion (j d B : ℤ) : ℤ := 2*j-d*B

/-- The primitive cancellation keeps its full public integer root.
The common factor-coordinate root is stripped before scalar projection. -/
theorem primitive_coordinate_factorization (m j d B Y : ℤ) (hd : d^2=1) :
    (m*d)*Y^2+(m*B-2*(m*d)*j)*Y=
      (m*d)*Y*(Y-coefficientCompanion j d B) := by
  unfold coefficientCompanion
  linear_combination -m*B*Y*hd

/-- Weighted cancellation of the original N terms preserves the complete
factor-coordinate polynomial and its integer companion. -/
theorem weighted_coordinate_factorization (N m j d Y : ℤ) (left right : QuotientRow)
    (hdet : rowDet left right=m*d) (hd : d^2=1) :
    right.t*(left.a*Y^2+(m*left.b-2*left.a*j)*Y+N*left.t)-
      left.t*(right.a*Y^2+(m*right.b-2*right.a*j)*Y+N*right.t)=
        (m*d)*Y*(Y-coefficientCompanion j d (weightedRow left right).b) := by
  calc
    _ = (m*d)*Y^2+(m*(weightedRow left right).b-2*(m*d)*j)*Y := by
      rw [←hdet]
      unfold rowDet weightedRow
      ring
    _ = _ := primitive_coordinate_factorization m j d _ Y hd

/-- The power projection is a Fermat-direction encoding of this integer,
rather than an injective copy of all its additive local information. -/
theorem companion_giant_identity {m j d B E : ℤ} (hd : d^2=1)
    (he : E=m*d*(1-2*j)+m*B) : E=m*d*(1-coefficientCompanion j d B) := by
  unfold coefficientCompanion
  rw [he]
  linear_combination -m*B*hd

/-- Normalize the retained signed exponent by its primitive orientation. -/
def normalizedCompanion (m : ℤ) (d E : ℤ) : ℤ := 1-d*(E/m)

theorem normalizedCompanion_eq_coefficient {m j d B E : ℤ} (hm : m≠0) (hd : d^2=1)
    (he : E=m*d*(1-2*j)+m*B) :
    normalizedCompanion m d E=coefficientCompanion j d B := by
  have hmul : E=m*(d*(1-2*j)+B) := by rw [he]; ring
  rw [normalizedCompanion,hmul,Int.mul_ediv_cancel_left _ hm]
  unfold coefficientCompanion
  linear_combination -(1-2*j)*hd

theorem normalizedCompanion_exponent {m d E : ℤ} (hd : d^2=1) (hmE : m∣E) :
    E=m*d*(1-normalizedCompanion m d E) := by
  have he := Int.mul_ediv_cancel' hmE
  unfold normalizedCompanion
  calc
    E=m*(E/m) := he.symm
    _=m*d^2*(E/m) := by rw [hd,mul_one]
    _=m*d*(1-(1-d*(E/m))) := by ring

/-- Primitive orientation from the actual original packet pair. -/
def packetOrientation (m : ℕ) (w : WeightedPacket) : ℤ :=
  rowDet w.left.original w.right.original/(m : ℤ)

/-- The candidate is computed from the complete public weighted packet. -/
def packetCompanion (m : ℕ) (w : WeightedPacket) : ℤ :=
  normalizedCompanion m (packetOrientation m w) (weightedPacketExponent m w)

/-- All primitive and divisibility checks use public integer data. -/
def PrimitivePacket (m : ℕ) (w : WeightedPacket) : Prop :=
  0<m ∧ |rowDet w.left.original w.right.original|=(m : ℤ) ∧
    weightedPacketExponent m w%(m : ℤ)=0

/-- All primitive-packet checks are computable integer comparisons. -/
instance (m : ℕ) (w : WeightedPacket) : Decidable (PrimitivePacket m w) :=
  inferInstanceAs (Decidable (0<m ∧ |rowDet w.left.original w.right.original|=(m : ℤ) ∧
    weightedPacketExponent m w%(m : ℤ)=0))

theorem primitivePacket_orientation {m : ℕ} {w : WeightedPacket}
    (hp : PrimitivePacket m w) : packetOrientation m w=1 ∨ packetOrientation m w=-1 := by
  obtain ⟨hm,hd,_⟩ := hp
  have hmz : (m : ℤ)≠0 := by exact_mod_cast hm.ne'
  by_cases hz : 0≤rowDet w.left.original w.right.original
  · rw [abs_of_nonneg hz] at hd
    left
    simp only [packetOrientation,hd,Int.ediv_self hmz]
  · have hdn : rowDet w.left.original w.right.original=-(m : ℤ) := by
      rw [abs_of_nonpos (le_of_not_ge hz)] at hd
      linarith only [hd]
    right
    rw [packetOrientation,hdn,show -(m : ℤ)=(m : ℤ)*(-1) by ring,
      Int.mul_ediv_cancel_left _ hmz]

theorem primitivePacket_exponent {m : ℕ} {w : WeightedPacket}
    (hp : PrimitivePacket m w) :
    weightedPacketExponent m w=(m : ℤ)*packetOrientation m w*(1-packetCompanion m w) := by
  have hs : (packetOrientation m w)^2=1 := by
    rcases primitivePacket_orientation hp with h|h <;> rw [h] <;> norm_num
  exact normalizedCompanion_exponent hs (Int.dvd_iff_emod_eq_zero.mpr hp.2.2)

/-- Both public center choices retain the original row separately. -/
def centeredPacketRow (m : ℕ) (w : FamilyPacket) : QuotientRow :=
  SemiprimeQuotientCentering.shiftRow m w.residue w.shift w.original

/-- The complete signed linear coefficient after both retained shifts. -/
def packetLinearCoefficient (m : ℕ) (w : WeightedPacket) : ℤ :=
  (weightedRow (centeredPacketRow m w.left) (centeredPacketRow m w.right)).b

/-- Actual residue-family membership supplies both original coefficient
relations and their common residue, for every public center combination. -/
theorem weightedResiduePacket_relations {N m j : ℕ} (hm : 0<m) (hj : j.Coprime m)
    {w : WeightedPacket} (hw : w∈weightedResiduePackets N m j) :
    w.left.residue=j ∧ w.right.residue=j ∧
      quotientRelation N m j w.left.original.a w.left.original.b
        w.left.original.c w.left.original.t ∧
      quotientRelation N m j w.right.original.a w.right.original.b
        w.right.original.c w.right.original.t := by
  unfold weightedResiduePackets at hw
  obtain ⟨⟨left,right⟩,hz,hw⟩ := List.mem_flatMap.mp hw
  have hrows := List.of_mem_zip hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hrows.1
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp (List.mem_of_mem_tail hrows.2)
  have hl := (intermediate_row_correct hm hj hv).2.2
  have hr := (intermediate_row_correct hm hj hu).2.2
  simp only [pairPackets,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl <;> exact ⟨rfl,rfl,hl,hr⟩

/-- The executable normalization is the linear root of the actual centered
coefficient cancellation, rather than merely an exponent re-encoding. -/
theorem packetCompanion_eq_coefficient {N m : ℕ} {w : WeightedPacket}
    (hp : PrimitivePacket m w) (hs : w.right.residue=w.left.residue)
    (hl : quotientRelation N m w.left.residue w.left.original.a w.left.original.b
      w.left.original.c w.left.original.t)
    (hr : quotientRelation N m w.right.residue w.right.original.a w.right.original.b
      w.right.original.c w.right.original.t) :
    packetCompanion m w=coefficientCompanion w.left.residue
      (packetOrientation m w) (packetLinearCoefficient m w) := by
  have hmz : (m : ℤ)≠0 := by exact_mod_cast hp.1.ne'
  have hd : (packetOrientation m w)^2=1 := by
    rcases primitivePacket_orientation hp with h|h <;> rw [h] <;> norm_num
  have hmD : (m : ℤ)∣rowDet w.left.original w.right.original := by
    rw [←dvd_abs,hp.2.1]
  have hdet : rowDet w.left.original w.right.original=(m : ℤ)*packetOrientation m w :=
    (Int.mul_ediv_cancel' hmD).symm
  have hlc := SemiprimeQuotientCentering.shiftRow_relation hl w.left.shift
  have hrc := SemiprimeQuotientCentering.shiftRow_relation hr w.right.shift
  rw [hs] at hrc
  have he := weighted_giant_exponent hlc hrc
  rw [SemiprimeQuotientCentering.shiftRow_giant,
    SemiprimeQuotientCentering.shiftRow_giant] at he
  have he' : weightedPacketExponent m w=
    rowDet w.left.original w.right.original*(1-2*(w.left.residue : ℤ))+
      (m : ℤ)*packetLinearCoefficient m w := by
    simpa only [weightedPacketExponent,packetExponent,packetLinearCoefficient,
      centeredPacketRow,SemiprimeQuotientCentering.shiftRow,rowDet,weightedRow,hs] using he
  rw [hdet] at he'
  exact normalizedCompanion_eq_coefficient hmz hd he'

/-- This commuting identity applies to every filtered public packet. -/
theorem publicPacketCompanion_eq_coefficient {N m : ℕ} {w : WeightedPacket}
    (hw : w∈publicWeightedPackets N m) (hp : PrimitivePacket m w) :
    packetCompanion m w=coefficientCompanion w.left.residue
      (packetOrientation m w) (packetLinearCoefficient m w) := by
  obtain ⟨j,_,hw⟩ := List.mem_flatMap.mp hw
  split_ifs at hw with hj
  · obtain ⟨hl,hr,hleft,hright⟩ := weightedResiduePacket_relations hp.1 hj hw
    apply packetCompanion_eq_coefficient hp (hr.trans hl.symm)
    · simpa only [hl] using hleft
    · simpa only [hr] using hright
  · simp only [List.not_mem_nil] at hw

/-- The actual public companion is the other factor-coordinate root after
the global zero root has been removed, with every original packet retained. -/
theorem publicPacket_coordinate_factorization {N m : ℕ} {w : WeightedPacket}
    (hw : w∈publicWeightedPackets N m) (hp : PrimitivePacket m w) (Y : ℤ) :
    (centeredPacketRow m w.right).t*
        ((centeredPacketRow m w.left).a*Y^2+
          ((m : ℤ)*(centeredPacketRow m w.left).b-
            2*(centeredPacketRow m w.left).a*w.left.residue)*Y+
          (N : ℤ)*(centeredPacketRow m w.left).t)-
      (centeredPacketRow m w.left).t*
        ((centeredPacketRow m w.right).a*Y^2+
          ((m : ℤ)*(centeredPacketRow m w.right).b-
            2*(centeredPacketRow m w.right).a*w.left.residue)*Y+
          (N : ℤ)*(centeredPacketRow m w.right).t)=
        (m : ℤ)*packetOrientation m w*Y*(Y-packetCompanion m w) := by
  have hd : (packetOrientation m w)^2=1 := by
    rcases primitivePacket_orientation hp with h|h <;> rw [h] <;> norm_num
  have hmD : (m : ℤ)∣rowDet w.left.original w.right.original := by
    rw [←dvd_abs,hp.2.1]
  have hdet : rowDet (centeredPacketRow m w.left) (centeredPacketRow m w.right)=
      (m : ℤ)*packetOrientation m w := (Int.mul_ediv_cancel' hmD).symm
  rw [publicPacketCompanion_eq_coefficient hw hp]
  exact weighted_coordinate_factorization N m w.left.residue _ Y _ _ hdet hd

/-- Reject unchecked packets before projecting their companion integer. -/
def companionEntry (m : ℕ) (w : WeightedPacket) : Option ℤ :=
  if PrimitivePacket m w then some (packetCompanion m w) else none

/-- Every public residue and all four original center combinations remain. -/
def publicCompanions (N m : ℕ) : List ℤ :=
  (publicWeightedPackets N m).filterMap (companionEntry m)

/-- A single public residue can certify membership in the full constructor. -/
def residueCompanions (N m j : ℕ) : List ℤ :=
  (weightedResiduePackets N m j).filterMap (companionEntry m)

theorem publicCompanion_mem_of_residue {N m j : ℕ} (hj : j<m) (hc : j.Coprime m)
    {c : ℤ} (he : c∈residueCompanions N m j) : c∈publicCompanions N m := by
  obtain ⟨w,hw,he⟩ := List.mem_filterMap.mp he
  apply List.mem_filterMap.mpr
  refine ⟨w,?_,he⟩
  apply List.mem_flatMap.mpr
  refine ⟨j,List.mem_range.mpr hj,?_⟩
  change w∈(if j.Coprime m then weightedResiduePackets N m j else [])
  rwa [if_pos hc]

/-- Whole-modulus deduplication forks the retained original integer list. -/
def publicCompanionRoots (N m : ℕ) : Finset (ZMod N) :=
  ((publicCompanions N m).map fun (c : ℤ) => (c : ZMod N)).toFinset

theorem publicCompanionRoots_mem {N m : ℕ} {c : ℤ} (hc : c∈publicCompanions N m) :
    (c : ZMod N)∈publicCompanionRoots N m := by
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨c,hc,rfl⟩

/-- Public zero-companion endpoints precede one additive derivative source. -/
noncomputable def recoverCompanionRows (N m : ℕ) : Option ℕ :=
  let S := publicCompanionRoots N m
  match scanProper N (S.toList.map ZMod.val) with
  | some d => some d
  | none => SemiprimeRowDerivative.recoverRows S

theorem recoverCompanionRows_sound {N m d : ℕ} (hd : recoverCompanionRows N m=some d) :
    SemiprimeGroupSelection.ProperDivisor N d := by
  unfold recoverCompanionRows at hd
  cases he : scanProper N ((publicCompanionRoots N m).toList.map ZMod.val) with
  | some f =>
    simp only [he,Option.some.injEq] at hd
    subst d
    exact scanProper_sound he
  | none => exact SemiprimeRowDerivative.recoverRows_sound (by simpa only [he] using hd)

theorem recoverCompanionRows_of_proper_pair {N m : ℕ} [NeZero N] {c e : ℤ}
    (hc : c∈publicCompanions N m) (he : e∈publicCompanions N m)
    (hp : SemiprimeGroupSelection.ProperDivisor N
      (N.gcd ((e : ZMod N)-(c : ZMod N)).val)) :
    ∃ d, recoverCompanionRows N m=some d := by
  unfold recoverCompanionRows
  dsimp only
  cases hf : scanProper N ((publicCompanionRoots N m).toList.map ZMod.val) with
  | some d => exact ⟨d,rfl⟩
  | none =>
    exact SemiprimeRowDerivative.recoverRows_succeeds_of_proper_pair
      (publicCompanionRoots_mem hc) (publicCompanionRoots_mem he) hp

theorem recoverCompanionRows_of_endpoint {N m : ℕ} {c : ℤ}
    (hc : c∈publicCompanions N m)
    (hp : SemiprimeGroupSelection.ProperDivisor N (N.gcd (c : ZMod N).val)) :
    ∃ d, recoverCompanionRows N m=some d := by
  cases hf : scanProper N ((publicCompanionRoots N m).toList.map ZMod.val) with
  | some d =>
    exact ⟨d,by simp only [recoverCompanionRows,hf]⟩
  | none =>
    have hm : (c : ZMod N).val∈(publicCompanionRoots N m).toList.map ZMod.val :=
      List.mem_map.mpr ⟨(c : ZMod N),Finset.mem_toList.mpr (publicCompanionRoots_mem hc),rfl⟩
    have he := (scanProper_none_iff _ _).mp hf _ hm
    have hproper : 1<N.gcd (c : ZMod N).val ∧ N.gcd (c : ZMod N).val<N := ⟨hp.1,hp.2.1⟩
    rw [SemiprimeGroupSelection.checkedSignal,if_pos hproper] at he
    contradiction

theorem publicCompanions_length_le (N m : ℕ) :
    (publicCompanions N m).length≤2*(publicPackets N m).length :=
  (List.length_filterMap_le _ _).trans (publicWeightedPackets_length_le N m)

theorem publicCompanionRoots_card_le (N m : ℕ) :
    (publicCompanionRoots N m).card≤2*(publicPackets N m).length := by
  have h := List.toFinset_card_le ((publicCompanions N m).map fun (c : ℤ) => (c : ZMod N))
  simp only [List.length_map] at h
  exact h.trans (publicCompanions_length_le N m)

/-- At most one endpoint and two derivative/recovery queries per root.
Construction and polynomial bit costs are separate obligations. -/
theorem recoverCompanionRows_gcd_bound (N m : ℕ) :
    scanGcdCount N ((publicCompanionRoots N m).toList.map ZMod.val)+
      recoveryGcdCount N (fun i => residueLeaves (publicCompanionRoots N m) (i : ZMod N))
        (evaluatedColumns (publicCompanionRoots N m) (publicCompanionRoots N m).toList)≤
          6*(publicPackets N m).length := by
  have h1 := scanGcdCount_le N ((publicCompanionRoots N m).toList.map ZMod.val)
  have h2 := SemiprimeRowDerivative.recoverRows_gcd_bound (publicCompanionRoots N m)
  have h3 := publicCompanionRoots_card_le N m
  simp only [List.length_map,Finset.length_toList] at h1
  omega

set_option maxRecDepth 32768 in
/-- Integer companions reveal an additive pair outside the failed power
detector at N=2047. Both packets belong to the complete public constructor. -/
theorem control_companions_mem : (66 : ℤ)∈publicCompanions 2047 5 ∧
    (43 : ℤ)∈publicCompanions 2047 5 := by
  constructor
  · apply publicCompanion_mem_of_residue (j:=1) (by norm_num) (by norm_num [Nat.Coprime])
    decide +kernel
  · apply publicCompanion_mem_of_residue (j:=3) (by norm_num) (by norm_num [Nat.Coprime])
    decide +kernel

theorem control_companion_difference : SemiprimeGroupSelection.ProperDivisor 2047
    ((2047 : ℕ).gcd ((43 : ZMod 2047)-(66 : ZMod 2047)).val) := by
  norm_num [SemiprimeGroupSelection.ProperDivisor]
  decide +kernel

/-- The whole N-only companion constructor and derivative procedure
recover a proper factor without a group base or selected pair as input. -/
theorem control_public_companions_recovers : ∃ d, recoverCompanionRows 2047 5=some d :=
  recoverCompanionRows_of_proper_pair control_companions_mem.1 control_companions_mem.2
    control_companion_difference

set_option maxRecDepth 32768 in
theorem balanced_control_companions_mem : (2290 : ℤ)∈publicCompanions 2304167 13 ∧
    (1187 : ℤ)∈publicCompanions 2304167 13 := by
  constructor
  · apply publicCompanion_mem_of_residue (j:=2) (by norm_num) (by norm_num [Nat.Coprime])
    decide +kernel
  · apply publicCompanion_mem_of_residue (j:=4) (by norm_num) (by norm_num [Nat.Coprime])
    decide +kernel

theorem balanced_control_companion_difference : SemiprimeGroupSelection.ProperDivisor 2304167
    ((2304167 : ℕ).gcd ((1187 : ZMod 2304167)-(2290 : ZMod 2304167)).val) := by
  norm_num [SemiprimeGroupSelection.ProperDivisor]
  decide +kernel

theorem balanced_control_public_companions_recovers :
    ∃ d, recoverCompanionRows 2304167 13=some d :=
  recoverCompanionRows_of_proper_pair balanced_control_companions_mem.1
    balanced_control_companions_mem.2 balanced_control_companion_difference

set_option maxRecDepth 32768 in
/-- The earlier large short-window failure also has additive companions. -/
theorem older_control_companions_mem : (-8584010 : ℤ)∈publicCompanions 369867514421371 269 ∧
    (16407479 : ℤ)∈publicCompanions 369867514421371 269 := by
  constructor
  · apply publicCompanion_mem_of_residue (j:=49) (by norm_num) (by norm_num [Nat.Coprime])
    decide +kernel
  · apply publicCompanion_mem_of_residue (j:=93) (by norm_num) (by norm_num [Nat.Coprime])
    decide +kernel

theorem older_control_companion_difference : SemiprimeGroupSelection.ProperDivisor 369867514421371
    ((369867514421371 : ℕ).gcd ((16407479 : ZMod 369867514421371)-
      (-8584010 : ZMod 369867514421371)).val) := by
  norm_num [SemiprimeGroupSelection.ProperDivisor]
  decide +kernel

theorem older_control_public_companions_recovers :
    ∃ d, recoverCompanionRows 369867514421371 269=some d :=
  recoverCompanionRows_of_proper_pair older_control_companions_mem.1
    older_control_companions_mem.2 older_control_companion_difference

set_option maxRecDepth 32768 in
/-- The earlier whole original derivative-family miss has a literal
additive companion pair, without any group power or private selector input. -/
theorem derivative_control_companions_mem :
    (185529023096 : ℤ)∈publicCompanions 2518766418595894637609 3691 ∧
    (-1229252577510 : ℤ)∈publicCompanions 2518766418595894637609 3691 := by
  constructor
  · apply publicCompanion_mem_of_residue (j:=110) (by norm_num) (by norm_num [Nat.Coprime])
    decide +kernel
  · apply publicCompanion_mem_of_residue (j:=265) (by norm_num) (by norm_num [Nat.Coprime])
    decide +kernel

theorem derivative_control_companion_difference : SemiprimeGroupSelection.ProperDivisor
    2518766418595894637609 ((2518766418595894637609 : ℕ).gcd
      ((-1229252577510 : ZMod 2518766418595894637609)-
        (185529023096 : ZMod 2518766418595894637609)).val) := by
  norm_num [SemiprimeGroupSelection.ProperDivisor]
  decide +kernel

theorem derivative_control_public_companions_recovers :
    ∃ d, recoverCompanionRows 2518766418595894637609 3691=some d :=
  recoverCompanionRows_of_proper_pair derivative_control_companions_mem.1
    derivative_control_companions_mem.2 derivative_control_companion_difference

set_option maxRecDepth 32768 in
/-- A larger reference witness is checked against the complete public
constructor. Neither its factors nor the selected residues are inputs. -/
theorem larger_control_companions_mem :
    (29719657945802267 : ℤ)∈publicCompanions 788096216222522769981991129 30403 ∧
    (83379602944995 : ℤ)∈publicCompanions 788096216222522769981991129 30403 := by
  constructor
  · apply publicCompanion_mem_of_residue (j:=1685) (by norm_num) (by norm_num [Nat.Coprime])
    decide +kernel
  · apply publicCompanion_mem_of_residue (j:=13824) (by norm_num) (by norm_num [Nat.Coprime])
    decide +kernel

theorem larger_control_companion_difference : SemiprimeGroupSelection.ProperDivisor
    788096216222522769981991129 ((788096216222522769981991129 : ℕ).gcd
      ((83379602944995 : ZMod 788096216222522769981991129)-
        (29719657945802267 : ZMod 788096216222522769981991129)).val) := by
  norm_num [SemiprimeGroupSelection.ProperDivisor]
  decide +kernel

theorem larger_control_public_companions_recovers :
    ∃ d, recoverCompanionRows 788096216222522769981991129 30403=some d :=
  recoverCompanionRows_of_proper_pair larger_control_companions_mem.1
    larger_control_companions_mem.2 larger_control_companion_difference

set_option maxRecDepth 32768 in
theorem zero_period_control_companion_mem : (13 : ℤ)∈publicCompanions 143 3 := by
  apply publicCompanion_mem_of_residue (j:=1) (by norm_num) (by norm_num [Nat.Coprime])
  decide +kernel

theorem zero_period_control_public_companions_recovers : ∃ d, recoverCompanionRows 143 3=some d := by
  apply recoverCompanionRows_of_endpoint zero_period_control_companion_mem
  norm_num [SemiprimeGroupSelection.ProperDivisor]
  decide +kernel

end RiemannGaussian.SemiprimeCompanionRows
