/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeQuadraticPointJets

/-!
# Retain the residue shift of every original quotient quadratic

The factor-coordinate change Y=mX+j depends on the packet's residue.
In the common coordinate mX, the two roots are -j and alpha-j. These
roots retain the complete two-row resultant up to checked unit factors,
without a Sylvester matrix or a row-pair list. They supplement the old
joined detector. Useful-hit coverage and the full bit cost remain open.
-/

namespace RiemannGaussian.SemiprimeLiteralQuadraticRoots

open Polynomial SemiprimeQuotientRows SemiprimeQuotientCentering
open SemiprimeEuclidRowFamily SemiprimeCompanionRows SemiprimeAffineRowRoots
open SemiprimeCenteredOffsetExtractor SemiprimeAnchoredRowAreas
open SemiprimeQuadraticPointJets SemiprimeCartesianCompletion
open SemiprimeCompanionCoverage SemiprimeReflectedCompanions
open SemiprimeRowDerivative

/-- The known root in the common coordinate mX, before its residue shift. -/
def knownRoot (N : ℕ) (w : FamilyPacket) : ZMod N := -(w.residue : ZMod N)

/-- The nontrivial root retains the literal packet-specific residue shift. -/
def shiftedRoot (N m : ℕ) (w : FamilyPacket) : ZMod N :=
  packetRoot N m w false-(w.residue : ZMod N)

/-- Original coefficients after the common variable change T=mX. -/
noncomputable def commonPolynomial (N m : ℕ) (w : FamilyPacket) : (ZMod N)[X] :=
  quadraticPolynomial (w.original.a : ZMod N)
    ((m : ZMod N)*((centeredPacketRow m w).b : ZMod N))
    ((m : ZMod N)^2*((centeredPacketRow m w).c : ZMod N))

/-- Integer linear coefficient; no reduction or center is dropped. -/
theorem common_linear_integer (m : ℕ) (w : FamilyPacket) :
    (m : ℤ)*(centeredPacketRow m w).b=packetOffset m w+2*w.original.a*w.residue := by
  simp only [packetOffset]
  ring

/-- The shifted roots recover the exact common-coordinate linear coefficient. -/
theorem common_linear_roots {N m : ℕ} (w : FamilyPacket)
    (hu : IsUnit (w.original.a : ZMod N)) :
    (m : ZMod N)*((centeredPacketRow m w).b : ZMod N)=
      -(w.original.a : ZMod N)*(knownRoot N w+shiftedRoot N m w) := by
  have h := congrArg (fun z : ℤ => (z : ZMod N)) (common_linear_integer m w)
  push_cast at h
  have hr := packetRoot_coefficient (m:=m) w false hu
  simp only [packetScale,Bool.false_eq_true,if_false] at hr
  unfold knownRoot shiftedRoot
  linear_combination h+hr

/-- The full original constant term is retained before its known Nt part vanishes. -/
theorem common_constant_roots {N m : ℕ} (hm : 0<m) {w : FamilyPacket}
    (hw : w∈publicPackets N m) (hu : IsUnit (w.original.a : ZMod N)) :
    (m : ZMod N)^2*((centeredPacketRow m w).c : ZMod N)=
      (w.original.a : ZMod N)*knownRoot N w*shiftedRoot N m w := by
  have h := congrArg (fun z : ℤ => (z : ZMod N)) (publicPacket_tangent_integer hm hw)
  push_cast at h
  simp only [ZMod.natCast_self,zero_mul,add_zero] at h
  have hr := packetRoot_coefficient (m:=m) w false hu
  simp only [packetScale,Bool.false_eq_true,if_false] at hr
  unfold knownRoot shiftedRoot
  linear_combination -h+(w.residue : ZMod N)*hr

/-- A quadratic with its literal two roots, including equal or zero roots. -/
theorem quadratic_from_roots {R : Type*} [CommRing R] (a r s : R) :
    quadraticPolynomial a (-a*(r+s)) (a*r*s)=C a*(X-C r)*(X-C s) := by
  simp only [quadraticPolynomial,map_neg,map_mul,map_add]
  ring

/-- Every original public quadratic splits in the same common coordinate. -/
theorem publicPacket_common_split {N m : ℕ} (hm : 0<m) {w : FamilyPacket}
    (hw : w∈publicPackets N m) (hu : IsUnit (w.original.a : ZMod N)) :
    commonPolynomial N m w=C (w.original.a : ZMod N)*
      (X-C (knownRoot N w))*(X-C (shiftedRoot N m w)) := by
  unfold commonPolynomial
  rw [common_linear_roots w hu,common_constant_roots hm hw hu,quadratic_from_roots]

/-- The fixed-degree genuine Sylvester resultant is a four-difference product. -/
theorem split_quadratic_resultant {R : Type*} [CommRing R] (a d r s t v : R) :
    Polynomial.resultant (C a*(X-C r)*(X-C s)) (C d*(X-C t)*(X-C v)) 2 2=
      a^2*d^2*((r-t)*(r-v)*(s-t)*(s-v)) := by
  rw [←quadratic_from_roots,←quadratic_from_roots,quadratic_resultant]
  ring

/-- A common variable scaling changes the original degree-two resultant by m⁴. -/
theorem quadratic_resultant_scaling {R : Type*} [CommRing R] (m a b c d e f : R) :
    Polynomial.resultant (quadraticPolynomial a (m*b) (m^2*c))
        (quadraticPolynomial d (m*e) (m^2*f)) 2 2=
      m^4*Polynomial.resultant (quadraticPolynomial a b c) (quadraticPolynomial d e f) 2 2 := by
  rw [quadratic_resultant,quadratic_resultant]
  ring

/-- Retain the four complete root differences for an actual original row pair. -/
def rootDifferences (N m : ℕ) (u w : FamilyPacket) : ZMod N :=
  (knownRoot N u-knownRoot N w)*(knownRoot N u-shiftedRoot N m w)*
    (shiftedRoot N m u-knownRoot N w)*(shiftedRoot N m u-shiftedRoot N m w)

/-- The actual original quadratic pair has exactly the retained four differences. -/
theorem publicPacket_resultant_exact {N m : ℕ} (hm : 0<m) {u w : FamilyPacket}
    (hu : u∈publicPackets N m) (hw : w∈publicPackets N m)
    (hau : IsUnit (u.original.a : ZMod N)) (haw : IsUnit (w.original.a : ZMod N)) :
    (m : ZMod N)^4*Polynomial.resultant
      (quadraticPolynomial (u.original.a : ZMod N) ((centeredPacketRow m u).b : ZMod N)
        ((centeredPacketRow m u).c : ZMod N))
      (quadraticPolynomial (w.original.a : ZMod N) ((centeredPacketRow m w).b : ZMod N)
        ((centeredPacketRow m w).c : ZMod N)) 2 2=
      (u.original.a : ZMod N)^2*(w.original.a : ZMod N)^2*rootDifferences N m u w := by
  rw [←quadratic_resultant_scaling]
  change Polynomial.resultant (commonPolynomial N m u) (commonPolynomial N m w) 2 2=_
  rw [publicPacket_common_split hm hu hau,publicPacket_common_split hm hw haw,
    split_quadratic_resultant]
  rfl

/-- Unit scaling preserves the entire original resultant GCD, including prime powers. -/
theorem publicPacket_resultant_gcd {N m : ℕ} (hm : 0<m) {u w : FamilyPacket}
    (hu : u∈publicPackets N m) (hw : w∈publicPackets N m)
    (hmUnit : IsUnit (m : ZMod N))
    (hau : IsUnit (u.original.a : ZMod N)) (haw : IsUnit (w.original.a : ZMod N)) :
    N.gcd (Polynomial.resultant
      (quadraticPolynomial (u.original.a : ZMod N) ((centeredPacketRow m u).b : ZMod N)
        ((centeredPacketRow m u).c : ZMod N))
      (quadraticPolynomial (w.original.a : ZMod N) ((centeredPacketRow m w).b : ZMod N)
        ((centeredPacketRow m w).c : ZMod N)) 2 2).val=
      N.gcd (rootDifferences N m u w).val := by
  have h := SemiprimeRHCancellation.unit_mul_gcd_eq (hmUnit.pow 4).unit
    (Polynomial.resultant
      (quadraticPolynomial (u.original.a : ZMod N) ((centeredPacketRow m u).b : ZMod N)
        ((centeredPacketRow m u).c : ZMod N))
      (quadraticPolynomial (w.original.a : ZMod N) ((centeredPacketRow m w).b : ZMod N)
        ((centeredPacketRow m w).c : ZMod N)) 2 2)
  have hroots := SemiprimeRHCancellation.unit_mul_gcd_eq ((hau.pow 2).mul (haw.pow 2)).unit
    (rootDifferences N m u w)
  rw [(hmUnit.pow 4).unit_spec,publicPacket_resultant_exact hm hu hw hau haw] at h
  rw [((hau.pow 2).mul (haw.pow 2)).unit_spec] at hroots
  exact h.symm.trans hroots

/-- Original constant coefficients survive as endpoint signals, with their unit phases. -/
theorem common_constant_gcd {N m : ℕ} (hm : 0<m) {w : FamilyPacket}
    (hw : w∈publicPackets N m) (hmUnit : IsUnit (m : ZMod N))
    (ha : IsUnit (w.original.a : ZMod N)) (hj : IsUnit (knownRoot N w)) :
    N.gcd ((centeredPacketRow m w).c : ZMod N).val=N.gcd (shiftedRoot N m w).val := by
  have h := SemiprimeRHCancellation.unit_mul_gcd_eq (hmUnit.pow 2).unit
    ((centeredPacketRow m w).c : ZMod N)
  have hroots := SemiprimeRHCancellation.unit_mul_gcd_eq (ha.mul hj).unit (shiftedRoot N m w)
  rw [(hmUnit.pow 2).unit_spec,common_constant_roots hm hw ha] at h
  rw [(ha.mul hj).unit_spec] at hroots
  exact h.symm.trans hroots

/-- Original linear coefficients are the signed sum of the two retained roots. -/
theorem common_linear_gcd {N m : ℕ} (w : FamilyPacket)
    (hmUnit : IsUnit (m : ZMod N)) (ha : IsUnit (w.original.a : ZMod N)) :
    N.gcd ((centeredPacketRow m w).b : ZMod N).val=
      N.gcd (knownRoot N w+shiftedRoot N m w).val := by
  have h := SemiprimeRHCancellation.unit_mul_gcd_eq hmUnit.unit ((centeredPacketRow m w).b : ZMod N)
  have hroots := SemiprimeRHCancellation.unit_mul_gcd_eq ha.neg.unit
    (knownRoot N w+shiftedRoot N m w)
  rw [hmUnit.unit_spec,common_linear_roots w ha] at h
  rw [ha.neg.unit_spec] at hroots
  exact h.symm.trans hroots

/-- Known roots use m residue entries, including the common zero endpoint. -/
def knownRoots (N m : ℕ) : Finset (ZMod N) :=
  (Finset.range m).image fun j : ℕ => -(j : ZMod N)

/-- Keep all literal packet roots before whole-modulus deduplication. -/
def shiftedValues (N m : ℕ) : List (ZMod N) := (publicPackets N m).map (shiftedRoot N m)

/-- A linear-size carrier of both roots of every original quadratic. -/
def literalRoots (N m : ℕ) : Finset (ZMod N) := knownRoots N m∪(shiftedValues N m).toFinset

/-- The old signed companion and affine channels remain in the amended detector. -/
noncomputable def augmentedRoots (N m : ℕ) : Finset (ZMod N) := joinedRoots N m∪literalRoots N m

theorem publicPacket_residue_lt {N m : ℕ} {w : FamilyPacket} (hw : w∈publicPackets N m) :
    w.residue<m := by
  obtain ⟨j,hj,hw⟩ := List.mem_flatMap.mp hw
  have hjm := List.mem_range.mp hj
  split_ifs at hw
  · obtain ⟨z,_,hw⟩ := List.mem_flatMap.mp hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl <;> exact hjm
  · simp only [List.not_mem_nil] at hw

theorem literalRoots_known_mem {N m : ℕ} {w : FamilyPacket} (hw : w∈publicPackets N m) :
    knownRoot N w∈literalRoots N m := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨w.residue,Finset.mem_range.mpr (publicPacket_residue_lt hw),rfl⟩

theorem literalRoots_shifted_mem {N m : ℕ} {w : FamilyPacket} (hw : w∈publicPackets N m) :
    shiftedRoot N m w∈literalRoots N m := by
  apply Finset.mem_union_right
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨w,hw,rfl⟩)

theorem literalRoots_card_le (N m : ℕ) : (literalRoots N m).card≤(publicPackets N m).length+m := by
  have hk : (knownRoots N m).card≤m := by
    calc
      _ ≤ (Finset.range m).card := Finset.card_image_le
      _ = m := Finset.card_range m
  have hs : (shiftedValues N m).toFinset.card≤(publicPackets N m).length := by
    calc
      _ ≤ (shiftedValues N m).length := List.toFinset_card_le _
      _ = _ := by simp only [shiftedValues,List.length_map]
  have h := Finset.card_union_le (knownRoots N m) (shiftedValues N m).toFinset
  unfold literalRoots
  omega

theorem augmentedRoots_card_le (N m : ℕ) :
    (augmentedRoots N m).card≤5*(publicPackets N m).length+m := by
  have hl := literalRoots_card_le N m
  have ho := joinedRoots_card_le N m
  have h := Finset.card_union_le (joinedRoots N m) (literalRoots N m)
  unfold augmentedRoots
  omega

/-- The existing public prefix supplies the common-coordinate unit without factors. -/
theorem prefix_none_modulus_unit {N m : ℕ} (hm : 0<m) (hcover : m^2<N)
    (hnone : SemiprimeStrassenPrefix.factorPrefix N m=none) : IsUnit (m : ZMod N) := by
  have hu := prefix_none_bounded_int_unit hcover hnone
    (by exact_mod_cast hm.ne' : (m : ℤ)≠0)
    (by
      rw [abs_of_nonneg (Int.natCast_nonneg m)]
      exact_mod_cast (show m≤m^2 by simpa only [pow_two] using Nat.le_mul_self m))
  simpa only [Int.cast_natCast] using hu

/-- Every actual known root is also a unit after the public prefix fails. -/
theorem prefix_none_known_root_unit {N m : ℕ} (hm : 2≤m) (hcover : m^2<N)
    (hnone : SemiprimeStrassenPrefix.factorPrefix N m=none)
    {w : FamilyPacket} (hw : w∈publicPackets N m) : IsUnit (knownRoot N w) := by
  have hcop := publicPacket_residue_coprime hw
  have hj : w.residue≠0 := by
    intro hz
    rw [hz] at hcop
    simp only [Nat.coprime_zero_left] at hcop
    omega
  have hbound := (publicPacket_residue_lt hw).le.trans
    (show m≤m^2 by simpa only [pow_two] using Nat.le_mul_self m)
  have hu := prefix_none_bounded_int_unit hcover hnone
    (by exact_mod_cast hj : (w.residue : ℤ)≠0)
    (by rw [abs_of_nonneg (Int.natCast_nonneg _)]; exact_mod_cast hbound)
  simpa only [knownRoot,Int.cast_natCast] using hu.neg

/-- Original constant-coefficient GCDs survive after an entirely public preliminary stage. -/
theorem prefix_none_common_constant_gcd {N m : ℕ} (hm : 2≤m) (hcover : m^2<N)
    (hnone : SemiprimeStrassenPrefix.factorPrefix N m=none)
    {w : FamilyPacket} (hw : w∈publicPackets N m) :
    N.gcd ((centeredPacketRow m w).c : ZMod N).val=N.gcd (shiftedRoot N m w).val := by
  have hmpos : 0<m := by omega
  exact common_constant_gcd hmpos hw (prefix_none_modulus_unit hmpos hcover hnone)
    (prefix_none_publicPacket_leading_unit hmpos hcover hnone hw)
    (prefix_none_known_root_unit hm hcover hnone hw)

/-- Checked recovery retains the old root channels and the full literal shift. -/
noncomputable def recoverLiteralQuadratics (N m : ℕ) : Option ℕ :=
  match SemiprimeStrassenPrefix.factorPrefix N m with
  | some d => some d
  | none => recoverReflectedRows (augmentedRoots N m)

theorem recoverLiteralQuadratics_sound {N m d : ℕ} (hd : recoverLiteralQuadratics N m=some d) :
    SemiprimeGroupSelection.ProperDivisor N d := by
  unfold recoverLiteralQuadratics at hd
  cases hp : SemiprimeStrassenPrefix.factorPrefix N m with
  | some f =>
    simp only [hp,Option.some.injEq] at hd
    subst d
    exact SemiprimeStrassenPrefix.prefix_sound hp
  | none => exact recoverReflectedRows_sound (by simpa only [hp] using hd)

/-- All signed proper pairs survive deduplication and whole-N product saturation. -/
theorem recoverLiteralQuadratics_of_proper_pair {N m : ℕ} [NeZero N]
    {x t : ZMod N} (hx : x∈signedRoots (augmentedRoots N m))
    (ht : t∈signedRoots (augmentedRoots N m))
    (hp : SemiprimeGroupSelection.ProperDivisor N (N.gcd (t-x).val)) :
    ∃ d, recoverLiteralQuadratics N m=some d := by
  unfold recoverLiteralQuadratics
  cases hf : SemiprimeStrassenPrefix.factorPrefix N m with
  | some d => exact ⟨d,rfl⟩
  | none =>
    obtain ⟨d,hd⟩ := recoverRows_succeeds_of_proper_pair hx ht hp
    cases hr : recoverReflectedRows (augmentedRoots N m) with
    | some f => exact ⟨f,rfl⟩
    | none =>
      have hn := (recoverReflectedRows_none_iff_signed _).mp hr
      rw [hd] at hn
      contradiction

private theorem zero_or_unit_mul {R : Type*} [CommRing R] {x y : R}
    (hx : x=0 ∨ IsUnit x) (hy : y=0 ∨ IsUnit y) : x*y=0 ∨ IsUnit (x*y) := by
  rcases hx with hx|hx
  · exact Or.inl (by rw [hx,zero_mul])
  · rcases hy with hy|hy
    · exact Or.inl (by rw [hy,mul_zero])
    · exact Or.inr (hx.mul hy)

/-- Complete unit separation bounds the original four-difference product, including repeats. -/
theorem separated_rootDifferences_zero_or_unit {N m : ℕ} {S : Finset (ZMod N)}
    (hs : UnitSeparated S) {u w : FamilyPacket}
    (hur : knownRoot N u∈S) (hus : shiftedRoot N m u∈S)
    (hwr : knownRoot N w∈S) (hws : shiftedRoot N m w∈S) :
    rootDifferences N m u w=0 ∨ IsUnit (rootDifferences N m u w) := by
  have hd {x y : ZMod N} (hx : x∈S) (hy : y∈S) : x-y=0 ∨ IsUnit (x-y) := by
    by_cases hxy : y=x
    · exact Or.inl (by rw [hxy,sub_self])
    · exact Or.inr (hs x hx y hy hxy)
  exact zero_or_unit_mul (zero_or_unit_mul (zero_or_unit_mul (hd hur hwr) (hd hur hws))
    (hd hus hwr)) (hd hus hws)

/-- Every proper original row-pair resultant is recovered by the linear root carrier. -/
theorem recoverLiteralQuadratics_of_proper_original_resultant {N m : ℕ} (hm : 0<m)
    (hcover : m^2<N) {u w : FamilyPacket} (hu : u∈publicPackets N m)
    (hw : w∈publicPackets N m)
    (hp : SemiprimeGroupSelection.ProperDivisor N (N.gcd (Polynomial.resultant
      (quadraticPolynomial (u.original.a : ZMod N) ((centeredPacketRow m u).b : ZMod N)
        ((centeredPacketRow m u).c : ZMod N))
      (quadraticPolynomial (w.original.a : ZMod N) ((centeredPacketRow m w).b : ZMod N)
        ((centeredPacketRow m w).c : ZMod N)) 2 2).val)) :
    ∃ d, recoverLiteralQuadratics N m=some d := by
  let : NeZero N := ⟨by omega⟩
  unfold recoverLiteralQuadratics
  cases hf : SemiprimeStrassenPrefix.factorPrefix N m with
  | some d => exact ⟨d,rfl⟩
  | none =>
    cases hr : recoverReflectedRows (augmentedRoots N m) with
    | some d => exact ⟨d,rfl⟩
    | none =>
      have hcols := (recoverReflectedRows_none_iff _).mp hr
      have hs : UnitSeparated (augmentedRoots N m) := by
        intro x hx y hy hne
        exact ((reflectedColumn_isUnit_iff _ _).mp (hcols x hx)).2.1 y hy hne
      have hzero := separated_rootDifferences_zero_or_unit hs
        (Finset.mem_union_right _ (literalRoots_known_mem hu))
        (Finset.mem_union_right _ (literalRoots_shifted_mem hu))
        (Finset.mem_union_right _ (literalRoots_known_mem hw))
        (Finset.mem_union_right _ (literalRoots_shifted_mem hw))
      have hg := publicPacket_resultant_gcd hm hu hw (prefix_none_modulus_unit hm hcover hf)
        (prefix_none_publicPacket_leading_unit hm hcover hf hu)
        (prefix_none_publicPacket_leading_unit hm hcover hf hw)
      rw [hg] at hp
      rcases hzero with hz|hunit
      · simp only [hz,ZMod.val_zero,Nat.gcd_zero_right,
          SemiprimeGroupSelection.ProperDivisor,lt_self_iff_false,and_false,false_and] at hp
      · rw [(SemiprimeBulkNorm.gcd_one_iff_unit _).mpr hunit] at hp
        exact (lt_irrefl 1 hp.1).elim

private theorem reflected_none_of_subset {N : ℕ} [NeZero N] {S T : Finset (ZMod N)}
    (hsub : S⊆T) (hT : recoverReflectedRows T=none) : recoverReflectedRows S=none := by
  have hcols := (recoverReflectedRows_none_iff _).mp hT
  apply (recoverReflectedRows_none_iff _).mpr
  intro x hx
  have h := (reflectedColumn_isUnit_iff _ _).mp (hcols x (hsub hx))
  exact (reflectedColumn_isUnit_iff _ _).mpr
    ⟨h.1,fun y hy hne => h.2.1 y (hsub hy) hne,fun y hy hne => h.2.2 y (hsub hy) hne⟩

theorem coefficientChecks_le {N m : ℕ} (hm : 0<m) {k : ℕ} (hk : k∈coefficientChecks N m) :
    k≤m := by
  simp only [coefficientChecks,List.mem_append,List.mem_map] at hk
  rcases hk with ⟨w,hw,rfl⟩|⟨w,hw,rfl⟩
  · have h := (SemiprimeRowAreaSpectrum.publicPacket_coefficient_bounds hm hw).1
    rw [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  · have h := (SemiprimeRowAreaSpectrum.publicPacket_coefficient_bounds hm hw).2
    rw [Int.abs_eq_natAbs] at h
    exact_mod_cast h

/-- A failed public prefix also discharges every old coefficient scan entry. -/
theorem prefix_none_coefficient_scan {N m : ℕ} (hm : 0<m) (hcover : m^2<N)
    (hnone : SemiprimeStrassenPrefix.factorPrefix N m=none) :
    scanProper N (coefficientChecks N m)=none := by
  apply (scanProper_none_iff _ _).mpr
  intro k hk
  by_cases hz : k=0
  · subst k
    simp [SemiprimeGroupSelection.checkedSignal]
  · have hbound := (coefficientChecks_le hm hk).trans
      (show m≤m^2 by simpa only [pow_two] using Nat.le_mul_self m)
    have hcop := SemiprimeStrassenPrefix.prefix_none_coprime_integer hcover hnone
      (Nat.pos_of_ne_zero hz) hbound
    simp only [SemiprimeGroupSelection.checkedSignal,show N.gcd k=1 from hcop,
      lt_self_iff_false,false_and,if_false]

/-- Enlarging the original detector preserves all old successful coefficient and root branches. -/
theorem recoverLiteralQuadratics_preserves_joined {N m d : ℕ} (hm : 0<m)
    (hcover : m^2<N) (hd : recoverJoinedAffineRows N m=some d) :
    ∃ f, recoverLiteralQuadratics N m=some f := by
  let : NeZero N := ⟨by omega⟩
  unfold recoverLiteralQuadratics
  cases hf : SemiprimeStrassenPrefix.factorPrefix N m with
  | some f => exact ⟨f,rfl⟩
  | none =>
    cases hr : recoverReflectedRows (augmentedRoots N m) with
    | some f => exact ⟨f,rfl⟩
    | none =>
      have ho := reflected_none_of_subset (show joinedRoots N m⊆augmentedRoots N m from
        Finset.subset_union_left) hr
      have hscan := prefix_none_coefficient_scan hm hcover hf
      unfold recoverJoinedAffineRows at hd
      rw [hscan,ho] at hd
      contradiction

/-- Public-prefix and shared-polynomial recovery queries, excluding their construction. -/
noncomputable def literalGcdCount (N m : ℕ) : ℕ :=
  recoveryGcdCount N (SemiprimeStrassenPrefix.blockLeaves N m)
    (SemiprimeStrassenPrefix.blockColumns N m)+
    match SemiprimeStrassenPrefix.factorPrefix N m with
    | some _ => 0
    | none => recoveryGcdCount N (fun i => reflectedLeaves (augmentedRoots N m) (i : ZMod N))
        (reflectedColumns (augmentedRoots N m))

/-- This linear GCD-query bound does not supply the polynomial or bit clocks. -/
theorem literalGcdCount_le (N m : ℕ) :
    literalGcdCount N m≤15*(publicPackets N m).length+5*m+1 := by
  have hp := SemiprimeStrassenPrefix.prefix_gcd_bound N m
  have hr := recoverReflectedRows_gcd_bound (augmentedRoots N m)
  have hc := augmentedRoots_card_le N m
  unfold literalGcdCount
  cases SemiprimeStrassenPrefix.factorPrefix N m <;> dsimp only <;> omega

theorem literalGcdCount_prime_le (N : ℕ) {m : ℕ} (hm : m.Prime) :
    literalGcdCount N m≤120*m*(Nat.log2 m+1)^2+5*m+1 := by
  calc
    _ ≤ 15*(publicPackets N m).length+5*m+1 := literalGcdCount_le N m
    _ ≤ 15*(8*m*(Nat.log2 m+1)^2)+5*m+1 := by
      have h := SemiprimeEuclidRowBudget.publicPackets_length_le N hm
      omega
    _ = _ := by ring

end RiemannGaussian.SemiprimeLiteralQuadraticRoots
