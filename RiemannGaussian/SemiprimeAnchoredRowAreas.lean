/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCenteredOffsetExtractor

/-!
# Three-row information through an anchored slope polynomial

Keep the full coefficient rows before taking their area. Integer division
removes the known global N from the three-row determinant. Two minors against
one public anchor convert the remaining area to a difference of unit-guarded
slopes. One root polynomial detects all proper areas containing this anchor.
It does not detect every triple or establish universal sixth-root coverage.
-/

namespace RiemannGaussian.SemiprimeAnchoredRowAreas

open SemiprimeQuotientRows SemiprimeQuotientCentering SemiprimeEuclidRowFamily
open SemiprimeAffineRowRoots SemiprimeCartesianCompletion SemiprimeRowDerivative

/-- Signed coefficient area, retaining the offset column before any norm. -/
def rowArea (m : ℕ) (u w v : FamilyPacket) : ℤ :=
  Matrix.det !![u.original.a,packetOffset m u,u.original.t;
    w.original.a,packetOffset m w,w.original.t;
    v.original.a,packetOffset m v,v.original.t]

/-- The actual Nt column contributes an exact global factor N. -/
theorem original_row_area (N m : ℕ) (u w v : FamilyPacket) :
    Matrix.det !![u.original.a,packetOffset m u,(N : ℤ)*u.original.t;
      w.original.a,packetOffset m w,(N : ℤ)*w.original.t;
      v.original.a,packetOffset m v,(N : ℤ)*v.original.t]=(N : ℤ)*rowArea m u w v := by
  simp [rowArea,Matrix.det_fin_three]
  ring

theorem original_row_area_div {N m : ℕ} (hN : 0<N) (u w v : FamilyPacket) :
    Matrix.det !![u.original.a,packetOffset m u,(N : ℤ)*u.original.t;
      w.original.a,packetOffset m w,(N : ℤ)*w.original.t;
      v.original.a,packetOffset m v,(N : ℤ)*v.original.t]/(N : ℤ)=rowArea m u w v := by
  rw [original_row_area,Int.mul_ediv_cancel_left _ (by exact_mod_cast hN.ne')]

/-- The signed minor against the anchor's offset column. -/
def offsetMinor (m : ℕ) (u w : FamilyPacket) : ℤ :=
  u.original.a*packetOffset m w-w.original.a*packetOffset m u

/-- Keep the denominator minor separate and check it before inversion. -/
def denominatorMinor (u w : FamilyPacket) : ℤ :=
  u.original.a*w.original.t-w.original.a*u.original.t

/-- Two anchored minors retain the complete three-row area. -/
theorem anchored_minor_identity (m : ℕ) (u w v : FamilyPacket) :
    offsetMinor m u w*denominatorMinor u v-offsetMinor m u v*denominatorMinor u w=
      u.original.a*rowArea m u w v := by
  simp [offsetMinor,denominatorMinor,rowArea,Matrix.det_fin_three]
  ring

/-- Only the guarded detector uses this normalized slope. -/
def anchorSlope (N m : ℕ) (u w : FamilyPacket) : ZMod N :=
  (offsetMinor m u w : ZMod N)*(denominatorMinor u w : ZMod N)⁻¹

theorem anchorSlope_coefficient {N m : ℕ} (u w : FamilyPacket)
    (hw : IsUnit (denominatorMinor u w : ZMod N)) :
    (denominatorMinor u w : ZMod N)*anchorSlope N m u w=(offsetMinor m u w : ZMod N) := by
  unfold anchorSlope
  rw [mul_left_comm,ZMod.mul_inv_of_unit _ hw,mul_one]

/-- Slope differences encode areas up to three checked unit phases. -/
theorem anchorSlope_difference {N m : ℕ} (u w v : FamilyPacket)
    (hw : IsUnit (denominatorMinor u w : ZMod N))
    (hv : IsUnit (denominatorMinor u v : ZMod N)) :
    (denominatorMinor u w : ZMod N)*(denominatorMinor u v : ZMod N)*
        (anchorSlope N m u w-anchorSlope N m u v)=
      (u.original.a : ZMod N)*(rowArea m u w v : ZMod N) := by
  have hwc := anchorSlope_coefficient (m:=m) u w hw
  have hvc := anchorSlope_coefficient (m:=m) u v hv
  have h := congrArg (fun z : ℤ => (z : ZMod N)) (anchored_minor_identity m u w v)
  push_cast at h
  linear_combination (denominatorMinor u v : ZMod N)*hwc-
    (denominatorMinor u w : ZMod N)*hvc+h

/-- Exact GCD equality preserves prime powers and saturation. -/
theorem anchorSlope_area_gcd {N m : ℕ} (u w v : FamilyPacket)
    (hu : IsUnit (u.original.a : ZMod N))
    (hw : IsUnit (denominatorMinor u w : ZMod N))
    (hv : IsUnit (denominatorMinor u v : ZMod N)) :
    N.gcd (rowArea m u w v : ZMod N).val=
      N.gcd (anchorSlope N m u w-anchorSlope N m u v).val := by
  have ha := SemiprimeRHCancellation.unit_mul_gcd_eq hu.unit (rowArea m u w v : ZMod N)
  have hd := SemiprimeRHCancellation.unit_mul_gcd_eq (hw.mul hv).unit
    (anchorSlope N m u w-anchorSlope N m u v)
  rw [hu.unit_spec] at ha
  rw [(hw.mul hv).unit_spec,anchorSlope_difference u w v hw hv] at hd
  exact ha.symm.trans hd

/-- Keep singular minors out of normalization. The public GCD prefix
below retains the factor information from excluded minors. -/
noncomputable def slopeEntry (N m : ℕ) (u w : FamilyPacket) : Option (ZMod N) := by
  classical
  exact if IsUnit (denominatorMinor u w : ZMod N) then some (anchorSlope N m u w) else none

/-- One guarded normalized slope per original source packet. -/
noncomputable def anchorValues (N m : ℕ) (u : FamilyPacket) : List (ZMod N) :=
  (publicPackets N m).filterMap (slopeEntry N m u)

/-- Deduplicate the detector fork modulo the whole N, keeping source rows upstream. -/
noncomputable def anchorRoots (N m : ℕ) (u : FamilyPacket) : Finset (ZMod N) :=
  (anchorValues N m u).toFinset

theorem anchorRoots_mem {N m : ℕ} (u : FamilyPacket) {w : FamilyPacket}
    (hw : w∈publicPackets N m) (hu : IsUnit (denominatorMinor u w : ZMod N)) :
    anchorSlope N m u w∈anchorRoots N m u := by
  classical
  apply List.mem_toFinset.mpr
  apply List.mem_filterMap.mpr
  exact ⟨w,hw,by simp only [slopeEntry,if_pos hu]⟩

theorem anchorRoots_card_le (N m : ℕ) (u : FamilyPacket) :
    (anchorRoots N m u).card≤(publicPackets N m).length := by
  calc
    _ ≤ (anchorValues N m u).length := List.toFinset_card_le _
    _ ≤ _ := List.length_filterMap_le _ _

/-- Public minor GCDs preserve excluded nonunit information. -/
def anchorChecks (N m : ℕ) (u : FamilyPacket) : List ℕ :=
  (publicPackets N m).map fun w => (denominatorMinor u w).natAbs

/-- One public anchor supplies one root axis; no list of triples is constructed. -/
noncomputable def recoverAnchorAreas (N m : ℕ) (u : FamilyPacket) : Option ℕ :=
  match scanProper N (anchorChecks N m u) with
  | some d => some d
  | none => recoverRows (anchorRoots N m u)

theorem recoverAnchorAreas_sound {N m d : ℕ} {u : FamilyPacket}
    (h : recoverAnchorAreas N m u=some d) : SemiprimeGroupSelection.ProperDivisor N d := by
  unfold recoverAnchorAreas at h
  cases hp : scanProper N (anchorChecks N m u) with
  | some e =>
    simp only [hp,Option.some.injEq] at h
    subst e
    exact scanProper_sound hp
  | none =>
    simp only [hp] at h
    exact recoverRows_sound h

/-- Every proper area containing this anchor survives polynomial recovery,
including full-modulus saturation in a derivative output. -/
theorem recoverAnchorAreas_of_proper_area {N m : ℕ} [NeZero N]
    (u : FamilyPacket) {w v : FamilyPacket} (hw : w∈publicPackets N m) (hv : v∈publicPackets N m)
    (hu : IsUnit (u.original.a : ZMod N))
    (huw : IsUnit (denominatorMinor u w : ZMod N))
    (huv : IsUnit (denominatorMinor u v : ZMod N))
    (hp : SemiprimeGroupSelection.ProperDivisor N (N.gcd (rowArea m u w v : ZMod N).val)) :
    ∃ d, recoverAnchorAreas N m u=some d := by
  unfold recoverAnchorAreas
  cases hs : scanProper N (anchorChecks N m u) with
  | some d => exact ⟨d,rfl⟩
  | none =>
    have hpg : SemiprimeGroupSelection.ProperDivisor N
        (N.gcd (anchorSlope N m u w-anchorSlope N m u v).val) := by
      rwa [←anchorSlope_area_gcd u w v hu huw huv]
    exact recoverRows_succeeds_of_proper_pair (anchorRoots_mem u hv huv) (anchorRoots_mem u hw huw) hpg

/-- Recovery query clock for one anchor; construction and bit costs are separate. -/
noncomputable def anchorGcdCount (N m : ℕ) (u : FamilyPacket) : ℕ :=
  scanGcdCount N (anchorChecks N m u)+
    match scanProper N (anchorChecks N m u) with
    | some _ => 0
    | none => recoveryGcdCount N (fun i => residueLeaves (anchorRoots N m u) (i : ZMod N))
        (evaluatedColumns (anchorRoots N m u) (anchorRoots N m u).toList)

theorem anchorGcdCount_le (N m : ℕ) (u : FamilyPacket) :
    anchorGcdCount N m u≤3*(publicPackets N m).length := by
  have hp := scanGcdCount_le N (anchorChecks N m u)
  have hr := recoverRows_gcd_bound (anchorRoots N m u)
  have hc := anchorRoots_card_le N m u
  have hlen : (anchorChecks N m u).length=(publicPackets N m).length := by
    simp only [anchorChecks,List.length_map]
  rw [hlen] at hp
  unfold anchorGcdCount
  cases scanProper N (anchorChecks N m u) <;> dsimp only <;> omega

theorem anchorGcdCount_prime_le (N : ℕ) {m : ℕ} (hm : m.Prime) (u : FamilyPacket) :
    anchorGcdCount N m u≤24*m*(Nat.log2 m+1)^2 := by
  calc
    _ ≤ 3*(publicPackets N m).length := anchorGcdCount_le N m u
    _ ≤ 3*(8*m*(Nat.log2 m+1)^2) := Nat.mul_le_mul_left 3
      (SemiprimeEuclidRowBudget.publicPackets_length_le N hm)
    _ = _ := by ring

/-- The larger center retains the same actual public Euclidean vector. -/
def largerPacket (N m j : ℕ) (v : ℤ×ℕ) : FamilyPacket :=
  let z := liftRow N m j (publicInverse m j) v.1 v.2
  ⟨j,z,reflectedShift N m j z.a z.b z.t⟩

theorem largerPacket_mem_of_pair {N m j : ℕ} (hj : j<m) (hc : j.Coprime m)
    {v : ℤ×ℕ} (hv : v∈publicPairs N m j) : largerPacket N m j v∈publicPackets N m := by
  apply List.mem_flatMap.mpr
  refine ⟨j,List.mem_range.mpr hj,?_⟩
  change largerPacket N m j v∈(if j.Coprime m then residuePackets N m j else [])
  rw [if_pos hc]
  apply List.mem_flatMap.mpr
  exact ⟨v,hv,List.mem_cons_of_mem _ List.mem_cons_self⟩

/-- A public Euclidean stream with gcd one reaches a unit numerator.
This proves acquisition of an anchor, without assuming an area hit. -/
theorem euclidPairs_has_unit {r₀ r₁ x y : ℕ} (negative : Bool) (hr : 0<r₁)
    (hg : Nat.gcd r₀ r₁=1) :
    ∃ v∈euclidPairs r₀ r₁ x y negative, v.1.natAbs=1 := by
  by_cases h₁ : r₁=1
  · refine ⟨(signed negative r₁,y),?_,?_⟩
    · rw [euclidPairs,if_neg (by omega : r₁≠0)]
      exact List.mem_cons_self
    · simpa only [signed_natAbs] using h₁
  · have hg' : Nat.gcd r₁ (r₀%r₁)=1 := by
      rw [Nat.gcd_comm r₁ (r₀%r₁),←Nat.gcd_rec r₁ r₀,Nat.gcd_comm]
      exact hg
    have hr' : 0<r₀%r₁ := by
      by_contra hn
      have he : r₀%r₁=0 := by omega
      rw [he,Nat.gcd_zero_right] at hg'
      contradiction
    obtain ⟨v,hv,hu⟩ := euclidPairs_has_unit (!negative) hr' hg'
    refine ⟨v,?_,hu⟩
    rw [euclidPairs,if_neg hr.ne']
    exact List.mem_cons_of_mem _ (List.mem_append_right _ hv)
termination_by r₁
decreasing_by exact Nat.mod_lt _ hr

/-- The control anchor comes from a fixed public unit-numerator rule. -/
def publicUnitAnchor (N m : ℕ) : Option FamilyPacket :=
  ((publicPairs N m 1).find? fun v => v.1.natAbs==1).map (largerPacket N m 1)

theorem publicUnitAnchor_exists {N m : ℕ} (hm : 1<m) (hN : m.Coprime N) :
    ∃ u, publicUnitAnchor N m=some u := by
  have hc := quotientSlope_coprime (by omega : 0<m) hN (Nat.coprime_one_left m)
  have hg : Nat.gcd m (quotientSlope N m 1%m)=1 := by
    rw [Nat.gcd_comm m (quotientSlope N m 1%m),←Nat.gcd_rec]
    exact hc
  have hr : 0<quotientSlope N m 1%m := by
    by_contra hn
    have he : quotientSlope N m 1%m=0 := by omega
    rw [he,Nat.gcd_zero_right] at hg
    omega
  obtain ⟨v,hv,hu⟩ := euclidPairs_has_unit (x:=0) (y:=1) false hr hg
  have hs : ((publicPairs N m 1).find? fun v => v.1.natAbs==1).isSome :=
    List.find?_isSome.mpr ⟨v,hv,by simpa only [beq_iff_eq] using hu⟩
  cases hf : (publicPairs N m 1).find? (fun v => v.1.natAbs==1) with
  | none => simp only [hf,Option.isSome_none,Bool.false_eq_true] at hs
  | some z => exact ⟨largerPacket N m 1 z,by simp only [publicUnitAnchor,hf,Option.map_some]⟩

/-- Successful anchor selection returns an actual public row with unit
integer numerator. The source remains available before normalization. -/
theorem publicUnitAnchor_spec {N m : ℕ} (hm : 1<m) {u : FamilyPacket}
    (hu : publicUnitAnchor N m=some u) : u∈publicPackets N m ∧ u.original.a.natAbs=1 := by
  cases hf : (publicPairs N m 1).find? (fun v => v.1.natAbs==1) with
  | none => simp [publicUnitAnchor,hf] at hu
  | some z =>
    simp only [publicUnitAnchor,hf,Option.map_some,Option.some.injEq] at hu
    subst u
    refine ⟨largerPacket_mem_of_pair hm (Nat.coprime_one_left m) (List.mem_of_find?_eq_some hf),?_⟩
    have ha := List.find?_some hf
    simpa only [largerPacket,liftRow,beq_iff_eq] using ha

theorem publicUnitAnchor_unit {N m : ℕ} (hm : 1<m) {u : FamilyPacket}
    (hu : publicUnitAnchor N m=some u) : IsUnit (u.original.a : ZMod N) := by
  exact (Int.isUnit_iff_natAbs_eq.mpr (publicUnitAnchor_spec hm hu).2).map (Int.castRingHom (ZMod N))

/-- Select the anchor using public Euclidean data, then recover its area axis. -/
noncomputable def recoverChosenAnchorAreas (N m : ℕ) : Option ℕ :=
  (publicUnitAnchor N m).bind (recoverAnchorAreas N m)

theorem recoverChosenAnchorAreas_sound {N m d : ℕ}
    (h : recoverChosenAnchorAreas N m=some d) : SemiprimeGroupSelection.ProperDivisor N d := by
  unfold recoverChosenAnchorAreas at h
  cases hs : publicUnitAnchor N m with
  | none => simp [hs] at h
  | some u =>
    simp only [hs,Option.bind_some] at h
    exact recoverAnchorAreas_sound h

/-- The public unit-numerator larger-center control anchor. -/
def controlAnchor : FamilyPacket := largerPacket 6396434398051 19 1 (1,3)
/-- The second actual public original row in the area certificate. -/
def controlSecond : FamilyPacket := smallerPacket 6396434398051 19 11 (-9,1)
/-- The third actual public original row in the area certificate. -/
def controlThird : FamilyPacket := smallerPacket 6396434398051 19 16 (1,8)

set_option maxRecDepth 32768 in
theorem control_public_vectors :
    ((1 : ℤ),3)∈publicPairs 6396434398051 19 1 ∧
      ((-9 : ℤ),1)∈publicPairs 6396434398051 19 11 ∧
      ((1 : ℤ),8)∈publicPairs 6396434398051 19 16 := by decide +kernel

theorem control_membership :
    controlAnchor∈publicPackets 6396434398051 19 ∧
      controlSecond∈publicPackets 6396434398051 19 ∧ controlThird∈publicPackets 6396434398051 19 := by
  exact ⟨largerPacket_mem_of_pair (by norm_num) (by norm_num [Nat.Coprime]) control_public_vectors.1,
    smallerPacket_mem_of_pair (by norm_num) (by norm_num [Nat.Coprime]) control_public_vectors.2.1,
    smallerPacket_mem_of_pair (by norm_num) (by norm_num [Nat.Coprime]) control_public_vectors.2.2⟩

set_option maxRecDepth 32768 in
theorem control_offsets_and_minors :
    packetOffset 19 controlAnchor=-9529224 ∧ packetOffset 19 controlSecond=16375576 ∧
      packetOffset 19 controlThird=-26582115 ∧
      denominatorMinor controlAnchor controlSecond=28 ∧ denominatorMinor controlAnchor controlThird=5 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem control_area : rowArea 19 controlAnchor controlSecond controlThird=130543748 := by
  decide +kernel

theorem control_units :
    IsUnit (controlAnchor.original.a : ZMod 6396434398051) ∧
      IsUnit (denominatorMinor controlAnchor controlSecond : ZMod 6396434398051) ∧
      IsUnit (denominatorMinor controlAnchor controlThird : ZMod 6396434398051) := by
  change IsUnit (1 : ZMod 6396434398051) ∧ _
  refine ⟨isUnit_one,?_⟩
  rw [control_offsets_and_minors.2.2.2.1,control_offsets_and_minors.2.2.2.2]
  constructor
  all_goals
    apply (SemiprimeBulkNorm.gcd_one_iff_unit _).mp
    norm_num [ZMod.val]
    decide +kernel

theorem control_area_gcd :
    (6396434398051 : ℕ).gcd (rowArea 19 controlAnchor controlSecond controlThird : ZMod 6396434398051).val=
      1919761 := by
  rw [control_area]
  norm_num [ZMod.val]
  decide +kernel

theorem control_anchor_recovers : ∃ d, recoverAnchorAreas 6396434398051 19 controlAnchor=some d := by
  apply recoverAnchorAreas_of_proper_area controlAnchor control_membership.2.1 control_membership.2.2
    control_units.1 control_units.2.1 control_units.2.2
  rw [control_area_gcd]
  norm_num [SemiprimeGroupSelection.ProperDivisor]

set_option maxRecDepth 32768 in
theorem control_public_anchor : publicUnitAnchor 6396434398051 19=some controlAnchor := by
  have h : (publicPairs 6396434398051 19 1).find? (fun v => v.1.natAbs==1)=some (1,3) := by
    decide +kernel
  simp only [publicUnitAnchor,h,Option.map_some]
  rfl

/-- The N,m-only anchor-selection program recovers this noncanonical-modulus control. -/
theorem control_chosen_recovers : ∃ d, recoverChosenAnchorAreas 6396434398051 19=some d := by
  simpa only [recoverChosenAnchorAreas,control_public_anchor,Option.bind_some]
    using control_anchor_recovers

end RiemannGaussian.SemiprimeAnchoredRowAreas
