/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeAffineProjectionObstruction

/-!
# Two signed coordinate-dual row axes

The area of a row, its signed coordinate dual, and a third row factors
into small coefficient phases and one scalar difference. This preserves
this particular three-row channel with two values per original public
packet. The coordinate dual is defined explicitly; membership of every
dual in the Euclidean stream is not assumed. Universal useful-hit coverage
and a complete sixth-root bit clock remain unproved.
-/

namespace RiemannGaussian.SemiprimeSymmetricRowAxes

open SemiprimeQuotientRows SemiprimeQuotientCentering SemiprimeEuclidRowFamily
open SemiprimeCompanionRows SemiprimeSameResidueAreas SemiprimeAffineRowRoots
open SemiprimeCompanionCoverage SemiprimeReflectedCompanions
open SemiprimeLiteralQuadraticRoots SemiprimeCenteredOffsetExtractor
open SemiprimeQuadraticPointJets SemiprimeCartesianCompletion SemiprimeRowDerivative

/-- Both coefficient sums remain signed, including the globally zero cases. -/
def axisDenominator (w : FamilyPacket) (minus : Bool) : ℤ :=
  if minus then w.original.a-w.original.t else w.original.a+w.original.t

/-- The complementary small coefficient is the area phase. -/
def axisPhase (w : FamilyPacket) (minus : Bool) : ℤ := axisDenominator w (!minus)

/-- Two rational scalar axes; use their factor transport only after unit guards. -/
def axisRoot (N m : ℕ) (w : FamilyPacket) (minus : Bool) : ZMod N :=
  -(packetOffset m w : ZMod N)*(axisDenominator w minus : ZMod N)⁻¹

/-- The literal integer area retains the signed dual middle row. -/
def dualCoordinateArea (m : ℕ) (u v : FamilyPacket) (minus : Bool) : ℤ :=
  Matrix.det !![u.original.a,packetOffset m u,u.original.t;
    u.original.t,(if minus then -packetOffset m u else packetOffset m u),u.original.a;
    v.original.a,packetOffset m v,v.original.t]

theorem dualCoordinateArea_factor (m : ℕ) (u v : FamilyPacket) (minus : Bool) :
    dualCoordinateArea m u v minus = -axisPhase u minus*
      (axisDenominator u minus*packetOffset m v-
        axisDenominator v minus*packetOffset m u) := by
  cases minus <;> simp [dualCoordinateArea,axisPhase,axisDenominator,Matrix.det_fin_three]
    <;> ring

theorem axisRoot_coefficient {N m : ℕ} (w : FamilyPacket) (minus : Bool)
    (hu : IsUnit (axisDenominator w minus : ZMod N)) :
    (axisDenominator w minus : ZMod N)*axisRoot N m w minus=
      -(packetOffset m w : ZMod N) := by
  unfold axisRoot
  rw [mul_left_comm,ZMod.mul_inv_of_unit _ hu,mul_one]

theorem axisRoot_eq_zero_of_denominator_zero {N m : ℕ} (w : FamilyPacket) (minus : Bool)
    (hz : axisDenominator w minus=0) : axisRoot N m w minus=0 := by
  simp [axisRoot,hz,ZMod.inv_zero]

theorem dualCoordinateArea_axis {N m : ℕ} (u v : FamilyPacket) (minus : Bool)
    (hu : IsUnit (axisDenominator u minus : ZMod N))
    (hv : IsUnit (axisDenominator v minus : ZMod N)) :
    (dualCoordinateArea m u v minus : ZMod N)=
      -(axisPhase u minus : ZMod N)*(axisDenominator u minus : ZMod N)*
        (axisDenominator v minus : ZMod N)*(axisRoot N m u minus-axisRoot N m v minus) := by
  have hr := axisRoot_coefficient (m:=m) u minus hu
  have hs := axisRoot_coefficient (m:=m) v minus hv
  rw [dualCoordinateArea_factor]
  push_cast
  linear_combination (axisPhase u minus : ZMod N)*(axisDenominator v minus : ZMod N)*hr-
    (axisPhase u minus : ZMod N)*(axisDenominator u minus : ZMod N)*hs

/-- Whole-N area transport retains proper factors, prime powers and saturation. -/
theorem dualCoordinateArea_gcd {N m : ℕ} (u v : FamilyPacket) (minus : Bool)
    (hp : IsUnit (axisPhase u minus : ZMod N))
    (hu : IsUnit (axisDenominator u minus : ZMod N))
    (hv : IsUnit (axisDenominator v minus : ZMod N)) :
    N.gcd (dualCoordinateArea m u v minus : ZMod N).val=
      N.gcd (axisRoot N m u minus-axisRoot N m v minus).val := by
  have h := SemiprimeRHCancellation.unit_mul_gcd_eq ((hp.neg.mul hu).mul hv).unit
    (axisRoot N m u minus-axisRoot N m v minus)
  rw [((hp.neg.mul hu).mul hv).unit_spec,←dualCoordinateArea_axis u v minus hu hv] at h
  exact h

/-- The full original public coefficient diamond pays both new denominator guards. -/
theorem publicPacket_axis_abs_le {N m : ℕ} (hm : 0<m) {w : FamilyPacket}
    (hw : w∈publicPackets N m) (minus : Bool) : |axisDenominator w minus|≤(m : ℤ) := by
  have hb := publicPacket_coefficient_sum_le hm hw
  cases minus
  · exact (abs_add_le _ _).trans hb
  · have h := abs_sub_le w.original.a 0 w.original.t
    simp only [sub_zero,zero_sub,abs_neg] at h
    exact h.trans hb

/-- A failed N-only prefix supplies every nonzero axis coefficient unit. -/
theorem prefix_none_axis_unit {N m : ℕ} (hm : 0<m) (hcover : m^2<N)
    (hn : SemiprimeStrassenPrefix.factorPrefix N m=none)
    {w : FamilyPacket} (hw : w∈publicPackets N m) (minus : Bool)
    (hz : axisDenominator w minus≠0) : IsUnit (axisDenominator w minus : ZMod N) := by
  apply prefix_none_bounded_int_unit hcover hn hz
  have hb := publicPacket_axis_abs_le hm hw minus
  have hm' : m≤m^2 := by simpa only [pow_two] using Nat.le_mul_self m
  exact hb.trans (by exact_mod_cast hm')

/-- Public source membership, the prefix, and three nonzero integers discharge all phases. -/
theorem publicPacket_dualCoordinateArea_gcd {N m : ℕ} (hm : 0<m) (hcover : m^2<N)
    (hn : SemiprimeStrassenPrefix.factorPrefix N m=none)
    {u v : FamilyPacket} (hu : u∈publicPackets N m) (hv : v∈publicPackets N m)
    (minus : Bool) (hpu : axisPhase u minus≠0)
    (hdu : axisDenominator u minus≠0) (hdv : axisDenominator v minus≠0) :
    N.gcd (dualCoordinateArea m u v minus : ZMod N).val=
      N.gcd (axisRoot N m u minus-axisRoot N m v minus).val :=
  dualCoordinateArea_gcd u v minus
    (prefix_none_axis_unit hm hcover hn hu (!minus) hpu)
    (prefix_none_axis_unit hm hcover hn hu minus hdu)
    (prefix_none_axis_unit hm hcover hn hv minus hdv)

/-- Every original packet emits each of the two axes, without constructing pairs. -/
def axisValues (N m : ℕ) (minus : Bool) : List (ZMod N) :=
  (publicPackets N m).map (fun w => axisRoot N m w minus)

/-- Complete axis values, deduplicated only over the original modulus. -/
noncomputable def axisRoots (N m : ℕ) : Finset (ZMod N) :=
  (axisValues N m false).toFinset∪(axisValues N m true).toFinset

theorem axisRoots_mem {N m : ℕ} {w : FamilyPacket} (hw : w∈publicPackets N m)
    (minus : Bool) : axisRoot N m w minus∈axisRoots N m := by
  have h : axisRoot N m w minus∈(axisValues N m minus).toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨w,hw,rfl⟩)
  cases minus
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ h

theorem axisRoots_card_le (N m : ℕ) : (axisRoots N m).card≤2*(publicPackets N m).length := by
  have h₀ := List.toFinset_card_le (axisValues N m false)
  have h₁ := List.toFinset_card_le (axisValues N m true)
  have hl (side : Bool) : (axisValues N m side).length=(publicPackets N m).length :=
    List.length_map _
  rw [hl] at h₀ h₁
  have h := Finset.card_union_le (axisValues N m false).toFinset
    (axisValues N m true).toFinset
  unfold axisRoots
  omega

/-- Retain every preceding amended root, adding only the two signed axes. -/
noncomputable def symmetricRoots (N m : ℕ) : Finset (ZMod N) :=
  augmentedRoots N m∪axisRoots N m

theorem symmetricRoots_card_le (N m : ℕ) :
    (symmetricRoots N m).card≤7*(publicPackets N m).length+m := by
  have h₀ := augmentedRoots_card_le N m
  have h₁ := axisRoots_card_le N m
  have h := Finset.card_union_le (augmentedRoots N m) (axisRoots N m)
  unfold symmetricRoots
  omega

/-- The public small-factor prefix precedes complete reflected recovery. -/
noncomputable def recoverSymmetricRows (N m : ℕ) : Option ℕ :=
  match SemiprimeStrassenPrefix.factorPrefix N m with
  | some d => some d
  | none => recoverReflectedRows (symmetricRoots N m)

theorem recoverSymmetricRows_sound {N m d : ℕ} (hd : recoverSymmetricRows N m=some d) :
    SemiprimeGroupSelection.ProperDivisor N d := by
  unfold recoverSymmetricRows at hd
  cases hp : SemiprimeStrassenPrefix.factorPrefix N m with
  | some f =>
    simp only [hp,Option.some.injEq] at hd
    subst d
    exact SemiprimeStrassenPrefix.prefix_sound hp
  | none => exact recoverReflectedRows_sound (by simpa only [hp] using hd)

private theorem reflected_none_of_subset {N : ℕ} [NeZero N] {S T : Finset (ZMod N)}
    (hsub : S⊆T) (hT : recoverReflectedRows T=none) : recoverReflectedRows S=none := by
  have hcols := (recoverReflectedRows_none_iff _).mp hT
  apply (recoverReflectedRows_none_iff _).mpr
  intro x hx
  have h := (reflectedColumn_isUnit_iff _ _).mp (hcols x (hsub hx))
  exact (reflectedColumn_isUnit_iff _ _).mpr
    ⟨h.1,fun y hy hne => h.2.1 y (hsub hy) hne,fun y hy hne => h.2.2 y (hsub hy) hne⟩

/-- Every prior success survives the enlarged source and its saturated recovery. -/
theorem recoverSymmetricRows_preserves_literal {N m d : ℕ} [NeZero N]
    (hd : recoverLiteralQuadratics N m=some d) :
    ∃ f, recoverSymmetricRows N m=some f := by
  unfold recoverSymmetricRows
  cases hf : SemiprimeStrassenPrefix.factorPrefix N m with
  | some f => exact ⟨f,rfl⟩
  | none =>
    have ho : recoverReflectedRows (augmentedRoots N m)=some d := by
      simpa only [recoverLiteralQuadratics,hf] using hd
    cases hr : recoverReflectedRows (symmetricRoots N m) with
    | some f => exact ⟨f,rfl⟩
    | none =>
      have hn := reflected_none_of_subset (show augmentedRoots N m⊆symmetricRoots N m from
        Finset.subset_union_left) hr
      rw [ho] at hn
      contradiction

theorem recoverSymmetricRows_of_proper_pair {N m : ℕ} [NeZero N]
    {x t : ZMod N} (hx : x∈signedRoots (symmetricRoots N m))
    (ht : t∈signedRoots (symmetricRoots N m))
    (hp : SemiprimeGroupSelection.ProperDivisor N (N.gcd (t-x).val)) :
    ∃ d, recoverSymmetricRows N m=some d := by
  unfold recoverSymmetricRows
  cases hf : SemiprimeStrassenPrefix.factorPrefix N m with
  | some d => exact ⟨d,rfl⟩
  | none =>
    obtain ⟨d,hd⟩ := recoverRows_succeeds_of_proper_pair hx ht hp
    cases hr : recoverReflectedRows (symmetricRoots N m) with
    | some f => exact ⟨f,rfl⟩
    | none =>
      have hn := (recoverReflectedRows_none_iff_signed _).mp hr
      rw [hd] at hn
      contradiction

/-- This is a complete extraction statement for this guarded coordinate-dual channel,
not a claim that such a proper area exists on every semiprime. -/
theorem recoverSymmetricRows_of_proper_dual_area {N m : ℕ} (hm : 0<m) (hcover : m^2<N)
    {u v : FamilyPacket} (hu : u∈publicPackets N m) (hv : v∈publicPackets N m)
    (minus : Bool) (hpu : axisPhase u minus≠0)
    (hdu : axisDenominator u minus≠0) (hdv : axisDenominator v minus≠0)
    (hp : SemiprimeGroupSelection.ProperDivisor N
      (N.gcd (dualCoordinateArea m u v minus : ZMod N).val)) :
    ∃ d, recoverSymmetricRows N m=some d := by
  let : NeZero N := ⟨by omega⟩
  by_cases hn : SemiprimeStrassenPrefix.factorPrefix N m=none
  · rw [publicPacket_dualCoordinateArea_gcd hm hcover hn hu hv minus hpu hdu hdv] at hp
    apply recoverSymmetricRows_of_proper_pair
      (signedRoots_mem (Finset.mem_union_right _ (axisRoots_mem hv minus)))
      (signedRoots_mem (Finset.mem_union_right _ (axisRoots_mem hu minus))) hp
  · cases hf : SemiprimeStrassenPrefix.factorPrefix N m with
    | none => exact (hn hf).elim
    | some d => exact ⟨d,by simp [recoverSymmetricRows,hf]⟩

/-- Recovery queries exclude polynomial construction, sorting, acquisition and bit costs. -/
noncomputable def symmetricGcdCount (N m : ℕ) : ℕ :=
  recoveryGcdCount N (SemiprimeStrassenPrefix.blockLeaves N m)
    (SemiprimeStrassenPrefix.blockColumns N m)+
    match SemiprimeStrassenPrefix.factorPrefix N m with
    | some _ => 0
    | none => recoveryGcdCount N (fun i => reflectedLeaves (symmetricRoots N m) (i : ZMod N))
        (reflectedColumns (symmetricRoots N m))

theorem symmetricGcdCount_le (N m : ℕ) :
    symmetricGcdCount N m≤21*(publicPackets N m).length+5*m+1 := by
  have hp := SemiprimeStrassenPrefix.prefix_gcd_bound N m
  have hr := recoverReflectedRows_gcd_bound (symmetricRoots N m)
  have hc := symmetricRoots_card_le N m
  unfold symmetricGcdCount
  cases SemiprimeStrassenPrefix.factorPrefix N m <;> dsimp only <;> omega

end RiemannGaussian.SemiprimeSymmetricRowAxes
