/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeReciprocalRows

/-!
# Folding the two row channels while retaining the original unit carrier

The reciprocal trace combines the ordinary and product-one correlations.
Its exact difference identity holds over the composite ring, with a unit
phase, so it retains all prime-power valuations. Whole-ring trace equality
needs a checked difference guard before any deduplication: mixed local
orientations can otherwise hide a factor. Original units and packets remain
upstream, and the plus/minus-one channel retains local self-inversion.

One polynomial on distinct traces then extracts both inter-trace channels.
This is an extraction theorem, not universal sixth-root row coverage or a
complete deterministic bit-machine complexity bound.
-/

namespace RiemannGaussian.SemiprimeTraceRows

open scoped BigOperators
open SemiprimeCartesianCompletion SemiprimeEuclidRowFamily SemiprimeRowDerivative

/-- The original unit is retained; this scalar is a downstream fork. -/
def traceValue {R : Type*} [CommRing R] (x : Rˣ) : R :=
  (x : R)+((x⁻¹ : Rˣ) : R)

theorem traceValue_inv {R : Type*} [CommRing R] (x : Rˣ) :
    traceValue x⁻¹=traceValue x := by simp [traceValue,add_comm]

/-- The two correlations are kept as a product with an exact public unit
phase, rather than a norm or a field-only division identity. -/
theorem trace_difference {R : Type*} [CommRing R] (x y : Rˣ) :
    traceValue x-traceValue y=
      (((x*y)⁻¹ : Rˣ) : R)*((x : R)-(y : R))*((x : R)*(y : R)-1) := by
  have hx : (x : R)*((x⁻¹ : Rˣ) : R)=1 := by simp
  have hy : (y : R)*((y⁻¹ : Rˣ) : R)=1 := by simp
  have hc : ((x*y : Rˣ) : R)*(traceValue x-traceValue y)=
      ((x : R)-(y : R))*((x : R)*(y : R)-1) := by
    simp only [traceValue,Units.val_mul]
    linear_combination (y : R)*hx-(x : R)*hy
  have hi : (((x*y)⁻¹ : Rˣ) : R)*((x*y : Rˣ) : R)=1 := by
    change (((x*y)⁻¹*(x*y) : Rˣ) : R)=1
    rw [inv_mul_cancel]
    rfl
  have he := congrArg (fun z => (((x*y)⁻¹ : Rˣ) : R)*z) hc
  simpa only [←mul_assoc,hi,one_mul] using he

/-- The trace preserves the GCD of the two-channel product exactly, even
at prime powers and full-modulus saturation. -/
theorem trace_difference_gcd {n : ℕ} (x y : (ZMod n)ˣ) :
    n.gcd (traceValue x-traceValue y).val=
      n.gcd (((x : ZMod n)-(y : ZMod n))*((x : ZMod n)*(y : ZMod n)-1)).val := by
  rw [trace_difference,mul_assoc]
  exact SemiprimeRHCancellation.unit_mul_gcd_eq ((x*y)⁻¹) _

/-- Local trace equality means ordinary equality or product one. -/
theorem trace_map_eq_iff {R F : Type*} [CommRing R] [CommRing F] [IsDomain F]
    (φ : R →+* F) (x y : Rˣ) :
    φ (traceValue x)=φ (traceValue y) ↔
      φ (x : R)=φ (y : R) ∨ φ (x : R)*φ (y : R)=1 := by
  rw [←sub_eq_zero,←map_sub,trace_difference]
  simp only [map_mul,map_sub,map_one]
  have hu : φ ((((x*y)⁻¹ : Rˣ) : R))≠0 :=
    (Units.isUnit ((x*y)⁻¹)).map φ |>.ne_zero
  simp only [mul_eq_zero,hu,false_or,sub_eq_zero]

/-- A nonzero nonunit canonical residue always has a proper GCD, for any
positive modulus. No semiprime or squarefree premise enters this guard. -/
theorem proper_gcd_of_nonzero_nonunit {n : ℕ} [NeZero n] {z : ZMod n}
    (hz : z≠0) (hu : ¬IsUnit z) :
    SemiprimeGroupSelection.ProperDivisor n (n.gcd z.val) := by
  have hv := ZMod.val_pos.mpr hz
  have hg := Nat.gcd_pos_of_pos_right n hv
  have hn : n.gcd z.val≠1 := by
    intro he
    exact hu ((SemiprimeBulkNorm.gcd_one_iff_unit z).mp he)
  exact ⟨by omega,(Nat.gcd_le_right n hv).trans_lt (ZMod.val_lt z),
    Nat.gcd_dvd_left n z.val⟩

/-- A failed proper-factor check is exactly a global zero or a unit, so
the guard distinguishes these before any scalar bucket is collapsed. -/
theorem checkedSignal_none_iff {n : ℕ} [NeZero n] (z : ZMod n) :
    SemiprimeGroupSelection.checkedSignal n z.val=none ↔ z=0 ∨ IsUnit z := by
  constructor
  · intro hn
    by_cases hz : z=0
    · exact Or.inl hz
    · right
      by_contra hu
      have hp := proper_gcd_of_nonzero_nonunit hz hu
      have he : SemiprimeGroupSelection.checkedSignal n z.val=some (n.gcd z.val) := by
        simp [SemiprimeGroupSelection.checkedSignal,hp.1,hp.2.1]
      rw [hn] at he
      contradiction
  · rintro (hz|hu)
    · simp [hz,SemiprimeGroupSelection.checkedSignal]
    · have hg := (SemiprimeBulkNorm.gcd_one_iff_unit z).mpr hu
      simp [SemiprimeGroupSelection.checkedSignal,hg]

/-- Whole trace equality together with a unit ordinary difference forces
one global inverse orientation. This is the guard used before collapse. -/
theorem product_one_of_trace_eq_unit_difference {R : Type*} [CommRing R]
    (x y : Rˣ) (ht : traceValue x=traceValue y)
    (hu : IsUnit ((x : R)-(y : R))) : (x : R)*(y : R)=1 := by
  have hh := congrArg (fun z => ((x*y : Rˣ) : R)*z) (sub_eq_zero.mpr ht)
  rw [trace_difference] at hh
  have hphase : ((x*y : Rˣ) : R)*(((x*y)⁻¹ : Rˣ) : R)=1 := by
    change (((x*y)*(x*y)⁻¹ : Rˣ) : R)=1
    rw [mul_inv_cancel]
    rfl
  have he : ((x : R)-(y : R))*((x : R)*(y : R)-1)=0 := by
    simpa only [←mul_assoc,hphase,one_mul,mul_zero] using hh
  obtain ⟨u,heq⟩ := hu
  rw [←heq] at he
  have hf := congrArg (fun z => ((u⁻¹ : Rˣ) : R)*z) he
  have : (x : R)*(y : R)-1=0 := by simpa [←mul_assoc] using hf
  exact sub_eq_zero.mp this

/-- A whole-modulus trace collision with neither global orientation
already exposes a proper factor. Blind trace deduplication is unsound. -/
theorem mixed_trace_collision_proper {n : ℕ} [NeZero n]
    (x y : (ZMod n)ˣ) (ht : traceValue x=traceValue y)
    (hne : (x : ZMod n)≠(y : ZMod n))
    (hprod : (x : ZMod n)*(y : ZMod n)≠1) :
    SemiprimeGroupSelection.ProperDivisor n
      (n.gcd ((x : ZMod n)-(y : ZMod n)).val) := by
  apply proper_gcd_of_nonzero_nonunit (sub_ne_zero.mpr hne)
  intro hu
  exact hprod (product_one_of_trace_eq_unit_difference x y ht hu)

/-- After its checked whole-trace guard fails, a collapsed row equals the
retained representative or its global inverse. Mixed orientations cannot
be discarded silently. -/
theorem global_trace_guard_none_orientation {n : ℕ} [NeZero n]
    (x y : (ZMod n)ˣ) (ht : traceValue x=traceValue y)
    (hn : SemiprimeGroupSelection.checkedSignal n
      ((x : ZMod n)-(y : ZMod n)).val=none) : x=y ∨ x=y⁻¹ := by
  rcases (checkedSignal_none_iff _).mp hn with hz|hu
  · exact Or.inl (Units.ext (sub_eq_zero.mp hz))
  · right
    apply Units.ext
    apply sub_eq_zero.mp
    rw [SemiprimeReciprocalRows.inverse_residual_eq,
      product_one_of_trace_eq_unit_difference x y ht hu,sub_self,mul_zero]

/-- Both channel factors are units exactly when the trace difference is
a unit. This identity concerns the richer pair carrier before collapse. -/
theorem trace_difference_isUnit_iff {R : Type*} [CommRing R] (x y : Rˣ) :
    IsUnit (traceValue x-traceValue y) ↔
      IsUnit ((x : R)-(y : R)) ∧ IsUnit ((x : R)*(y : R)-1) := by
  rw [trace_difference,mul_assoc]
  constructor
  · intro hu
    exact (Commute.all _ _).isUnit_mul_iff.mp
      ((Commute.all _ _).isUnit_mul_iff.mp hu).2
  · rintro ⟨hd,hp⟩
    exact (Units.isUnit ((x*y)⁻¹)).mul (hd.mul hp)

/-- A useful self-product hit survives in one raw sign endpoint. Keeping
x-1 and x+1 avoids losing this channel when inverse orbits are collapsed. -/
theorem self_product_endpoint_proper {n : ℕ} [NeZero n] (x : ZMod n)
    (hp : SemiprimeGroupSelection.ProperDivisor n (n.gcd (x*x-1).val)) :
    SemiprimeGroupSelection.ProperDivisor n (n.gcd (x-1).val) ∨
      SemiprimeGroupSelection.ProperDivisor n (n.gcd (x+1).val) := by
  have hz : x*x-1≠0 := by
    intro he
    have hh := hp.2.1
    simp [he] at hh
  have he : (x-1)*(x+1)=x*x-1 := by ring
  have hm : x-1≠0 := by
    intro hh
    exact hz (he.symm.trans (by rw [hh,zero_mul]))
  have ha : x+1≠0 := by
    intro hh
    exact hz (he.symm.trans (by rw [hh,mul_zero]))
  have hu : ¬IsUnit (x*x-1) := by
    intro hh
    have hg := (SemiprimeBulkNorm.gcd_one_iff_unit _).mpr hh
    have hl := hp.1
    omega
  by_cases hminus : IsUnit (x-1)
  · right
    apply proper_gcd_of_nonzero_nonunit ha
    intro hplus
    exact hu (he ▸ hminus.mul hplus)
  · exact Or.inl (proper_gcd_of_nonzero_nonunit hm hminus)

/-- Distinct whole-ring traces are the roots of the single folded
polynomial. The original unit set is still available upstream. -/
def traceRoots {n : ℕ} (S : Finset (ZMod n)ˣ) : Finset (ZMod n) := S.image traceValue

/-- The single derivative-polynomial stage on distinct global traces.
The original units supply the separate endpoint and collision guards. -/
noncomputable def recoverTraceRows {n : ℕ} (S : Finset (ZMod n)ˣ) : Option ℕ :=
  recoverRows (traceRoots S)

theorem recoverTraceRows_sound {n d : ℕ} {S : Finset (ZMod n)ˣ}
    (hd : recoverTraceRows S=some d) : SemiprimeGroupSelection.ProperDivisor n d :=
  recoverRows_sound hd

/-- Any two distinct global traces whose two-channel product is a nonunit
are detected by one derivative polynomial, with full saturation recovery. -/
theorem recoverTraceRows_succeeds_of_nonunit_pair {n : ℕ} [NeZero n]
    {S : Finset (ZMod n)ˣ} {x y : (ZMod n)ˣ} (hx : x∈S) (hy : y∈S)
    (hne : traceValue x≠traceValue y)
    (hh : n.gcd (((x : ZMod n)-(y : ZMod n))*((x : ZMod n)*(y : ZMod n)-1)).val≠1) :
    ∃ d, recoverTraceRows S=some d := by
  have hp : SemiprimeGroupSelection.ProperDivisor n
      (n.gcd (traceValue x-traceValue y).val) := by
    apply proper_gcd_of_nonzero_nonunit (sub_ne_zero.mpr hne)
    intro hu
    exact hh ((trace_difference_gcd x y).symm.trans
      ((SemiprimeBulkNorm.gcd_one_iff_unit _).mpr hu))
  exact recoverRows_succeeds_of_proper_pair
    (Finset.mem_image.mpr ⟨y,hy,rfl⟩) (Finset.mem_image.mpr ⟨x,hx,rfl⟩) hp

/-- The folded derivative and one selected trace-row scan use at most
twice the original unit count in GCD queries. Guards and bit costs are
separate and cannot be inferred from this scalar query bound. -/
theorem recoverTraceRows_gcd_bound {n : ℕ} (S : Finset (ZMod n)ˣ) :
    recoveryGcdCount n (fun i => residueLeaves (traceRoots S) (i : ZMod n))
      (evaluatedColumns (traceRoots S) (traceRoots S).toList) ≤ 2*S.card := by
  exact (recoverRows_gcd_bound (traceRoots S)).trans
    (Nat.mul_le_mul_left 2 (Finset.card_image_le))

/-- Original public units are retained before the trace projection. -/
def publicUnitRoots {n : ℕ} (m : ℕ) (g : (ZMod n)ˣ) : Finset (ZMod n)ˣ :=
  ((publicPackets n m).map fun w => g^packetExponent m w).toFinset

theorem publicUnitRoots_mem_of_exponent {n m : ℕ} (g : (ZMod n)ˣ) {e : ℤ}
    (he : e∈publicExponents n m) : g^e∈publicUnitRoots m g := by
  obtain ⟨w,hw,hwe⟩ := List.mem_map.mp he
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨w,hw,by rw [hwe]⟩

/-- This is the folded polynomial stage. Endpoint and global-trace guards
belong before it and are not hidden in its specification. -/
noncomputable def recoverPublicTraceRows {n : ℕ} (m : ℕ) (g : (ZMod n)ˣ) : Option ℕ :=
  recoverTraceRows (publicUnitRoots m g)

theorem recoverPublicTraceRows_sound {n m d : ℕ} {g : (ZMod n)ˣ}
    (hd : recoverPublicTraceRows m g=some d) : SemiprimeGroupSelection.ProperDivisor n d :=
  recoverTraceRows_sound hd

theorem publicTraceRows_gcd_bound {n m : ℕ} (g : (ZMod n)ˣ) :
    recoveryGcdCount n
      (fun i => residueLeaves (traceRoots (publicUnitRoots m g)) (i : ZMod n))
      (evaluatedColumns (traceRoots (publicUnitRoots m g))
        (traceRoots (publicUnitRoots m g)).toList) ≤ 2*(publicPackets n m).length := by
  apply (recoverTraceRows_gcd_bound (publicUnitRoots m g)).trans
  apply Nat.mul_le_mul_left
  exact ((publicPackets n m).map fun w => g^packetExponent m w).toFinset_card_le.trans
    (by simp)

private theorem inverse_value_of_product_one {R : Type*} [CommRing R]
    (x : Rˣ) (a : R) (ha : (x : R)*a=1) : ((x⁻¹ : Rˣ) : R)=a := by
  have hi : ((x⁻¹ : Rˣ) : R)*(x : R)=1 := by simp
  calc
    _ = ((x⁻¹ : Rˣ) : R)*1 := by rw [mul_one]
    _ = ((x⁻¹ : Rˣ) : R)*((x : R)*a) := by rw [ha]
    _ = a := by rw [←mul_assoc,hi,one_mul]

/-- A literal mixed-orientation collision would be erased by unguarded
trace deduplication, but its original row difference recovers five. -/
theorem mixed_trace_control :
    traceValue (ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 35))=
      traceValue (ZMod.unitOfCoprime 32 (by norm_num : Nat.Coprime 32 35)) ∧
    SemiprimeGroupSelection.checkedSignal 35 ((2-32 : ZMod 35).val)=some 5 := by
  have hi₂ : (((ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 35))⁻¹ :
      (ZMod 35)ˣ) : ZMod 35)=18 := by
    apply inverse_value_of_product_one
    norm_num only [ZMod.coe_unitOfCoprime]
    reduce_mod_char
  have hi₃₂ : (((ZMod.unitOfCoprime 32 (by norm_num : Nat.Coprime 32 35))⁻¹ :
      (ZMod 35)ˣ) : ZMod 35)=23 := by
    apply inverse_value_of_product_one
    norm_num only [ZMod.coe_unitOfCoprime]
    reduce_mod_char
  constructor
  · simp only [traceValue,hi₂,hi₃₂,ZMod.coe_unitOfCoprime]
    reduce_mod_char
  · have hv : ((2-32 : ZMod 35).val)=5 := by decide +kernel
    rw [hv]
    norm_num [SemiprimeGroupSelection.checkedSignal]

private def controlTraceUnit₁ : (ZMod 2518766418595894637609)ˣ :=
  ZMod.unitOfCoprime 459898352550707889411
    (by norm_num : Nat.Coprime 459898352550707889411 2518766418595894637609)

private def controlTraceUnit₂ : (ZMod 2518766418595894637609)ˣ :=
  ZMod.unitOfCoprime 588586918346787592002
    (by norm_num : Nat.Coprime 588586918346787592002 2518766418595894637609)

private theorem controlTraceUnit₁_original : controlTraceUnit₁=
    SemiprimeReciprocalRows.controlBase^(3596798445668641429783915 : ℤ) := by
  apply Units.ext
  simpa only [controlTraceUnit₁,ZMod.coe_unitOfCoprime,Nat.cast_ofNat]
    using SemiprimeReciprocalRows.control_values.1.symm

private theorem controlTraceUnit₂_original : controlTraceUnit₂=
    SemiprimeReciprocalRows.controlBase^(3037632300775047433790237 : ℤ) := by
  apply Units.ext
  simpa only [controlTraceUnit₂,ZMod.coe_unitOfCoprime,Nat.cast_ofNat]
    using SemiprimeReciprocalRows.control_values.2.symm

set_option maxRecDepth 32768 in
/-- Exact traces of the same original public powers used by the reciprocal
control. Inverses are checked by multiplication, not a trusted oracle. -/
theorem control_trace_values :
    traceValue (SemiprimeReciprocalRows.controlBase^(3596798445668641429783915 : ℤ))=
      2246103499706283744873 ∧
    traceValue (SemiprimeReciprocalRows.controlBase^(3037632300775047433790237 : ℤ))=
      2138336311656083492267 := by
  rw [←controlTraceUnit₁_original,←controlTraceUnit₂_original]
  have hi₁ : (((controlTraceUnit₁)⁻¹ :
      (ZMod 2518766418595894637609)ˣ) : ZMod 2518766418595894637609)=1786205147155575855462 := by
    apply inverse_value_of_product_one
    norm_num only [controlTraceUnit₁,ZMod.coe_unitOfCoprime]
    reduce_mod_char
  have hi₂ : (((controlTraceUnit₂)⁻¹ :
      (ZMod 2518766418595894637609)ˣ) : ZMod 2518766418595894637609)=1549749393309295900265 := by
    apply inverse_value_of_product_one
    norm_num only [controlTraceUnit₂,ZMod.coe_unitOfCoprime]
    reduce_mod_char
  simp only [traceValue]
  rw [hi₁,hi₂]
  norm_num only [controlTraceUnit₁,controlTraceUnit₂,ZMod.coe_unitOfCoprime]
  constructor <;> reduce_mod_char

set_option maxRecDepth 32768 in
/-- The complete N-only public folded detector succeeds on the larger
ordinary-row stress input. Neither the proving pair nor a factor is an
algorithm input. This is one control, not a coverage guarantee. -/
theorem control_public_trace_recovers :
    ∃ d, recoverPublicTraceRows 3691 SemiprimeReciprocalRows.controlBase=some d ∧
      SemiprimeGroupSelection.ProperDivisor 2518766418595894637609 d := by
  have hp : SemiprimeGroupSelection.ProperDivisor 2518766418595894637609
      ((2518766418595894637609 : ℕ).gcd
        ((2246103499706283744873-2138336311656083492267 :
          ZMod 2518766418595894637609)).val) := by
    norm_num [SemiprimeGroupSelection.ProperDivisor,ZMod.val_ofNat]
  have hx := publicUnitRoots_mem_of_exponent SemiprimeReciprocalRows.controlBase
    SemiprimeReciprocalRows.control_exponents.1
  have hy := publicUnitRoots_mem_of_exponent SemiprimeReciprocalRows.controlBase
    SemiprimeReciprocalRows.control_exponents.2
  have hg : SemiprimeGroupSelection.ProperDivisor 2518766418595894637609
      ((2518766418595894637609 : ℕ).gcd
        (traceValue (SemiprimeReciprocalRows.controlBase^(3596798445668641429783915 : ℤ))-
          traceValue (SemiprimeReciprocalRows.controlBase^(3037632300775047433790237 : ℤ))).val) := by
    rw [control_trace_values.1,control_trace_values.2]
    exact hp
  obtain ⟨d,hd⟩ := recoverRows_succeeds_of_proper_pair
    (Finset.mem_image.mpr ⟨_,hy,rfl⟩) (Finset.mem_image.mpr ⟨_,hx,rfl⟩) hg
  exact ⟨d,hd,recoverPublicTraceRows_sound hd⟩

end RiemannGaussian.SemiprimeTraceRows
