/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryWeightRun

/-! # Native acquisition stages of the original recovery weights
These are actual retained scalar/control reports. Rational normalization and
integer digit costs remain a separate refinement, not unit physical-bit steps.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1RecoveryWeightRunBounds
open SemiprimeD1RecoveryWeightRun SemiprimeD1RecoveryScalarRun

/-- Every acquired multiplicity is bounded by the original taper rectangle. -/
theorem multiplicity_value_le (g : Geometry) (h u q : ℕ) :
    (multiplicityRun g h u q).value ≤ h*u := by
  dsimp [multiplicityRun]
  exact Nat.mul_le_mul_left h (Nat.sub_le _ _)

/-- Actual bounded valuation traversal, including multiplicity arithmetic. -/
theorem multiplicity_work (g : Geometry) (h u q : ℕ) :
    (multiplicityRun g h u q).work ≤ 5*g.size+8 := by
  have ho:=orderFuel_work g.size ((q:ℤ)-g.center).natAbs
  dsimp only [multiplicityRun]
  omega

/-- Original grid traversal, powers and every copied slope cell are retained. -/
theorem grid_work (g : Geometry) (h u t : ℕ) (qs : List ℕ) :
    (gridRows g h u t qs).work ≤ qs.length*(5*g.size+20*(h*u)+100)+1 := by
  induction qs with
  | nil => simp [gridRows]
  | cons q qs ih =>
    have hm:=multiplicity_value_le g h u q
    have hw:=multiplicity_work g h u q
    simp only [gridRows]
    split_ifs
    · dsimp only
      simp only [List.length_cons]
      nlinarith
    · dsimp only
      simp only [intPower_work,repeat_work,repeat_value,List.length_replicate,List.length_cons]
      nlinarith

/-- Each right-recursive scalar sum charges all visited indices. -/
theorem sum_work (j : ℕ) (inv powers : Array ℚ) (keys : List ℕ) :
    (sumWeights j inv powers keys).work ≤ 7*keys.length+1 := by
  induction keys with
  | nil => simp [sumWeights]
  | cons k ks ih =>
    simp only [sumWeights]
    split_ifs <;> dsimp only <;> simp only [List.length_cons] <;> omega

/-- The outer scalar multiplication is charged in addition to the whole sum. -/
theorem weight_work (E : ℚ) (j : ℕ) (inv powers : Array ℚ) (keys : List ℕ) :
    (weightRun E j inv powers keys).work ≤ 7*keys.length+4 := by
  have h:=sum_work j inv powers keys
  dsimp only [weightRun]
  omega

/-- Cached canonical extraction retains every supplied *executed* scalar report. -/
theorem canonical_work (rs : List (Run ℚ)) :
    (canonicalRows rs).work=(rs.map (fun r => r.work)).sum+4*rs.length+1 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [canonicalRows,List.map_cons,List.sum_cons,List.length_cons,ih]; omega

/-- The actual power cache has quadratic native scalar/control work. -/
theorem powers_work (x : ℚ) (q : ℕ) :
    (powersRun x q).work ≤ 30*(q+1)^2 := by
  have hs : ((List.range q).map (fun n => (rationalPower x n).work)).sum ≤ q*(3*q+1) := by
    have he : ((List.range q).map (fun n => (rationalPower x n).work)).length • (3*q+1) = q*(3*q+1) := by simp
    rw [← he]
    apply List.sum_le_length_nsmul
    intro n hn
    obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hn
    rw [rationalPower_work]
    have hk':=List.mem_range.mp hk
    omega
  simp only [powersRun,indices_work,indices_value,List.map_map,Function.comp_def,List.length_range]
  nlinarith

/-- Actual slope payload length, including every recursive grid frame. -/
theorem grid_length (g : Geometry) (h u t : ℕ) (qs : List ℕ) :
    (gridRows g h u t qs).slopes.length ≤ qs.length*(h*u) := by
  induction qs with
  | nil => simp [gridRows]
  | cons q qs ih =>
    have hm:=multiplicity_value_le g h u q
    simp only [gridRows]
    split_ifs <;> dsimp only
    · simp only [List.length_cons]; nlinarith
    · simp only [List.length_append,repeat_value,List.length_replicate,List.length_cons]; nlinarith

/-- Native canonical extraction of all original local weights is quadratic. -/
theorem local_rows_work (E : ℚ) (inv powers : Array ℚ) (keys : List ℕ) :
    (canonicalRows (keys.map (fun j => weightRun E j inv powers keys))).work ≤
      keys.length*(7*keys.length+8)+1 := by
  rw [canonical_work]
  have hs : ((keys.map (fun j => weightRun E j inv powers keys)).map (fun r => r.work)).sum ≤
      keys.length*(7*keys.length+4) := by
    have he : ((keys.map (fun j => weightRun E j inv powers keys)).map (fun r => r.work)).length •
        (7*keys.length+4)=keys.length*(7*keys.length+4) := by simp
    rw [← he]
    apply List.sum_le_length_nsmul
    intro z hz
    obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hz
    obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hr
    exact weight_work E j inv powers keys
  simp only [List.length_map]
  nlinarith

/-- A fully explicit fixed polynomial for the actual original node producer.
The parameters are the original exponent and acquired grid/taper dimensions,
never rational magnitudes or an advised operation count. -/
def nodeBudget (a N h u : ℕ) : ℕ :=
  (3*a+8)+(N*N+4*N+1)+(N*(5*N+20*(h*u)+100)+1)+(5*N+8)+
    2*(N*(h*u))*((h*u)*(h*u+1))+(3*(h*u)^2+2)+
    ((h*u)^2+4*(h*u)+1)+30*(h*u+1)^2+(h*u)*(7*(h*u)+8)+1+4*(h*u)+20

/-- Actual original node work has an original-parameter polynomial bound.
This bounds the retained native scalar/control report, not the cost of GCD or
big-integer primitives; those require the separately derived bit heights. -/
theorem acquire_work (a M u : ℕ) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) :
    (SemiprimeD1RecoveryWeightRun.acquire a M u t).work ≤
      nodeBudget a (SemiprimeD1WireKernelOriginal.size a) (SemiprimeD1TaperedLoss.height M u) u := by
  let g:=geometry a t.val
  let h:=SemiprimeD1TaperedLoss.height M u
  let q:=(multiplicityRun g h u t.val).value
  let cs:=(gridRows g h u t.val (indices g.size).value).slopes
  have hq : q ≤ h*u := multiplicity_value_le g h u t.val
  have hg:=grid_work g h u t.val (indices g.size).value
  have hl:=grid_length g h u t.val (indices g.size).value
  have hm:=multiplicity_work g h u t.val
  have hp:=powers_work (-(g.point:ℚ)/(g.alpha:ℚ)) q
  have hc:=local_rows_work
    (((gridRows g h u t.val (indices g.size).value).numerator:ℚ)/
      ((gridRows g h u t.val (indices g.size).value).denominator:ℚ))
    (SemiprimeJetArray.inverse (SemiprimeHermiteArrayHeight.buildAffine q cs).coefficients q).coefficients
    (powersRun (-(g.point:ℚ)/(g.alpha:ℚ)) q).value (indices q).value
  have ha:=SemiprimeHermiteArrayHeight.buildAffine_work q cs
  have hi:=SemiprimeJetArray.inverse_work (SemiprimeHermiteArrayHeight.buildAffine q cs).coefficients q
  have hgeom : g.work=3*a+8 := by simp [g,geometry,intPower_work]
  have hsize : g.size=SemiprimeD1WireKernelOriginal.size a := geometry_size a t.val
  simp only [indices_value,List.length_range] at hg hl hc
  have hlin : 2*cs.length*(q*(q+1)) ≤ 2*(g.size*(h*u))*((h*u)*(h*u+1)) := by
    gcongr
    simpa only [cs,indices_value] using hl
  have hpow : 30*(q+1)^2 ≤ 30*(h*u+1)^2 := by gcongr
  have hquad : 3*q^2 ≤ 3*(h*u)^2 := by gcongr
  have hidx : q*q+4*q+1 ≤ (h*u)^2+4*(h*u)+1 := by nlinarith
  have hcan : q*(7*q+8) ≤ (h*u)*(7*(h*u)+8) := by gcongr
  change g.work+(indices g.size).work+(gridRows g h u t.val (indices g.size).value).work+
    (multiplicityRun g h u t.val).work+
    (SemiprimeHermiteArrayHeight.buildAffine q cs).arithmetic+
    (SemiprimeHermiteArrayHeight.buildAffine q cs).reads+
    (SemiprimeJetArray.inverse (SemiprimeHermiteArrayHeight.buildAffine q cs).coefficients q).arithmetic+
    (SemiprimeJetArray.inverse (SemiprimeHermiteArrayHeight.buildAffine q cs).coefficients q).reads+
    (indices q).work+(powersRun (-(g.point:ℚ)/(g.alpha:ℚ)) q).work+_+4*(indices q).value.length+20 ≤ _
  simp only [indices_work,indices_value,List.length_range,hgeom,ha.1,ha.2]
  have hb : nodeBudget a (SemiprimeD1WireKernelOriginal.size a) (SemiprimeD1TaperedLoss.height M u) u = nodeBudget a g.size h u := by rw [hsize]
  rw [hb]
  unfold nodeBudget
  change _ ≤ (3*a+8)+(g.size*g.size+4*g.size+1)+
    (g.size*(5*g.size+20*(h*u)+100)+1)+(5*g.size+8)+
    2*(g.size*(h*u))*((h*u)*(h*u+1))+(3*(h*u)^2+2)+
    ((h*u)^2+4*(h*u)+1)+30*(h*u+1)^2+(h*u)*(7*(h*u)+8)+1+4*(h*u)+20
  have haa:=ha.1
  have har:=ha.2
  have hia:=hi.1
  have hir:=hi.2.1
  dsimp only [g,h,q,cs] at *
  simp only [indices_value,pow_two,Nat.mul_assoc] at *
  omega

end RiemannGaussian.SemiprimeD1RecoveryWeightRunBounds
