/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRowAreaSpectrum

/-!
# Same-residue area obstruction with both centers retained

The original Euclidean stream has the stronger coefficient envelope
|a|+t ≤ m. This bounds the mixed-center area direction by m³, before any
residue division. On balanced semiprimes the public center difference is
at most p+2. Thus, beyond a small-factor prefix, every same-residue triple
has zero or unit area, even when its centers differ. Cross-residue areas
and universal sixth-root factoring remain open.
-/

namespace RiemannGaussian.SemiprimeSameResidueAreas

open SemiprimeQuotientRows SemiprimeQuotientCentering SemiprimeEuclidRowFamily
open SemiprimeWeightedRows SemiprimeCompanionRows SemiprimeCompanionCenterSpectrum
open SemiprimeAffineRowRoots SemiprimeCenteredOffsetExtractor SemiprimeAnchoredRowAreas
open SemiprimeRowAreaSpectrum

/-- Keep the signed numerator and denominator together until their joint bound. -/
theorem euclidPairs_sum_le {m r₀ r₁ x y : ℕ} {negative : Bool}
    (horder : r₁<r₀) (hy : 0<y) (hdet : r₀*y+r₁*x=m)
    {z : ℤ×ℕ} (hz : z∈euclidPairs r₀ r₁ x y negative) : z.1.natAbs+z.2≤m := by
  rw [euclidPairs] at hz
  split_ifs at hz with hr
  · simp only [List.not_mem_nil] at hz
  · have hrpos : 0<r₁ := by omega
    simp only [List.mem_cons,List.mem_append,List.mem_map] at hz
    rcases hz with hcur|hmid|htail
    · subst z
      simp only [signed_natAbs]
      have h₁ := Nat.mul_le_mul_right y (show r₁+1≤r₀ by omega)
      have h₂ := Nat.mul_le_mul_left r₁ (show 1≤y by omega)
      nlinarith only [h₁,h₂,hdet,Nat.zero_le (r₁*x)]
    · obtain ⟨k,hk,rfl⟩ := hmid
      simp only [signed_natAbs]
      have hk' : k+1<r₀/r₁ := by have := List.mem_range.mp hk; omega
      have hmul : (k+1)*r₁≤r₀ :=
        (Nat.mul_le_mul_right r₁ hk'.le).trans (Nat.div_mul_le_self _ _)
      have hs := congrArg (fun z => z*y) (Nat.sub_add_cancel hmul)
      have hn : (r₀-(k+1)*r₁)*y+r₁*(x+(k+1)*y)=m := by
        nlinarith only [hs,hdet]
      have h₁ := Nat.mul_le_mul_left (r₀-(k+1)*r₁) (show 1≤y by omega)
      have h₂ := Nat.le_mul_of_pos_left (x+(k+1)*y) hrpos
      omega
    · have hq : 0<r₀/r₁ := Nat.div_pos horder.le hrpos
      have hn : r₁*(x+r₀/r₁*y)+(r₀%r₁)*y=m := by
        rw [←euclid_determinant_step,hdet]
      exact euclidPairs_sum_le (Nat.mod_lt _ hrpos) (by positivity) hn htail
termination_by r₁
decreasing_by exact Nat.mod_lt _ (by omega)

theorem publicPairs_sum_le {N m j : ℕ} (hm : 0<m) {z : ℤ×ℕ}
    (hz : z∈publicPairs N m j) : z.1.natAbs+z.2≤m :=
  euclidPairs_sum_le (Nat.mod_lt _ hm) (by decide) (by simp) hz

/-- The original public constructor supplies a diamond, rather than only a box. -/
theorem publicPacket_coefficient_sum_le {N m : ℕ} (hm : 0<m) {w : FamilyPacket}
    (hw : w∈publicPackets N m) : |w.original.a|+|w.original.t|≤(m : ℤ) := by
  obtain ⟨j,_,hw⟩ := List.mem_flatMap.mp hw
  split_ifs at hw
  · obtain ⟨z,hz,hw⟩ := List.mem_flatMap.mp hw
    have hb := publicPairs_sum_le hm hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl
    all_goals
      change |z.1|+|(z.2 : ℤ)|≤(m : ℤ)
      rw [Int.abs_eq_natAbs,abs_of_nonneg (Int.natCast_nonneg z.2)]
      exact_mod_cast hb
  · simp only [List.not_mem_nil] at hw

/-- A signed coefficient minor respects the full joint envelope. -/
theorem publicPacket_minor_abs_le {N m : ℕ} (hm : 0<m) {u w : FamilyPacket}
    (hu : u∈publicPackets N m) (hw : w∈publicPackets N m) :
    |denominatorMinor u w|≤(m : ℤ)^2 := by
  have hub := publicPacket_coefficient_sum_le hm hu
  have hwb := publicPacket_coefficient_sum_le hm hw
  have h := abs_sub_le (u.original.a*w.original.t) 0 (w.original.a*u.original.t)
  simp only [sub_zero,zero_sub,abs_neg,abs_mul] at h
  have hprod := mul_le_mul hub hwb
    (add_nonneg (abs_nonneg _) (abs_nonneg _)) (Int.natCast_nonneg m)
  have hdiag₁ := mul_nonneg (abs_nonneg u.original.a) (abs_nonneg w.original.a)
  have hdiag₂ := mul_nonneg (abs_nonneg u.original.t) (abs_nonneg w.original.t)
  unfold denominatorMinor
  nlinarith only [h,hprod,hdiag₁,hdiag₂]

theorem centerFlag_difference_abs_le (us ws : Bool) : |centerFlag us-centerFlag ws|≤1 := by
  cases us <;> cases ws <;> norm_num [centerFlag]

/-- One differing center contributes a signed minor with its full source retained. -/
theorem mixedArea_middle_center (u w v : FamilyPacket) (us ws : Bool) :
    mixedArea u w v us ws us=(centerFlag ws-centerFlag us)*
      (w.original.a-w.original.t)*denominatorMinor u v := by
  simp [mixedArea,denominatorMinor,Matrix.det_fin_three]
  ring

theorem publicPacket_center_minor_abs_le {N m : ℕ} (hm : 0<m) {u w v : FamilyPacket}
    (hu : u∈publicPackets N m) (hw : w∈publicPackets N m) (hv : v∈publicPackets N m)
    (us ws : Bool) :
    |(centerFlag us-centerFlag ws)*(u.original.a-u.original.t)*denominatorMinor w v|≤
      (m : ℤ)^3 := by
  have hdiff := abs_sub_le u.original.a 0 u.original.t
  simp only [sub_zero,zero_sub,abs_neg] at hdiff
  have hc := hdiff.trans (publicPacket_coefficient_sum_le hm hu)
  have hf := centerFlag_difference_abs_le us ws
  have hd := publicPacket_minor_abs_le hm hw hv
  rw [abs_mul,abs_mul]
  calc
    _ ≤ (1*(m : ℤ))*(m : ℤ)^2 :=
      mul_le_mul (mul_le_mul hf hc (abs_nonneg _) (by decide : (0 : ℤ)≤1)) hd
        (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- Both public centers, in all eight orientations, satisfy the cubic envelope. -/
theorem publicPacket_mixedArea_abs_le {N m : ℕ} (hm : 0<m) {u w v : FamilyPacket}
    (hu : u∈publicPackets N m) (hw : w∈publicPackets N m) (hv : v∈publicPackets N m)
    (us ws vs : Bool) : |mixedArea u w v us ws vs|≤(m : ℤ)^3 := by
  cases us <;> cases ws <;> cases vs
  · rw [mixedArea_same_center,abs_zero]; positivity
  · rw [mixedArea_last_center,neg_mul,neg_mul,abs_neg]
    exact publicPacket_center_minor_abs_le hm hv hu hw true false
  · rw [mixedArea_middle_center]
    exact publicPacket_center_minor_abs_le hm hw hu hv true false
  · rw [mixedArea_first_center,neg_mul,neg_mul,abs_neg]
    exact publicPacket_center_minor_abs_le hm hu hw hv false true
  · rw [mixedArea_first_center,neg_mul,neg_mul,abs_neg]
    exact publicPacket_center_minor_abs_le hm hu hw hv true false
  · rw [mixedArea_middle_center]
    exact publicPacket_center_minor_abs_le hm hw hu hv false true
  · rw [mixedArea_last_center,neg_mul,neg_mul,abs_neg]
    exact publicPacket_center_minor_abs_le hm hv hu hw false true
  · rw [mixedArea_same_center,abs_zero]; positivity

theorem centerDifference_nonneg (N : ℕ) : 0≤centerDifference N := by
  have h := Nat.sqrt_le_sqrt ((Nat.div_le_self N 2).trans (show N≤2*N by omega))
  have hz : ((N/2).sqrt : ℤ)≤(2*N).sqrt := by exact_mod_cast h
  simp [centerDifference,centerA]
  omega

/-- Floor-square-root errors are retained in the public center bound. -/
theorem sqrt_center_difference_le (N : ℕ) : (2*N).sqrt≤2*(N/2).sqrt+2 := by
  have hh := Nat.sqrt_le' (2*N)
  have hl := Nat.lt_succ_sqrt' (N/2)
  have hd := Nat.mod_add_div N 2
  have hr := Nat.mod_lt N (by decide : 0<2)
  nlinarith only [hh,hl,hd,hr]

theorem balanced_centerDifference_abs_le {p q : ℕ} (hq : q≤2*p) :
    |centerDifference (p*q)|≤(p : ℤ)+2 := by
  have hN : p*q≤2*p^2 := by nlinarith only [Nat.mul_le_mul_left p hq]
  have hdiv : p*q/2≤p^2 := by have := Nat.div_mul_le_self (p*q) 2; omega
  have hl : (p*q/2).sqrt≤p := by nlinarith only [Nat.sqrt_le' (p*q/2),hdiv]
  have hc := sqrt_center_difference_le (p*q)
  have hb : (2*(p*q)).sqrt≤(p*q/2).sqrt+p+2 := by omega
  have hbz : ((2*(p*q)).sqrt : ℤ)≤((p*q/2).sqrt : ℤ)+p+2 := by exact_mod_cast hb
  rw [abs_of_nonneg (centerDifference_nonneg (p*q))]
  simp [centerDifference,centerA]
  omega

/-- The mixed-center channel is bounded before the common residue division. -/
theorem publicPacket_mixed_area_bound {N m : ℕ} (hm : 0<m) {u w v : FamilyPacket}
    (hu : u∈publicPackets N m) (hw : w∈publicPackets N m) (hv : v∈publicPackets N m)
    (us ws vs : Bool) (huc : CenterChoice N m u us) (hwc : CenterChoice N m w ws)
    (hvc : CenterChoice N m v vs) :
    2*|rowArea m u w v|≤6*(m : ℤ)^4+|centerDifference N| *(m : ℤ)^3 := by
  have he := mixed_center_area u w v us ws vs huc hwc hvc
  have hb := publicPacket_errorArea_abs_le hm hu hw hv us ws vs
  have hmixed := publicPacket_mixedArea_abs_le hm hu hw hv us ws vs
  have ht := abs_sub_le (-errorArea N m u w v us ws vs) 0
    (centerDifference N*mixedArea u w v us ws vs)
  simp only [sub_zero,zero_sub,abs_neg,abs_mul] at ht
  have habs := congrArg abs he
  rw [abs_mul] at habs
  norm_num at habs
  have hp := mul_le_mul_of_nonneg_left hmixed (abs_nonneg (centerDifference N))
  nlinarith only [habs,ht,hb,hp]

/-- Divide the combined signed area, rather than dividing its channels separately. -/
theorem publicPacket_same_residue_normalized_bound {N m : ℕ} (hm : 0<m)
    (hcop : m.Coprime N) {u w v : FamilyPacket} (hu : u∈publicPackets N m)
    (hw : w∈publicPackets N m) (hv : v∈publicPackets N m)
    (hwu : w.residue=u.residue) (hvu : v.residue=u.residue) :
    2*|residueArea m u w v|≤6*(m : ℤ)+|centerDifference N| := by
  obtain ⟨us,huc⟩ := publicPacket_center_choice hu
  obtain ⟨ws,hwc⟩ := publicPacket_center_choice hw
  obtain ⟨vs,hvc⟩ := publicPacket_center_choice hv
  have hb := publicPacket_mixed_area_bound hm hu hw hv us ws vs huc hwc hvc
  rw [publicPacket_residueArea_exact hm hcop hu hw hv hwu hvu,abs_mul,
    abs_of_pos (by positivity : (0 : ℤ)<(m : ℤ)^3)] at hb
  apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℤ)<(m : ℤ)^3)).mp
  nlinarith only [hb]

/-- A nonzero signed integer smaller than both primes is a unit, including squares. -/
theorem bounded_int_isUnit {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {k : ℤ}
    (hk : k≠0) (hkp : |k|<(p : ℤ)) (hkq : |k|<(q : ℤ)) :
    IsUnit (k : ZMod (p*q)) := by
  have hpos := Int.natAbs_pos.mpr hk
  have hnp : k.natAbs<p := by rw [Int.abs_eq_natAbs] at hkp; exact_mod_cast hkp
  have hnq : k.natAbs<q := by rw [Int.abs_eq_natAbs] at hkq; exact_mod_cast hkq
  have hpc := (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hpos hnp)).symm
  have hqc := (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hpos hnq)).symm
  have hu := (ZMod.isUnit_iff_coprime k.natAbs (p*q)).mpr (hpc.mul_right hqc)
  have habsu : IsUnit ((|k| : ℤ) : ZMod (p*q)) := by
    simpa only [Int.abs_eq_natAbs,Int.cast_natCast] using hu
  by_cases hnonneg : 0≤k
  · simpa only [abs_of_nonneg hnonneg] using habsu
  · rw [abs_of_neg (lt_of_not_ge hnonneg),Int.cast_neg] at habsu
    simpa only [neg_neg] using habsu.neg

/-- Every same-residue triple is zero or unit in the balanced hard branch.
All centers are supplied by actual public membership. -/
theorem balanced_publicPacket_same_residue_zero_or_unit {p q m : ℕ} (hm : 0<m)
    (hp : p.Prime) (hq : q.Prime) (hpq : p≤q) (hqp : q≤2*p)
    (hcop : m.Coprime (p*q)) (hpm : 6*m+2<p) {u w v : FamilyPacket}
    (hu : u∈publicPackets (p*q) m) (hw : w∈publicPackets (p*q) m)
    (hv : v∈publicPackets (p*q) m) (hwu : w.residue=u.residue)
    (hvu : v.residue=u.residue) :
    rowArea m u w v=0 ∨ IsUnit (rowArea m u w v : ZMod (p*q)) := by
  have he := publicPacket_residueArea_exact hm hcop hu hw hv hwu hvu
  have hb := publicPacket_same_residue_normalized_bound hm hcop hu hw hv hwu hvu
  have hc := balanced_centerDifference_abs_le hqp
  have hpmz : 6*(m : ℤ)+2<p := by exact_mod_cast hpm
  have hpqz : (p : ℤ)≤q := by exact_mod_cast hpq
  have hkp : |residueArea m u w v|<(p : ℤ) := by nlinarith only [hb,hc,hpmz]
  by_cases hk : residueArea m u w v=0
  · exact Or.inl (by rw [he,hk,mul_zero])
  · apply Or.inr
    have hkunit := bounded_int_isUnit hp hq hk hkp (hkp.trans_le hpqz)
    have hmunit := (ZMod.isUnit_iff_coprime m (p*q)).mpr hcop
    rw [he]
    push_cast
    exact (hmunit.pow 3).mul hkunit

theorem balanced_publicPacket_same_residue_no_proper_gcd {p q m : ℕ} (hm : 0<m)
    (hp : p.Prime) (hq : q.Prime) (hpq : p≤q) (hqp : q≤2*p)
    (hcop : m.Coprime (p*q)) (hpm : 6*m+2<p) {u w v : FamilyPacket}
    (hu : u∈publicPackets (p*q) m) (hw : w∈publicPackets (p*q) m)
    (hv : v∈publicPackets (p*q) m) (hwu : w.residue=u.residue)
    (hvu : v.residue=u.residue) :
    ¬SemiprimeGroupSelection.ProperDivisor (p*q)
      ((p*q).gcd (rowArea m u w v : ZMod (p*q)).val) := by
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  rcases balanced_publicPacket_same_residue_zero_or_unit hm hp hq hpq hqp hcop hpm
      hu hw hv hwu hvu with hz|hunit
  · simp only [hz,Int.cast_zero,ZMod.val_zero,Nat.gcd_zero_right,
      SemiprimeGroupSelection.ProperDivisor,lt_self_iff_false,and_false,false_and,not_false_eq_true]
  · rw [(SemiprimeBulkNorm.gcd_one_iff_unit _).mpr hunit]
    simp only [SemiprimeGroupSelection.ProperDivisor,lt_self_iff_false,false_and,not_false_eq_true]

end RiemannGaussian.SemiprimeSameResidueAreas
