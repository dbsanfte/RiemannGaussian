/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSymmetricRowAxes

/-!
# Actual public residue-partner offset cancellation

For two actual packets with swapped oriented coefficients and partner
residues, the two quotient relations force their offset difference to be
divisible by m squared. Opposite public centers restrict that difference
to zero or one signed m-squared step. After the public prefix, the paired
affine-root difference is therefore zero or a unit, never a proper-factor
signal. This does not assume every packet has a partner in the stream.
-/

namespace RiemannGaussian.SemiprimeRowPartnerOffsets

open SemiprimeQuotientRows SemiprimeQuotientCentering SemiprimeEuclidRowFamily
open SemiprimeCompanionRows SemiprimeCompanionCenterSpectrum SemiprimeCenteredOffsetExtractor
open SemiprimeRowAreaSpectrum SemiprimeQuadraticPointJets SemiprimeAffineRowRoots
open SemiprimeLiteralQuadraticRoots
open SemiprimeSymmetricRowAxes

/-- The oriented difference before modular reduction or centering bounds. -/
def partnerDelta (m : ℕ) (u v : FamilyPacket) (s : ℤ) : ℤ :=
  packetOffset m v-s*packetOffset m u

/-- The two true factor residues satisfy the public partner relation automatically. -/
theorem factor_residue_product_dvd (p q m : ℕ) :
    (m : ℤ)∣(p : ℤ)*q-(p%m : ℕ)*(q%m : ℕ) := by
  have hp : (p%m : ℕ)+(m : ℤ)*(p/m : ℕ)=(p : ℤ) := by
    exact_mod_cast Nat.mod_add_div p m
  have hq : (q%m : ℕ)+(m : ℤ)*(q/m : ℕ)=(q : ℤ) := by
    exact_mod_cast Nat.mod_add_div q m
  refine ⟨(p/m : ℕ)*(q : ℤ)+(p%m : ℕ)*(q/m : ℕ),?_⟩
  linear_combination -(q : ℤ)*hp-(p%m : ℕ)*hq

theorem publicPacket_coefficient_residue_dvd {N m : ℕ} (hm : 0<m)
    {u : FamilyPacket} (hu : u∈publicPackets N m) :
    (m : ℤ)∣u.original.a*u.residue^2-(N : ℤ)*u.original.t := by
  have h := publicPacket_original_relation hm hu
  unfold quotientRelation at h
  refine ⟨(u.residue : ℤ)*u.original.b-(m : ℤ)*u.original.c,?_⟩
  linear_combination h

/-- The public partner congruence forces the second m-divisible factor. -/
theorem publicPacket_partner_coefficient_dvd {N m : ℕ} (hm : 0<m)
    {u : FamilyPacket} (hu : u∈publicPackets N m) {k : ℕ}
    (hprod : (m : ℤ)∣(N : ℤ)-(u.residue : ℤ)*k) :
    (m : ℤ)∣u.original.a*u.residue-u.original.t*k := by
  obtain ⟨c,hc⟩ := publicPacket_coefficient_residue_dvd hm hu
  obtain ⟨d,hd⟩ := hprod
  have he : (u.residue : ℤ)*(u.original.a*u.residue-u.original.t*k)=
      (m : ℤ)*(c+u.original.t*d) := by
    linear_combination hc+u.original.t*hd
  obtain ⟨x,y,hxy⟩ := (publicPacket_residue_coprime hu).isCoprime
  refine ⟨x*(c+u.original.t*d)+y*(u.original.a*u.residue-u.original.t*k),?_⟩
  linear_combination x*he-(u.original.a*u.residue-u.original.t*k)*hxy

/-- Two m-divisible factors explain the complete m-squared cancellation. -/
theorem publicPacket_partner_delta_dvd {N m : ℕ} (hm : 0<m)
    {u v : FamilyPacket} (hu : u∈publicPackets N m) (hv : v∈publicPackets N m)
    (s : ℤ) (ha : v.original.a=s*u.original.t) (ht : v.original.t=s*u.original.a)
    (hprod : (m : ℤ)∣(N : ℤ)-(u.residue : ℤ)*v.residue) :
    (m : ℤ)^2∣partnerDelta m u v s := by
  obtain ⟨e,he⟩ := publicPacket_partner_coefficient_dvd hm hu hprod
  obtain ⟨d,hd⟩ := hprod
  have hur := publicPacket_tangent_integer hm hu
  have hvr := publicPacket_tangent_integer hm hv
  rw [ha,ht] at hvr
  have hident : (u.residue : ℤ)*v.residue*partnerDelta m u v s =
      (m : ℤ)^2*((u.residue : ℤ)*(centeredPacketRow m v).c-
        s*(v.residue : ℤ)*(centeredPacketRow m u).c-s*d*e) := by
    unfold partnerDelta
    linear_combination (u.residue : ℤ)*hvr-s*(v.residue : ℤ)*hur-
      s*((u.original.a*u.residue-u.original.t*v.residue)*hd+
        (m : ℤ)*d*he)
  have hcop := ((publicPacket_residue_coprime hu).mul_left
    (publicPacket_residue_coprime hv)).pow_right 2
  obtain ⟨x,y,hxy⟩ := hcop.isCoprime
  simp only [Nat.cast_mul,Nat.cast_pow] at hxy
  refine ⟨x*((u.residue : ℤ)*(centeredPacketRow m v).c-
    s*(v.residue : ℤ)*(centeredPacketRow m u).c-s*d*e)+y*partnerDelta m u v s,?_⟩
  linear_combination x*hident-partnerDelta m u v s*hxy

theorem partner_delta_abs_le {N m : ℕ} (hm : 0<m) (u v : FamilyPacket) (s : ℤ)
    (hs : s=-1 ∨ s=1) (ha : v.original.a=s*u.original.t)
    (ht : v.original.t=s*u.original.a) (side : Bool)
    (huc : CenterChoice N m u side) (hvc : CenterChoice N m v (!side)) :
    |partnerDelta m u v s|≤(m : ℤ)^2 := by
  have hur := packet_center_equation u side huc
  have hvr := packet_center_equation v (!side) hvc
  have hA : centerA N (!side)=centerB N side := rfl
  have hB : centerB N (!side)=centerA N side := by simp only [centerB,Bool.not_not]
  rw [ha,ht,hA,hB] at hvr
  have hδ : 2*partnerDelta m u v s=
      s*packetCenterError N m u side-packetCenterError N m v (!side) := by
    unfold partnerDelta
    linear_combination s*hur-hvr
  have heu := packetCenterError_abs_le (N:=N) hm u side
  have hev := packetCenterError_abs_le (N:=N) hm v (!side)
  have hsabs : |s*packetCenterError N m u side|=|packetCenterError N m u side| := by
    rcases hs with rfl|rfl <;> simp
  have hb := abs_sub_le (s*packetCenterError N m u side) 0
    (packetCenterError N m v (!side))
  simp only [sub_zero,zero_sub,abs_neg,hsabs] at hb
  have hδabs := congrArg abs hδ
  norm_num only [abs_mul,Int.reduceAbs] at hδabs
  nlinarith

theorem bounded_multiple {d z : ℤ} (hd : 0<d) (hdiv : d∣z) (hb : |z|≤d) :
    z=0 ∨ z=d ∨ z=-d := by
  obtain ⟨k,hk⟩ := hdiv
  have hz := abs_le.mp hb
  have hlo : -1≤k := by
    by_contra hc
    have hm := mul_le_mul_of_nonneg_left (show k≤-2 by omega) hd.le
    nlinarith
  have hhi : k≤1 := by
    by_contra hc
    have hm := mul_le_mul_of_nonneg_left (show 2≤k by omega) hd.le
    nlinarith
  have hcases : k=0 ∨ k=1 ∨ k=-1 := by omega
  rcases hcases with rfl|rfl|rfl <;> simp_all

/-- On the actual source, the public prefix makes every nonzero partner correction a unit. -/
theorem publicPacket_partner_delta_zero_or_unit {N m : ℕ} (hm : 0<m) (hcover : m^2<N)
    (hn : SemiprimeStrassenPrefix.factorPrefix N m=none)
    {u v : FamilyPacket} (hu : u∈publicPackets N m) (hv : v∈publicPackets N m)
    (s : ℤ) (hs : s=-1 ∨ s=1) (ha : v.original.a=s*u.original.t)
    (ht : v.original.t=s*u.original.a)
    (hprod : (m : ℤ)∣(N : ℤ)-(u.residue : ℤ)*v.residue) (side : Bool)
    (huc : CenterChoice N m u side) (hvc : CenterChoice N m v (!side)) :
    (partnerDelta m u v s : ZMod N)=0 ∨ IsUnit (partnerDelta m u v s : ZMod N) := by
  have hd := publicPacket_partner_delta_dvd hm hu hv s ha ht hprod
  have hb := partner_delta_abs_le hm u v s hs ha ht side huc hvc
  have hp : 0<(m : ℤ)^2 := by positivity
  have hmUnit := (prefix_none_modulus_unit hm hcover hn).pow 2
  rcases bounded_multiple hp hd hb with h0|hplus|hminus
  · exact Or.inl (by rw [h0,Int.cast_zero])
  · exact Or.inr (by simpa only [hplus,Int.cast_pow,Int.cast_natCast] using hmUnit)
  · exact Or.inr (by simpa only [hminus,Int.cast_neg,Int.cast_pow,Int.cast_natCast]
      using hmUnit.neg)

/-- The natural paired affine channels give whole-N matches or unit differences.
This explains the duplicates; it does not force a useful factor collision. -/
theorem publicPacket_partner_root_zero_or_unit {N m : ℕ} (hm : 0<m) (hcover : m^2<N)
    (hn : SemiprimeStrassenPrefix.factorPrefix N m=none)
    {u v : FamilyPacket} (hu : u∈publicPackets N m) (hv : v∈publicPackets N m)
    (s : ℤ) (hs : s=-1 ∨ s=1) (ha : v.original.a=s*u.original.t)
    (ht : v.original.t=s*u.original.a)
    (hprod : (m : ℤ)∣(N : ℤ)-(u.residue : ℤ)*v.residue) (side : Bool)
    (huc : CenterChoice N m u side) (hvc : CenterChoice N m v (!side)) :
    packetRoot N m v false-packetRoot N m u true=0 ∨
      IsUnit (packetRoot N m v false-packetRoot N m u true) := by
  have hva := prefix_none_publicPacket_leading_unit hm hcover hn hv
  have htUnit : IsUnit (u.original.t : ZMod N) := by
    have h := hva
    rw [ha,Int.cast_mul] at h
    exact isUnit_of_mul_isUnit_right h
  have hur := packetRoot_coefficient (m:=m) u true htUnit
  have hvr := packetRoot_coefficient (m:=m) v false hva
  simp only [packetScale,if_true] at hur
  simp only [packetScale,Bool.false_eq_true,if_false] at hvr
  have ha' : (v.original.a : ZMod N)=(s : ZMod N)*(u.original.t : ZMod N) := by
    rw [ha,Int.cast_mul]
  have he : (v.original.a : ZMod N)*
      (packetRoot N m v false-packetRoot N m u true)=-(partnerDelta m u v s : ZMod N) := by
    unfold partnerDelta
    push_cast
    rw [ha'] at hvr ⊢
    linear_combination hvr-(s : ZMod N)*hur
  have hd := publicPacket_partner_delta_zero_or_unit hm hcover hn hu hv s hs ha ht
    hprod side huc hvc
  rcases hd with hz|hunit
  · rw [hz,neg_zero] at he
    have h := congrArg (fun x => (v.original.a : ZMod N)⁻¹*x) he
    rw [←mul_assoc,ZMod.inv_mul_of_unit _ hva,one_mul,mul_zero] at h
    exact Or.inl h
  · have hprodUnit : IsUnit ((v.original.a : ZMod N)*
        (packetRoot N m v false-packetRoot N m u true)) := he ▸ hunit.neg
    exact Or.inr (isUnit_of_mul_isUnit_right hprodUnit)

/-- Even the correct hidden-factor residue pair supplies no proper signal from
this swapped-center symmetry. The factors select proof witnesses only. -/
theorem publicPacket_factor_residue_root_zero_or_unit {p q m : ℕ}
    (hm : 0<m) (hcover : m^2<p*q)
    (hn : SemiprimeStrassenPrefix.factorPrefix (p*q) m=none)
    {u v : FamilyPacket} (hu : u∈publicPackets (p*q) m) (hv : v∈publicPackets (p*q) m)
    (hj : u.residue=p%m) (hk : v.residue=q%m)
    (s : ℤ) (hs : s=-1 ∨ s=1) (ha : v.original.a=s*u.original.t)
    (ht : v.original.t=s*u.original.a) (side : Bool)
    (huc : CenterChoice (p*q) m u side) (hvc : CenterChoice (p*q) m v (!side)) :
    packetRoot (p*q) m v false-packetRoot (p*q) m u true=0 ∨
      IsUnit (packetRoot (p*q) m v false-packetRoot (p*q) m u true) := by
  have hprod : (m : ℤ)∣(p*q : ℕ)-(u.residue : ℤ)*v.residue := by
    simpa only [hj,hk,Nat.cast_mul] using factor_residue_product_dvd p q m
  exact publicPacket_partner_root_zero_or_unit hm hcover hn hu hv s hs ha ht
    hprod side huc hvc

/-- Neither new signed axis gains a proper signal from its natural partner.
For the minus axis, the corresponding comparison is the reflected sum. -/
theorem publicPacket_partner_axis_zero_or_unit {N m : ℕ} (hm : 0<m) (hcover : m^2<N)
    (hn : SemiprimeStrassenPrefix.factorPrefix N m=none)
    {u v : FamilyPacket} (hu : u∈publicPackets N m) (hv : v∈publicPackets N m)
    (s : ℤ) (hs : s=-1 ∨ s=1) (ha : v.original.a=s*u.original.t)
    (ht : v.original.t=s*u.original.a)
    (hprod : (m : ℤ)∣(N : ℤ)-(u.residue : ℤ)*v.residue) (side : Bool)
    (huc : CenterChoice N m u side) (hvc : CenterChoice N m v (!side))
    (minus : Bool) (hdu : axisDenominator u minus≠0) :
    axisRoot N m v minus-(if minus then -axisRoot N m u minus else axisRoot N m u minus)=0 ∨
      IsUnit (axisRoot N m v minus-
        (if minus then -axisRoot N m u minus else axisRoot N m u minus)) := by
  have hc : axisDenominator v minus=(if minus then -s else s)*axisDenominator u minus := by
    cases minus <;> simp [axisDenominator,ha,ht] <;> ring
  have hsne : s≠0 := by rcases hs with rfl|rfl <;> norm_num
  have hphase : (if minus then -s else s)≠0 := by cases minus <;> simp [hsne]
  have huUnit := prefix_none_axis_unit hm hcover hn hu minus hdu
  have hvUnit := prefix_none_axis_unit hm hcover hn hv minus
    (show axisDenominator v minus≠0 by rw [hc]; exact mul_ne_zero hphase hdu)
  have hur := axisRoot_coefficient (m:=m) u minus huUnit
  have hvr := axisRoot_coefficient (m:=m) v minus hvUnit
  have he : (axisDenominator v minus : ZMod N)*
      (axisRoot N m v minus-(if minus then -axisRoot N m u minus else axisRoot N m u minus))=
      -(partnerDelta m u v s : ZMod N) := by
    unfold partnerDelta
    push_cast
    rw [hc,Int.cast_mul] at hvr ⊢
    cases minus <;> simp only [Bool.false_eq_true,if_false,if_true,Int.cast_neg] at hvr ⊢
    · linear_combination hvr-(s : ZMod N)*hur
    · linear_combination hvr-(s : ZMod N)*hur
  have hd := publicPacket_partner_delta_zero_or_unit hm hcover hn hu hv s hs ha ht
    hprod side huc hvc
  rcases hd with hz|hunit
  · rw [hz,neg_zero] at he
    have h := congrArg (fun x => (axisDenominator v minus : ZMod N)⁻¹*x) he
    rw [←mul_assoc,ZMod.inv_mul_of_unit _ hvUnit,one_mul,mul_zero] at h
    exact Or.inl h
  · have hprodUnit : IsUnit ((axisDenominator v minus : ZMod N)*
        (axisRoot N m v minus-
          (if minus then -axisRoot N m u minus else axisRoot N m u minus))) := he ▸ hunit.neg
    exact Or.inr (isUnit_of_mul_isUnit_right hprodUnit)

/-- Correct factor residues also fail to force a signal in the two new axes. -/
theorem publicPacket_factor_residue_axis_zero_or_unit {p q m : ℕ}
    (hm : 0<m) (hcover : m^2<p*q)
    (hn : SemiprimeStrassenPrefix.factorPrefix (p*q) m=none)
    {u v : FamilyPacket} (hu : u∈publicPackets (p*q) m) (hv : v∈publicPackets (p*q) m)
    (hj : u.residue=p%m) (hk : v.residue=q%m)
    (s : ℤ) (hs : s=-1 ∨ s=1) (ha : v.original.a=s*u.original.t)
    (ht : v.original.t=s*u.original.a) (side : Bool)
    (huc : CenterChoice (p*q) m u side) (hvc : CenterChoice (p*q) m v (!side))
    (minus : Bool) (hdu : axisDenominator u minus≠0) :
    axisRoot (p*q) m v minus-
        (if minus then -axisRoot (p*q) m u minus else axisRoot (p*q) m u minus)=0 ∨
      IsUnit (axisRoot (p*q) m v minus-
        (if minus then -axisRoot (p*q) m u minus else axisRoot (p*q) m u minus)) := by
  have hprod : (m : ℤ)∣(p*q : ℕ)-(u.residue : ℤ)*v.residue := by
    simpa only [hj,hk,Nat.cast_mul] using factor_residue_product_dvd p q m
  exact publicPacket_partner_axis_zero_or_unit hm hcover hn hu hv s hs ha ht
    hprod side huc hvc minus hdu

end RiemannGaussian.SemiprimeRowPartnerOffsets
