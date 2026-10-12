/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorFareyFourierAudit
import Mathlib.Data.Nat.Totient

/-!
# Native ordered rational gaps and the denominator triangle

An actual gap uses reduced ordinary-integer fractions and excludes EVERY
intermediate fraction with denominator at most the literal cutoff. Its
denominator chart retains the strict q+r>N boundary. All numerators,
unit endpoints and discontinuities are literal; no equidistribution or
continuous gap distribution is assumed.
-/

namespace RiemannGaussian.ArithmeticOperatorOrderedGapGeometry
noncomputable section
open scoped Classical BigOperators

/-- Literal adjacent reduced fractions a/q<c/r in [0,1]. The exclusion
includes unreduced intermediate fractions too, which only strengthens
the harmless choice of representatives for the SAME rational set. -/
def actualGap (N a q c r : ℕ) : Prop :=
  0<q ∧ q≤N ∧ 0<r ∧ r≤N ∧ a<q ∧ c≤r ∧
    a.Coprime q ∧ c.Coprime r ∧ a*r<c*q ∧
    ∀ e f : ℕ,0<f → f≤N → ¬(a*f<e*q ∧ e*r<c*f)

/-- The exact strict denominator triangle, including N=1 and (1,1). -/
def triangle (N q r : ℕ) : Prop :=
  0<q ∧ q≤N ∧ 0<r ∧ r≤N ∧ N<q+r

private theorem common_divisor_det {a q c r d : ℕ}
    (hdet : c*q=a*r+1) (hl : d∣c*q) (hr : d∣a*r) : d∣1 := by
  have hh : d∣1+a*r := by simpa only [hdet,Nat.add_comm] using hl
  exact (Nat.dvd_add_iff_left hr).mpr hh

/-- Determinant one forces ALL three primitive conditions, not just
the denominators' coprimality. No prime support is postulated. -/
theorem coprime_of_det {a q c r : ℕ} (hdet : c*q=a*r+1) :
    a.Coprime q ∧ c.Coprime r ∧ q.Coprime r := by
  have hl : a.Coprime q := Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp
    (common_divisor_det hdet
      (dvd_mul_of_dvd_right (Nat.gcd_dvd_right a q) c)
      (dvd_mul_of_dvd_left (Nat.gcd_dvd_left a q) r)))
  have hr : c.Coprime r := Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp
    (common_divisor_det hdet
      (dvd_mul_of_dvd_left (Nat.gcd_dvd_left c r) q)
      (dvd_mul_of_dvd_right (Nat.gcd_dvd_right c r) a)))
  have hd : q.Coprime r := Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp
    (common_divisor_det hdet
      (dvd_mul_of_dvd_right (Nat.gcd_dvd_left q r) c)
      (dvd_mul_of_dvd_right (Nat.gcd_dvd_right q r) a)))
  exact ⟨hl,hr,hd⟩

/-- Any fraction strictly between a determinant-one pair has denominator
at least q+r. Both strict inequalities and EVERY integer endpoint stay. -/
theorem between_denominator {a q c r e f : ℕ}
    (hdet : c*q=a*r+1) (hl : a*f<e*q) (hr : e*r<c*f) : q+r≤f := by
  have h1 := Nat.mul_le_mul_left r (Nat.succ_le_of_lt hl)
  have h2 := Nat.mul_le_mul_left q (Nat.succ_le_of_lt hr)
  have h3 := congrArg (fun z : ℕ => f*z) hdet
  nlinarith

private theorem negative_residue {q : ℕ} (hq : 0<q) (v : ℕ)
    (hv : v.Coprime q) : ∃ b : ℕ,b<q ∧ q∣v*b+1 := by
  let : NeZero q := ⟨hq.ne'⟩
  let u := ZMod.unitOfCoprime v hv
  let b := (-(↑(u⁻¹) : ZMod q)).val
  refine ⟨b,ZMod.val_lt _,?_⟩
  apply (ZMod.natCast_eq_zero_iff (v*b+1) q).mp
  have hb : (b : ZMod q)=-(↑(u⁻¹) : ZMod q) := ZMod.natCast_zmod_val _
  have hu : (v : ZMod q)=(u : ZMod q) := (ZMod.coe_unitOfCoprime v hv).symm
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,hb,hu,mul_neg,
    Units.mul_inv,neg_add_cancel]

/-- Every primitive denominator pair has its genuine reduced unimodular
numerators, including the endpoint q=1. -/
theorem exists_lift {q r : ℕ} (hq : 0<q) (hr : 0<r) (hc : q.Coprime r) :
    ∃ a c : ℕ,a<q ∧ c≤r ∧ c*q=a*r+1 := by
  obtain ⟨a,ha,hd⟩ := negative_residue hq r hc.symm
  have hd' : q∣a*r+1 := by simpa only [Nat.mul_comm] using hd
  let c := (a*r+1)/q
  have he : c*q=a*r+1 := by exact Nat.div_mul_cancel hd'
  refine ⟨a,c,ha,?_,he⟩
  have hh := Nat.mul_le_mul_right r (Nat.succ_le_of_lt ha)
  apply Nat.le_of_mul_le_mul_right (c := q) ?_ hq
  nlinarith

/-- Exact chart direction: EVERY primitive triangle pair supplies an
actual adjacent rational gap; it is not only a candidate denominator. -/
theorem triangle_has_actual_gap {N q r : ℕ} (ht : triangle N q r)
    (hc : q.Coprime r) : ∃ a c : ℕ,actualGap N a q c r := by
  obtain ⟨hq,hqN,hr,hrN,hqr⟩ := ht
  obtain ⟨a,c,ha,hcr,hdet⟩ := exists_lift hq hr hc
  obtain ⟨hap,hcp,_⟩ := coprime_of_det hdet
  refine ⟨a,c,hq,hqN,hr,hrN,ha,hcr,hap,hcp,by omega,?_⟩
  intro e f _ hf hbetween
  have he := between_denominator hdet hbetween.1 hbetween.2
  omega

private theorem next_candidate {N a q : ℕ} (hq : 0<q) (hqN : q≤N)
    (ha : a<q) (hc : a.Coprime q) :
    ∃ b c : ℕ,0<b ∧ b≤N ∧ N<q+b ∧ c≤b ∧ c*q=a*b+1 := by
  obtain ⟨v,hv,hd⟩ := negative_residue hq a hc
  let b := v+q*((N-v)/q)
  have hvN : v≤N := (Nat.le_of_lt hv).trans hqN
  have he : b+(N-v)%q=N := by
    dsimp [b]
    have hh := Nat.mod_add_div (N-v) q
    omega
  have hbN : b≤N := by omega
  have hNb : N<q+b := by have hh := Nat.mod_lt (N-v) hq; omega
  have hb : 0<b := by omega
  have hdb : q∣a*b+1 := by
    dsimp [b]
    have hterm : q∣a*(q*((N-v)/q)) := by
      exact dvd_mul_of_dvd_right (dvd_mul_right q ((N-v)/q)) a
    have hjoin := Nat.dvd_add hd hterm
    convert hjoin using 1
    ring
  let c := (a*b+1)/q
  have hdet : c*q=a*b+1 := Nat.div_mul_cancel hdb
  refine ⟨b,c,hb,hbN,hNb,?_,hdet⟩
  apply Nat.le_of_mul_le_mul_right (c := q) ?_ hq
  have hh := Nat.mul_le_mul_right b (Nat.succ_le_of_lt ha)
  nlinarith

/-- The converse is proved from the actual no-intermediate-fraction
condition, WITHOUT assuming determinant one as part of adjacency. -/
theorem actual_gap_triangle {N a q c r : ℕ} (hg : actualGap N a q c r) :
    triangle N q r ∧ c*q=a*r+1 := by
  obtain ⟨hq,hqN,hr,hrN,ha,hcr,hap,hcp,hl,hno⟩ := hg
  obtain ⟨b,e,hb,hbN,hNb,heb,hdet⟩ := next_candidate hq hqN ha hap
  have heq : e*r=c*b := by
    apply Nat.le_antisymm
    · by_contra he
      have he' : c*b<e*r := Nat.lt_of_not_ge he
      have hbden := between_denominator hdet hl he'
      omega
    · by_contra he
      have he' : e*r<c*b := Nat.lt_of_not_ge he
      exact hno e b hb hbN ⟨by omega,he'⟩
  have hep : e.Coprime b := (coprime_of_det hdet).2.1
  have hbr : b∣r := hep.symm.dvd_of_dvd_mul_left (by
    rw [heq]
    exact dvd_mul_left b c)
  have hrb : r∣b := hcp.symm.dvd_of_dvd_mul_left (by
    rw [←heq]
    exact dvd_mul_left r e)
  have hbe : b=r := Nat.dvd_antisymm hbr hrb
  have hec : e=c := by rw [hbe] at heq; nlinarith
  subst b
  subst e
  exact ⟨⟨hq,hqN,hr,hrN,hNb⟩,hdet⟩

/-- Full native denominator dictionary, with the ACTUAL order exclusion
proved in both directions. No Farey-list enumeration is taken as an axiom. -/
theorem exists_actual_gap_iff (N q r : ℕ) :
    (∃ a c : ℕ,actualGap N a q c r) ↔ triangle N q r ∧ q.Coprime r := by
  constructor
  · rintro ⟨a,c,hg⟩
    obtain ⟨ht,hd⟩ := actual_gap_triangle hg
    exact ⟨ht,(coprime_of_det hd).2.2⟩
  · rintro ⟨ht,hc⟩
    exact triangle_has_actual_gap ht hc

/-- The chart has NO extra numerator multiplicity. Actual order and
reduction determine the unique numerator pair, including both endpoints. -/
theorem actual_gap_numerators_unique {N a q c r a' c' : ℕ}
    (h : actualGap N a q c r) (h' : actualGap N a' q c' r) : a=a' ∧ c=c' := by
  obtain ⟨ht,hd⟩ := actual_gap_triangle h
  obtain ⟨_,hd'⟩ := actual_gap_triangle h'
  have hq : 0<q := ht.1
  let : NeZero q := ⟨hq.ne'⟩
  have hcp : r.Coprime q := (coprime_of_det hd).2.2.symm
  have hu : IsUnit (r : ZMod q) := by
    simpa only [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime r hcp).isUnit
  have he := congrArg (fun x : ℕ => (x : ZMod q)) hd
  have he' := congrArg (fun x : ℕ => (x : ZMod q)) hd'
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,ZMod.natCast_self,mul_zero] at he he'
  have hm : (a : ZMod q)*(r : ZMod q)=(a' : ZMod q)*(r : ZMod q) := by
    linear_combination he'-he
  have hav := congrArg ZMod.val (hu.mul_right_cancel hm)
  have ha : a<q := h.2.2.2.2.1
  have ha' : a'<q := h'.2.2.2.2.1
  rw [ZMod.val_natCast_of_lt ha,ZMod.val_natCast_of_lt ha'] at hav
  refine ⟨hav,?_⟩
  rw [hav] at hd
  nlinarith

/-- Exact bijective denominator chart, now stated with actual unique
adjacent numerators and no external Farey-order identification premise. -/
theorem existsUnique_actual_gap_iff (N q r : ℕ) :
    (∃! v : ℕ×ℕ,actualGap N v.1 q v.2 r) ↔ triangle N q r ∧ q.Coprime r := by
  constructor
  · rintro ⟨v,hv,_⟩
    exact (exists_actual_gap_iff N q r).mp ⟨v.1,v.2,hv⟩
  · intro hh
    obtain ⟨a,c,hac⟩ := (exists_actual_gap_iff N q r).mpr hh
    refine ⟨(a,c),hac,?_⟩
    intro v hv
    obtain ⟨ha,hc⟩ := actual_gap_numerators_unique hv hac
    exact Prod.ext ha hc

/-- Actual Archimedean gap, from the exact integer determinant. -/
theorem actual_gap_value {N a q c r : ℕ} (hg : actualGap N a q c r) :
    (c : ℝ)/r-(a : ℝ)/q=1/((q : ℝ)*r) := by
  obtain ⟨ht,hd⟩ := actual_gap_triangle hg
  have hq : (q : ℝ)≠0 := by exact_mod_cast ht.1.ne'
  have hr : (r : ℝ)≠0 := by exact_mod_cast ht.2.2.1.ne'
  have hdet : (c : ℝ)*q=(a : ℝ)*r+1 := by exact_mod_cast hd
  field_simp
  linear_combination hdet

end
end RiemannGaussian.ArithmeticOperatorOrderedGapGeometry
