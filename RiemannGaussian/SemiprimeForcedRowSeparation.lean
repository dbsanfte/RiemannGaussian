/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitGcd

/-!
# Forced rows separate except for a public slope-one seed

The exact arithmetic witness has a short weight difference. The routed
rough order in the other field is coprime to the smaller field's full
cardinality, so a common hit forces that difference to vanish. At a prime
row modulus this requires seed slope one and zero wrap. A short seed trial
catches this exception. Remaining forced merged hits can therefore be
read as checked factors without quadratic recovery at common global tags.
Acquisition and the full factorizer's bit costs remain separate obligations.
-/

namespace RiemannGaussian.SemiprimeForcedRowSeparation

open SemiprimeQuotientRows SemiprimeDenseRowCoverage SemiprimeDenseRowCarries
open SemiprimeWideWrapCoverage SemiprimeHyperbolicWrapCoverage
open SemiprimeWrapIndexRecovery SemiprimeMergedIndexAcquisition
open SemiprimeGroupSelection SemiprimeLocalOrderRouting SemiprimeCentreFreeCover
open SemiprimeIntervalJet

/-- The exact factor index retains the complete Fermat multiplier of the
other-field residual, not only an equality modulo a projected period. -/
theorem exact_row_exponent {p q m j a b c t x i : ℤ}
    (hp : p=m*x+j) (hrel : quotientRelation (p*q) m j a b c t)
    (hindex : quadratic a b c x=p*i) (hp0 : p≠0) :
    giantExponent m j a b c-m^2*i=(p-1)*(t*q-a) := by
  have hs := scaled_quadratic_factor_sum hp hrel
  rw [hindex] at hs
  have hi : m^2*i=a*p+b*m-2*a*j+t*q := by
    apply mul_left_cancel₀ hp0
    nlinarith only [hs]
  rw [giantExponent_eq hrel,hi]
  ring

/-- Coprimality with the full smaller cardinality and a short weight
force a common exact row hit to have equal leading and cofactor weights. -/
theorem common_exact_hit_weight {G : Type*} [CommGroup G] (g : G)
    {p q m j a b c t x i : ℤ} {d : ℕ}
    (hp : p=m*x+j) (hrel : quotientRelation (p*q) m j a b c t)
    (hindex : quadratic a b c x=p*i) (hp0 : p≠0)
    (hd : orderOf g=d) (hcop : IsCoprime (d : ℤ) (p-1))
    (hq : (d : ℤ)∣q-1) (hshort : |t-a|<(d : ℤ))
    (hhit : g^giantExponent m j a b c=g^(m^2*i)) : a=t := by
  have hexp := exact_row_exponent hp hrel hindex hp0
  have hdiv := (orderOf_dvd_sub_iff_zpow_eq_zpow).mpr hhit
  rw [hd,hexp] at hdiv
  have hweight := hcop.dvd_of_dvd_mul_left hdiv
  have hqweight : (d : ℤ)∣t*(q-1) := dvd_mul_of_dvd_right hq t
  have hdiff : (d : ℤ)∣t-a := by
    have he : (t*q-a)-t*(q-1)=t-a := by ring
    simpa only [he] using hweight.sub hqweight
  have habs : (t-a).natAbs<(d : ℤ).natAbs := by
    simpa only [Int.natAbs_natCast] using
      (show (t-a).natAbs<d by exact_mod_cast
        (show ((t-a).natAbs : ℤ)<d by simpa only [Int.natCast_natAbs] using hshort))
  have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiff habs
  omega

/-- Every proved linear wrap has a weight difference below the routed
other period. This uses physical source bounds, without balanced factors. -/
theorem wrapped_weight_bound {m A t k : ℕ} (hm : 1<m)
    (hA : A<m) (ht : t<m) (hk : k≤2*m+1) :
    |(t : ℤ)-((t : ℤ)*A-(m : ℤ)*k)|≤4*(m : ℤ)^2 := by
  have hmz : (2 : ℤ)≤m := by exact_mod_cast hm
  have hAz : (A : ℤ)≤m := by exact_mod_cast hA.le
  have htz : (t : ℤ)≤m := by exact_mod_cast ht.le
  have hkz : (k : ℤ)≤2*(m : ℤ)+1 := by exact_mod_cast hk
  have hta := mul_le_mul htz hAz (by positivity : (0 : ℤ)≤A)
    (by positivity : (0 : ℤ)≤m)
  have hmk := mul_le_mul_of_nonneg_left hkz (by positivity : (0 : ℤ)≤m)
  apply abs_le.mpr
  constructor <;> nlinarith [show (0 : ℤ)≤(t : ℤ)*A by positivity,
    show (0 : ℤ)≤(m : ℤ)*k by positivity]

/-- At the selected prime modulus, equality of the two weights has only
the public slope-one, zero-wrap possibility. The actual denominator is
strictly between zero and the prime modulus. -/
theorem equal_weight_exception {m A t k : ℕ} (hm : m.Prime)
    (hA : A<m) (ht : 0<t) (htm : t<m)
    (he : (t : ℤ)*A-(m : ℤ)*k=t) : A=1 ∧ k=0 := by
  have hdiv : (m : ℤ)∣(t : ℤ)*((A : ℤ)-1) := by
    refine ⟨(k : ℤ),?_⟩
    nlinarith only [he]
  have hcop : t.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ht htm)).symm
  have hd := hcop.isCoprime.symm.dvd_of_dvd_mul_left hdiv
  have hsmall : ((A : ℤ)-1).natAbs<(m : ℤ).natAbs := by
    have hm2 := hm.two_le
    simp only [Int.natAbs_natCast]
    have hh : |(A : ℤ)-1|<(m : ℤ) := abs_lt.mpr (by constructor <;> omega)
    exact_mod_cast (by simpa only [Int.natCast_natAbs] using hh :
      (((A : ℤ)-1).natAbs : ℤ)<m)
  have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hsmall
  have hA1 : A=1 := by omega
  have hmz : (0 : ℤ)<m := by exact_mod_cast hm.pos
  constructor
  · exact hA1
  · rw [hA1,Nat.cast_one,mul_one] at he
    have hz : (m : ℤ)*k=0 := by omega
    have hkz : (k : ℤ)=0 := (mul_eq_zero.mp hz).resolve_left hmz.ne'
    exact_mod_cast hkz

/-- The retained rough local orders imply the other order is coprime to
the FULL smaller field cardinality. No full-order oracle is assumed. -/
theorem long_other_coprime {p q m : ℕ} (hp : p.Prime)
    (hpq : p≤q) (hsize : p*q≤m^6) (g : (ZMod (p*q))ˣ)
    (hlong : LongData g m) :
    (orderOf (rightUnit (projectedUnit g m))).Coprime (p-1) := by
  let : Fact p.Prime := ⟨hp⟩
  apply rough_order_coprime_cardinality hp.one_lt
    (SemiprimeGroupCoverage.smaller_factor_le_cubic_width hpq hsize)
    (ZMod.orderOf_units_dvd_card_sub_one (leftUnit (projectedUnit g m)))
    (by have hh := hlong.2.2.2.1.1; nlinarith only [hh])
    hlong.2.2.2.2.1 hlong.2.2.2.2.2.2

/-- On the actual long branch, a common hit of an exact forced row has
slope one and zero full wrap. This is a general arithmetic exclusion. -/
theorem forced_common_hit_exception {p q m t k : ℕ} {i : ℤ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≤q) (hm : m.Prime)
    (hN : m.Coprime (p*q)) (hsize : p*q≤m^6)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (ht : 0<t) (htm : t<m) (hk : k≤2*m+1)
    (hindex : quadratic (wrappedRow (p*q) m (p%m) t k).a
      (wrappedRow (p*q) m (p%m) t k).b
      (wrappedRow (p*q) m (p%m) t k).c (p/m : ℕ)=(p : ℤ)*i)
    (hhit : wrappedValue t k
        (progressionSeed (rightUnit (projectedUnit g m)) (p*q) m (p%m))=
      (rightUnit (projectedUnit g m))^((m : ℤ)^2*i)) :
    (progressionSeed (projectedUnit g m) (p*q) m (p%m)).slope=1 ∧ k=0 := by
  let : Fact q.Prime := ⟨hq⟩
  have hm0 := hm.pos
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hrel : quotientRelation ((p : ℤ)*q) m (p%m : ℕ)
      (wrappedRow (p*q) m (p%m) t k).a
      (wrappedRow (p*q) m (p%m) t k).b
      (wrappedRow (p*q) m (p%m) t k).c (t : ℤ) := by
    simpa only [Nat.cast_mul,wrappedRow] using
      wrappedRow_relation (N:=p*q) (t:=t) (k:=k) hm0 hj
  have hcoord : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+(p%m : ℕ) := by
    have hh := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  let d := orderOf (rightUnit (projectedUnit g m))
  have hc : IsCoprime (d : ℤ) ((p : ℤ)-1) := by
    have hh := (long_other_coprime hp hpq hsize g hlong).isCoprime
    simpa only [Nat.cast_sub hp.one_le,Nat.cast_one] using hh
  have hd : (d : ℤ)∣(q : ℤ)-1 := by
    have hh := ZMod.orderOf_units_dvd_card_sub_one (rightUnit (projectedUnit g m))
    have hcast : (d : ℤ)∣((q-1 : ℕ) : ℤ) := by exact_mod_cast hh
    simpa only [Nat.cast_sub hq.one_le,Nat.cast_one] using hcast
  have hA : representative (p*q) m (p%m) 1<m := Nat.mod_lt _ hm0
  have hshort : |(t : ℤ)-(wrappedRow (p*q) m (p%m) t k).a|<(d : ℤ) := by
    have hw := wrapped_weight_bound (by have hh := hm.two_le; omega) hA htm hk
    have hl := hlong.2.2.2.1.2
    have hlz : 4*(m : ℤ)^2<(d : ℤ) := by
      exact_mod_cast (by nlinarith only [hl] : 4*m^2<d)
    exact lt_of_le_of_lt hw hlz
  rw [wrappedValue_eq] at hhit
  have he := common_exact_hit_weight (rightUnit (projectedUnit g m)) hcoord hrel
    hindex (by exact_mod_cast hp.ne_zero) rfl hc hd hshort hhit
  exact equal_weight_exception hm hA ht htm he

/-- Preserve both routed periods when the short seed reader uses g^(m^2). -/
theorem long_seed_periods {p q m : ℕ} (hm : 1<m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    2*m≤orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      ((projectedUnit g m)^(m^2) : ZMod (p*q))) ∧
    2*m≤orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      ((projectedUnit g m)^(m^2) : ZMod (p*q))) := by
  have heP : orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      ((projectedUnit g m)^(m^2) : ZMod (p*q)))=
        orderOf (leftUnit (projectedUnit g m)) := by
    change orderOf (((Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom)
      ((projectedUnit g m)^(m^2)) : (ZMod p)ˣ) : ZMod p)=_
    rw [orderOf_units,map_pow]
    exact ((rough_coprime_small (by omega : 0<m) le_rfl
      hlong.2.2.2.2.2.1).pow_right 2).orderOf_pow
  have heQ : orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      ((projectedUnit g m)^(m^2) : ZMod (p*q)))=
        orderOf (rightUnit (projectedUnit g m)) := by
    change orderOf (((Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom)
      ((projectedUnit g m)^(m^2)) : (ZMod q)ˣ) : ZMod q)=_
    rw [orderOf_units,map_pow]
    exact ((rough_coprime_small (by omega : 0<m) le_rfl
      hlong.2.2.2.2.2.2).pow_right 2).orderOf_pow
  rw [heP,heQ]
  have hP := hlong.2.2.2.1.1
  have hQ := hlong.2.2.2.1.2
  constructor <;> nlinarith only [hP,hQ,hm]

/-- Short denominator-one trial retains the original quadratic at wrap
zero. This is a public specification using only its cached seed. -/
noncomputable def recoverSeedTrial {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (s : ProgressionSeed ((ZMod N)ˣ)) : Option ℕ :=
  match recoverTaggedInterval (g^(m^2)) s.step (2*m) m with
  | none => none
  | some (Sum.inl d) => some d
  | some (Sum.inr r) => recoverCandidates N (wrappedRecovery N m 1 0 s (r : ℤ))

/-- Every short seed result is checked, including false seed targets. -/
theorem recoverSeedTrial_sound {N m d : ℕ} (g : (ZMod N)ˣ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (h : recoverSeedTrial g m s=some d) :
    ProperDivisor N d := by
  unfold recoverSeedTrial at h
  split at h
  · cases h
  · rename_i e he
    cases h
    exact recoverTaggedInterval_factor_sound _ _ he
  · exact recoverCandidates_sound h

/-- A short original seed index gives a checked factor whether the
interval reader separates the fields or preserves a common global index. -/
theorem recoverSeedTrial_succeeds {p q m r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : 1<m)
    (g : (ZMod (p*q))ˣ) (s : ProgressionSeed ((ZMod (p*q))ˣ))
    (hr : r<2*m)
    (hLP : 2*m≤orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      (g^(m^2) : ZMod (p*q))))
    (hLQ : 2*m≤orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      (g^(m^2) : ZMod (p*q))))
    (hhit : ZMod.castHom (dvd_mul_right p q) (ZMod p) (s.step : ZMod (p*q))=
      (ZMod.castHom (dvd_mul_right p q) (ZMod p) (g^(m^2) : ZMod (p*q)))^r)
    (hroot : (p : ℤ)∈wrappedRecovery (p*q) m 1 0 s (r : ℤ)) :
    ∃ d, recoverSeedTrial g m s=some d := by
  have hcover : 2*m≤m^2 := by nlinarith only [hm]
  rcases recoverTaggedInterval_preserves_root hp hq hpq (g^(m^2)) s.step
      hr hcover hLP hLQ hhit with hd|hright
  · obtain ⟨d,hd⟩ := hd
    exact ⟨d,by simp only [recoverSeedTrial,hd]⟩
  · have hpDiv : ProperDivisor (p*q) p :=
      ⟨hp.one_lt,by nlinarith only [hp.pos,hq.one_lt],dvd_mul_right p q⟩
    obtain ⟨d,hd⟩ := recoverCandidates_succeeds hpDiv hroot
    exact ⟨d,by simp only [recoverSeedTrial,hright,hd]⟩

/-- Only slope-one cached descriptors can host the forced common-hit
exception. No private residue or successful denominator is supplied. -/
def exceptionSeeds {G : Type*} [CommGroup G] (g : G) (N m : ℕ) :
    List (ProgressionSeed G) :=
  (progressionSeeds g N m).filter (fun s => s.slope==1)

/-- Every relevant public seed is retained by the literal filter. -/
theorem exceptionSeed_mem {G : Type*} [CommGroup G] {g : G} {N m : ℕ}
    {s : ProgressionSeed G} (hmem : s∈progressionSeeds g N m) (hA : s.slope=1) :
    s∈exceptionSeeds g N m := by
  simp only [exceptionSeeds,List.mem_filter,beq_iff_eq]
  exact ⟨hmem,hA⟩

/-- The short exception stream has at most the original linear seed count. -/
theorem exceptionSeeds_length_le {G : Type*} [CommGroup G] (g : G) (N m : ℕ) :
    (exceptionSeeds g N m).length≤m-1 := by
  have hh := List.length_filter_le (fun s : ProgressionSeed G => s.slope==1)
    (progressionSeeds g N m)
  simpa only [exceptionSeeds,progressionSeeds,List.length_map,List.length_range] using hh

/-- Scan the public exception descriptors, stopping at a checked factor. -/
noncomputable def scanSeedTrials {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    List (ProgressionSeed ((ZMod N)ˣ))→Option ℕ
  | [] => none
  | s::xs => match recoverSeedTrial g m s with
    | some d => some d
    | none => scanSeedTrials g m xs

/-- Every successful short exception scan returns a proper divisor. -/
theorem scanSeedTrials_sound {N m d : ℕ} (g : (ZMod N)ˣ)
    {xs : List (ProgressionSeed ((ZMod N)ˣ))}
    (h : scanSeedTrials g m xs=some d) : ProperDivisor N d := by
  induction xs with
  | nil => simp only [scanSeedTrials] at h; cases h
  | cons s xs ih =>
    unfold scanSeedTrials at h
    split at h
    · rename_i e he
      cases h
      exact recoverSeedTrial_sound g s he
    · exact ih h

/-- Success at any retained seed suffices for the entire public scan. -/
theorem scanSeedTrials_succeeds_of_member {N m d : ℕ} (g : (ZMod N)ˣ)
    (s : ProgressionSeed ((ZMod N)ˣ)) {xs : List (ProgressionSeed ((ZMod N)ˣ))}
    (hmem : s∈xs) (hd : recoverSeedTrial g m s=some d) :
    ∃ e, scanSeedTrials g m xs=some e := by
  induction xs with
  | nil => simp only [List.not_mem_nil] at hmem
  | cons s' xs ih =>
    rw [scanSeedTrials]
    cases he : recoverSeedTrial g m s' with
    | some e => exact ⟨e,rfl⟩
    | none =>
      rcases List.mem_cons.mp hmem with hh|hh
      · cases hh
        rw [hd] at he
        cases he
      · exact ih hh

/-- Zero wrap transports the short forced index to the original
denominator-one seed. Its nonnegative exact index is still below 2m. -/
theorem zero_wrap_short_seed_index {p q m t : ℕ} {i : ℤ}
    (hm : 1<m) (hp : 0<p) (hpq : p≤q) (hprefix : m^2≤p)
    (hN : m.Coprime (p*q)) (hsize : p*q≤m^6) (ht : 0<t)
    (hi : i.natAbs<2*m)
    (hindex : quadratic (wrappedRow (p*q) m (p%m) t 0).a
      (wrappedRow (p*q) m (p%m) t 0).b
      (wrappedRow (p*q) m (p%m) t 0).c (p/m : ℕ)=(p : ℤ)*i) :
    ∃ I : ℤ, 0≤I ∧ I.natAbs<2*m ∧
      quadratic (seedRow (p*q) m (p%m)).a (seedRow (p*q) m (p%m)).b
        (seedRow (p*q) m (p%m)).c (p/m : ℕ)=(p : ℤ)*I := by
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  obtain ⟨I,hI,hquad⟩ := row_index_exists hp hN
    (denseRow_relation (N:=p*q) (t:=1) (by omega) hj false)
  change quadratic (seedRow (p*q) m (p%m)).a (seedRow (p*q) m (p%m)).b
    (seedRow (p*q) m (p%m)).c (p/m : ℕ)=(p : ℤ)*I at hquad
  have hden : (denseRow (p*q) m (p%m) 1 false).t=(1 : ℤ) := rfl
  rw [hden,one_mul] at hI
  change (m : ℤ)^2*I=(seedRow (p*q) m (p%m)).a*p+
    (seedRow (p*q) m (p%m)).b*m-2*(seedRow (p*q) m (p%m)).a*(p%m : ℕ)+q at hI
  have hnonneg := (seed_index_bounds hm hpq hprefix hsize hI).1
  have hcoord : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+(p%m : ℕ) := by
    have hh := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  have htransport := wrappedRow_index (N:=p*q) (t:=t) (k:=0) hcoord hquad
  simp only [Nat.cast_zero,zero_mul,sub_zero] at htransport
  have he : i=(t : ℤ)*I := by
    apply mul_left_cancel₀ (by exact_mod_cast hp.ne' : (p : ℤ)≠0)
    exact hindex.symm.trans htransport
  have hmul : I.natAbs ≤ i.natAbs := by
    rw [he,Int.natAbs_mul,Int.natAbs_natCast]
    have hh := Nat.mul_le_mul_right I.natAbs (show 1≤t by omega)
    simpa only [one_mul] using hh
  exact ⟨I,hnonneg,lt_of_le_of_lt hmul hi,hquad⟩

/-- A common forced row is caught by the public short exception scan.
This eliminates the exceptional denominator and full-wrap tags. -/
theorem forced_common_hit_seed_scan {p q m t k : ℕ} {i : ℤ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : m.Prime)
    (hprefix : m^2≤p) (hN : m.Coprime (p*q)) (hsize : p*q≤m^6)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (ht : 0<t) (htm : t<m) (hk : k≤2*m+1) (hi : i.natAbs<2*m)
    (hindex : quadratic (wrappedRow (p*q) m (p%m) t k).a
      (wrappedRow (p*q) m (p%m) t k).b
      (wrappedRow (p*q) m (p%m) t k).c (p/m : ℕ)=(p : ℤ)*i)
    (hhit : wrappedValue t k
        (progressionSeed (rightUnit (projectedUnit g m)) (p*q) m (p%m))=
      (rightUnit (projectedUnit g m))^((m : ℤ)^2*i)) :
    ∃ d, scanSeedTrials (projectedUnit g m) m
      (exceptionSeeds (projectedUnit g m) (p*q) m)=some d := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hA,hk0⟩ := forced_common_hit_exception hp hq hpq.le hm hN hsize g hlong
    ht htm hk hindex hhit
  subst k
  have hm1 : 1<m := by have hh := hm.two_le; omega
  obtain ⟨I,hI0,hI,hquad⟩ := zero_wrap_short_seed_index hm1 hp.pos hpq.le hprefix
    hN hsize ht hi hindex
  let r := I.toNat
  have hrI : (r : ℤ)=I := Int.toNat_of_nonneg hI0
  have hr : r<2*m := by
    have hh : r=I.natAbs := by
      have hz : (r : ℤ)=(I.natAbs : ℤ) := by
        rw [hrI,Int.natCast_natAbs,abs_of_nonneg hI0]
      exact_mod_cast hz
    omega
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hrel : quotientRelation ((p : ℤ)*q) m (p%m : ℕ)
      (seedRow (p*q) m (p%m)).a (seedRow (p*q) m (p%m)).b
      (seedRow (p*q) m (p%m)).c (1 : ℤ) := by
    simpa only [Nat.cast_mul,Nat.cast_one,seedRow,denseRow,liftRow] using
      (denseRow_relation (N:=p*q) (t:=1) (by omega) hj false)
  have hcoord : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+(p%m : ℕ) := by
    have hh := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  let h := projectedUnit g m
  let s := progressionSeed h (p*q) m (p%m)
  have hperiod : (leftUnit h)^((p : ℤ)-1)=1 := by
    have hh := ZMod.units_pow_card_sub_one_eq_one p (leftUnit h)
    simpa only [←zpow_natCast,Nat.cast_sub hp.one_le,Nat.cast_one] using hh
  have hlocal := quotient_row_power_hit (leftUnit h) hcoord hrel hquad
    (by exact_mod_cast hp.ne_zero) hperiod
  have hstep : leftUnit s.step=(leftUnit h)^((m : ℤ)^2*I) := by
    simpa only [s,progressionSeed,leftUnit,map_zpow] using hlocal
  have hglobalpow : h^((m : ℤ)^2*I)=(h^(m^2))^r := by
    simp only [←zpow_natCast,←zpow_mul,Nat.cast_pow,hrI]
  have hreader : ZMod.castHom (dvd_mul_right p q) (ZMod p) (s.step : ZMod (p*q))=
      (ZMod.castHom (dvd_mul_right p q) (ZMod p) (h^(m^2) : ZMod (p*q)))^r := by
    have he : leftUnit s.step=leftUnit (h^((m : ℤ)^2*I)) := by
      simpa only [leftUnit,map_zpow] using hstep
    rw [hglobalpow] at he
    have hh := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) he
    simpa [leftUnit,RingHom.toMonoidHom] using hh
  have ha : (seedRow (p*q) m (p%m)).a≠0 := by
    change (representative (p*q) m (p%m) 1 : ℤ)≠0
    change representative (p*q) m (p%m) 1=1 at hA
    rw [hA]
    decide
  have hroot : (p : ℤ)∈wrappedRecovery (p*q) m 1 0 s (r : ℤ) := by
    rw [wrappedRecovery_eq]
    have hh := integerRoots_complete ha (quotient_row_recovery_equation hcoord hrel hquad)
    simpa only [wrappedRow,Nat.cast_one,Nat.cast_zero,one_mul,zero_mul,mul_zero,
      sub_zero,hrI,Nat.cast_mul] using hh
  have hperiods := long_seed_periods hm1 g hlong
  obtain ⟨d,hd⟩ := recoverSeedTrial_succeeds hp hq hpq hm1 h s hr
    hperiods.1 hperiods.2 hreader hroot
  have hj0 : 0<p%m := by
    by_contra! hn
    have hz : p%m=0 := by omega
    simp only [hz,Nat.coprime_zero_left] at hj
    have hh := hm.two_le
    omega
  exact scanSeedTrials_succeeds_of_member h s
    (exceptionSeed_mem (progressionSeed_mem h hj0 (Nat.mod_lt p hm.pos)) hA) hd

/-- Normalizing a merged half preserves the original collision in BOTH
directions; the reverse implication is needed to exclude global aliases. -/
theorem merged_root_iff {G : Type*} [CommGroup G] (g : G)
    (N m j t k : ℕ) (i : ℤ) (upper : Bool) (r : ℕ)
    (hz : combinedIndex m j k i=mergedStart m upper+r) :
    mergedTarget g m t (progressionSeed g N m j) upper=(commonStep g m)^r ↔
      wrappedValue t k (progressionSeed g N m j)=g^((m : ℤ)^2*i) := by
  constructor
  · intro hr
    have hh : (progressionSeed g N m j).step^t=
        (commonStep g m)^combinedIndex m j k i := by
      calc
        (progressionSeed g N m j).step^t=
            mergedTarget g m t (progressionSeed g N m j) upper*
              (commonStep g m)^mergedStart m upper := by
          simp only [mergedTarget,mul_assoc,←zpow_add,neg_add_cancel,zpow_zero,mul_one]
        _=(commonStep g m)^r*(commonStep g m)^mergedStart m upper := by rw [hr]
        _=(commonStep g m)^combinedIndex m j k i := by
          rw [←zpow_natCast,←zpow_add,hz]
          congr 1
          omega
    exact (merged_hit_iff g N m j t k i).mpr hh
  · intro hh
    exact mergedTarget_root g m t (progressionSeed g N m j) upper r hz
      ((merged_hit_iff g N m j t k i).mp hh)

/-- A simple original root that is absent in the other field returns a
checked factor, never a common global index. Mixed-index saturation is
included by the existing exact three-scalar reader. -/
theorem recoverTaggedInterval_separating_root {p q L b k : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (alpha x : (ZMod (p*q))ˣ) (hk : k<L) (hcover : L≤b^2)
    (hLP : L≤orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      (alpha : ZMod (p*q))))
    (hLQ : L≤orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      (alpha : ZMod (p*q))))
    (hroot : ZMod.castHom (dvd_mul_right p q) (ZMod p) (x : ZMod (p*q))=
      (ZMod.castHom (dvd_mul_right p q) (ZMod p) (alpha : ZMod (p*q)))^k)
    (hother : ZMod.castHom (dvd_mul_left q p) (ZMod q) (x : ZMod (p*q))≠
      (ZMod.castHom (dvd_mul_left q p) (ZMod q) (alpha : ZMod (p*q)))^k) :
    ∃ d, recoverTaggedInterval alpha x L b=some (Sum.inl d) := by
  rcases recoverTaggedInterval_preserves_root hp hq hpq alpha x hk hcover hLP hLQ
      hroot with hd|hglobal
  · exact hd
  · have hh := (recoverTaggedInterval_index_sound alpha x hglobal).2
    have hQ := congrArg (ZMod.castHom (dvd_mul_left q p) (ZMod q)) hh
    rw [map_pow] at hQ
    exact False.elim (hother hQ)

/-- The main merged reader uses only checked factor results. Common
global tags are skipped without calling merged quadratic recovery. -/
noncomputable def recoverFactorHalf {N : ℕ} (g : (ZMod N)ˣ) (m t : ℕ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (upper : Bool) : Option ℕ :=
  match recoverTaggedInterval (commonStep g m) (mergedTarget g m t s upper)
      (mergedLength m) (2*m) with
  | some (Sum.inl d) => some d
  | _ => none

/-- Every factor-only half result remains a checked proper divisor. -/
theorem recoverFactorHalf_sound {N m t d : ℕ} (g : (ZMod N)ˣ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (upper : Bool)
    (h : recoverFactorHalf g m t s upper=some d) : ProperDivisor N d := by
  unfold recoverFactorHalf at h
  split at h
  · rename_i e he
    cases h
    exact recoverTaggedInterval_factor_sound _ _ he
  · cases h

/-- Scan every public residue/denominator target using only factor
results; no supplied private successful column is an algorithm input. -/
noncomputable def scanFactorColumns {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    List (ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool)→Option ℕ
  | [] => none
  | (t,s,upper)::xs => match recoverFactorHalf g m t s upper with
    | some d => some d
    | none => scanFactorColumns g m xs

/-- The complete factor-only scan returns only checked factors. -/
theorem scanFactorColumns_sound {N m d : ℕ} (g : (ZMod N)ˣ)
    {xs : List (ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool)}
    (h : scanFactorColumns g m xs=some d) : ProperDivisor N d := by
  induction xs with
  | nil => simp only [scanFactorColumns] at h; cases h
  | cons col xs ih =>
    rcases col with ⟨t,s,upper⟩
    unfold scanFactorColumns at h
    split at h
    · rename_i e he
      cases h
      exact recoverFactorHalf_sound g s upper he
    · exact ih h

/-- One successful public member makes the complete factor-only scan
succeed, even when earlier columns return common global indices. -/
theorem scanFactorColumns_succeeds_of_member {N m t d : ℕ} (g : (ZMod N)ˣ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (upper : Bool)
    {xs : List (ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool)}
    (hmem : (t,s,upper)∈xs) (hd : recoverFactorHalf g m t s upper=some d) :
    ∃ e, scanFactorColumns g m xs=some e := by
  induction xs with
  | nil => simp only [List.not_mem_nil] at hmem
  | cons col xs ih =>
    rcases col with ⟨t',s',upper'⟩
    rw [scanFactorColumns]
    cases he : recoverFactorHalf g m t' s' upper' with
    | some e => exact ⟨e,rfl⟩
    | none =>
      rcases List.mem_cons.mp hmem with hh|hh
      · cases hh
        rw [hd] at he
        cases he
      · exact ih hh

/-- The whole public long reader checks the short exceptional seeds,
then uses the original common merged batch without quadratic reconstruction. -/
noncomputable def recoverLongRows {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) : Option ℕ :=
  match scanSeedTrials g m (exceptionSeeds g N m) with
  | some d => some d
  | none => scanFactorColumns g m (mergedColumns g N m)

/-- Every return of the amended whole-source reader is a proper factor. -/
theorem recoverLongRows_sound {N m d : ℕ} (g : (ZMod N)ˣ)
    (h : recoverLongRows g m=some d) : ProperDivisor N d := by
  unfold recoverLongRows at h
  split at h
  · rename_i e he
    cases h
    exact scanSeedTrials_sound g he
  · exact scanFactorColumns_sound g h

/-- A separating original row gives a factor-only merged half. Unit
normalization preserves the missing other-field root in both directions. -/
theorem recoverFactorHalf_of_separating_hit {p q m j t k r : ℕ} {i : ℤ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (g : (ZMod (p*q))ˣ)
    (upper : Bool) (hr : r<mergedLength m)
    (hz : combinedIndex m j k i=mergedStart m upper+r)
    (hLP : mergedLength m≤orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      ((commonStep g m : (ZMod (p*q))ˣ) : ZMod (p*q))))
    (hLQ : mergedLength m≤orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      ((commonStep g m : (ZMod (p*q))ˣ) : ZMod (p*q))))
    (hP : wrappedValue t k (progressionSeed (leftUnit g) (p*q) m j)=
      (leftUnit g)^((m : ℤ)^2*i))
    (hQ : wrappedValue t k (progressionSeed (rightUnit g) (p*q) m j)≠
      (rightUnit g)^((m : ℤ)^2*i)) :
    ∃ d, recoverFactorHalf g m t (progressionSeed g (p*q) m j) upper=some d := by
  let s := progressionSeed g (p*q) m j
  let x := mergedTarget g m t s upper
  let beta := commonStep g m
  have hrP := (merged_root_iff (leftUnit g) (p*q) m j t k i upper r hz).mpr hP
  have hPu : leftUnit x=(leftUnit beta)^r := by
    simpa only [x,s,beta,leftUnit,mergedTarget_map,commonStep,map_zpow] using hrP
  have hProot : ZMod.castHom (dvd_mul_right p q) (ZMod p) (x : ZMod (p*q))=
      (ZMod.castHom (dvd_mul_right p q) (ZMod p) (beta : ZMod (p*q)))^r := by
    have hh := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hPu
    simpa [leftUnit,RingHom.toMonoidHom] using hh
  have hQroot : ZMod.castHom (dvd_mul_left q p) (ZMod q) (x : ZMod (p*q))≠
      (ZMod.castHom (dvd_mul_left q p) (ZMod q) (beta : ZMod (p*q)))^r := by
    intro hh
    have hQu : rightUnit x=(rightUnit beta)^r := by
      apply Units.ext
      simpa [rightUnit,RingHom.toMonoidHom] using hh
    have hrQ : mergedTarget (rightUnit g) m t
        (progressionSeed (rightUnit g) (p*q) m j) upper=(commonStep (rightUnit g) m)^r := by
      simpa only [x,s,beta,rightUnit,mergedTarget_map,commonStep,map_zpow] using hQu
    exact hQ ((merged_root_iff (rightUnit g) (p*q) m j t k i upper r hz).mp hrQ)
  obtain ⟨d,hd⟩ := recoverTaggedInterval_separating_root hp hq hpq beta x hr
    (merged_interval_cover m) hLP hLQ hProot hQroot
  dsimp only [beta,x,s] at hd
  exact ⟨d,by simp only [recoverFactorHalf,hd]⟩

/-- Failure of the linear seed precheck forces a separating member in
the entire public merged stream at every remaining factor ratio. The
proof uses the exact arithmetic witness, with no generic-position premise. -/
theorem long_after_seed_scan_factor_column {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : m.Prime)
    (hprefix : m^2≤p) (hN : m.Coprime (p*q)) (hsize : p*q≤m^6)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hseed : scanSeedTrials (projectedUnit g m) m
      (exceptionSeeds (projectedUnit g m) (p*q) m)=none) :
    ∃ (t : ℕ) (upper : Bool),
      (t,progressionSeed (projectedUnit g m) (p*q) m (p%m),upper)∈
        mergedColumns (projectedUnit g m) (p*q) m ∧
      ∃ d, recoverFactorHalf (projectedUnit g m) m t
        (progressionSeed (projectedUnit g m) (p*q) m (p%m)) upper=some d := by
  let : Fact p.Prime := ⟨hp⟩
  have hm1 : 1<m := by have hh := hm.two_le; omega
  obtain ⟨t,k,i,_hmem,ht,htm,_htx,hk,hi,_ha,hindex⟩ :=
    hyperbolicRows_index_coverage hm1 hp.pos hpq.le hprefix hN hsize
  let h := projectedUnit g m
  have hQ : wrappedValue t k (progressionSeed (rightUnit h) (p*q) m (p%m))≠
      (rightUnit h)^((m : ℤ)^2*i) := by
    intro hh
    obtain ⟨d,hd⟩ := forced_common_hit_seed_scan hp hq hpq hm hprefix hN hsize
      g hlong ht htm hk hi hindex hh
    rw [hseed] at hd
    cases hd
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hj0 : 0<p%m := by
    by_contra! hn
    have hz : p%m=0 := by omega
    simp only [hz,Nat.coprime_zero_left] at hj
    have hh := hm.two_le
    omega
  have hrel : quotientRelation ((p : ℤ)*q) m (p%m : ℕ)
      (wrappedRow (p*q) m (p%m) t k).a
      (wrappedRow (p*q) m (p%m) t k).b
      (wrappedRow (p*q) m (p%m) t k).c (t : ℤ) := by
    simpa only [Nat.cast_mul,wrappedRow] using
      wrappedRow_relation (N:=p*q) (t:=t) (k:=k) hm.pos hj
  have hcoord : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+(p%m : ℕ) := by
    have hh := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  have hperiod : (leftUnit h)^((p : ℤ)-1)=1 := by
    have hh := ZMod.units_pow_card_sub_one_eq_one p (leftUnit h)
    simpa only [←zpow_natCast,Nat.cast_sub hp.one_le,Nat.cast_one] using hh
  have hP : wrappedValue t k (progressionSeed (leftUnit h) (p*q) m (p%m))=
      (leftUnit h)^((m : ℤ)^2*i) := by
    rw [wrappedValue_eq]
    exact quotient_row_power_hit (leftUnit h) hcoord hrel hindex
      (by exact_mod_cast hp.ne_zero) hperiod
  have hcombined := combinedIndex_bounds hm1 (by omega : 1≤p%m)
    (Nat.mod_lt p hm.pos) hk hi
  obtain ⟨upper,r,hr,hz⟩ := combinedIndex_half hcombined.1 hcombined.2
  have hperiods := long_common_periods hm1 g hlong
  obtain ⟨d,hd⟩ := recoverFactorHalf_of_separating_hit hp hq hpq h upper hr hz
    hperiods.1 hperiods.2 hP hQ
  exact ⟨t,upper,mergedColumn_mem (progressionSeed_mem h hj0 (Nat.mod_lt p hm.pos))
    ht htm upper,d,hd⟩

/-- The amended public long reader is complete at every factor ratio:
the short exception scan succeeds or a factor-only merged column does. -/
theorem recoverLongRows_complete {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : m.Prime)
    (hprefix : m^2≤p) (hN : m.Coprime (p*q)) (hsize : p*q≤m^6)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    ∃ d, recoverLongRows (projectedUnit g m) m=some d := by
  by_cases hseed : scanSeedTrials (projectedUnit g m) m
      (exceptionSeeds (projectedUnit g m) (p*q) m)=none
  · obtain ⟨t,upper,hmem,d,hd⟩ := long_after_seed_scan_factor_column hp hq hpq hm
      hprefix hN hsize g hlong hseed
    obtain ⟨e,he⟩ := scanFactorColumns_succeeds_of_member (projectedUnit g m)
      (progressionSeed (projectedUnit g m) (p*q) m (p%m)) upper hmem hd
    exact ⟨e,by simp only [recoverLongRows,hseed,he]⟩
  · obtain ⟨d,hd⟩ := Option.ne_none_iff_exists'.mp hseed
    exact ⟨d,by simp only [recoverLongRows,hd]⟩

/-- The actual N-only matched-width long-route output feeds the complete
amended reader. Neither a successful private row nor an order oracle is
an input. The full acquisition and bit budgets remain open. -/
theorem long_public_route_factor_only_succeeds {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      ∃ d, recoverLongRows (projectedUnit (ZMod.unitOfCoprime a hc) m) m=some d ∧
        ProperDivisor (p*q) d := by
  have hd := routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hd
  obtain ⟨hc,hlong⟩ := hd
  let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
  let g := ZMod.unitOfCoprime a hc
  have hN := Nat.mul_pos hp.pos hq.pos
  have hmBounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hbudget : p*q≤m^6 := (SemiprimeLehmanCoverage.sixthWidth_upper (p*q)).trans
    (Nat.pow_le_pow_left hmBounds.1 6)
  have hcover : m^2<p*q := public_modulus_prefix_below_input hN hB
  have hprefix := SemiprimeStrassenPrefix.prefix_none_excludes_small_prime
    hcover hp (dvd_mul_right p q) hnone
  have hm : m.Prime := SemiprimeEuclidRowBudget.publicRowModulus_prime (p*q)
  have hcop := SemiprimeStrassenPrefix.prefix_none_coprime_integer hcover hnone hm.pos
    (by have hh := hm.two_le; nlinarith only [hh] : m≤m^2)
  obtain ⟨d,hd⟩ := recoverLongRows_complete hp hq hpq hm hprefix.le hcop.symm
    hbudget g hlong
  exact ⟨hc,d,hd,recoverLongRows_sound _ hd⟩

/-- Slope one is a public square-root residue condition, obtained from
the exact quotient slope and the same Bezout inverse used by the seed. -/
theorem slope_one_square_residue {N m j : ℕ} (hm : 0<m)
    (hj : j.Coprime m) (hA : representative N m j 1=1) :
    (j : ZMod m)^2=(N : ZMod m) := by
  have hr := representative_congruence (N:=N) (j:=j) (t:=1) hm
  rw [hA,Nat.cast_one,mul_one] at hr
  have hi := ((publicInverse_correct hj).pow 2).mul_left (N : ℤ)
  have hcross : (j : ℤ)^2*((N : ℤ)*(publicInverse m j)^2) ≡ (N : ℤ) [ZMOD m] := by
    convert hi using 1 <;> first | rfl | ring
  have hs : (j : ℤ)^2 ≡ (N : ℤ) [ZMOD m] := by
    have hh := (hr.mul_left ((j : ℤ)^2)).trans hcross
    simpa only [mul_one] using hh
  have hz := (ZMod.intCast_eq_intCast_iff ((j : ℤ)^2) (N : ℤ) m).mpr hs
  simpa only [Int.cast_pow,Int.cast_natCast] using hz

/-- At a prime modulus, the exception menu contains at most TWO
literal cached seeds. This bounds the number of quadratic recovery trials,
not just a count of equivalence classes or private factor residues. -/
theorem exceptionSeeds_length_le_two {G : Type*} [CommGroup G]
    (g : G) (N : ℕ) {m : ℕ} (hm : m.Prime) :
    (exceptionSeeds g N m).length≤2 := by
  let : Fact m.Prime := ⟨hm⟩
  let : NeZero m := ⟨hm.ne_zero⟩
  let indices := (List.range (m-1)).filter (fun r => representative N m (r+1) 1==1)
  have hbounds {r : ℕ} (hr : r∈indices.toFinset) :
      r+1<m ∧ representative N m (r+1) 1=1 := by
    have hh : r∈indices := List.mem_toFinset.mp hr
    have hb := List.mem_filter.mp hh
    have hrange := List.mem_range.mp hb.1
    exact ⟨by omega,by simpa only [beq_iff_eq] using hb.2⟩
  have hlength : (exceptionSeeds g N m).length=indices.length := by
    simp only [exceptionSeeds,progressionSeeds,List.filter_map,List.length_map]
    rfl
  rw [hlength]
  have hnodup : indices.Nodup := (List.nodup_range (n:=m-1)).filter _
  have hcard := List.toFinset_card_of_nodup hnodup
  by_cases hempty : indices.toFinset=∅
  · rw [hempty,Finset.card_empty] at hcard
    omega
  · obtain ⟨r0,hr0⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hb0 := hbounds hr0
    have hj0 : (r0+1).Coprime m :=
      (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hb0.1)).symm
    have hs0 := slope_one_square_residue hm.pos hj0 hb0.2
    have hz0 : ((r0+1 : ℕ) : ZMod m)≠0 := by
      intro hz
      have hv := congrArg ZMod.val hz
      simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hb0.1,ZMod.val_zero] at hv
      omega
    let : NeZero (((r0+1 : ℕ) : ZMod m)) := ⟨hz0⟩
    have hsubset : indices.toFinset⊆{r0,m-r0-2} := by
      intro r hr
      have hb := hbounds hr
      have hj : (r+1).Coprime m :=
        (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hb.1)).symm
      have hs := slope_one_square_residue hm.pos hj hb.2
      have he := sq_eq_sq_iff_eq_or_eq_neg.mp (hs.trans hs0.symm)
      rcases he with he|he
      · have hv := congrArg ZMod.val he
        simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hb.1,Nat.mod_eq_of_lt hb0.1] at hv
        exact Finset.mem_insert.mpr (Or.inl (by omega))
      · have hv := congrArg ZMod.val he
        rw [ZMod.val_natCast,ZMod.val_neg_of_ne_zero,ZMod.val_natCast,
          Nat.mod_eq_of_lt hb.1,Nat.mod_eq_of_lt hb0.1] at hv
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (by omega)))
    have hle := (Finset.card_le_card hsubset).trans Finset.card_le_two
    rw [hcard] at hle
    exact hle

/-- The short exception acquisition has a linear root/target/cache input
scale. The main merged source remains quadratic and is not priced here. -/
theorem exception_input_bound {G : Type*} [CommGroup G]
    (g : G) (N : ℕ) {m : ℕ} (hm : m.Prime) :
    2*m+(exceptionSeeds g N m).length+(progressionSeeds g N m).length+1≤3*m+2 := by
  have hseeds := exceptionSeeds_length_le_two g N hm
  have hcache : (progressionSeeds g N m).length=m-1 := by
    simp only [progressionSeeds,List.length_map,List.length_range]
  have hm0 := hm.pos
  omega

/-- Read only the factor channel of the three supplied common-polynomial
scalars. This reader never constructs a quadratic candidate list. -/
noncomputable def readFactorJet {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (c : ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool) (jet : ZMod N×ZMod N×ZMod N) : Option ℕ :=
  match recoverTaggedJet (commonStep g m) (mergedTarget g m c.1 c.2.1 c.2.2)
      (mergedLength m) (2*m) jet with
  | some (Sum.inl d) => some d
  | _ => none

/-- Exact acquisition keeps this factor-only reader equal to the original
interval specification through saturation and common global zeros. -/
theorem readFactorJet_exact {N : ℕ} (g : (ZMod N)ˣ) (m t : ℕ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (upper : Bool) :
    readFactorJet g m (t,s,upper)
      (evaluateMergedPolynomials
        (mergedPolynomials ((commonStep g m : (ZMod N)ˣ) : ZMod N) m)
        ((mergedTarget g m t s upper : (ZMod N)ˣ) : ZMod N))=
      recoverFactorHalf g m t s upper := by
  simp only [readFactorJet,mergedPolynomials_eval_exact,recoverFactorHalf,recoverTaggedInterval]

/-- Consume the original aligned shared jet batch, skipping every common
global tag without reconstructing its wrap or quadratic coefficients. -/
noncomputable def scanFactorJetBatch {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    List ((ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool)×(ZMod N×ZMod N×ZMod N))→Option ℕ
  | [] => none
  | (c,jet)::xs => match readFactorJet g m c jet with
    | some d => some d
    | none => scanFactorJetBatch g m xs

/-- The aligned batch equals the complete factor-only public scan, for
every target list rather than only a supplied successful private tag. -/
theorem scanFactorJetBatch_map_exact {N m : ℕ} (g : (ZMod N)ˣ)
    (xs : List (ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool)) :
    scanFactorJetBatch g m (xs.map fun c =>
      (c,evaluateMergedPolynomials
        (mergedPolynomials ((commonStep g m : (ZMod N)ˣ) : ZMod N) m)
        ((mergedTarget g m c.1 c.2.1 c.2.2 : (ZMod N)ˣ) : ZMod N)))=
      scanFactorColumns g m xs := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    rcases c with ⟨t,s,upper⟩
    simp only [List.map_cons,scanFactorJetBatch,readFactorJet_exact,scanFactorColumns]
    cases he : recoverFactorHalf g m t s upper with
    | some d => rfl
    | none => exact ih

/-- The unchanged common-polynomial acquisition serves the amended reader. -/
theorem factorBatch_scan_exact {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    scanFactorJetBatch g m (mergedBatchJets g m)=
      scanFactorColumns g m (mergedColumns g N m) :=
  scanFactorJetBatch_map_exact g _

/-- Combine the short exception trials with the unchanged whole-source
acquisition. The acquisition backend and its bit cost remain unresolved. -/
noncomputable def recoverLongBatch {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) : Option ℕ :=
  match scanSeedTrials g m (exceptionSeeds g N m) with
  | some d => some d
  | none => scanFactorJetBatch g m (mergedBatchJets g m)

/-- Whole-batch evaluation preserves the complete amended public reader. -/
theorem recoverLongBatch_eq {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    recoverLongBatch g m=recoverLongRows g m := by
  simp only [recoverLongBatch,factorBatch_scan_exact,recoverLongRows]

/-- Every factor returned after shared batch acquisition is proper. -/
theorem recoverLongBatch_sound {N m d : ℕ} (g : (ZMod N)ˣ)
    (h : recoverLongBatch g m=some d) : ProperDivisor N d := by
  rw [recoverLongBatch_eq] at h
  exact recoverLongRows_sound g h

/-- The actual matched-width public long output is complete using the
short exceptional seeds and ONLY the factor channel of the shared batch. -/
theorem long_public_route_factor_batch_succeeds {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      ∃ d, recoverLongBatch (projectedUnit (ZMod.unitOfCoprime a hc) m) m=some d ∧
        ProperDivisor (p*q) d := by
  obtain ⟨hc,d,hd,hproper⟩ := long_public_route_factor_only_succeeds hp hq hpq hB hnone hroute
  exact ⟨hc,d,by rwa [recoverLongBatch_eq],hproper⟩

/-- One original seed trial constructs a quadratic candidate list only
on its checked common-index branch. This is proof-side call accounting. -/
noncomputable def seedTrialQuadraticCount {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (s : ProgressionSeed ((ZMod N)ˣ)) : ℕ :=
  match recoverTaggedInterval (g^(m^2)) s.step (2*m) m with
  | some (Sum.inr _) => 1
  | _ => 0

/-- A seed trial invokes quadratic candidate construction at most once. -/
theorem seedTrialQuadraticCount_le_one {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (s : ProgressionSeed ((ZMod N)ˣ)) : seedTrialQuadraticCount g m s≤1 := by
  unfold seedTrialQuadraticCount
  split <;> omega

/-- Count only trials actually visited before success in the seed scan. -/
noncomputable def seedScanQuadraticCount {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    List (ProgressionSeed ((ZMod N)ˣ))→ℕ
  | [] => 0
  | s::xs => seedTrialQuadraticCount g m s+
    match recoverSeedTrial g m s with
    | some _ => 0
    | none => seedScanQuadraticCount g m xs

/-- The actual early-stopping scan cannot invoke more quadratic
constructions than the supplied descriptor count. -/
theorem seedScanQuadraticCount_le_length {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (xs : List (ProgressionSeed ((ZMod N)ˣ))) :
    seedScanQuadraticCount g m xs≤xs.length := by
  induction xs with
  | nil => simp only [seedScanQuadraticCount,List.length_nil,le_refl]
  | cons s xs ih =>
    have hc := seedTrialQuadraticCount_le_one g m s
    rw [seedScanQuadraticCount]
    cases he : recoverSeedTrial g m s <;> simp only [List.length_cons] <;> omega

/-- At most two quadratic candidate constructions remain in the entire
amended long reader. The main factor-only batch invokes none. Each such
construction has at most two checked candidates by the frozen root list. -/
theorem long_seed_quadratic_count {N m : ℕ} (hm : m.Prime) (g : (ZMod N)ˣ) :
    seedScanQuadraticCount g m (exceptionSeeds g N m)≤2 :=
  (seedScanQuadraticCount_le_length g m _).trans (exceptionSeeds_length_le_two g N hm)

/-- Budget every candidate that a visited common-index seed trial may
check. Early success in its candidate list can only lower actual queries. -/
noncomputable def seedTrialCandidateBudget {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (s : ProgressionSeed ((ZMod N)ˣ)) : ℕ :=
  match recoverTaggedInterval (g^(m^2)) s.step (2*m) m with
  | some (Sum.inr r) => (wrappedRecovery N m 1 0 s (r : ℤ)).length
  | _ => 0

/-- A quadratic construction supplies at most two checked candidates. -/
theorem seedTrialCandidateBudget_le {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (s : ProgressionSeed ((ZMod N)ˣ)) :
    seedTrialCandidateBudget g m s≤2*seedTrialQuadraticCount g m s := by
  unfold seedTrialCandidateBudget seedTrialQuadraticCount
  cases he : recoverTaggedInterval (g^(m^2)) s.step (2*m) m with
  | none => simp
  | some value =>
    cases value with
    | inl d => simp
    | inr r => exact wrappedRecovery_length_le_two _ _ _ _ _ _

/-- Candidate-query budget follows the same actual visited seed prefix. -/
noncomputable def seedScanCandidateBudget {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    List (ProgressionSeed ((ZMod N)ˣ))→ℕ
  | [] => 0
  | s::xs => seedTrialCandidateBudget g m s+
    match recoverSeedTrial g m s with
    | some _ => 0
    | none => seedScanCandidateBudget g m xs

/-- All visited candidate budgets are charged against the visited
quadratic construction count, including false common global seed hits. -/
theorem seedScanCandidateBudget_le {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (xs : List (ProgressionSeed ((ZMod N)ˣ))) :
    seedScanCandidateBudget g m xs≤2*seedScanQuadraticCount g m xs := by
  induction xs with
  | nil => simp only [seedScanCandidateBudget,seedScanQuadraticCount,Nat.mul_zero,le_refl]
  | cons s xs ih =>
    have hc := seedTrialCandidateBudget_le g m s
    rw [seedScanCandidateBudget,seedScanQuadraticCount]
    cases he : recoverSeedTrial g m s <;> dsimp only <;> omega

/-- At most four quadratic candidates are checked in the entire amended
long reader, with no quadratic candidate checks in the main merged batch. -/
theorem long_seed_candidate_budget {N m : ℕ} (hm : m.Prime) (g : (ZMod N)ˣ) :
    seedScanCandidateBudget g m (exceptionSeeds g N m)≤4 := by
  have hc := seedScanCandidateBudget_le g m (exceptionSeeds g N m)
  have hq := long_seed_quadratic_count hm g
  omega

end RiemannGaussian.SemiprimeForcedRowSeparation
