/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeDenseRatioObstruction
import RiemannGaussian.SemiprimeDenseLoopObstruction
import RiemannGaussian.SemiprimeLocalOrderRouting

/-!
# Periodic index forcing and the remaining routing gap

Reducing the true dense-row indices modulo a period of the baby power can
force an actual modular collision without a small exact recovery index.
The required period bound is explicit. Rough long local orders exclude
that bound at prime sixth-root widths, so this is not an all-ratio repair
of the remaining long branch. A separate arithmetic interval criterion
excludes whole-modulus saturation and converts a local hit to a proper GCD.
None of these statements prices acquisition of the implicit dense source.
-/

namespace RiemannGaussian.SemiprimeDensePeriodForcing

open SemiprimeQuotientRows SemiprimeDenseRowCoverage SemiprimeDenseRowCarries
open SemiprimeDenseRatioObstruction SemiprimeLocalOrderRouting

/-- Binning the remainders of the same m true indices forces a short
modular difference when a period fits in m-1 bins. The index function and
period enter the proof only; neither is supplied to the public source. -/
theorem period_index_pigeonhole {m K D : ℕ} (hm : 1<m) (hK : 0<K)
    (hD : 0<D) (hsize : D≤(m-1)*K) (f : ℕ→ℤ) :
    ∃ s t : ℕ, s<t ∧ t<m ∧
      |f t%(D : ℤ)-f s%(D : ℤ)|<(K : ℤ) := by
  classical
  let bin (t : ℕ) : ℕ := (f t%(D : ℤ)).toNat/K
  have hrem (t : ℕ) : 0≤f t%(D : ℤ) ∧ f t%(D : ℤ)<D := by
    exact ⟨Int.emod_nonneg _ (by exact_mod_cast hD.ne'),
      Int.emod_lt_of_pos _ (by exact_mod_cast hD)⟩
  have hmap : Set.MapsTo bin (Finset.range m) (Finset.range (m-1)) := by
    intro t _ht
    have hb := hrem t
    have hc := Int.toNat_of_nonneg hb.1
    have hn : (f t%(D : ℤ)).toNat<(m-1)*K := by omega
    exact Finset.mem_range.mpr
      ((Nat.div_lt_iff_lt_mul hK).mpr (by simpa [Nat.mul_comm] using hn))
  obtain ⟨s,hs,t,ht,hne,he⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s:=Finset.range m) (t:=Finset.range (m-1)) (by simp; omega) hmap
  have hclose : |f t%(D : ℤ)-f s%(D : ℤ)|<(K : ℤ) := by
    have hcs := Int.toNat_of_nonneg (hrem s).1
    have hct := Int.toNat_of_nonneg (hrem t).1
    have hds := Nat.mod_add_div (f s%(D : ℤ)).toNat K
    have hdt := Nat.mod_add_div (f t%(D : ℤ)).toNat K
    have hrs := Nat.mod_lt (f s%(D : ℤ)).toNat hK
    have hrt := Nat.mod_lt (f t%(D : ℤ)).toNat hK
    change (f s%(D : ℤ)).toNat/K=(f t%(D : ℤ)).toNat/K at he
    rw [←he] at hdt
    exact abs_lt.mpr (by omega)
  rcases lt_or_gt_of_ne hne with hst|hts
  · exact ⟨s,t,hst,Finset.mem_range.mp ht,hclose⟩
  · refine ⟨t,s,hts,Finset.mem_range.mp hs,?_⟩
    simpa only [abs_sub_comm] using hclose

/-- The same emitted difference row has a small modular index J. Its
literal quadratic still uses the true index i, which can be arbitrarily
larger. The statement does not assert recovery at J. -/
theorem denseRows_period_index_coverage {p q m K D : ℕ} (hm : 1<m)
    (hp : 0<p) (hN : m.Coprime (p*q)) (hK : 0<K) (hD : 0<D)
    (hsize : D≤(m-1)*K) :
    ∃ (t : ℕ) (negative : Bool) (i J : ℤ),
      (p%m,denseRow (p*q) m (p%m) t negative)∈denseRows (p*q) m ∧
      (denseRow (p*q) m (p%m) t negative).a≠0 ∧
      0<t ∧ t<m ∧ |J|≤(K : ℤ)+3 ∧ i ≡ J [ZMOD D] ∧
      quadratic (denseRow (p*q) m (p%m) t negative).a
        (denseRow (p*q) m (p%m) t negative).b
          (denseRow (p*q) m (p%m) t negative).c (p/m : ℕ)=(p : ℤ)*i := by
  have hm₀ : 0<m := by omega
  have hpcop : p.Coprime m :=
    (hN.of_dvd_right (dvd_mul_right p q)).symm
  have hjcop : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hpcop.symm
  have hj : 0<p%m := by
    by_contra! hz
    have he : p%m=0 := by omega
    simp only [he,Nat.coprime_zero_left] at hjcop
    omega
  have hindices : ∀ t : ℕ, ∃ i : ℤ,
      (m : ℤ)^2*i=(denseRow (p*q) m (p%m) t false).a*p+
        (denseRow (p*q) m (p%m) t false).b*m-
          2*(denseRow (p*q) m (p%m) t false).a*(p%m : ℕ)+
            (denseRow (p*q) m (p%m) t false).t*q ∧
      quadratic (denseRow (p*q) m (p%m) t false).a
        (denseRow (p*q) m (p%m) t false).b
          (denseRow (p*q) m (p%m) t false).c (p/m : ℕ)=(p : ℤ)*i :=
    fun t => row_index_exists hp hN (denseRow_relation hm₀ hjcop false)
  choose f hf using hindices
  obtain ⟨s,t,hst,htm,hclose⟩ := period_index_pigeonhole hm hK hD hsize f
  obtain ⟨negative,ha⟩ := representative_difference (N:=p*q) (j:=p%m) hm₀ hst
  have hT : 0<t-s := by omega
  have hTm : t-s<m := by omega
  obtain ⟨i,hi,hquad⟩ := row_index_exists hp hN
    (denseRow_relation (N:=p*q) (t:=t-s) hm₀ hjcop negative)
  have hden : (denseRow (p*q) m (p%m) (t-s) negative).t=
      (denseRow (p*q) m (p%m) t false).t-
        (denseRow (p*q) m (p%m) s false).t := by
    change ((t-s : ℕ) : ℤ)=(t : ℤ)-(s : ℤ)
    omega
  have hshift := difference_relift_index hm₀ ha hden
    (denseRow_b_bound hm false) (denseRow_b_bound hm false)
    (denseRow_b_bound hm negative) (hf s).1 (hf t).1 hi
  let J : ℤ := f t%(D : ℤ)-f s%(D : ℤ)+(i-(f t-f s))
  have hbound : |J|≤(K : ℤ)+3 := by
    have hb := abs_add_le (f t%(D : ℤ)-f s%(D : ℤ)) (i-(f t-f s))
    change |J|≤_ at hb
    linarith only [hb,hclose,hshift]
  have hcong : i ≡ J [ZMOD D] := by
    have hc := ((Int.mod_modEq (f t) (D : ℤ)).sub
      (Int.mod_modEq (f s) (D : ℤ))).add_right (i-(f t-f s))
    have he : f t-f s+(i-(f t-f s))=i := by ring
    change J ≡ f t-f s+(i-(f t-f s)) [ZMOD D] at hc
    rw [he] at hc
    exact hc.symm
  exact ⟨t-s,negative,i,J,denseRow_mem hj (Nat.mod_lt p hm₀) hT hTm negative,
    denseRow_a_ne_zero hm hN hjcop hT hTm negative,hT,hTm,hbound,hcong,hquad⟩

/-- Any confirmed period, rather than an exact-order oracle, permits
the modular replacement of an exponent. -/
theorem zpow_eq_of_period_congruent {G : Type*} [Group G] (g : G)
    {D : ℕ} (hpow : g^D=1) {i J : ℤ} (h : i ≡ J [ZMOD D]) :
    g^i=g^J := by
  rw [zpow_eq_zpow_emod' i hpow,zpow_eq_zpow_emod' J hpow,h.eq]

/-- The period needed for forcing belongs to the baby generator g^(m²),
so a common factor of m² and the local order is fully retained. -/
theorem denseRows_period_collision_coverage {p q m K D : ℕ} (hm : 1<m)
    (hp : p.Prime) (hN : m.Coprime (p*q)) (hK : 0<K) (hD : 0<D)
    (hsize : D≤(m-1)*K) (g : (ZMod p)ˣ) (hpow : (g^(m^2))^D=1) :
    ∃ (t : ℕ) (negative : Bool) (J : ℤ),
      0<t ∧ t<m ∧ J.natAbs≤K+3 ∧
      g^giantExponent m (p%m : ℕ) (denseRow (p*q) m (p%m) t negative).a
        (denseRow (p*q) m (p%m) t negative).b
          (denseRow (p*q) m (p%m) t negative).c=g^((m : ℤ)^2*J) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨t,negative,i,J,_hmem,_ha,ht,htm,hbound,hcong,hquad⟩ :=
    denseRows_period_index_coverage hm hp.pos hN hK hD hsize
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hcoord : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+(p%m : ℕ) := by
    have hd := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  have hrel : quotientRelation ((p : ℤ)*q) m (p%m : ℕ)
      (denseRow (p*q) m (p%m) t negative).a
      (denseRow (p*q) m (p%m) t negative).b
      (denseRow (p*q) m (p%m) t negative).c
      (denseRow (p*q) m (p%m) t negative).t := by
    simpa only [Nat.cast_mul] using denseRow_relation (N:=p*q) (t:=t)
      (by omega : 0<m) hj negative
  have hperiod : g^((p : ℤ)-1)=1 := by
    have h := ZMod.units_pow_card_sub_one_eq_one p g
    have hz : g^((p-1 : ℕ) : ℤ)=1 := by simpa only [zpow_natCast] using h
    simpa only [Nat.cast_sub hp.one_le,Nat.cast_one] using hz
  have htrue := quotient_row_power_hit g hcoord hrel hquad
    (by exact_mod_cast hp.ne_zero) hperiod
  have halias := zpow_eq_of_period_congruent (g^(m^2)) hpow hcong
  have hiJ : g^((m : ℤ)^2*i)=g^((m : ℤ)^2*J) := by
    simpa only [←zpow_natCast,←zpow_mul,Nat.cast_pow] using halias
  have hJ : J.natAbs≤K+3 := by
    have hz : (J.natAbs : ℤ)≤(K+3 : ℕ) := by
      simpa only [Int.natCast_natAbs,Nat.cast_add,Nat.cast_ofNat] using hbound
    exact_mod_cast hz
  exact ⟨t,negative,J,ht,htm,hJ,htrue.trans hiJ⟩

/-- Centering transport reaches the actual one-seed-per-residue cache.
No small exact integer root at I is asserted or required. -/
theorem public_progression_period_coverage {p q m K D : ℕ} (hm : 1<m)
    (hp : p.Prime) (hN : m.Coprime (p*q)) (hK : 0<K) (hD : 0<D)
    (hsize : D≤(m-1)*K) (g : (ZMod (p*q))ˣ)
    (hpow : ((leftUnit g)^(m^2))^D=1) :
    ∃ (t : ℕ) (negative : Bool) (I : ℤ),
      0<t ∧ t<m ∧ I.natAbs≤K+2*m+4 ∧
      progressionSeed g (p*q) m (p%m)∈progressionSeeds g (p*q) m ∧
      Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
        (progressionValue m t negative (progressionSeed g (p*q) m (p%m)))=
          (leftUnit g)^((m : ℤ)^2*I) := by
  obtain ⟨t,negative,J,ht,htm,hJ,hhit⟩ :=
    denseRows_period_collision_coverage hm hp hN hK hD hsize (leftUnit g) hpow
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hj₀ : 0<p%m := by
    by_contra! hn
    have he : p%m=0 := by omega
    simp only [he,Nat.coprime_zero_left] at hj
    omega
  let I : ℤ := J+centeringCarry (p*q) m (p%m) t negative
  have hcarry := centeringCarry_bound (N:=p*q) hm hj (Nat.mod_lt p (by omega))
    ht htm negative
  have hcarryNat : (centeringCarry (p*q) m (p%m) t negative).natAbs≤2*m+1 := by
    have hc : ((centeringCarry (p*q) m (p%m) t negative).natAbs : ℤ)≤(2*m+1 : ℕ) := by
      simpa only [Int.natCast_natAbs,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
        Nat.cast_one] using hcarry
    exact_mod_cast hc
  have hbound : I.natAbs≤K+2*m+4 := by
    have hb := Int.natAbs_add_le J (centeringCarry (p*q) m (p%m) t negative)
    change I.natAbs≤_ at hb
    omega
  have he := denseRow_giant_carries (N:=p*q) (t:=t) (by omega : 0<m) hj negative
  rw [he] at hhit
  have hphase : (leftUnit g)^reducedExponent (p*q) m (p%m) t negative=
      (leftUnit g)^((m : ℤ)^2*I) := by
    have h₁ : reducedExponent (p*q) m (p%m) t negative=
        (reducedExponent (p*q) m (p%m) t negative-
          (m : ℤ)^2*centeringCarry (p*q) m (p%m) t negative)+
            (m : ℤ)^2*centeringCarry (p*q) m (p%m) t negative := by ring
    rw [h₁,zpow_add,hhit,←zpow_add]
    congr 1
    dsimp only [I]
    ring
  refine ⟨t,negative,I,ht,htm,hbound,
    progressionSeed_mem g hj₀ (Nat.mod_lt p (by omega)),?_⟩
  rw [progressionValue_map,progressionValue_eq]
  exact hphase

/-- The original linear cache radius fixes the modular bin width after
the exact centering charge has been paid. -/
theorem linear_period_capacity {m : ℕ} (hm : 8≤m) :
    (m-1)*(3*m+11)<(2*m)^2 := by
  have hmz : (8 : ℤ)≤m := by exact_mod_cast hm
  have hsub : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  have hpos : 0≤(m : ℤ)*(m-8) := mul_nonneg (by omega) (by omega)
  have he : (((m-1)*(3*m+11) : ℕ) : ℤ)<((2*m)^2 : ℕ) := by
    simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_pow,hsub]
    nlinarith only [hpos]
  exact_mod_cast he

/-- Roughness at a prime width prevents the baby power from reducing
either local order. This is an arithmetic consequence of routing. -/
theorem rough_baby_order {G : Type*} [Monoid G] (g : G) {B : ℕ}
    (hB : B.Prime) (hrough : ∀ r, r.Prime → r∣orderOf g → B<r) :
    orderOf (g^(B^2))=orderOf g := by
  have hc : B.Coprime (orderOf g) := hB.coprime_iff_not_dvd.mpr (by
    intro hd
    exact (lt_irrefl B) (hrough B hB hd))
  exact (hc.symm.pow_right 2).orderOf_pow

/-- At prime widths, the remaining projected-long branch excludes
every period small enough for this modular-bin forcing argument in the
unchanged radius 5B+15. This is not a no-hit theorem for the actual rows. -/
theorem long_branch_excludes_period_bound {p q B : ℕ}
    (hB : B.Prime) (hB8 : 8≤B) (g : (ZMod (p*q))ˣ) (hlong : LongData g B) :
    ∀ D, 0<D → (((leftUnit (SemiprimeCentreFreeCover.projectedUnit g B))^(B^2))^D=1 ∨
      ((rightUnit (SemiprimeCentreFreeCover.projectedUnit g B))^(B^2))^D=1) →
      (B-1)*(3*B+11)<D := by
  have hcap := linear_period_capacity hB8
  intro D hD hpow
  rcases hpow with hpow|hpow
  · have hd := orderOf_dvd_iff_pow_eq_one.mpr hpow
    rw [rough_baby_order _ hB hlong.2.2.2.2.2.1] at hd
    exact hcap.trans (hlong.2.2.2.1.1.trans_le (Nat.le_of_dvd hD hd))
  · have hd := orderOf_dvd_iff_pow_eq_one.mpr hpow
    rw [rough_baby_order _ hB hlong.2.2.2.2.2.2] at hd
    exact hcap.trans (hlong.2.2.2.1.2.trans_le (Nat.le_of_dvd hD hd))

/-- Prime sixth-root widths are unchanged by the actual least-prime
public selector; the preceding obstruction applies to that constructor. -/
theorem publicRowModulus_eq_prime_width {N B : ℕ}
    (hwidth : SemiprimeLehmanCoverage.sixthWidth N=B) (hB : B.Prime) :
    SemiprimeEuclidRowBudget.publicRowModulus N=B := by
  unfold SemiprimeEuclidRowBudget.publicRowModulus
  simp only [hwidth,max_eq_right hB.one_le]
  exact Nat.le_antisymm
    (SemiprimeEuclidRowBudget.publicPrimeAtLeast_minimal B hB.pos hB le_rfl)
    (SemiprimeEuclidRowBudget.publicPrimeAtLeast_ge B hB.pos)

/-- The exclusion uses the actual public modulus on every input with
a prime sixth-root width at least eight, not a freely supplied scale. -/
theorem public_long_branch_excludes_period_bound {p q : ℕ}
    (hB : (SemiprimeLehmanCoverage.sixthWidth (p*q)).Prime)
    (hB8 : 8≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (g : (ZMod (p*q))ˣ)
    (hlong : LongData g (SemiprimeLehmanCoverage.sixthWidth (p*q))) :
    let B := SemiprimeLehmanCoverage.sixthWidth (p*q)
    let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
    ∀ D, 0<D → (((leftUnit (SemiprimeCentreFreeCover.projectedUnit g B))^(m^2))^D=1 ∨
      ((rightUnit (SemiprimeCentreFreeCover.projectedUnit g B))^(m^2))^D=1) →
      (m-1)*(3*m+11)<D := by
  dsimp only
  rw [publicRowModulus_eq_prime_width rfl hB]
  exact long_branch_excludes_period_bound hB hB8 g hlong

/-- The cached exponent retains an explicit small correction to tN;
this identity uses the actual public quotient relation. -/
theorem reducedExponent_arithmetic {N m j t : ℕ} (hm : 0<m)
    (hj : j.Coprime m) (negative : Bool) :
    reducedExponent N m j t negative=(t : ℤ)*N+
      (carryRow N m j t negative).a+(carryRow N m j t negative).b*m-
        2*(carryRow N m j t negative).a*j := by
  have hr := giantExponent_eq (carryRow_relation (N:=N) (t:=t) hm hj negative)
  have he : giantExponent m j (carryRow N m j t negative).a
      (carryRow N m j t negative).b (carryRow N m j t negative).c=
        reducedExponent N m j t negative := by
    simp only [giantExponent,carryRow,reducedExponent,rawLinear]
    ring
  change giantExponent m j (carryRow N m j t negative).a
    (carryRow N m j t negative).b (carryRow N m j t negative).c=
      (t : ℤ)*N+(carryRow N m j t negative).a+
        (carryRow N m j t negative).b*m-2*(carryRow N m j t negative).a*j at hr
  rw [he] at hr
  exact hr

/-- The public short-window residual has a bounded correction to tN.
No field equality or exact-root premise is used in this bound. -/
theorem reduced_residual_bound {N m j t R : ℕ} (hm : 1<m)
    (hj : j.Coprime m) (hjm : j<m) (ht : 0<t) (htm : t<m)
    (negative : Bool) {I : ℤ} (hI : I.natAbs≤R) :
    |reducedExponent N m j t negative-(t : ℤ)*N-(m : ℤ)^2*I|≤
      ((R+2*m+2)*m^2+m : ℕ) := by
  have ha := dense_leading_bound (N:=N) (j:=j) (t:=t) (by omega : 0<m) negative
  have ha' : |(carryRow N m j t negative).a|≤(m : ℤ) := by
    simpa only [carryRow,denseRow_leading_carry] using ha
  have hb := rawLinear_bound (N:=N) hm hjm ht htm negative
  have hL := recoveryLinear_bound (a:=(carryRow N m j t negative).a)
    (b:=rawLinear N m j t negative) (K:=2*m) (by omega : j≤m) ha'
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat,pow_two,mul_assoc] using hb) hI
  have he := reducedExponent_arithmetic (N:=N) (t:=t) (by omega : 0<m) hj negative
  have hdelta : reducedExponent N m j t negative-(t : ℤ)*N-(m : ℤ)^2*I=
      (carryRow N m j t negative).a+
        ((carryRow N m j t negative).b*m-2*(carryRow N m j t negative).a*j-
          (m : ℤ)^2*I) := by rw [he]; ring
  rw [hdelta]
  have hsum := abs_add_le (carryRow N m j t negative).a
    ((carryRow N m j t negative).b*m-2*(carryRow N m j t negative).a*j-
      (m : ℤ)^2*I)
  simp only [carryRow] at hsum hL ha' ⊢
  push_cast at hL
  push_cast
  linarith only [hsum,ha',hL]

/-- The global order divides the exact Euler period for two distinct
prime factors. This is proof-side divisibility, not a computed order. -/
theorem global_order_dvd_euler {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (g : (ZMod (p*q))ˣ) :
    orderOf g∣(p-1)*(q-1) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  rw [global_order_eq_lcm hp hq hpq]
  exact Nat.lcm_dvd
    ((ZMod.orderOf_units_dvd_card_sub_one (leftUnit g)).trans (dvd_mul_right _ _))
    ((ZMod.orderOf_units_dvd_card_sub_one (rightUnit g)).trans (dvd_mul_left _ _))

/-- Subtracting t times the Euler period exposes t(p+q-1), rather
than the large tN term. If its entire public correction window lies
strictly between zero and the global order, no pair can saturate N. -/
theorem cached_pair_not_global {p q m j t R : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (hm : 1<m) (hj : j.Coprime m) (hjm : j<m)
    (ht : 0<t) (htm : t<m) (g : (ZMod (p*q))ˣ) (negative : Bool)
    {I : ℤ} (hI : I.natAbs≤R)
    (hlower : (R+2*m+2)*m^2+m<p+q-1)
    (hupper : m*(p+q-1)+((R+2*m+2)*m^2+m)<orderOf g) :
    progressionValue m t negative (progressionSeed g (p*q) m j)≠
      g^((m : ℤ)^2*I) := by
  rw [progressionValue_eq]
  intro heq
  have hdiv := orderOf_dvd_sub_iff_zpow_eq_zpow.mpr heq
  have hphi := global_order_dvd_euler hp hq hpq g
  have hphiZ : (orderOf g : ℤ)∣((p-1)*(q-1) : ℕ) := by exact_mod_cast hphi
  have hmult : (orderOf g : ℤ)∣(t : ℤ)*((p-1)*(q-1) : ℕ) :=
    hphiZ.mul_left (t : ℤ)
  have hd := dvd_sub hdiv hmult
  have heuler : (((p-1)*(q-1) : ℕ) : ℤ)=(p*q : ℕ)-(p+q-1 : ℕ) := by
    simp only [Nat.cast_mul,Nat.cast_sub hp.one_le,Nat.cast_sub hq.one_le,
      Nat.cast_sub (by have h := hp.one_le; omega : 1≤p+q),Nat.cast_add,Nat.cast_one]
    ring
  let delta : ℤ := reducedExponent (p*q) m j t negative-
    (t : ℤ)*(p*q : ℕ)-(m : ℤ)^2*I
  have hdelta := abs_le.mp (reduced_residual_bound (N:=p*q) hm hj hjm ht htm negative hI)
  change -((R+2*m+2)*m^2+m : ℕ)≤delta ∧ delta≤((R+2*m+2)*m^2+m : ℕ) at hdelta
  have hlowerZ : (((R+2*m+2)*m^2+m : ℕ) : ℤ)<(p+q-1 : ℕ) := by
    exact_mod_cast hlower
  have hupperZ : (m : ℤ)*(p+q-1 : ℕ)+((R+2*m+2)*m^2+m : ℕ)<orderOf g := by
    exact_mod_cast hupper
  have ht₁ : (1 : ℤ)≤t := by exact_mod_cast ht
  have htmZ : (t : ℤ)≤m := by exact_mod_cast htm.le
  have hS : (0 : ℤ)≤(p+q-1 : ℕ) := by positivity
  have hmul₀ := mul_le_mul_of_nonneg_right ht₁ hS
  have hmul₁ := mul_le_mul_of_nonneg_right htmZ hS
  have hbox : 0<(t : ℤ)*(p+q-1 : ℕ)+delta ∧
      (t : ℤ)*(p+q-1 : ℕ)+delta<(orderOf g : ℤ) := by
    constructor <;> linarith only [hdelta.1,hdelta.2,hlowerZ,hupperZ,hmul₀,hmul₁]
  have hn := SemiprimeDenseLoopObstruction.no_divisor_in_open_period
    (D:=(orderOf g : ℤ)) (h:=0) (by exact_mod_cast orderOf_pos g) (by simpa using hbox.1)
      (by simpa using hbox.2)
  have hnorm : reducedExponent (p*q) m j t negative-(m : ℤ)^2*I-
      (t : ℤ)*((p-1)*(q-1) : ℕ)=(t : ℤ)*(p+q-1 : ℕ)+delta := by
    rw [heuler]
    dsimp only [delta]
    ring
  rw [hnorm] at hd
  exact hn hd

/-- A signed cached pair which hits p and does not collide globally
has a proper residual GCD p. Whole-modulus saturation is retained as a
real obstruction, rather than cancelled in the composite ring. -/
theorem local_hit_not_global_gcd {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (u v : (ZMod (p*q))ˣ)
    (hP : Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom u=
      Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom v)
    (hne : u≠v) :
    (p*q).gcd ((u : ZMod (p*q))-(v : ZMod (p*q))).val=p := by
  have hPv : ZMod.castHom (dvd_mul_right p q) (ZMod p) (u : ZMod (p*q))=
      ZMod.castHom (dvd_mul_right p q) (ZMod p) (v : ZMod (p*q)) := by
    have h := congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) hP
    change ZMod.castHom (dvd_mul_right p q) (ZMod p) (u : ZMod (p*q))=
      ZMod.castHom (dvd_mul_right p q) (ZMod p) (v : ZMod (p*q)) at h
    exact h
  have hQv : ZMod.castHom (dvd_mul_left q p) (ZMod q) (u : ZMod (p*q))≠
      ZMod.castHom (dvd_mul_left q p) (ZMod q) (v : ZMod (p*q)) := by
    intro he
    apply hne
    apply Units.ext
    exact SemiprimeIntervalJet.eq_of_prime_reductions hp hq hpq _ _ hPv he
  apply SemiprimeCentreFreeCover.separating_residue_gcd hp hq
  · rw [map_sub,sub_eq_zero]
    exact hPv
  · rw [map_sub,sub_ne_zero]
    exact hQv

/-- Periodic forcing together with the explicit Euler-normalized order
window gives a proper GCD in the literal public cache, for arbitrary
factor ratios. Both quantitative premises remain visible and unpriced. -/
theorem public_progression_period_gcd_coverage {p q m K D : ℕ} (hm : 1<m)
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hN : m.Coprime (p*q))
    (hK : 0<K) (hD : 0<D) (hsize : D≤(m-1)*K) (g : (ZMod (p*q))ˣ)
    (hpow : ((leftUnit g)^(m^2))^D=1)
    (hlower : (K+4*m+6)*m^2+m<p+q-1)
    (hupper : m*(p+q-1)+((K+4*m+6)*m^2+m)<orderOf g) :
    ∃ (t : ℕ) (negative : Bool) (I : ℤ),
      0<t ∧ t<m ∧ I.natAbs≤K+2*m+4 ∧
      progressionSeed g (p*q) m (p%m)∈progressionSeeds g (p*q) m ∧
      (p*q).gcd
        (((progressionValue m t negative (progressionSeed g (p*q) m (p%m)) :
          (ZMod (p*q))ˣ) : ZMod (p*q))-
          ((g^((m : ℤ)^2*I) : (ZMod (p*q))ˣ) : ZMod (p*q))).val=p := by
  obtain ⟨t,negative,I,ht,htm,hI,hmem,hhit⟩ :=
    public_progression_period_coverage hm hp hN hK hD hsize g hpow
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hL : ((K+2*m+4)+2*m+2)*m^2+m<p+q-1 := by
    convert hlower using 1
    ring
  have hU : m*(p+q-1)+(((K+2*m+4)+2*m+2)*m^2+m)<orderOf g := by
    convert hupper using 1
    ring
  have hne := cached_pair_not_global hp hq hpq hm hj (Nat.mod_lt p (by omega))
    ht htm g negative hI hL hU
  refine ⟨t,negative,I,ht,htm,hI,hmem,?_⟩
  apply local_hit_not_global_gcd hp hq hpq _ _ _ hne
  simpa only [map_zpow,leftUnit] using hhit

end RiemannGaussian.SemiprimeDensePeriodForcing
