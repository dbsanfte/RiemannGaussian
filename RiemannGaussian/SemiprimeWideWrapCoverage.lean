/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeDensePeriodForcing
import RiemannGaussian.SemiprimeStrassenPrefix

/-!
# Arbitrary-ratio exact index forcing by wider numerator wraps

The previous dense family restricts each numerator to two canonical
representatives. Removing that restriction allows the same public seed to
be shifted by the integral null direction (m,j,0). At the true residue,
this subtracts k times the factor quotient p/m from the exact factor index.
Pigeonhole on multiples of the seed index modulo that quotient forces a
short exact index at every factor ratio after the quadratic factor prefix.

The public wrap range has quadratic size, and the explicit family has
quartic size. One cached descriptor still generates every row's power and
recovery polynomial. Coverage is proved here; fast acquisition and the
full one-sixth bit-operation bound are not.
-/

namespace RiemannGaussian.SemiprimeWideWrapCoverage

open SemiprimeQuotientRows SemiprimeDenseRowCoverage SemiprimeDenseRowCarries
open SemiprimeDensePeriodForcing

/-- An N-only upper bound on the required nonnegative numerator wrap. -/
def wrapCap (m : ℕ) : ℕ := 2*m^2+1

/-- Keep the seed's full quadratic and shift by the public null direction.
There is no canonical-numerator restriction or factor input. -/
def wrappedRow (N m j t k : ℕ) : QuotientRow :=
  ⟨(t : ℤ)*(seedRow N m j).a-(m : ℤ)*k,
    (t : ℤ)*(seedRow N m j).b-(j : ℤ)*k,
    (t : ℤ)*(seedRow N m j).c,t,0⟩

/-- The executable full family is explicit for coverage and size accounting.
Compressed acquisition need not materialize this list, but is not priced here. -/
def wrappedRows (N m : ℕ) : List (ℕ×QuotientRow) :=
  (List.range (m-1)).flatMap fun r =>
    (List.range (m-1)).flatMap fun s =>
      (List.range (wrapCap m+1)).map fun k =>
        (r+1,wrappedRow N m (r+1) (s+1) k)

/-- Evaluate the widened two-parameter progression from the SAME public
cached seed. The wrap k is retained instead of a prescribed floor carry. -/
def wrappedValue {G : Type*} [CommGroup G] (t k : ℕ) (s : ProgressionSeed G) : G :=
  s.step^t*s.carryStep^(-(k : ℤ))

/-- Candidate recovery uses only the cached public coefficients, the
chosen positive denominator, nonnegative wrap and signed target index. -/
def wrappedRecovery {G : Type*} (N m t k : ℕ) (s : ProgressionSeed G)
    (i : ℤ) : List ℤ :=
  let a := (t : ℤ)*s.slope-(m : ℤ)*k
  let b := (t : ℤ)*s.linear-(s.residue : ℤ)*k
  integerRoots a (b*m-2*a*s.residue-(m : ℤ)^2*i) (t*N : ℕ)

/-- Every enlarged row satisfies the original exact quotient relation. -/
theorem wrappedRow_relation {N m j t k : ℕ} (hm : 0<m) (hj : j.Coprime m) :
    let z := wrappedRow N m j t k
    quotientRelation N m j z.a z.b z.c z.t := by
  have hs := denseRow_relation (N:=N) (t:=1) hm hj false
  change quotientRelation N m j (seedRow N m j).a (seedRow N m j).b
    (seedRow N m j).c 1 at hs
  simp only [wrappedRow,quotientRelation] at ⊢
  unfold quotientRelation at hs
  linear_combination (t : ℤ)*hs

/-- The exact hidden factor index changes by k copies of the factor
quotient x, rather than by a public centering carry alone. -/
theorem wrappedRow_index {N m j t k : ℕ} {p x iSeed : ℤ}
    (hcoord : p=(m : ℤ)*x+j)
    (hseed : quadratic (seedRow N m j).a (seedRow N m j).b
      (seedRow N m j).c x=p*iSeed) :
    quadratic (wrappedRow N m j t k).a (wrappedRow N m j t k).b
      (wrappedRow N m j t k).c x=p*((t : ℤ)*iSeed-(k : ℤ)*x) := by
  simp only [wrappedRow,quadratic] at ⊢
  unfold quadratic at hseed
  linear_combination (t : ℤ)*hseed+(k : ℤ)*x*hcoord

/-- Every emitted positive denominator remains informative despite its
larger numerator: its nonzero class modulo m is unchanged. -/
theorem wrappedRow_a_ne_zero {N m j t k : ℕ} (hm : 1<m)
    (hN : m.Coprime N) (hj : j.Coprime m) (ht : 0<t) (htm : t<m) :
    (wrappedRow N m j t k).a≠0 := by
  have hc := quotientSlope_coprime (by omega : 0<m) hN hj
  intro he
  have hdiv : (m : ℤ)∣(t : ℤ)*(representative N m j 1 : ℤ) := by
    refine ⟨k,?_⟩
    change (t : ℤ)*(representative N m j 1 : ℤ)-(m : ℤ)*k=0 at he
    linarith only [he]
  have hdivNat : m∣t*representative N m j 1 := by exact_mod_cast hdiv
  have hrc : m.Coprime (representative N m j 1) := by
    change Nat.gcd m ((quotientSlope N m j*1)%m)=1
    rw [Nat.mul_one,Nat.gcd_comm m ((quotientSlope N m j)%m),←Nat.gcd_rec]
    exact hc
  rw [Nat.mul_comm] at hdivNat
  have hd := hrc.dvd_of_dvd_mul_left hdivNat
  exact (not_le_of_gt htm) (Nat.le_of_dvd ht hd)

/-- The literal public family contains every specified row in its ranges. -/
theorem wrappedRow_mem {N m j t k : ℕ} (hj : 0<j) (hjm : j<m)
    (ht : 0<t) (htm : t<m) (hk : k≤wrapCap m) :
    (j,wrappedRow N m j t k)∈wrappedRows N m := by
  apply List.mem_flatMap.mpr
  refine ⟨j-1,List.mem_range.mpr (by omega),?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨t-1,List.mem_range.mpr (by omega),?_⟩
  apply List.mem_map.mpr
  refine ⟨k,List.mem_range.mpr (by omega),?_⟩
  have hj' : j-1+1=j := by omega
  have ht' : t-1+1=t := by omega
  rw [hj',ht']

/-- The sixth-power budget and completed quadratic prefix give the
asymmetric factor and quotient bounds needed for the public wrap cap. -/
theorem post_prefix_factor_bounds {p q m : ℕ} (hm : 1<m) (hpq : p≤q)
    (hprefix : m^2≤p) (hsize : p*q≤m^6) :
    p≤m^3 ∧ q≤m^4 ∧ m≤p/m ∧ p/m≤m^2 := by
  have hm₀ : 0<m := by omega
  have hp₂ : p^2≤(m^3)^2 := by
    calc
      p^2≤p*q := by nlinarith only [Nat.mul_le_mul_left p hpq]
      _≤m^6 := hsize
      _=(m^3)^2 := by ring
  have hp₃ : p≤m^3 := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp hp₂
  have hq₄ : q≤m^4 := by
    have hmul := (Nat.mul_le_mul_right q hprefix).trans hsize
    have he : m^6=m^2*m^4 := by ring
    rw [he] at hmul
    exact (Nat.mul_le_mul_left_iff (by positivity : 0<m^2)).mp hmul
  have hx₀ : m≤p/m := by
    apply (Nat.le_div_iff_mul_le hm₀).mpr
    simpa only [pow_two] using hprefix
  have hx₁ : p/m≤m^2 := by
    have hd := Nat.div_le_div_right hp₃ (c:=m)
    have he : m^3=m^2*m := by ring
    rw [he,Nat.mul_div_cancel _ hm₀] at hd
    exact hd
  exact ⟨hp₃,hq₄,hx₀,hx₁⟩

/-- The actual denominator-one factor index is nonnegative after the
quadratic prefix and is at most the public quadratic wrap cap. -/
theorem seed_index_bounds {p q m : ℕ} (hm : 1<m) (hpq : p≤q)
    (hprefix : m^2≤p) (hsize : p*q≤m^6) {iSeed : ℤ}
    (hi : (m : ℤ)^2*iSeed=(seedRow (p*q) m (p%m)).a*p+
      (seedRow (p*q) m (p%m)).b*m-
        2*(seedRow (p*q) m (p%m)).a*(p%m : ℕ)+q) :
    0 ≤ iSeed ∧ iSeed≤(wrapCap m : ℤ) := by
  obtain ⟨hp₃,hq₄,_hx₀,_hx₁⟩ := post_prefix_factor_bounds hm hpq hprefix hsize
  let a : ℤ := (seedRow (p*q) m (p%m)).a
  let b : ℤ := (seedRow (p*q) m (p%m)).b
  have ha₀ : 0≤a := by change (0 : ℤ)≤representative (p*q) m (p%m) 1; positivity
  have ha₁ : a≤m := by
    change (representative (p*q) m (p%m) 1 : ℤ)≤m
    exact_mod_cast (Nat.mod_lt _ (by omega : 0<m)).le
  have hb := abs_le.mp (denseRow_b_bound (N:=p*q) (j:=p%m) (t:=1) hm false)
  change -(m : ℤ)≤b ∧ b≤m at hb
  have hmz : (2 : ℤ)≤m := by exact_mod_cast hm
  have hjm : ((p%m : ℕ) : ℤ)≤m-1 := by
    have hh := Nat.mod_lt p (by omega : 0<m)
    omega
  have hpre : (m : ℤ)^2≤p := by exact_mod_cast hprefix
  have hqp : (p : ℤ)≤q := by exact_mod_cast hpq
  have hpz : (p : ℤ)≤(m : ℤ)^3 := by exact_mod_cast hp₃
  have hqz : (q : ℤ)≤(m : ℤ)^4 := by exact_mod_cast hq₄
  have hfactor : 0≤(p : ℤ)-2*(p%m : ℕ) := by nlinarith only [hmz,hjm,hpre]
  have hapos := mul_nonneg ha₀ hfactor
  have hblo := mul_le_mul_of_nonneg_right hb.1 (by omega : (0 : ℤ)≤m)
  have hbhi := mul_le_mul_of_nonneg_right hb.2 (by omega : (0 : ℤ)≤m)
  have hap := mul_le_mul ha₁ hpz (by positivity : (0 : ℤ)≤p)
    (by omega : (0 : ℤ)≤m)
  have haj := mul_nonneg ha₀ (by positivity : (0 : ℤ)≤(p%m : ℕ))
  change (m : ℤ)^2*iSeed=a*p+b*m-2*a*(p%m : ℕ)+q at hi
  constructor
  · nlinarith only [hi,hapos,hblo,hpre,hqp,hmz]
  · change iSeed≤(2*m^2+1 : ℕ)
    push_cast
    nlinarith only [hi,hap,hbhi,haj,hqz,hmz]

/-- The arithmetic mechanism: m multiples of one nonnegative integer
modulo a quotient x in [m,m²] force an exact signed index <2m. The wrap
is bounded independently of that unknown quotient. -/
theorem quotient_index_pigeonhole {m x C : ℕ} (hm : 1<m)
    (hx₀ : m≤x) (hx₁ : x≤m^2) {iSeed : ℤ}
    (hi₀ : 0 ≤ iSeed) (hi₁ : iSeed≤(C : ℤ)) :
    ∃ t k : ℕ, 0<t ∧ t<m ∧ k≤C ∧
      |(t : ℤ)*iSeed-(k : ℤ)*x|<(2*m : ℕ) := by
  have hxpos : 0<x := by omega
  have hcap : x≤(m-1)*(2*m) := by
    have hmz : (2 : ℤ)≤m := by exact_mod_cast hm
    have hs : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
    have hc : (m : ℤ)^2≤((m-1 : ℕ) : ℤ)*(2*m : ℕ) := by
      push_cast
      rw [hs]
      nlinarith only [hmz]
    exact hx₁.trans (by exact_mod_cast hc)
  obtain ⟨s,t,hst,htm,hclose⟩ := period_index_pigeonhole hm
    (by positivity : 0<2*m) hxpos hcap (fun t => (t : ℤ)*iSeed)
  let d : ℤ := ((t : ℤ)*iSeed)/(x : ℤ)-((s : ℤ)*iSeed)/(x : ℤ)
  have hxz : (0 : ℤ)<x := by exact_mod_cast hxpos
  have hstz : (s : ℤ)≤t := by exact_mod_cast hst.le
  have hd₀ : 0≤d := by
    have he := Int.ediv_le_ediv hxz (mul_le_mul_of_nonneg_right hstz hi₀)
    dsimp only [d]
    omega
  have htx : (t : ℤ)≤x := by omega
  have hquot : ((t : ℤ)*iSeed)/(x : ℤ) ≤ iSeed := by
    have he := Int.ediv_le_ediv hxz (mul_le_mul_of_nonneg_right htx hi₀)
    rw [Int.mul_ediv_cancel_left iSeed hxz.ne'] at he
    exact he
  have hsquot : 0≤((s : ℤ)*iSeed)/(x : ℤ) :=
    Int.ediv_nonneg (mul_nonneg (by positivity) hi₀) hxz.le
  have hd₁ : d≤C := by dsimp only [d]; omega
  let k : ℕ := d.toNat
  have hkcast : (k : ℤ)=d := Int.toNat_of_nonneg hd₀
  have hk : k≤C := by omega
  have hsdiv := Int.emod_add_mul_ediv ((s : ℤ)*iSeed) (x : ℤ)
  have htdiv := Int.emod_add_mul_ediv ((t : ℤ)*iSeed) (x : ℤ)
  have he : ((t-s : ℕ) : ℤ)*iSeed-(k : ℤ)*x=
      (t : ℤ)*iSeed%(x : ℤ)-(s : ℤ)*iSeed%(x : ℤ) := by
    rw [hkcast]
    have hT : ((t-s : ℕ) : ℤ)=(t : ℤ)-(s : ℤ) := by omega
    rw [hT]
    dsimp only [d]
    linear_combination hsdiv-htdiv
  exact ⟨t-s,k,by omega,by omega,hk,by simpa only [he] using hclose⟩

/-- Every factor ratio has an actual widened row with a small EXACT
factor index. The source uses only N and m; p and q are coverage witnesses. -/
theorem wrappedRows_index_coverage {p q m : ℕ} (hm : 1<m) (hp : 0<p)
    (hpq : p≤q) (hprefix : m^2≤p) (hN : m.Coprime (p*q))
    (hsize : p*q≤m^6) :
    ∃ (t k : ℕ) (i : ℤ),
      (p%m,wrappedRow (p*q) m (p%m) t k)∈wrappedRows (p*q) m ∧
      0<t ∧ t<m ∧ k≤wrapCap m ∧ i.natAbs<2*m ∧
      (wrappedRow (p*q) m (p%m) t k).a≠0 ∧
      quadratic (wrappedRow (p*q) m (p%m) t k).a
        (wrappedRow (p*q) m (p%m) t k).b
          (wrappedRow (p*q) m (p%m) t k).c (p/m : ℕ)=(p : ℤ)*i := by
  have hm₀ : 0<m := by omega
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hj₀ : 0<p%m := by
    by_contra! hn
    have he : p%m=0 := by omega
    simp only [he,Nat.coprime_zero_left] at hj
    omega
  obtain ⟨iSeed,hiSeed,hquadSeed⟩ := row_index_exists hp hN
    (denseRow_relation (N:=p*q) (t:=1) hm₀ hj false)
  have hden : (denseRow (p*q) m (p%m) 1 false).t=(1 : ℤ) := rfl
  rw [hden,one_mul] at hiSeed
  change (m : ℤ)^2*iSeed=(seedRow (p*q) m (p%m)).a*p+
    (seedRow (p*q) m (p%m)).b*m-2*(seedRow (p*q) m (p%m)).a*(p%m : ℕ)+q at hiSeed
  change quadratic (seedRow (p*q) m (p%m)).a (seedRow (p*q) m (p%m)).b
    (seedRow (p*q) m (p%m)).c (p/m : ℕ)=(p : ℤ)*iSeed at hquadSeed
  have hiBounds := seed_index_bounds hm hpq hprefix hsize hiSeed
  obtain ⟨_hp,_hq,hx₀,hx₁⟩ := post_prefix_factor_bounds hm hpq hprefix hsize
  obtain ⟨t,k,ht,htm,hk,hclose⟩ := quotient_index_pigeonhole hm hx₀ hx₁
    hiBounds.1 hiBounds.2
  let i : ℤ := (t : ℤ)*iSeed-(k : ℤ)*(p/m : ℕ)
  have hi : i.natAbs<2*m := by
    have hz : (i.natAbs : ℤ)<(2*m : ℕ) := by
      simpa only [Int.natCast_natAbs] using hclose
    exact_mod_cast hz
  have hcoord : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+(p%m : ℕ) := by
    have hd := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  exact ⟨t,k,i,wrappedRow_mem hj₀ (Nat.mod_lt p hm₀) ht htm hk,ht,htm,hk,hi,
    wrappedRow_a_ne_zero hm hN hj ht htm,wrappedRow_index hcoord hquadSeed⟩

/-- Every full row power is generated from the two cached public units. -/
theorem wrappedValue_eq {G : Type*} [CommGroup G] (g : G)
    (N m j t k : ℕ) :
    wrappedValue t k (progressionSeed g N m j)=
      g^giantExponent m j (wrappedRow N m j t k).a
        (wrappedRow N m j t k).b (wrappedRow N m j t k).c := by
  simp only [wrappedValue,progressionSeed,←zpow_natCast,←zpow_mul,←zpow_add]
  congr 1
  simp only [wrappedRow,giantExponent]
  ring

/-- The cached recovery formula retains the complete literal root list
of the enlarged original row, rather than a modular-index substitute. -/
theorem wrappedRecovery_eq {G : Type*} [CommGroup G] (g : G)
    (N m j t k : ℕ) (i : ℤ) :
    wrappedRecovery N m t k (progressionSeed g N m j) i=
      integerRoots (wrappedRow N m j t k).a
        ((wrappedRow N m j t k).b*m-2*(wrappedRow N m j t k).a*j-
          (m : ℤ)^2*i) (t*N : ℕ) := by
  rfl

/-- All prime-field collisions and exact integer factor recovery follow
from the quotient pigeonhole, for every factor ratio and every base. -/
theorem wrapped_prime_collision_coverage {p q m : ℕ} (hm : 1<m)
    (hp : p.Prime) (hpq : p≤q) (hprefix : m^2≤p) (hN : m.Coprime (p*q))
    (hsize : p*q≤m^6) (g : (ZMod p)ˣ) :
    ∃ (t k : ℕ) (i : ℤ),
      0<t ∧ t<m ∧ k≤wrapCap m ∧ i.natAbs<2*m ∧
      wrappedValue t k (progressionSeed g (p*q) m (p%m))=g^((m : ℤ)^2*i) ∧
      (p : ℤ)∈wrappedRecovery (p*q) m t k
        (progressionSeed g (p*q) m (p%m)) i := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨t,k,i,_hmem,ht,htm,hk,hi,ha,hquad⟩ :=
    wrappedRows_index_coverage hm hp.pos hpq hprefix hN hsize
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hrel : quotientRelation ((p : ℤ)*q) m (p%m : ℕ)
      (wrappedRow (p*q) m (p%m) t k).a (wrappedRow (p*q) m (p%m) t k).b
      (wrappedRow (p*q) m (p%m) t k).c (t : ℤ) := by
    simpa only [Nat.cast_mul,wrappedRow] using
      wrappedRow_relation (N:=p*q) (t:=t) (k:=k) (by omega : 0<m) hj
  have hcoord : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+(p%m : ℕ) := by
    have hd := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  have hperiod : g^((p : ℤ)-1)=1 := by
    have h := ZMod.units_pow_card_sub_one_eq_one p g
    have hz : g^((p-1 : ℕ) : ℤ)=1 := by simpa only [zpow_natCast] using h
    simpa only [Nat.cast_sub hp.one_le,Nat.cast_one] using hz
  have hhit := quotient_row_power_hit g hcoord hrel hquad
    (by exact_mod_cast hp.ne_zero) hperiod
  have hroot := integerRoots_complete ha (quotient_row_recovery_equation hcoord hrel hquad)
  refine ⟨t,k,i,ht,htm,hk,hi,?_,?_⟩
  · rw [wrappedValue_eq]
    exact hhit
  · rw [wrappedRecovery_eq]
    exact hroot

/-- The new value commutes with the unavailable prime-field map, while
its constructor continues to use the original public global unit. -/
theorem wrappedValue_map {G H : Type*} [CommGroup G] [CommGroup H]
    (φ : G→*H) (g : G) (N m j t k : ℕ) :
    φ (wrappedValue t k (progressionSeed g N m j))=
      wrappedValue t k (progressionSeed (φ g) N m j) := by
  rw [wrappedValue_eq,wrappedValue_eq,map_zpow]

/-- Recovery is entirely independent of the ambient group or base. -/
theorem wrappedRecovery_base_independent {G H : Type*}
    [CommGroup G] [CommGroup H] (g : G) (h : H) (N m j t k : ℕ) (i : ℤ) :
    wrappedRecovery N m t k (progressionSeed g N m j) i=
      wrappedRecovery N m t k (progressionSeed h N m j) i := by
  rw [wrappedRecovery_eq,wrappedRecovery_eq]

/-- Universal arbitrary-ratio exact-recovery coverage of the original
public cache, extended to the explicit quadratic wrap range. There is
no assumed small local period or order, separation or nonsaturation. -/
theorem public_wrapped_coverage {p q m : ℕ} (hm : 1<m)
    (hp : p.Prime) (hpq : p≤q) (hprefix : m^2≤p) (hN : m.Coprime (p*q))
    (hsize : p*q≤m^6) (g : (ZMod (p*q))ˣ) :
    let π : (ZMod (p*q))ˣ→*(ZMod p)ˣ :=
      Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
    ∃ (t k : ℕ) (i : ℤ),
      progressionSeed g (p*q) m (p%m)∈progressionSeeds g (p*q) m ∧
      0<t ∧ t<m ∧ k≤wrapCap m ∧ i.natAbs<2*m ∧
      π (wrappedValue t k (progressionSeed g (p*q) m (p%m)))=(π g)^((m : ℤ)^2*i) ∧
      (p : ℤ)∈wrappedRecovery (p*q) m t k (progressionSeed g (p*q) m (p%m)) i := by
  let π : (ZMod (p*q))ˣ→*(ZMod p)ˣ :=
    Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
  obtain ⟨t,k,i,ht,htm,hk,hi,hhit,hroot⟩ :=
    wrapped_prime_collision_coverage hm hp hpq hprefix hN hsize (π g)
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hj₀ : 0<p%m := by
    by_contra! hn
    have he : p%m=0 := by omega
    simp only [he,Nat.coprime_zero_left] at hj
    omega
  refine ⟨t,k,i,progressionSeed_mem g hj₀ (Nat.mod_lt p (by omega)),
    ht,htm,hk,hi,?_,?_⟩
  · rw [wrappedValue_map]
    exact hhit
  · rw [wrappedRecovery_base_independent g (π g)]
    exact hroot

/-- Failure of the existing complete public quadratic prefix supplies
all factor-size and inverse premises of the arbitrary-ratio coverage.
There is no hidden small-period or small-index input at this interface. -/
theorem public_wrapped_after_prefix {p q m : ℕ} (hm : 1<m)
    (hp : p.Prime) (hpq : p≤q) (hcover : m^2<p*q) (hsize : p*q≤m^6)
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q) m=none)
    (g : (ZMod (p*q))ˣ) :
    let π : (ZMod (p*q))ˣ→*(ZMod p)ˣ :=
      Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
    ∃ (t k : ℕ) (i : ℤ),
      progressionSeed g (p*q) m (p%m)∈progressionSeeds g (p*q) m ∧
      0<t ∧ t<m ∧ k≤wrapCap m ∧ i.natAbs<2*m ∧
      π (wrappedValue t k (progressionSeed g (p*q) m (p%m)))=(π g)^((m : ℤ)^2*i) ∧
      (p : ℤ)∈wrappedRecovery (p*q) m t k (progressionSeed g (p*q) m (p%m)) i := by
  have hprefix := SemiprimeStrassenPrefix.prefix_none_excludes_small_prime
    hcover hp (dvd_mul_right p q) hnone
  have hmm : m≤m^2 := by nlinarith only [hm]
  have hc := SemiprimeStrassenPrefix.prefix_none_coprime_integer
    hcover hnone (by omega : 0<m) hmm
  exact public_wrapped_coverage hm hp hpq hprefix.le hc.symm hsize g

/-- The doubled least-prime modulus still has its complete quadratic
prefix strictly below every input of public sixth-root width at least four. -/
theorem public_modulus_prefix_below_input {N : ℕ} (hN : 0<N)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth N) :
    (SemiprimeEuclidRowBudget.publicRowModulus N)^2<N := by
  let B := SemiprimeLehmanCoverage.sixthWidth N
  have hm := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm₂ := Nat.pow_le_pow_left hm.2 2
  have hb₂ : 4≤B^2 := by dsimp only [B]; nlinarith only [hB]
  have hh := Nat.mul_le_mul_right (B^2) hb₂
  have hB₄ : (2*B)^2≤B^4 := by nlinarith only [hh]
  have hstep := SemiprimeGroupCoverage.sixth_budget_above_quadratic_prefix hB
  exact hm₂.trans_lt (hB₄.trans_lt (hstep.trans
    (SemiprimeLehmanCoverage.sixthWidth_lower hN)))

/-- The arbitrary-ratio collision/recovery theorem is available at the
ACTUAL public modulus after its original complete prefix returns none.
Both factor sizes and the modulus budget are discharged from N-only data. -/
theorem actual_public_wrapped_after_prefix {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≤q) (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (g : (ZMod (p*q))ˣ) :
    let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
    let π : (ZMod (p*q))ˣ→*(ZMod p)ˣ :=
      Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
    ∃ (t k : ℕ) (i : ℤ),
      progressionSeed g (p*q) m (p%m)∈progressionSeeds g (p*q) m ∧
      0<t ∧ t<m ∧ k≤wrapCap m ∧ i.natAbs<2*m ∧
      π (wrappedValue t k (progressionSeed g (p*q) m (p%m)))=(π g)^((m : ℤ)^2*i) ∧
      (p : ℤ)∈wrappedRecovery (p*q) m t k (progressionSeed g (p*q) m (p%m)) i := by
  have hN : 0<p*q := Nat.mul_pos hp.pos hq.pos
  have hmBounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 1<SemiprimeEuclidRowBudget.publicRowModulus (p*q) := by omega
  have hbudget := (SemiprimeLehmanCoverage.sixthWidth_upper (p*q)).trans
    (Nat.pow_le_pow_left hmBounds.1 6)
  exact public_wrapped_after_prefix hm hp hpq
    (public_modulus_prefix_below_input hN hB) hbudget hnone g

/-- Exact explicit output count. The short baby axis does not make
the enlarged logical row family a linear-size constructed source. -/
theorem wrappedRows_length (N m : ℕ) :
    (wrappedRows N m).length=(m-1)^2*(wrapCap m+1) := by
  simp [wrappedRows,List.length_flatMap,pow_two]
  ring

/-- Expanding the complete widened source has quartic output size.
This is a literal-list bound, not a lower bound for compressed acquisition. -/
theorem wrappedRows_output_lower_bound (N m : ℕ) (hm : 1<m) :
    m^4≤2*(wrappedRows N m).length := by
  have hm' : m≤2*(m-1) := by omega
  have hs := Nat.pow_le_pow_left hm' 2
  have hmul := Nat.mul_le_mul_left (m^2) hs
  rw [wrappedRows_length,wrapCap]
  nlinarith only [hmul]

end RiemannGaussian.SemiprimeWideWrapCoverage
