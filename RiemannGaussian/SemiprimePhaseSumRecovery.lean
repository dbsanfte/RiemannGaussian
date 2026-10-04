/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeGlobalPhaseCancellation

/-!
# One factor-sum recovery trial for the common global phase

An integral common phase is the literal factor sum minus one: the routed
global order and the Euler period forbid any other short integer value.
An exact forced common hit has this phase, and cross-row cancellation
transfers it to any earlier verified global tag. Thus one public recovery
trial suffices before continuing with the factor-only interval reader.
The full collision acquisition and bit-operation budgets remain open.
-/

namespace RiemannGaussian.SemiprimePhaseSumRecovery

open SemiprimeQuotientRows SemiprimeDenseRowCoverage SemiprimeDenseRowCarries
open SemiprimeWideWrapCoverage SemiprimeHyperbolicWrapCoverage
open SemiprimeMergedIndexAcquisition SemiprimeForcedRowSeparation
open SemiprimeGlobalPhaseCancellation SemiprimeWrapIndexRecovery
open SemiprimeGroupSelection SemiprimeLocalOrderRouting SemiprimeCentreFreeCover
open SemiprimeLongPowerRouting SemiprimeDensePeriodForcing

/-- A signed public candidate for the literal sum, retaining the full
offset and original merged index. The reader checks division integrality. -/
def phaseSum (m t : ℕ) (δ z : ℤ) : ℤ :=
  1-δ+((m : ℤ)*z)/(t : ℤ)

/-- An integral phase sum is small regardless of whether the globally
verified row is the private factor witness. -/
theorem integral_phase_sum_bound {m t : ℕ} {δ z S : ℤ}
    (hm : 1<m) (ht : 0<t)
    (hδ : -3*(m : ℤ)^2≤δ ∧ δ≤(m : ℤ)^2)
    (hz : -4*(m : ℤ)^2≤z ∧ z<2*(m : ℤ)^2)
    (he : (m : ℤ)*z=(t : ℤ)*(S-1+δ)) : |S|≤4*(m : ℤ)^4 := by
  have htZ : (1 : ℤ)≤t := by exact_mod_cast ht
  have hmZ : (2 : ℤ)≤m := by exact_mod_cast hm
  have hzA : |z|≤4*(m : ℤ)^2 := abs_le.mpr
    (by constructor <;> nlinarith only [hz.1,hz.2,sq_nonneg (m : ℤ)])
  have hδA : |δ|≤3*(m : ℤ)^2 := abs_le.mpr
    (by constructor <;> nlinarith only [hδ.1,hδ.2,sq_nonneg (m : ℤ)])
  have hscale := mul_le_mul_of_nonneg_left hzA (by positivity : (0 : ℤ)≤m)
  have hden := mul_le_mul_of_nonneg_right htZ (abs_nonneg (S-1+δ))
  have heA := congrArg abs he
  simp only [abs_mul,abs_of_nonneg (by positivity : (0 : ℤ)≤m),
    abs_of_nonneg (by positivity : (0 : ℤ)≤t)] at heA
  have hs : |S-1+δ|≤4*(m : ℤ)^3 := by nlinarith only [hscale,hden,heA]
  have h23 : (m : ℤ)^2≤(m : ℤ)^3 := by
    have hh := mul_nonneg (by omega : (0 : ℤ)≤(m : ℤ)-1) (sq_nonneg (m : ℤ))
    nlinarith only [hh]
  have h13 : (1 : ℤ)≤(m : ℤ)^3 := by nlinarith only [h23,hmZ]
  have h34 : 2*(m : ℤ)^3≤(m : ℤ)^4 := by
    have hh := mul_nonneg (by omega : (0 : ℤ)≤(m : ℤ)-2)
      (by positivity : (0 : ℤ)≤(m : ℤ)^3)
    nlinarith only [hh]
  have htri := abs_add_le (S-1+δ) (1-δ)
  have hother := abs_sub (1 : ℤ) δ
  simp only [abs_one] at hother
  have hident : (S-1+δ)+(1-δ)=S := by ring
  rw [hident] at htri
  nlinarith only [htri,hother,hs,hδA,h23,h13,h34]

/-- Every integral common phase equals the literal factor sum. Euler
divisibility and the routed large order exclude all other short integers. -/
theorem integral_global_phase_sum {p q m j t : ℕ} {z S : ℤ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : m.Prime)
    (hsize : p*q≤m^6) (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hhit : GlobalHit (projectedUnit g m) (p*q) m j t z)
    (he : (m : ℤ)*z=(t : ℤ)*(S-1+seedOffset (p*q) m j)) :
    S=(p : ℤ)+q := by
  rcases hhit with ⟨ht,htm,hj,hjm,hz,hzm,hglobal⟩
  have hc : j.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjm)).symm
  have hd := (hit_residual_iff (projectedUnit g m) hm.pos hc z).mp hglobal
  have heq : (t : ℤ)*((p*q : ℕ)+seedOffset (p*q) m j)-(m : ℤ)*z=
      (t : ℤ)*((p*q : ℕ)+1-S) := by nlinarith only [he]
  rw [heq] at hd
  have hshort := (long_global_coprime_small hp hq hpq g hlong ht htm.le).isCoprime
  have hsignal := hshort.dvd_of_dvd_mul_left hd
  have hphi := global_order_dvd_euler hp hq hpq (projectedUnit g m)
  have hphiZ : (orderOf (projectedUnit g m) : ℤ)∣(((p-1)*(q-1) : ℕ) : ℤ) := by
    exact_mod_cast hphi
  have heuler : (((p-1)*(q-1) : ℕ) : ℤ)=(p*q : ℕ)+1-((p : ℤ)+q) := by
    simp only [Nat.cast_mul,Nat.cast_sub hp.one_le,Nat.cast_sub hq.one_le,
      Nat.cast_one]
    ring
  rw [heuler] at hphiZ
  have hdiff := hsignal.sub hphiZ
  have hident : ((p*q : ℕ)+1-S)-((p*q : ℕ)+1-((p : ℤ)+q))=(p : ℤ)+q-S := by ring
  rw [hident] at hdiff
  have hS := integral_phase_sum_bound hm.one_lt ht
    (seedOffset_bounds (N:=p*q) hm.one_lt hj hjm) ⟨hz,hzm⟩ he
  have hsum := factor_sum_bound hp hq hm.pos hsize (projectedUnit g m) hlong.2.2.2.1
  have hsumZ : (p : ℤ)+q≤2*(m : ℤ)^4 := by exact_mod_cast hsum
  have hbound := abs_sub ((p : ℤ)+q) S
  rw [abs_of_nonneg (by positivity : (0 : ℤ)≤(p : ℤ)+q)] at hbound
  have hab : |(p : ℤ)+q-S|<(orderOf (projectedUnit g m) : ℤ) := by
    have ho : 16*(m : ℤ)^4<(orderOf (projectedUnit g m) : ℤ) := by
      exact_mod_cast long_global_order_bound hp hq hpq g hlong
    nlinarith only [hbound,hS,hsumZ,ho]
  rw [←Int.natCast_natAbs] at hab
  have habN : ((p : ℤ)+q-S).natAbs<(orderOf (projectedUnit g m) : ℤ).natAbs := by
    simpa only [Int.natAbs_natCast] using
      (show ((p : ℤ)+q-S).natAbs<orderOf (projectedUnit g m) by exact_mod_cast hab)
  have hzS := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiff habN
  omega

/-- The public integral division preserves the exact phase sum equation. -/
theorem phaseSum_equation {m t : ℕ} {δ z : ℤ}
    (hd : (t : ℤ)∣(m : ℤ)*z) :
    (m : ℤ)*z=(t : ℤ)*(phaseSum m t δ z-1+δ) := by
  have he := Int.ediv_mul_cancel hd
  unfold phaseSum
  nlinarith only [he]

/-- Any integral common tag yields the actual sum, including false row
tags. The trial never needs either local order as a numerical input. -/
theorem phaseSum_eq_sum {p q m j t : ℕ} {z : ℤ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : m.Prime)
    (hsize : p*q≤m^6) (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hhit : GlobalHit (projectedUnit g m) (p*q) m j t z)
    (hd : (t : ℤ)∣(m : ℤ)*z) :
    phaseSum m t (seedOffset (p*q) m j) z=(p : ℤ)+q :=
  integral_global_phase_sum hp hq hpq hm hsize g hlong hhit (phaseSum_equation hd)

/-- The original exact forced common row has the true integral sum
phase. The proved equal-weight exception retains all integer carries. -/
theorem forced_common_phase_sum {p q m t k : ℕ} {i : ℤ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≤q) (hm : m.Prime)
    (hN : m.Coprime (p*q)) (hsize : p*q≤m^6)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (ht : 0<t) (htm : t<m) (hk : k≤2*m+1)
    (hindex : quadratic (wrappedRow (p*q) m (p%m) t k).a
      (wrappedRow (p*q) m (p%m) t k).b
      (wrappedRow (p*q) m (p%m) t k).c (p/m : ℕ)=(p : ℤ)*i)
    (hhit : (progressionSeed (projectedUnit g m) (p*q) m (p%m)).step^t=
      (commonStep (projectedUnit g m) m)^combinedIndex m (p%m) k i) :
    (m : ℤ)*combinedIndex m (p%m) k i=
      (t : ℤ)*((p : ℤ)+q-1+seedOffset (p*q) m (p%m)) := by
  have hfull := (merged_hit_iff (projectedUnit g m) (p*q) m (p%m) t k i).mpr hhit
  have hQ := congrArg
    (Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom) hfull
  rw [wrappedValue_map,map_zpow] at hQ
  change wrappedValue t k (progressionSeed (rightUnit (projectedUnit g m))
    (p*q) m (p%m))=(rightUnit (projectedUnit g m))^((m : ℤ)^2*i) at hQ
  obtain ⟨hA,hk₀⟩ := forced_common_hit_exception hp hq hpq hm hN hsize g hlong
    ht htm hk hindex hQ
  change representative (p*q) m (p%m) 1=1 at hA
  subst k
  have hseedA : (seedRow (p*q) m (p%m)).a=(1 : ℤ) := by
    change (representative (p*q) m (p%m) 1 : ℤ)=1
    rw [hA,Nat.cast_one]
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hr := wrappedRow_relation (N:=p*q) (t:=t) (k:=0) hm.pos hj
  have hrel : quotientRelation ((p : ℤ)*q) m (p%m : ℕ)
      (wrappedRow (p*q) m (p%m) t 0).a
      (wrappedRow (p*q) m (p%m) t 0).b
      (wrappedRow (p*q) m (p%m) t 0).c (t : ℤ) := by
    simpa only [Nat.cast_mul,wrappedRow] using hr
  have hcoord : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+(p%m : ℕ) := by
    have hh := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  have hscaled := scaled_quadratic_factor_sum hcoord hrel
  rw [hindex] at hscaled
  have he : (m : ℤ)^2*i=
      (t : ℤ)*p+(t : ℤ)*(seedRow (p*q) m (p%m)).b*m-
        2*(t : ℤ)*(p%m : ℕ)+(t : ℤ)*q := by
    apply mul_left_cancel₀ (by exact_mod_cast hp.ne_zero : (p : ℤ)≠0)
    simp only [wrappedRow,hseedA,Nat.cast_zero,mul_zero,sub_zero,mul_one] at hscaled
    nlinarith only [hscaled]
  unfold combinedIndex seedOffset
  simp only [hA,Nat.cast_one,Nat.cast_zero,mul_zero,add_zero]
  nlinarith only [he]

/-- A true integral sum phase transfers to any other common tag by the
exact cross-row cancellation identity. -/
theorem phase_sum_transfer {m t t₀ : ℕ} {δ δ₀ z z₀ S : ℤ} (ht : 0<t)
    (hphase : (t : ℤ)*t₀*(δ-δ₀)=(m : ℤ)*((t₀ : ℤ)*z-(t : ℤ)*z₀))
    (hs : (m : ℤ)*z=(t : ℤ)*(S-1+δ)) :
    (m : ℤ)*z₀=(t₀ : ℤ)*(S-1+δ₀) := by
  apply mul_left_cancel₀ (by exact_mod_cast ht.ne' : (t : ℤ)≠0)
  linear_combination (t₀ : ℤ)*hs+hphase

/-- One public smaller-factor candidate from a signed factor-sum guess. -/
def factorSumCandidate (N : ℕ) (S : ℤ) : ℕ :=
  let s := S.toNat
  (s-(s^2-4*N).sqrt)/2

/-- The single candidate is exact at the literal factor sum. -/
theorem factorSumCandidate_exact {p q : ℕ} (hpq : p≤q) :
    factorSumCandidate (p*q) ((p : ℤ)+q)=p := by
  unfold factorSumCandidate
  rw [←Nat.cast_add,Int.toNat_natCast]
  dsimp only
  rw [SemiprimeCommonOrder.index_discriminant_square hpq,Nat.sqrt_eq']
  have he := Nat.sub_add_cancel hpq
  omega

/-- The public phase trial constructs one sum candidate only when the
signed division is integral, then independently checks its proper GCD. -/
def recoverPhaseSum {G : Type*} (N m t : ℕ) (s : ProgressionSeed G) (z : ℤ) : Option ℕ :=
  if (t : ℤ)∣(m : ℤ)*z then
    checkedSignal N (factorSumCandidate N (phaseSum m t (cachedOffset m s) z))
  else none

/-- An arbitrary phase guess can return only a checked proper divisor. -/
theorem recoverPhaseSum_sound {G : Type*} {N m t d : ℕ}
    (s : ProgressionSeed G) (z : ℤ) (h : recoverPhaseSum N m t s z=some d) :
    ProperDivisor N d := by
  unfold recoverPhaseSum at h
  split_ifs at h
  exact checkedSignal_sound h

/-- A true sum phase supplies integral division and exactly the smaller
factor, with a single public GCD check. -/
theorem recoverPhaseSum_of_equation {G : Type*} {p q m t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≤q) (ht : 0<t)
    (s : ProgressionSeed G) (z : ℤ)
    (he : (m : ℤ)*z=(t : ℤ)*((p : ℤ)+q-1+cachedOffset m s)) :
    recoverPhaseSum (p*q) m t s z=some p := by
  have hd : (t : ℤ)∣(m : ℤ)*z := by rw [he]; exact dvd_mul_right _ _
  have hsum : phaseSum m t (cachedOffset m s) z=(p : ℤ)+q := by
    unfold phaseSum
    rw [he,Int.mul_ediv_cancel_left _ (by exact_mod_cast ht.ne' : (t : ℤ)≠0)]
    ring
  unfold recoverPhaseSum
  rw [if_pos hd,hsum,factorSumCandidate_exact hpq,checkedSignal,
    Nat.gcd_eq_right (dvd_mul_right p q),if_pos]
  exact ⟨hp.one_lt,by nlinarith only [hp.pos,hq.one_lt]⟩

/-- Every integral globally verified tag recovers the smaller factor,
even when it is a false tag for the exact factor row. -/
theorem recoverPhaseSum_integral_global {p q m j t : ℕ} {z : ℤ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : m.Prime)
    (hsize : p*q≤m^6) (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hhit : GlobalHit (projectedUnit g m) (p*q) m j t z)
    (hd : (t : ℤ)∣(m : ℤ)*z) :
    recoverPhaseSum (p*q) m t (progressionSeed (projectedUnit g m) (p*q) m j) z=some p := by
  have hs := phaseSum_eq_sum hp hq hpq.ne hm hsize g hlong hhit hd
  unfold recoverPhaseSum
  rw [if_pos hd,cachedOffset_seed,hs,factorSumCandidate_exact hpq.le,checkedSignal,
    Nat.gcd_eq_right (dvd_mul_right p q),if_pos]
  exact ⟨hp.one_lt,by nlinarith only [hp.pos,hq.one_lt]⟩

/-- A failed phase trial at a verified global tag has fractional phase
on the actual long branch. It cannot be an inexact integral sum guess. -/
theorem failed_phase_nonintegral {p q m j t : ℕ} {z : ℤ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : m.Prime)
    (hsize : p*q≤m^6) (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hhit : GlobalHit (projectedUnit g m) (p*q) m j t z)
    (hfail : recoverPhaseSum (p*q) m t
      (progressionSeed (projectedUnit g m) (p*q) m j) z=none) :
    ¬(t : ℤ)∣(m : ℤ)*z := by
  intro hd
  rw [recoverPhaseSum_integral_global hp hq hpq hm hsize g hlong hhit hd] at hfail
  cases hfail

/-- Cached source and denominator bounds are retained by every original
merged column. These are public stream properties, not successful tags. -/
theorem mergedColumn_source {G : Type*} [CommGroup G] {g : G} {N m : ℕ}
    {c : ℕ×ProgressionSeed G×Bool} (hc : c∈mergedColumns g N m) :
    0<c.1 ∧ c.1<m ∧ 1≤c.2.1.residue ∧ c.2.1.residue<m ∧
      c.2.1=progressionSeed g N m c.2.1.residue := by
  obtain ⟨s,hs,hmiddle⟩ := List.mem_flatMap.mp hc
  obtain ⟨r,hr,hpair⟩ := List.mem_flatMap.mp hmiddle
  have hbr := List.mem_range.mp hr
  have hseed := cached_seed_source hs
  rcases List.mem_cons.mp hpair with he|he
  · subst c
    exact ⟨by omega,by omega,hseed.1,hseed.2⟩
  · have he' : c=(r+1,s,true) := by simpa only [List.mem_singleton] using he
    subst c
    exact ⟨by omega,by omega,hseed.1,hseed.2⟩

/-- An original source column returning a common reader index is a
verified bounded global tag with its exact cached small offset. -/
theorem column_reader_global {N m r : ℕ} (g : (ZMod N)ˣ)
    (c : ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool) (hc : c∈mergedColumns g N m)
    (hread : recoverTaggedInterval (commonStep g m)
      (mergedTarget g m c.1 c.2.1 c.2.2) (mergedLength m) (2*m)=some (Sum.inr r)) :
    GlobalHit g N m c.2.1.residue c.1 (mergedStart m c.2.2+r) := by
  obtain ⟨ht,htm,hj,hjm,hseed⟩ := mergedColumn_source hc
  rw [hseed] at hread
  exact merged_reader_global_tag g c.2.2 ht htm hj hjm hread

/-- One exact sum phase transfers to any common source column returned
by the reader. The first public common tag need not be the forced row. -/
theorem common_column_trial_of_sum {p q m r r₀ : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (c c₀ : ℕ×ProgressionSeed ((ZMod (p*q))ˣ)×Bool)
    (hc : c∈mergedColumns (projectedUnit g m) (p*q) m)
    (hc₀ : c₀∈mergedColumns (projectedUnit g m) (p*q) m)
    (hread : recoverTaggedInterval (commonStep (projectedUnit g m) m)
      (mergedTarget (projectedUnit g m) m c.1 c.2.1 c.2.2)
      (mergedLength m) (2*m)=some (Sum.inr r))
    (hread₀ : recoverTaggedInterval (commonStep (projectedUnit g m) m)
      (mergedTarget (projectedUnit g m) m c₀.1 c₀.2.1 c₀.2.2)
      (mergedLength m) (2*m)=some (Sum.inr r₀))
    (hsum : (m : ℤ)*(mergedStart m c.2.2+r)=
      (c.1 : ℤ)*((p : ℤ)+q-1+cachedOffset m c.2.1)) :
    recoverPhaseSum (p*q) m c₀.1 c₀.2.1 (mergedStart m c₀.2.2+r₀)=some p := by
  have hglobal := column_reader_global _ c hc hread
  have hglobal₀ := column_reader_global _ c₀ hc₀ hread₀
  have hs := mergedColumn_source hc
  have hs₀ := mergedColumn_source hc₀
  have hoff : cachedOffset m c.2.1=seedOffset (p*q) m c.2.1.residue := by
    rw [hs.2.2.2.2,cachedOffset_seed]
    rfl
  have hoff₀ : cachedOffset m c₀.2.1=seedOffset (p*q) m c₀.2.1.residue := by
    rw [hs₀.2.2.2.2,cachedOffset_seed]
    rfl
  have he := long_global_phase hp hq hpq.ne hm g hlong hglobal hglobal₀
  rw [hoff] at hsum
  have hsum₀ := phase_sum_transfer hs.1 he hsum
  rw [←hoff₀] at hsum₀
  exact recoverPhaseSum_of_equation hp hq hpq.le hs₀.1 _ _ hsum₀

/-- The unchanged saturation-complete reader at one original column. -/
noncomputable def readColumn {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (c : ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool) : Option (ℕ⊕ℕ) :=
  recoverTaggedInterval (commonStep g m) (mergedTarget g m c.1 c.2.1 c.2.2)
    (mergedLength m) (2*m)

/-- An arithmetic witness column either returns a factor or preserves
its exact factor-sum phase. This is proof-side information only. -/
def InformativeColumn (p q m : ℕ) (g : (ZMod (p*q))ˣ)
    (c : ℕ×ProgressionSeed ((ZMod (p*q))ˣ)×Bool) : Prop :=
  (∃ d, readColumn g m c=some (Sum.inl d)) ∨
    ∃ r, readColumn g m c=some (Sum.inr r) ∧
      (m : ℤ)*(mergedStart m c.2.2+r)=
        (c.1 : ℤ)*((p : ℤ)+q-1+cachedOffset m c.2.1)

/-- Exact arithmetic forcing supplies an informative original public
column at every factor ratio, with all mixed-index saturation retained. -/
theorem long_informative_column {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : m.Prime)
    (hprefix : m^2≤p) (hN : m.Coprime (p*q)) (hsize : p*q≤m^6)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    ∃ c∈mergedColumns (projectedUnit g m) (p*q) m,
      InformativeColumn p q m (projectedUnit g m) c := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨t,k,i,_,ht,htm,_,hk,hi,_,hindex⟩ :=
    hyperbolicRows_index_coverage hm.one_lt hp.pos hpq.le hprefix hN hsize
  let h := projectedUnit g m
  let s := progressionSeed h (p*q) m (p%m)
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hj₀ : 0<p%m := by
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
  have hcombined := combinedIndex_bounds hm.one_lt (by omega : 1≤p%m)
    (Nat.mod_lt p hm.pos) hk hi
  obtain ⟨upper,r,hr,hz⟩ := combinedIndex_half hcombined.1 hcombined.2
  let c : ℕ×ProgressionSeed ((ZMod (p*q))ˣ)×Bool := (t,s,upper)
  have hc : c∈mergedColumns h (p*q) m :=
    mergedColumn_mem (progressionSeed_mem h hj₀ (Nat.mod_lt p hm.pos)) ht htm upper
  refine ⟨c,hc,?_⟩
  have hrP := (merged_root_iff (leftUnit h) (p*q) m (p%m) t k i upper r hz).mpr hP
  let beta := commonStep h m
  let x := mergedTarget h m t s upper
  have hPu : leftUnit x=(leftUnit beta)^r := by
    simpa only [x,s,beta,leftUnit,mergedTarget_map,commonStep,map_zpow] using hrP
  have hProot : ZMod.castHom (dvd_mul_right p q) (ZMod p) (x : ZMod (p*q))=
      (ZMod.castHom (dvd_mul_right p q) (ZMod p) (beta : ZMod (p*q)))^r := by
    have hh := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hPu
    simpa [leftUnit,RingHom.toMonoidHom] using hh
  have hperiods := long_common_periods hm.one_lt g hlong
  have hreader := recoverTaggedInterval_preserves_root hp hq hpq beta x hr
    (merged_interval_cover m) hperiods.1 hperiods.2 hProot
  change (∃ d, readColumn h m c=some (Sum.inl d)) ∨
    readColumn h m c=some (Sum.inr r) at hreader
  rcases hreader with hf|hglobal
  · exact Or.inl hf
  · have hb := column_reader_global h c hc hglobal
    have hstep := hb.2.2.2.2.2.2
    change s.step^t=(commonStep h m)^(mergedStart m upper+r) at hstep
    rw [←hz] at hstep
    have hsum := forced_common_phase_sum hp hq hpq.le hm hN hsize g hlong
      ht htm hk hindex hstep
    rw [hz] at hsum
    exact Or.inr ⟨r,hglobal,by simpa only [c,s,cachedOffset_seed] using hsum⟩

/-- Scan original columns until a factor or the first common global
index. Try its phase once; on failure use only the factor channel thereafter. -/
noncomputable def scanPhaseColumns {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    List (ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool)→Option ℕ
  | [] => none
  | c::xs => match readColumn g m c with
    | none => scanPhaseColumns g m xs
    | some (Sum.inl d) => some d
    | some (Sum.inr r) => match recoverPhaseSum N m c.1 c.2.1 (mergedStart m c.2.2+r) with
      | some d => some d
      | none => scanFactorColumns g m xs

/-- The amended scan returns only proper divisors for every input. -/
theorem scanPhaseColumns_sound {N m d : ℕ} (g : (ZMod N)ˣ)
    (xs : List (ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool))
    (hscan : scanPhaseColumns g m xs=some d) : ProperDivisor N d := by
  induction xs with
  | nil => simp only [scanPhaseColumns] at hscan; cases hscan
  | cons c xs ih =>
    simp only [scanPhaseColumns] at hscan
    split at hscan
    · exact ih hscan
    · rename_i e he
      cases hscan
      exact recoverTaggedInterval_factor_sound _ _ he
    · split at hscan
      · rename_i e he
        cases hscan
        exact recoverPhaseSum_sound _ _ he
      · exact scanFactorColumns_sound g hscan

/-- Original source membership plus an informative arithmetic witness
suffices for the once-only phase scan. A false earlier global tag is fully
accounted for: its failed phase trial excludes the witness's global branch. -/
theorem scanPhaseColumns_complete_of_witness {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (xs : List (ℕ×ProgressionSeed ((ZMod (p*q))ˣ)×Bool))
    (hsource : ∀ c∈xs, c∈mergedColumns (projectedUnit g m) (p*q) m)
    (hwitness : ∃ c∈xs, InformativeColumn p q m (projectedUnit g m) c) :
    ∃ d, scanPhaseColumns (projectedUnit g m) m xs=some d := by
  induction xs with
  | nil => obtain ⟨c,hc,_⟩ := hwitness; cases hc
  | cons c xs ih =>
    have hcsource := hsource c (List.mem_cons_self)
    have htail : ∀ w∈xs, w∈mergedColumns (projectedUnit g m) (p*q) m := by
      intro w hw
      exact hsource w (List.mem_cons_of_mem c hw)
    obtain ⟨w,hw,hinfo⟩ := hwitness
    cases he : readColumn (projectedUnit g m) m c with
    | none =>
      have hwxs : w∈xs := by
        rcases List.mem_cons.mp hw with heq|hmem
        · subst w
          rcases hinfo with ⟨d,hd⟩|⟨r,hr,_⟩
          · rw [he] at hd; cases hd
          · rw [he] at hr; cases hr
        · exact hmem
      obtain ⟨d,hd⟩ := ih htail ⟨w,hwxs,hinfo⟩
      exact ⟨d,by simp only [scanPhaseColumns,he,hd]⟩
    | some outcome =>
      cases outcome with
      | inl d => exact ⟨d,by simp only [scanPhaseColumns,he]⟩
      | inr r =>
        cases htrial : recoverPhaseSum (p*q) m c.1 c.2.1 (mergedStart m c.2.2+r) with
        | some d => exact ⟨d,by simp only [scanPhaseColumns,he,htrial]⟩
        | none =>
          rcases hinfo with ⟨d,hd⟩|⟨r',hr',hsum⟩
          · have hwxs : w∈xs := by
              rcases List.mem_cons.mp hw with heq|hmem
              · subst w
                rw [he] at hd
                cases hd
              · exact hmem
            have hfactor : recoverFactorHalf (projectedUnit g m) m w.1 w.2.1 w.2.2=some d := by
              simp only [readColumn] at hd
              simp only [recoverFactorHalf,hd]
            obtain ⟨e,he'⟩ := scanFactorColumns_succeeds_of_member (projectedUnit g m)
              w.2.1 w.2.2 hwxs hfactor
            exact ⟨e,by simp only [scanPhaseColumns,he,htrial,he']⟩
          · have hsuccess := common_column_trial_of_sum hp hq hpq hm g hlong w c
              (hsource w hw) hcsource hr' he hsum
            rw [htrial] at hsuccess
            cases hsuccess

/-- The entire original main stream is complete without a separate
short exception acquisition. Its single global phase trial is public. -/
theorem scanPhaseColumns_complete {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : m.Prime)
    (hprefix : m^2≤p) (hN : m.Coprime (p*q)) (hsize : p*q≤m^6)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    ∃ d, scanPhaseColumns (projectedUnit g m) m
      (mergedColumns (projectedUnit g m) (p*q) m)=some d :=
  scanPhaseColumns_complete_of_witness hp hq hpq hm g hlong _ (fun _ hc => hc)
    (long_informative_column hp hq hpq hm hprefix hN hsize g hlong)

/-- The actual public matched-width long route feeds the complete
once-only phase reader without a separate seed-exception precheck. -/
theorem long_public_route_phase_reader_succeeds {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      ∃ d, scanPhaseColumns h m (mergedColumns h (p*q) m)=some d ∧
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
  obtain ⟨d,hd⟩ := scanPhaseColumns_complete hp hq hpq hm hprefix.le hcop.symm
    hbudget g hlong
  exact ⟨hc,d,hd,scanPhaseColumns_sound _ _ hd⟩

/-- The same reader consumes an acquired original three-scalar jet. -/
noncomputable def readColumnJet {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (c : ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool) (jet : ZMod N×ZMod N×ZMod N) :
    Option (ℕ⊕ℕ) :=
  recoverTaggedJet (commonStep g m) (mergedTarget g m c.1 c.2.1 c.2.2)
    (mergedLength m) (2*m) jet

/-- The unchanged common polynomial and both marked derivatives supply
exactly the original reader, including different-index saturation. -/
theorem readColumnJet_exact {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (c : ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool) :
    readColumnJet g m c
      (evaluateMergedPolynomials
        (mergedPolynomials ((commonStep g m : (ZMod N)ˣ) : ZMod N) m)
        ((mergedTarget g m c.1 c.2.1 c.2.2 : (ZMod N)ˣ) : ZMod N))=readColumn g m c := by
  simp only [readColumnJet,mergedPolynomials_eval_exact,readColumn,recoverTaggedInterval]

/-- The acquired aligned whole batch makes one phase trial at its first
common index and then consumes only the factor channel of the remaining jets. -/
noncomputable def scanPhaseJetBatch {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    List ((ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool)×(ZMod N×ZMod N×ZMod N))→Option ℕ
  | [] => none
  | (c,jet)::xs => match readColumnJet g m c jet with
    | none => scanPhaseJetBatch g m xs
    | some (Sum.inl d) => some d
    | some (Sum.inr r) => match recoverPhaseSum N m c.1 c.2.1 (mergedStart m c.2.2+r) with
      | some d => some d
      | none => scanFactorJetBatch g m xs

/-- Exact aligned acquisition preserves the whole once-only controller
for any original column list, not only an assumed successful witness. -/
theorem scanPhaseJetBatch_map_exact {N m : ℕ} (g : (ZMod N)ˣ)
    (xs : List (ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool)) :
    scanPhaseJetBatch g m (xs.map fun c =>
      (c,evaluateMergedPolynomials
        (mergedPolynomials ((commonStep g m : (ZMod N)ˣ) : ZMod N) m)
        ((mergedTarget g m c.1 c.2.1 c.2.2 : (ZMod N)ˣ) : ZMod N)))=
      scanPhaseColumns g m xs := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    simp only [List.map_cons,scanPhaseJetBatch,readColumnJet_exact,scanPhaseColumns]
    cases he : readColumn g m c with
    | none => exact ih
    | some outcome =>
      cases outcome with
      | inl d => rfl
      | inr r =>
        dsimp only
        cases htrial : recoverPhaseSum N m c.1 c.2.1 (mergedStart m c.2.2+r) with
        | some d => rfl
        | none => exact scanFactorJetBatch_map_exact (m:=m) g xs

/-- The original shared whole-source jet batch equals the complete new
reader. No short exceptional-seed batch is part of this controller. -/
theorem phaseBatch_scan_exact {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    scanPhaseJetBatch g m (mergedBatchJets g m)=
      scanPhaseColumns g m (mergedColumns g N m) :=
  scanPhaseJetBatch_map_exact g _

/-- Whole shared acquisition supplies the complete actual N-only long
branch, with one sum candidate and the original saturation-complete jets. -/
theorem long_public_route_phase_batch_succeeds {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      ∃ d, scanPhaseJetBatch h m (mergedBatchJets h m)=some d ∧ ProperDivisor (p*q) d := by
  obtain ⟨hc,d,hd,hproper⟩ := long_public_route_phase_reader_succeeds hp hq hpq hB hnone hroute
  exact ⟨hc,d,by rwa [phaseBatch_scan_exact],hproper⟩

/-- The phase branch constructs one quadratic sum candidate and issues
one public candidate check exactly when its signed division is integral. -/
def phaseTrialCandidateBudget (m t : ℕ) (z : ℤ) : ℕ :=
  if (t : ℤ)∣(m : ℤ)*z then 1 else 0

/-- One phase trial has at most one candidate construction and check. -/
theorem phaseTrialCandidateBudget_le_one (m t : ℕ) (z : ℤ) :
    phaseTrialCandidateBudget m t z≤1 := by
  unfold phaseTrialCandidateBudget
  split_ifs <;> omega

/-- A failed first common-phase trial on the actual long branch spends
ZERO quadratic sum constructions and candidate checks: its phase is fractional. -/
theorem failed_common_column_candidate_budget_zero {p q m r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : m.Prime)
    (hsize : p*q≤m^6) (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (c : ℕ×ProgressionSeed ((ZMod (p*q))ˣ)×Bool)
    (hc : c∈mergedColumns (projectedUnit g m) (p*q) m)
    (hread : readColumn (projectedUnit g m) m c=some (Sum.inr r))
    (hfail : recoverPhaseSum (p*q) m c.1 c.2.1 (mergedStart m c.2.2+r)=none) :
    phaseTrialCandidateBudget m c.1 (mergedStart m c.2.2+r)=0 := by
  have hglobal := column_reader_global _ c hc hread
  have hs := mergedColumn_source hc
  rw [hs.2.2.2.2] at hfail
  have hfrac := failed_phase_nonintegral hp hq hpq hm hsize g hlong hglobal hfail
  simp only [phaseTrialCandidateBudget,if_neg hfrac]

/-- Follow the actual visited prefix of the once-only controller. Its
factor-only tail contains no additional quadratic sum candidate calls. -/
noncomputable def phaseScanCandidateBudget {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    List (ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool)→ℕ
  | [] => 0
  | c::xs => match readColumn g m c with
    | none => phaseScanCandidateBudget g m xs
    | some (Sum.inl _) => 0
    | some (Sum.inr r) => phaseTrialCandidateBudget m c.1 (mergedStart m c.2.2+r)

/-- The ENTIRE controller has at most one quadratic sum construction
and one candidate GCD check, regardless of the number of global tags.
Interval acquisition and bounded-index decoder costs are not counted. -/
theorem phaseScanCandidateBudget_le_one {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (xs : List (ℕ×ProgressionSeed ((ZMod N)ˣ)×Bool)) :
    phaseScanCandidateBudget g m xs≤1 := by
  induction xs with
  | nil => simp only [phaseScanCandidateBudget]; omega
  | cons c xs ih =>
    simp only [phaseScanCandidateBudget]
    cases he : readColumn g m c with
    | none => exact ih
    | some outcome =>
      cases outcome with
      | inl d => change 0≤1; omega
      | inr r => exact phaseTrialCandidateBudget_le_one _ _ _

end RiemannGaussian.SemiprimePhaseSumRecovery
