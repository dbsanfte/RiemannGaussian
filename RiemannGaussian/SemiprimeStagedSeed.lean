/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHead

/-!
# Raw seed screening and checked staged projection

The raw N-1 power has coprime local orders. With the public repetition
count, a factorial stage cannot send two nontrivial local components to
one simultaneously. Checking the GCD after every stage therefore exposes
a proper factor before a nontrivial raw seed can collapse globally.
Finding a raw seed within a sixth-root public scan remains a separate
unproved requirement; no universal factoring exponent is claimed here.
-/

namespace RiemannGaussian.SemiprimeStagedSeed

open SemiprimeCentreFreeCover

/-- A successor stage reuses the preceding power. -/
theorem stagedProjection_succ {G : Type*} [Monoid G] (g : G) (i L : ℕ) :
    stagedProjection g (i+1) L=(stagedProjection g i L)^((i+1)^L) := by
  simp only [stagedProjection, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-- Once the smaller prime factors have been removed, one stage cannot
annihilate both nontrivial components of coprime local order. -/
theorem factorial_step_not_both_one {G H : Type*} [Group G] [Finite G]
    [Group H] [Finite H] (g : G) (h : H) (i L : ℕ)
    (hc : (orderOf g).Coprime (orderOf h))
    (hgBound : orderOf g<2^L) (hhBound : orderOf h<2^L)
    (hg : g^((i.factorial)^L)≠1) (hh : h^((i.factorial)^L)≠1) :
    ¬(g^(((i+1).factorial)^L)=1 ∧ h^(((i+1).factorial)^L)=1) := by
  intro hnext
  have he (x : G) : x^(((i+1).factorial)^L)=
      (x^((i.factorial)^L))^((i+1)^L) := by
    rw [Nat.factorial_succ, mul_pow, Nat.mul_comm, pow_mul]
  have he' (x : H) : x^(((i+1).factorial)^L)=
      (x^((i.factorial)^L))^((i+1)^L) := by
    rw [Nat.factorial_succ, mul_pow, Nat.mul_comm, pow_mul]
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd
    (fun horder => hg (orderOf_eq_one_iff.mp horder))
  obtain ⟨s, hs, hsd⟩ := Nat.exists_prime_and_dvd
    (fun horder => hh (orderOf_eq_one_iff.mp horder))
  have hrpow : r ∣ (i+1)^L := hrd.trans
    (orderOf_dvd_of_pow_eq_one (he g ▸ hnext.1))
  have hspow : s ∣ (i+1)^L := hsd.trans
    (orderOf_dvd_of_pow_eq_one (he' h ▸ hnext.2))
  have hrle := Nat.le_of_dvd (show 0 < i+1 by omega) (hr.dvd_of_dvd_pow hrpow)
  have hsle := Nat.le_of_dvd (show 0 < i+1 by omega) (hs.dvd_of_dvd_pow hspow)
  have hrgt := factorial_projection_rough g (le_refl _) hgBound hr hrd
  have hsgt := factorial_projection_rough h (le_refl _) hhBound hs hsd
  have hrs : r=s := by omega
  have hcp := hc.of_dvd (hrd.trans (orderOf_pow_dvd _))
    (hsd.trans (orderOf_pow_dvd _))
  rw [← hrs, Nat.coprime_self] at hcp
  exact hr.ne_one hcp

/-- The public logarithmic repetition count dominates the raw order in
either prime field; no local order is an algorithm input. -/
theorem raw_order_lt_public_repetitions {p q : ℕ} (hp : p.Prime) (hq : 0<q)
    (g : (ZMod p)ˣ) : orderOf (g^(p*q-1))<2^(Nat.clog 2 (p*q+1)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hbound : orderOf (g^(p*q-1))≤p-1 :=
    Nat.le_of_dvd (by have h := hp.one_lt; omega)
      (ZMod.orderOf_units_dvd_card_sub_one _)
  have hpN : p-1<p*q+1 := by
    have hpp : p≤p*q := by nlinarith
    omega
  exact hbound.trans_lt (hpN.trans_le (Nat.le_pow_clog (by decide) _))

/-- Every stage is mapped from the same retained public raw seed. -/
theorem map_staged_raw {N r : ℕ} (hrN : r∣N) (g : (ZMod N)ˣ) (i L : ℕ) :
    Units.map (ZMod.castHom hrN (ZMod r)).toMonoidHom
      (stagedProjection (g^(N-1)) i L)=
    ((Units.map (ZMod.castHom hrN (ZMod r)).toMonoidHom g)^(N-1))^
      ((i.factorial)^L) := by
  rw [stagedProjection_eq]
  simp only [map_pow]

/-- Retain the public unit at every stage, before extracting its GCD. -/
def publicStage {N : ℕ} (g : (ZMod N)ˣ) (i : ℕ) : (ZMod N)ˣ :=
  stagedProjection (g^(N-1)) i (Nat.clog 2 (N+1))

/-- Literal public residual GCD at a charged projection stage. -/
def stageGcd {N : ℕ} (g : (ZMod N)ˣ) (i : ℕ) : ℕ :=
  N.gcd ((publicStage g i : ZMod N)-1).val

/-- A clear preceding stage rules out a globally trivial successor.
Any component which closes first must therefore expose a proper GCD. -/
theorem stage_gcd_ne_modulus_of_clear {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (g : (ZMod (p*q))ˣ) (i : ℕ) (hclear : stageGcd g i=1) :
    stageGcd g (i+1)≠p*q := by
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  let L := Nat.clog 2 (p*q+1)
  let gp := Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom g
  let gq := Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom g
  change (p*q).gcd ((stagedProjection (g^(p*q-1)) i L : (ZMod (p*q))ˣ)-1 :
    ZMod (p*q)).val=1 at hclear
  have hpClear := clear_unit_component_order_ne_one hp (dvd_mul_right p q)
    (stagedProjection (g^(p*q-1)) i L) hclear
  have hqClear := clear_unit_component_order_ne_one hq (dvd_mul_left q p)
    (stagedProjection (g^(p*q-1)) i L) hclear
  rw [map_staged_raw] at hpClear hqClear
  have hstep := factorial_step_not_both_one (gp^(p*q-1)) (gq^(p*q-1)) i L
    (SemiprimeOrderSeparation.projected_orders_coprime hp hq gp gq)
    (raw_order_lt_public_repetitions hp hq.pos gp)
    (by simpa [Nat.mul_comm] using raw_order_lt_public_repetitions hq hp.pos gq)
    (fun he => hpClear (orderOf_eq_one_iff.mpr he))
    (fun he => hqClear (orderOf_eq_one_iff.mpr he))
  intro hcollapse
  have hz := SemiprimeSourceHead.residual_zero_of_gcd_eq_modulus
    ((publicStage g (i+1) : ZMod (p*q))-1) hcollapse
  have hunit : publicStage g (i+1)=1 :=
    Units.ext (sub_eq_zero.mp hz)
  apply hstep
  constructor
  · have he := congrArg (Units.map
      (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom) hunit
    simpa only [publicStage, map_staged_raw, map_one] using he
  · have he := congrArg (Units.map
      (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom) hunit
    simpa only [publicStage, map_staged_raw, map_one] using he

/-- A globally nontrivial raw seed cannot start at the full-modulus GCD. -/
theorem raw_gcd_ne_modulus {N : ℕ} [NeZero N] (g : (ZMod N)ˣ)
    (hraw : g^(N-1)≠1) : stageGcd g 0≠N := by
  intro he
  have hz := SemiprimeSourceHead.residual_zero_of_gcd_eq_modulus
    ((publicStage g 0 : ZMod N)-1) he
  apply hraw
  have hu : publicStage g 0=1 := Units.ext (sub_eq_zero.mp hz)
  simpa only [publicStage, stagedProjection, List.range_zero, List.foldl_nil] using hu

/-- Every GCD after screening is clear unless an actual proper factor
has appeared in this same public trace. -/
theorem all_stages_clear_of_no_proper {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (g : (ZMod (p*q))ˣ) (hraw : g^(p*q-1)≠1) (B : ℕ)
    (hno : ∀ i≤B, ¬(1<stageGcd g i ∧ stageGcd g i<p*q)) :
    stageGcd g B=1 := by
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hN : 0<p*q := Nat.mul_pos hp.pos hq.pos
  have hpos (i : ℕ) : 0<stageGcd g i := Nat.gcd_pos_of_pos_left _ hN
  have hle (i : ℕ) : stageGcd g i≤p*q := Nat.gcd_le_left _ hN
  induction B with
  | zero =>
    have hnN := raw_gcd_ne_modulus g hraw
    have hn := hno 0 (le_refl _)
    have hl := hle 0
    have hp0 := hpos 0
    omega
  | succ B ih =>
    have hprev := ih (fun i hi => hno i (by omega))
    have hnN := stage_gcd_ne_modulus_of_clear hp hq g B hprev
    have hn := hno (B+1) (le_refl _)
    have hl := hle (B+1)
    have hp0 := hpos (B+1)
    omega

/-- Screening once suffices: either a staged GCD is a proper factor or
the final projected unit has clear GCD. This does not assert a short
scan always contains such a raw seed. -/
theorem public_projection_clear_or_factor {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (g : (ZMod (p*q))ˣ) (hraw : g^(p*q-1)≠1) (B : ℕ) :
    (∃ i≤B, SemiprimeGroupSelection.ProperDivisor (p*q) (stageGcd g i)) ∨
      stageGcd g B=1 := by
  by_cases he : ∃ i≤B, 1<stageGcd g i ∧ stageGcd g i<p*q
  · obtain ⟨i, hi, h1, hN⟩ := he
    exact Or.inl ⟨i, hi, h1, hN, Nat.gcd_dvd_left _ _⟩
  · right
    apply all_stages_clear_of_no_proper hp hq g hraw B
    intro i hi hh
    exact he ⟨i, hi, hh⟩

/-- The last retained stage is precisely the original public projector. -/
theorem publicStage_eq_projectedUnit {N : ℕ} (g : (ZMod N)ˣ) (B : ℕ) :
    publicStage g B=projectedUnit g B := by
  exact stagedProjection_eq _ _ _

/-- Computing all stage values uses a scan, retaining each preceding
power rather than recomputing separate factorial projections. -/
def unitTrace {N : ℕ} (g : (ZMod N)ˣ) (B : ℕ) : List (ZMod N)ˣ :=
  (List.range B).scanl (fun x i => x^((i+1)^(Nat.clog 2 (N+1)))) (g^(N-1))

/-- B power stages retain B+1 checked residual values, including raw. -/
theorem unitTrace_length {N : ℕ} (g : (ZMod N)ˣ) (B : ℕ) :
    (unitTrace g B).length=B+1 := by
  simp [unitTrace]

/-- Each scan entry is the original factorial projection at its label. -/
theorem unitTrace_eq_map {N : ℕ} (g : (ZMod N)ˣ) (B : ℕ) :
    unitTrace g B=(List.range (B+1)).map (publicStage g) := by
  apply List.ext_getElem
  · simp [unitTrace_length]
  · intro i hi hj
    have hiB : i≤B := by rw [unitTrace_length] at hi; omega
    simp only [unitTrace, List.getElem_scanl, List.take_range,
      Nat.min_eq_left hiB, List.getElem_map, List.getElem_range]
    rfl

/-- Stage residuals are literal unit-minus-one values; their GCDs are
extracted only at the checked scan. -/
def residualTrace {N : ℕ} (g : (ZMod N)ˣ) (B : ℕ) : List ℕ :=
  (unitTrace g B).map (fun u : (ZMod N)ˣ => ((u : ZMod N)-1).val)

/-- A public, checked projection scan; every returned value divides N. -/
def checkedProjection {N : ℕ} (g : (ZMod N)ˣ) (B : ℕ) : Option ℕ :=
  SemiprimeCartesianCompletion.scanProper N (residualTrace g B)

theorem checkedProjection_sound {N d B : ℕ} (g : (ZMod N)ˣ)
    (hs : checkedProjection g B=some d) : SemiprimeGroupSelection.ProperDivisor N d :=
  SemiprimeCartesianCompletion.scanProper_sound hs

/-- Only B+1 GCD queries are charged to this one checked projection.
This is an operation count, not a bit-complexity theorem. -/
theorem checkedProjection_gcd_count {N : ℕ} (g : (ZMod N)ˣ) (B : ℕ) :
    SemiprimeCartesianCompletion.scanGcdCount N (residualTrace g B)≤B+1 := by
  have h := SemiprimeCartesianCompletion.scanGcdCount_le N (residualTrace g B)
  simpa only [residualTrace, List.length_map, unitTrace_length] using h

/-- The executable retained trace supplies the clear final certificate
if its checked scan returns no factor. -/
theorem checkedProjection_none_clear {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (g : (ZMod (p*q))ˣ) (hraw : g^(p*q-1)≠1)
    (hnone : checkedProjection g B=none) : stageGcd g B=1 := by
  apply all_stages_clear_of_no_proper hp hq g hraw B
  intro i hi hproper
  have hm : ((publicStage g i : ZMod (p*q))-1).val ∈ residualTrace g B := by
    rw [residualTrace, unitTrace_eq_map, List.map_map]
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩
  have hn := (SemiprimeCartesianCompletion.scanProper_none_iff _ _).mp hnone _ hm
  change 1<(p*q).gcd ((publicStage g i : ZMod (p*q))-1).val ∧
    (p*q).gcd ((publicStage g i : ZMod (p*q))-1).val<p*q at hproper
  simp only [SemiprimeGroupSelection.checkedSignal] at hn
  simp [hproper] at hn

/-- A final scalar collapse of a screened seed forces a preceding proper
factor in the checked trace. It is not a failure of staged projection. -/
theorem checkedProjection_succeeds_of_final_kernel {p q B : ℕ}
    (hp : p.Prime) (hq : q.Prime) (g : (ZMod (p*q))ˣ)
    (hraw : g^(p*q-1)≠1) (hfinal : projectedUnit g B=1) :
    ∃ d, checkedProjection g B=some d := by
  cases he : checkedProjection g B with
  | some d => exact ⟨d, rfl⟩
  | none =>
    have hh := checkedProjection_none_clear hp hq g hraw he
    have hN : stageGcd g B=p*q := by
      simp only [stageGcd, publicStage_eq_projectedUnit, hfinal, Units.val_one,
        sub_self, ZMod.val_zero, Nat.gcd_zero_right]
    have hp1 := hp.one_lt
    have hq1 := hq.one_lt
    have hpq1 : 1<p*q := by nlinarith
    omega

/-- Raw seed usability depends only on public N and the candidate base.
It does not perform any factorial stage or construct a row. -/
def rawSeedTest (N a : ℕ) : Bool :=
  decide (a.Coprime N ∧ (a : ZMod N)^(N-1)≠1)

/-- B consecutive public candidate bases, from 2 through B+1. -/
def screenSeed (N B : ℕ) : Option ℕ :=
  (List.range' 2 B).find? (rawSeedTest N)

/-- The screen retains a usable base and its exact public range. -/
theorem screenSeed_sound {N B a : ℕ} (hs : screenSeed N B=some a) :
    2≤a ∧ a<B+2 ∧ a.Coprime N ∧ (a : ZMod N)^(N-1)≠1 := by
  have hm := List.mem_of_find?_eq_some hs
  have ht := List.find?_some hs
  have hb : 2≤a ∧ a<2+B := List.mem_range'_1.mp hm
  have hu : a.Coprime N ∧ (a : ZMod N)^(N-1)≠1 := by
    simpa only [rawSeedTest, decide_eq_true_eq] using ht
  exact ⟨hb.1, by omega, hu⟩

/-- An exhausted scan means all its unit bases lie in the raw kernel.
No theorem here excludes this outcome for a sixth-root width. -/
theorem screenSeed_none_iff (N B : ℕ) : screenSeed N B=none ↔
    ∀ a, 2≤a → a<B+2 → a.Coprime N → (a : ZMod N)^(N-1)=1 := by
  simp [screenSeed, rawSeedTest, Nat.add_comm]

/-- The raw test count stops at the first usable seed. -/
def rawScanCount (N : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: tail => 1+if rawSeedTest N a then 0 else rawScanCount N tail

theorem rawScanCount_le (N : ℕ) (bases : List ℕ) :
    rawScanCount N bases≤bases.length := by
  induction bases with
  | nil => simp [rawScanCount]
  | cons a tail ih =>
    cases ht : rawSeedTest N a <;> simp [rawScanCount, ht]
    omega

/-- At most B raw powers and B unit GCD checks precede the single
factorial projection. A short-scan coverage guarantee is still open. -/
theorem screenSeed_test_count (N B : ℕ) : rawScanCount N (List.range' 2 B)≤B := by
  simpa only [List.length_range'] using rawScanCount_le N (List.range' 2 B)

/-- The screened natural base supplies an actual public unit and a
nontrivial raw power; local orders are not additional inputs. -/
theorem screenSeed_unit_certificate {N B a : ℕ} (hs : screenSeed N B=some a) :
    ∃ g : (ZMod N)ˣ, (g : ZMod N)=(a : ZMod N) ∧ g^(N-1)≠1 := by
  obtain ⟨_, _, hc, hn⟩ := screenSeed_sound hs
  obtain ⟨g, hg⟩ := (ZMod.isUnit_iff_coprime a N).mpr hc
  refine ⟨g, hg, ?_⟩
  intro he
  apply hn
  have hv := congrArg (fun u : (ZMod N)ˣ => (u : ZMod N)) he
  simpa only [Units.val_pow_eq_pow_val, hg, Units.val_one] using hv

/-- When both field cardinalities divide a common exponent, the final
scalar power is one for every public unit. This certificate uses both
retained reductions, not an observed single-base failure. -/
theorem common_field_exponent_kernel {p q E : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (g : (ZMod (p*q))ˣ) (hpE : p-1∣E) (hqE : q-1∣E) :
    g^E=1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  apply Units.ext
  apply SemiprimeIntervalJet.eq_of_prime_reductions hp hq hpq
  · let gp := Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom g
    have hh : gp^E=1 := orderOf_dvd_iff_pow_eq_one.mp
      ((ZMod.orderOf_units_dvd_card_sub_one gp).trans hpE)
    have he := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hh
    simpa [gp, RingHom.toMonoidHom] using he
  · let gq := Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom g
    have hh : gq^E=1 := orderOf_dvd_iff_pow_eq_one.mp
      ((ZMod.orderOf_units_dvd_card_sub_one gq).trans hqE)
    have he := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hh
    simpa [gq, RingHom.toMonoidHom] using he

set_option maxRecDepth 32768 in
/-- All final projected bases collapse on the saved kernel input, even
though an earlier raw GCD can already recover a factor. -/
theorem control_all_final_bases_kernel (g : (ZMod 1373653)ˣ) :
    projectedUnit g 11=1 := by
  unfold projectedUnit
  rw [← pow_mul]
  apply common_field_exponent_kernel (p:=829) (q:=1657)
    (by norm_num) (by norm_num) (by norm_num) g <;> norm_num [Nat.clog]

set_option maxRecDepth 32768 in
/-- The raw screen's first two bases are trivial; the third exposes 829
without constructing any rows or completing the factorial projection. -/
theorem control_raw_seed_factor :
    (2 : ZMod 1373653)^(1373653-1)=1 ∧
    (3 : ZMod 1373653)^(1373653-1)=1 ∧
    (5 : ZMod 1373653)^(1373653-1)=1370338 ∧
    Nat.gcd 1373653 (1370338-1)=829 := by
  norm_num
  reduce_mod_char
  norm_num

/-- Squaring the first raw-kernel base keeps base 4 in that kernel. -/
theorem control_raw_four_kernel : (4 : ZMod 1373653)^(1373653-1)=1 := by
  have he : (4 : ZMod 1373653)=(2 : ZMod 1373653)^2 := by norm_num
  rw [he, ← pow_mul, Nat.mul_comm, pow_mul, control_raw_seed_factor.1, one_pow]

/-- A deliberately short two-base scan is exhausted on this semiprime.
This is a control of the failure branch, not a sixth-root counterexample. -/
theorem control_two_base_screen_exhausted : screenSeed 1373653 2=none := by
  change ([2, 3] : List ℕ).find? (rawSeedTest 1373653)=none
  simp [rawSeedTest, control_raw_seed_factor.1, control_raw_seed_factor.2.1]

set_option maxRecDepth 32768 in
/-- A nontrivial raw seed exposes 19 at stage 3 on 19*29, even though
the final scalar projection at width 7 is globally one. -/
theorem control_staged_factor_before_final (g : (ZMod 551)ˣ)
    (hg : (g : ZMod 551)=2) :
    stageGcd g 0=1 ∧ stageGcd g 2=1 ∧ stageGcd g 3=19 ∧
      (projectedUnit g 7 : ZMod 551)=1 := by
  simp only [stageGcd, publicStage, stagedProjection_eq, projectedUnit,
    Units.val_pow_eq_pow_val, hg]
  norm_num [Nat.clog]
  reduce_mod_char
  norm_num [ZMod.val_ofNat]

end RiemannGaussian.SemiprimeStagedSeed
