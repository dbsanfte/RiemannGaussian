/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSeedLcm

/-!
# Local-period extraction after deterministic seed routing

An above-cap global order can hide a short order in one prime field.
The existing distinct-root polynomial batch detects unequal small local
orders without materializing their Cartesian collision grid. Failure of
that batch certifies two large local orders. The raw-kernel and projected
long-period cases still require sixth-root extraction and a bit backend.
-/

namespace RiemannGaussian.SemiprimeLocalOrderRouting

open SemiprimeGroupSelection SemiprimeCartesianCompletion SemiprimeCentreFreeCover

/-- Retained reduction of the original unit to the first prime field. -/
def leftUnit {p q : ℕ} (g : (ZMod (p*q))ˣ) : (ZMod p)ˣ :=
  Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom g

/-- Retained reduction of the same original unit to the second field. -/
def rightUnit {p q : ℕ} (g : (ZMod (p*q))ˣ) : (ZMod q)ˣ :=
  Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom g

/-- The first local carrier is the retained public base modulo p. -/
theorem leftUnit_natCast {p q k : ℕ} (g : (ZMod (p*q))ˣ)
    (hg : (g : ZMod (p*q))=(k : ZMod (p*q))) :
    (leftUnit g : ZMod p)=(k : ZMod p) := by
  change ZMod.castHom (dvd_mul_right p q) (ZMod p) (g : ZMod (p*q))=_
  rw [hg, map_natCast]

/-- The second local carrier retains the same public integer base. -/
theorem rightUnit_natCast {p q k : ℕ} (g : (ZMod (p*q))ˣ)
    (hg : (g : ZMod (p*q))=(k : ZMod (p*q))) :
    (rightUnit g : ZMod q)=(k : ZMod q) := by
  change ZMod.castHom (dvd_mul_left q p) (ZMod q) (g : ZMod (p*q))=_
  rw [hg, map_natCast]

/-- CRT identifies the global order with the LCM of the two local orders.
The equality is proof-side information, not an order oracle in the scan. -/
theorem global_order_eq_lcm {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (g : (ZMod (p*q))ˣ) :
    orderOf g=Nat.lcm (orderOf (leftUnit g)) (orderOf (rightUnit g)) := by
  have hdP : orderOf (leftUnit g)∣orderOf g := by
    apply orderOf_dvd_of_pow_eq_one
    simpa only [leftUnit, map_pow, map_one] using
      congrArg (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom)
        (pow_orderOf_eq_one g)
  have hdQ : orderOf (rightUnit g)∣orderOf g := by
    apply orderOf_dvd_of_pow_eq_one
    simpa only [rightUnit, map_pow, map_one] using
      congrArg (Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom)
        (pow_orderOf_eq_one g)
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    apply Units.ext
    apply SemiprimeIntervalJet.eq_of_prime_reductions hp hq hpq
    · have hpow := orderOf_dvd_iff_pow_eq_one.mp
        (Nat.dvd_lcm_left (orderOf (leftUnit g)) (orderOf (rightUnit g)))
      have hv := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hpow
      simpa [leftUnit, RingHom.toMonoidHom] using hv
    · have hpow := orderOf_dvd_iff_pow_eq_one.mp
        (Nat.dvd_lcm_right (orderOf (leftUnit g)) (orderOf (rightUnit g)))
      have hv := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hpow
      simpa [rightUnit, RingHom.toMonoidHom] using hv
  · exact Nat.lcm_dvd hdP hdQ

/-- A factor-separating giant/baby pair is recovered from the original
deflated columns, including the second-field orientation. -/
theorem recoverShort_of_pair {p q b j i : ℕ} (hp : p.Prime) (hq : q.Prime)
    (g : (ZMod (p*q))ˣ) (hj : 1≤j) (hjb : j≤b) (hi : i<b)
    (hhit : (leftUnit g)^(b*j)=(leftUnit g)^i ∧
        (rightUnit g)^(b*j)≠(rightUnit g)^i ∨
      (rightUnit g)^(b*j)=(rightUnit g)^i ∧
        (leftUnit g)^(b*j)≠(leftUnit g)^i) :
    ∃ d, recoverShort g b=some d := by
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hx : (g^(b*j) : ZMod (p*q)) ∈
      (List.range b).map (fun a => (g^(b*(a+1)) : ZMod (p*q))) := by
    apply List.mem_map.mpr
    refine ⟨j-1, List.mem_range.mpr (by omega), ?_⟩
    have he : j-1+1=j := by omega
    rw [he]
  have ht : (g^i : ZMod (p*q)) ∈
      (List.range b).map (fun a => (g^a : ZMod (p*q))) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  apply recoverResidueList_succeeds_of_proper_pair hx ht
  rcases hhit with hhit | hhit
  · rw [separating_power_gcd hp hq g hhit.1 hhit.2]
    exact ⟨hp.one_lt, by nlinarith [hq.one_lt, hp.pos], dvd_mul_right p q⟩
  · let x : ZMod (p*q) := (g^i : ZMod (p*q))-(g^(b*j) : ZMod (p*q))
    have hqdiv : q∣x.val := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      rw [castHom_val (dvd_mul_left q p)]
      change ZMod.castHom (dvd_mul_left q p) (ZMod q)
        ((g^i : ZMod (p*q))-(g^(b*j) : ZMod (p*q)))=0
      rw [map_sub]
      apply sub_eq_zero.mpr
      have hv := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hhit.1.symm
      simpa [rightUnit, RingHom.toMonoidHom] using hv
    have hpnot : ¬p∣x.val := by
      intro hd
      have he := (ZMod.natCast_eq_zero_iff _ p).mpr hd
      rw [castHom_val (dvd_mul_right p q)] at he
      change ZMod.castHom (dvd_mul_right p q) (ZMod p)
        ((g^i : ZMod (p*q))-(g^(b*j) : ZMod (p*q)))=0 at he
      rw [map_sub, sub_eq_zero] at he
      apply hhit.2
      apply Units.ext
      simpa [leftUnit, RingHom.toMonoidHom] using he.symm
    have hgcd : (p*q).gcd x.val=q :=
      Nat.gcd_mul_of_coprime_of_dvd (hp.coprime_iff_not_dvd.mpr hpnot) hqdiv
    change ProperDivisor (p*q) ((p*q).gcd x.val)
    rw [hgcd]
    exact ⟨hq.one_lt, by nlinarith [hp.one_lt, hq.pos], dvd_mul_left q p⟩

/-- Unequal local orders suffice for extraction whenever their minimum
lies in the square cover. Coprimality and projection are unnecessary. -/
theorem recoverShort_of_unequal {p q b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (g : (ZMod (p*q))ˣ) (hb : 0<b)
    (hne : orderOf (leftUnit g)≠orderOf (rightUnit g))
    (hsmall : min (orderOf (leftUnit g)) (orderOf (rightUnit g))≤b^2) :
    ∃ d, recoverShort g b=some d := by
  obtain ⟨j, i, hj, hjb, hi, hhit⟩ :=
    SemiprimeGroupCoverage.unequal_small_periods_have_cover
      (leftUnit g) (rightUnit g) hb hne hsmall
  exact recoverShort_of_pair hp hq g hj hjb hi hhit

/-- A public power test in the other field separates the orders when
one field cardinality already lies in the short cover. Used for controls. -/
theorem recoverShort_of_small_cardinality {p q b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (g : (ZMod (p*q))ˣ) (hb : 0<b) (hsmall : p-1≤b^2)
    (hother : (rightUnit g)^(p-1)≠1) : ∃ d, recoverShort g b=some d := by
  let : Fact p.Prime := ⟨hp⟩
  have hd : orderOf (leftUnit g)∣p-1 := ZMod.orderOf_units_dvd_card_sub_one _
  have hle : orderOf (leftUnit g)≤p-1 :=
    Nat.le_of_dvd (by have h := hp.one_lt; omega) hd
  apply recoverShort_of_unequal hp hq g hb
  · intro he
    rw [he] at hd
    exact hother (orderOf_dvd_iff_pow_eq_one.mp hd)
  · exact (min_le_left _ _).trans (hle.trans hsmall)

/-- A failed original-unit batch and an above-cap global order imply
that BOTH local periods exceed the cap, without hidden input orders. -/
theorem failed_original_short_forces_long {p q b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (g : (ZMod (p*q))ˣ) (hb : 0<b)
    (hlarge : b^2<orderOf g) (hnone : recoverShort g b=none) :
    b^2<orderOf (leftUnit g) ∧ b^2<orderOf (rightUnit g) := by
  have hmin : b^2<min (orderOf (leftUnit g)) (orderOf (rightUnit g)) := by
    by_contra hn
    by_cases he : orderOf (leftUnit g)=orderOf (rightUnit g)
    · have hg := global_order_eq_lcm hp hq hpq g
      rw [he, Nat.lcm_self] at hg
      rw [hg] at hlarge
      simp only [he, min_self] at hn
      omega
    · obtain ⟨d, hd⟩ := recoverShort_of_unequal hp hq g hb he (by omega)
      rw [hnone] at hd
      contradiction
  exact ⟨hmin.trans_le (min_le_left _ _), hmin.trans_le (min_le_right _ _)⟩

/-- Literal GCD count of the existing degree-at-most-b short batch. -/
noncomputable def shortGcdCount {N : ℕ} (g : (ZMod N)ˣ) (b : ℕ) : ℕ :=
  recoveryGcdCount N
    (fun i => residueLeaves ((List.range b).map
      (fun j => (g^(b*(j+1)) : ZMod N))).toFinset (i : ZMod N))
    (evaluatedColumns ((List.range b).map
      (fun j => (g^(b*(j+1)) : ZMod N))).toFinset
      ((List.range b).map (fun i => (g^i : ZMod N))))

/-- b roots and b targets cost at most 2b GCDs, with no b-by-b scan. -/
theorem shortGcdCount_le {N : ℕ} (g : (ZMod N)ˣ) (b : ℕ) :
    shortGcdCount g b≤2*b := by
  have h := recoverResidueList_gcd_bound
    ((List.range b).map (fun j => (g^(b*(j+1)) : ZMod N)))
    ((List.range b).map (fun i => (g^i : ZMod N)))
  simpa only [shortGcdCount, List.length_map, List.length_range, two_mul] using h

/-- Each short batch supplies b source records on each axis and one
polynomial of degree at most b, even when global residues repeat. -/
theorem short_source_budget {N : ℕ} [Nontrivial (ZMod N)]
    (g : (ZMod N)ˣ) (b : ℕ) :
    ((List.range b).map (fun j => (g^(b*(j+1)) : ZMod N))).length=b ∧
    ((List.range b).map (fun i => (g^i : ZMod N))).length=b ∧
    (rootPolynomial ((List.range b).map
      (fun j => (g^(b*(j+1)) : ZMod N))).toFinset id).natDegree≤b := by
  refine ⟨by simp, by simp, ?_⟩
  calc
    _=((List.range b).map (fun j => (g^(b*(j+1)) : ZMod N))).toFinset.card :=
      Polynomial.natDegree_finsetProd_X_sub_C_eq_card _ _
    _≤((List.range b).map (fun j => (g^(b*(j+1)) : ZMod N))).length :=
      List.toFinset_card_le _
    _=b := by simp

/-- A checked result of the original short batch is always a proper factor. -/
theorem recoverShort_sound {N b d : ℕ} (g : (ZMod N)ˣ)
    (hs : recoverShort g b=some d) : ProperDivisor N d :=
  recoverResidueBatch_sound hs

/-- Keep both local period bounds, rather than only their global LCM. -/
def LocalLong {p q : ℕ} (g : (ZMod (p*q))ˣ) (b : ℕ) : Prop :=
  b^2<orderOf (leftUnit g) ∧ b^2<orderOf (rightUnit g)

/-- A kernel outcome retains the seed, both local bounds, and its common
global order certificate. The numerical order has not been computed. -/
def KernelData {p q : ℕ} (g : (ZMod (p*q))ˣ) (B : ℕ) : Prop :=
  g^(p*q-1)=1 ∧ LocalLong g (2*B) ∧ orderOf g∣p-1 ∧ orderOf g∣q-1

/-- A projected outcome retains the original seed and the public clear
GCD, two long local periods, coprimality and both rough-order certificates. -/
def LongData {p q : ℕ} (g : (ZMod (p*q))ˣ) (B : ℕ) : Prop :=
  g^(p*q-1)≠1 ∧ LocalLong g (2*B) ∧
    (p*q).gcd ((projectedUnit g B : ZMod (p*q))-1).val=1 ∧
    LocalLong (projectedUnit g B) (2*B) ∧
    (orderOf (leftUnit (projectedUnit g B))).Coprime
      (orderOf (rightUnit (projectedUnit g B))) ∧
    (∀ r, r.Prime → r∣orderOf (leftUnit (projectedUnit g B)) → B<r) ∧
    (∀ r, r.Prime → r∣orderOf (rightUnit (projectedUnit g B)) → B<r)

/-- The public projection has coprime, B-rough local orders. These
properties follow from its N-only exponents and retained field maps. -/
theorem projected_local_structure {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (g : (ZMod (p*q))ˣ) (B : ℕ) :
    (orderOf (leftUnit (projectedUnit g B))).Coprime
      (orderOf (rightUnit (projectedUnit g B))) ∧
    (∀ r, r.Prime → r∣orderOf (leftUnit (projectedUnit g B)) → B<r) ∧
    (∀ r, r.Prime → r∣orderOf (rightUnit (projectedUnit g B)) → B<r) := by
  constructor
  · have h := SemiprimeOrderSeparation.further_projection_coprime hp hq
      (leftUnit g) (rightUnit g) ((B.factorial)^(Nat.clog 2 (p*q+1)))
    simpa only [leftUnit, rightUnit, projectedUnit, map_pow] using h
  constructor
  · intro r hr hd
    apply public_projection_rough hp hq.pos (leftUnit g) hr
    simpa only [leftUnit, projectedUnit, map_pow] using hd
  · intro r hr hd
    apply public_projection_rough hq hp.pos (rightUnit g) hr
    simpa only [rightUnit, projectedUnit, map_pow, Nat.mul_comm q p] using hd

/-- The two nonfactor outcomes name explicit public integer seeds. -/
inductive Route where
  | factor (d : ℕ)
  | kernelBase (k : ℕ)
  | longBase (k : ℕ)
  | unresolved
  deriving DecidableEq

/-- A precise certificate for every output of the refined route. -/
def GoodRoute (p q B : ℕ) : Route → Prop
  | .factor d => ProperDivisor (p*q) d
  | .kernelBase k => ∃ hc : k.Coprime (p*q), KernelData (ZMod.unitOfCoprime k hc) B
  | .longBase k => ∃ hc : k.Coprime (p*q), LongData (ZMod.unitOfCoprime k hc) B
  | .unresolved => False

/-- Public refinement of one selected base. Both polynomial batches use
2B roots and 2B targets; all projection stages remain checked. -/
noncomputable def refineBase (N B k : ℕ) : Route :=
  if hc : k.Coprime N then
    let g := ZMod.unitOfCoprime k hc
    match recoverShort g (2*B) with
    | some d => .factor d
    | none =>
      if g^(N-1)=1 then .kernelBase k else
        match SemiprimeStagedSeed.checkedProjection g B with
        | some d => .factor d
        | none =>
          match recoverShort (projectedUnit g B) (2*B) with
          | some d => .factor d
          | none => .longBase k
  else .unresolved

/-- The literal refinement never has an unresolved result for a certified
above-cap unit over two distinct primes. No local orders are inputs. -/
theorem refineBase_semiprime {p q B k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (hB : 0<B) (hc : k.Coprime (p*q))
    (hlarge : (2*B)^2<orderOf (ZMod.unitOfCoprime k hc)) :
    GoodRoute p q B (refineBase (p*q) B k) := by
  let g := ZMod.unitOfCoprime k hc
  rw [refineBase, dif_pos hc]
  change GoodRoute p q B
    (match recoverShort g (2*B) with
    | some d => .factor d
    | none => if g^(p*q-1)=1 then .kernelBase k else
      match SemiprimeStagedSeed.checkedProjection g B with
      | some d => .factor d
      | none => match recoverShort (projectedUnit g B) (2*B) with
        | some d => .factor d
        | none => .longBase k)
  cases hs : recoverShort g (2*B) with
  | some d => exact recoverShort_sound g hs
  | none =>
    dsimp only
    have horiginal := failed_original_short_forces_long hp hq hpq g
      (by omega) hlarge hs
    by_cases hraw : g^(p*q-1)=1
    · rw [if_pos hraw]
      exact ⟨hc, hraw, horiginal, SemiprimeCommonOrder.kernel_global_order_common
        hp hq hpq g hraw⟩
    · rw [if_neg hraw]
      cases hprojection : SemiprimeStagedSeed.checkedProjection g B with
      | some d => exact SemiprimeStagedSeed.checkedProjection_sound g hprojection
      | none =>
        dsimp only
        have hclear : (p*q).gcd ((projectedUnit g B : ZMod (p*q))-1).val=1 := by
          have h := SemiprimeStagedSeed.checkedProjection_none_clear hp hq g hraw hprojection
          simpa only [SemiprimeStagedSeed.stageGcd,
            SemiprimeStagedSeed.publicStage_eq_projectedUnit] using h
        cases hshort : recoverShort (projectedUnit g B) (2*B) with
        | some d => exact recoverShort_sound (projectedUnit g B) hshort
        | none =>
          obtain ⟨hP, hQ⟩ := failed_projected_short_forces_long hp hq g
            (by omega : 0<2*B) hclear hshort
          have hlong : LocalLong (projectedUnit g B) (2*B) := by
            simpa only [LocalLong, leftUnit, rightUnit, pow_two] using And.intro hP hQ
          exact ⟨hc, hraw, horiginal, hclear, hlong, projected_local_structure hp hq g B⟩

/-- N-only routing with a square check before any distinct-prime transport. -/
noncomputable def publicRoute (N : ℕ) : Route :=
  match SemiprimeCommonOrder.recoverSquare N with
  | some d => .factor d
  | none =>
    match SemiprimeSeedLcm.publicRoute N with
    | .factor d => .factor d
    | .largeBase k => refineBase N (SemiprimeLehmanCoverage.sixthWidth N) k
    | .unresolved => .unresolved

/-- Universal N-only factor-or-kernel-or-projected-long routing. The
remaining certificates are explicit nonfactor outcomes, not a factorizer. -/
theorem publicRoute_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    GoodRoute p q (SemiprimeLehmanCoverage.sixthWidth (p*q)) (publicRoute (p*q)) := by
  unfold publicRoute
  cases hsquare : SemiprimeCommonOrder.recoverSquare (p*q) with
  | some d => exact SemiprimeCommonOrder.recoverSquare_sound hsquare
  | none =>
    dsimp only
    have hpq : p≠q := by
      intro he
      subst q
      have h := SemiprimeCommonOrder.recoverSquare_semiprime_square hp
      rw [pow_two] at h
      rw [hsquare] at h
      contradiction
    have hB : 0<SemiprimeLehmanCoverage.sixthWidth (p*q) := by
      have h := SemiprimeLehmanCoverage.sixthWidth_upper (p*q)
      by_contra hn
      have he : SemiprimeLehmanCoverage.sixthWidth (p*q)=0 := by omega
      rw [he] at h
      have hpos := Nat.mul_pos hp.pos hq.pos
      norm_num only [zero_pow (by decide : 6≠0)] at h
      omega
    have hseed := SemiprimeSeedLcm.publicRoute_semiprime hp hq
    cases hroute : SemiprimeSeedLcm.publicRoute (p*q) with
    | factor d =>
      rw [hroute] at hseed
      exact hseed
    | largeBase k =>
      rw [hroute] at hseed
      obtain ⟨hc, hlarge⟩ := hseed
      exact refineBase_semiprime hp hq hpq hB hc hlarge
    | unresolved =>
      rw [hroute] at hseed
      exact False.elim hseed

/-- GCDs along the actual refinement path, including both short batches
only when reached. Polynomial and bit costs are separate work categories. -/
noncomputable def refinementGcdCount {N : ℕ} (g : (ZMod N)ˣ) (B : ℕ) : ℕ :=
  shortGcdCount g (2*B) +
    match recoverShort g (2*B) with
    | some _ => 0
    | none => if g^(N-1)=1 then 0 else
      scanGcdCount N (SemiprimeStagedSeed.residualTrace g B) +
        match SemiprimeStagedSeed.checkedProjection g B with
        | some _ => 0
        | none => shortGcdCount (projectedUnit g B) (2*B)

/-- At most 9B+1 GCD queries in the added two-batch refinement. This is
an operation count, not a certificate for the polynomial or bit backend. -/
theorem refinementGcdCount_le {N : ℕ} (g : (ZMod N)ˣ) (B : ℕ) :
    refinementGcdCount g B≤9*B+1 := by
  have hfirst := shortGcdCount_le g (2*B)
  have hsecond := shortGcdCount_le (projectedUnit g B) (2*B)
  have hprojection := SemiprimeStagedSeed.checkedProjection_gcd_count g B
  unfold refinementGcdCount
  split
  · nlinarith
  · split_ifs
    · nlinarith
    · split <;> nlinarith

/-- Include the actual base-unit test as one additional GCD query. -/
noncomputable def refineBaseGcdCount (N B k : ℕ) : ℕ :=
  1 + if hc : k.Coprime N then refinementGcdCount (ZMod.unitOfCoprime k hc) B else 0

/-- The complete added base refinement, including its unit test, uses
at most 9B+2 GCD queries. The seed procedure's costs are separate. -/
theorem refineBaseGcdCount_le (N B k : ℕ) : refineBaseGcdCount N B k≤9*B+2 := by
  unfold refineBaseGcdCount
  split
  · have h := refinementGcdCount_le (ZMod.unitOfCoprime k (by assumption)) B
    omega
  · omega

/-- Base two in the saved 29*101 control has a separating local power. -/
theorem control_twenty_nine_other_power : (2 : ZMod 101)^28≠1 := by
  reduce_mod_char
  decide

/-- The above-cap base-two control is now factored by the original short
batch; the earlier bounded global-order lookup alone had exhausted. -/
theorem control_twenty_nine_short (g : (ZMod (29*101))ˣ)
    (hg : (g : ZMod (29*101))=2) : ∃ d, recoverShort g 8=some d := by
  apply recoverShort_of_small_cardinality (by norm_num) (by norm_num) g
    (by decide) (by norm_num)
  intro he
  have hv := congrArg (fun u : (ZMod 101)ˣ => (u : ZMod 101)) he
  apply control_twenty_nine_other_power
  change (ZMod.castHom (dvd_mul_left 101 29) (ZMod 101)
    (g : ZMod (29*101)))^28=1 at hv
  simpa only [hg, map_ofNat] using hv

set_option maxRecDepth 32768 in
/-- The new Mersenne seed differs across fields at the first cardinality. -/
theorem control_mersenne_other_power : (3 : ZMod 164511353)^13366≠1 := by
  reduce_mod_char
  decide

/-- The selected base three in the saved small-order obstruction has a
proper factor in its degree-230 original-unit batch. All primes and the
short-cardinality premise are checked; no numerical orders are supplied. -/
theorem control_mersenne_short (g : (ZMod (13367*164511353))ˣ)
    (hg : (g : ZMod (13367*164511353))=3) :
    ∃ d, recoverShort g 230=some d := by
  apply recoverShort_of_small_cardinality
    SemiprimeSeedLcm.control_mersenne_arithmetic.1
    SemiprimeSeedLcm.control_mersenne_arithmetic.2.1 g (by decide) (by norm_num)
  intro he
  have hv := congrArg (fun u : (ZMod 164511353)ˣ => (u : ZMod 164511353)) he
  apply control_mersenne_other_power
  change (ZMod.castHom (dvd_mul_left 164511353 13367) (ZMod 164511353)
    (g : ZMod (13367*164511353)))^13366=1 at hv
  simpa only [hg, map_ofNat] using hv

/-- Exact primes, product, width and order-cap inequalities for a retained
large-kernel control, rather than only successful factor examples. -/
theorem control_large_kernel_arithmetic :
    Nat.Prime 20543 ∧ Nat.Prime 61627 ∧ Nat.Prime 10271 ∧
      20543*61627=1266003461 ∧ 32^6<(1266003461 : ℕ) ∧
      1266003461≤33^6 ∧ (66 : ℕ)^2<10271 := by
  norm_num

set_option maxRecDepth 32768 in
/-- Public field powers verifying both orders of the large-kernel control. -/
theorem control_large_kernel_powers :
    (2 : ZMod 20543)^10271=1 ∧ (2 : ZMod 61627)^20542=1 ∧
      (2 : ZMod 61627)^10271≠1 := by
  refine ⟨?_, ?_, ?_⟩
  · reduce_mod_char
  · reduce_mod_char
  · reduce_mod_char
    decide

/-- Both local orders of the saved kernel base are verified from public
powers. Their unequal large values are not advice to the routing function. -/
theorem control_large_kernel_orders (g : (ZMod (20543*61627))ˣ)
    (hg : (g : ZMod (20543*61627))=2) :
    orderOf (leftUnit g)=10271 ∧ orderOf (rightUnit g)=20542 := by
  have hr : Nat.Prime 10271 := control_large_kernel_arithmetic.2.2.1
  let : Fact (Nat.Prime 10271) := ⟨hr⟩
  have hP := leftUnit_natCast g hg
  have hQ := rightUnit_natCast g hg
  obtain ⟨hpowP, hpowQ, hnotQ⟩ := control_large_kernel_powers
  constructor
  · apply orderOf_eq_prime
    · apply Units.ext
      simpa only [Units.val_pow_eq_pow_val, hP, Units.val_one, Nat.cast_ofNat] using hpowP
    · intro he
      have hv := congrArg (fun u : (ZMod 20543)ˣ => (u : ZMod 20543)) he
      simp only [hP, Units.val_one, Nat.cast_ofNat] at hv
      exact (by decide : (2 : ZMod 20543)≠1) hv
  · apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
    · apply Units.ext
      simpa only [Units.val_pow_eq_pow_val, hQ, Units.val_one, Nat.cast_ofNat] using hpowQ
    · intro r hrprime hrd he
      have hv := congrArg (fun u : (ZMod 61627)ˣ => (u : ZMod 61627)) he
      simp only [Units.val_pow_eq_pow_val, hQ, Units.val_one, Nat.cast_ofNat] at hv
      have hdiv : r∣2*10271 := by norm_num at hrd ⊢; exact hrd
      rcases hrprime.dvd_mul.mp hdiv with htwo | hlarge
      · have heq : r=2 := (Nat.prime_dvd_prime_iff_eq hrprime (by decide)).mp htwo
        subst r
        exact hnotQ (by simpa only [show (20542/2 : ℕ)=10271 from rfl] using hv)
      · have heq : r=10271 := (Nat.prime_dvd_prime_iff_eq hrprime hr).mp hlarge
        subst r
        exact (by decide : (2 : ZMod 61627)^2≠1)
          (by simpa only [show (20542/10271 : ℕ)=2 from rfl] using hv)

/-- A fully checked remaining kernel certificate: both local periods
exceed 4B^2. It is explicit evidence of the residual branch, not a factor. -/
theorem control_large_kernel_certificate (g : (ZMod (20543*61627))ˣ)
    (hg : (g : ZMod (20543*61627))=2) : KernelData g 33 := by
  have hp := control_large_kernel_arithmetic.1
  have hq := control_large_kernel_arithmetic.2.1
  obtain ⟨hP, hQ⟩ := control_large_kernel_orders g hg
  have hglobal : orderOf g=20542 := by
    rw [global_order_eq_lcm hp hq (by decide) g, hP, hQ]
    norm_num
  have hraw : g^(20543*61627-1)=1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hglobal]
    norm_num
  refine ⟨hraw, ?_, SemiprimeCommonOrder.kernel_global_order_common hp hq (by decide) g hraw⟩
  simp only [LocalLong, hP, hQ]
  norm_num

end RiemannGaussian.SemiprimeLocalOrderRouting
