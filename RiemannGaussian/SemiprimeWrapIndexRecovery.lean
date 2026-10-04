/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeWideWrapCoverage
import RiemannGaussian.SemiprimeSharedIntervalJet

/-!
# Recover widened numerator wraps without expanding their interval

The widened source has uniform arithmetic collision coverage. For one
fixed public residue, denominator and short target index, its wrap axis
is a geometric interval. The existing product and two derivatives retain
that wrap index. Here a public controller returns either a proper factor
or the common original wrap, keeping the latter for exact quadratic
recovery instead of discarding a whole-modulus collision.

Simple local roots follow from the rough long-order routing certificate
at the SAME width as the row modulus. The exceptional residue one cannot
be the smaller factor's residue on this branch under the sixth-power
budget. Acquiring the three scalars and searching the remaining axes,
and the full one-sixth bit-operation bound, remain open.
-/

namespace RiemannGaussian.SemiprimeWrapIndexRecovery

open SemiprimeGroupSelection SemiprimeLocalOrderRouting SemiprimeCentreFreeCover
open SemiprimeQuotientRows SemiprimeDenseRowCarries SemiprimeWideWrapCoverage
open SemiprimeIntervalJet

/-- A rough order is coprime to every positive integer at most the width. -/
theorem rough_coprime_small {d m a : ℕ} (ha : 0<a) (ham : a≤m)
    (hrough : ∀ r, r.Prime → r∣d → m<r) : d.Coprime a := by
  by_contra hn
  obtain ⟨r,hr,hrd,hra⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  have hle := (Nat.le_of_dvd ha hra).trans ham
  exact (not_le_of_gt (hrough r hr hrd)) hle

/-- The actual carry exponent preserves a rough local period away from
residue one. No numerical order is supplied to the constructor. -/
theorem rough_carry_order {G : Type*} [Group G] (g : G) {m j : ℕ}
    (hm : 0<m) (hj : 1<j) (hjm : j<m)
    (hrough : ∀ r, r.Prime → r∣orderOf g → m<r) :
    orderOf (g^((m : ℤ)*(1-(j : ℤ))))=orderOf g := by
  have hc : (orderOf g).Coprime (m*(j-1)) :=
    (rough_coprime_small hm le_rfl hrough).mul_right
      (rough_coprime_small (by omega) (by omega) hrough)
  have hjz : ((j-1 : ℕ) : ℤ)=(j : ℤ)-1 := by omega
  have he : g^((m : ℤ)*(1-(j : ℤ)))=(g^(m*(j-1)))⁻¹ := by
    simp only [←zpow_natCast,←zpow_neg]
    congr 1
    rw [Nat.cast_mul,hjz]
    ring
  rw [he,orderOf_inv,hc.orderOf_pow]

/-- The trivial carry at residue one cannot be the smaller factor's
actual residue on the matched-width long-order branch. -/
theorem long_true_residue_ne_one {p q m : ℕ} (hp : p.Prime)
    (hpq : p≤q) (hm : 1<m) (hprefix : m^2≤p) (hsize : p*q≤m^6)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) : p%m≠1 := by
  let h := projectedUnit g m
  let d := orderOf (leftUnit h)
  have hdlong : (2*m)^2<d := hlong.2.2.2.1.1
  let : Fact p.Prime := ⟨hp⟩
  have hdcard : d∣p-1 := ZMod.orderOf_units_dvd_card_sub_one (leftUnit h)
  have hdrough : ∀ r, r.Prime → r∣d → m<r := hlong.2.2.2.2.2.1
  have hcop : m.Coprime d := (rough_coprime_small (by omega) le_rfl hdrough).symm
  obtain ⟨hpup,_,_,_⟩ := post_prefix_factor_bounds hm hpq hprefix hsize
  intro hj
  have hmd : m∣p-1 := by
    have hdiv := Nat.mod_add_div p m
    refine ⟨p/m,?_⟩
    omega
  have hprod := hcop.mul_dvd_of_dvd_of_dvd hmd hdcard
  have hbound := Nat.le_of_dvd (by have hpp := hp.one_lt; omega : 0<p-1) hprod
  have hmul := Nat.mul_lt_mul_of_pos_left hdlong (by omega : 0<m)
  have hsub : p-1≤p := Nat.sub_le _ _
  nlinarith only [hm,hpup,hbound,hmul,hsub]

/-- The widened wrap interval has length below both actual carry-step
periods for every nonexceptional residue on the matched-width route. -/
theorem long_carry_periods {p q m j : ℕ} (hm : 1<m) (hj : 1<j) (hjm : j<m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    let alpha := (progressionSeed (projectedUnit g m) (p*q) m j).carryStep
    wrapCap m+1 ≤ orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      (alpha : ZMod (p*q))) ∧
    wrapCap m+1 ≤ orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      (alpha : ZMod (p*q))) := by
  have heP : orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      ((progressionSeed (projectedUnit g m) (p*q) m j).carryStep : ZMod (p*q)))=
      orderOf (leftUnit (projectedUnit g m)) := by
    change orderOf (((Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom)
      ((projectedUnit g m)^((m : ℤ)*(1-(j : ℤ)))) : (ZMod p)ˣ) : ZMod p)=_
    rw [orderOf_units,map_zpow]
    exact rough_carry_order (leftUnit (projectedUnit g m))
      (by omega) hj hjm hlong.2.2.2.2.2.1
  have heQ : orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      ((progressionSeed (projectedUnit g m) (p*q) m j).carryStep : ZMod (p*q)))=
      orderOf (rightUnit (projectedUnit g m)) := by
    change orderOf (((Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom)
      ((projectedUnit g m)^((m : ℤ)*(1-(j : ℤ)))) : (ZMod q)ˣ) : ZMod q)=_
    rw [orderOf_units,map_zpow]
    exact rough_carry_order (rightUnit (projectedUnit g m))
      (by omega) hj hjm hlong.2.2.2.2.2.2
  dsimp only
  rw [heP,heQ]
  have hP := hlong.2.2.2.1.1
  have hQ := hlong.2.2.2.1.2
  unfold wrapCap
  constructor <;> nlinarith only [hm,hP,hQ]

/-- Read three supplied scalars. A left value is a checked factor; a
right value is a checked common original interval index. Scalar correctness
is required for coverage, but every output is checked independently. -/
noncomputable def recoverTaggedJet {N : ℕ} (alpha x : (ZMod N)ˣ)
    (L b : ℕ) (jet : ZMod N × ZMod N × ZMod N) : Option (ℕ ⊕ ℕ) := by
  classical
  exact
  let P := jet.1
  let d := N.gcd P.val
  if 1<d ∧ d<N then some (Sum.inl d)
  else if P=0 then
    if hu : IsUnit ((x : ZMod N)*jet.2.1) then
      let s := -((hu.unit⁻¹ : (ZMod N)ˣ) : ZMod N)*jet.2.2
      if s.val<L ∧ (x : ZMod N)=(alpha : ZMod N)^s.val then some (Sum.inr s.val)
      else (recoverIndex s b).map Sum.inl
    else none
  else none

/-- The exact interval specification supplies its three scalars to
the public reader. Their acquisition can use a shared blocked evaluator. -/
noncomputable def recoverTaggedInterval {N : ℕ} (alpha x : (ZMod N)ˣ)
    (L b : ℕ) : Option (ℕ ⊕ ℕ) :=
  recoverTaggedJet alpha x L b
    (intervalProduct (alpha : ZMod N) (x : ZMod N) L,
      targetDerivative (alpha : ZMod N) (x : ZMod N) L,
      baseDerivative (alpha : ZMod N) (x : ZMod N) L)

/-- Every factor returned by the tag-preserving controller is proper. -/
theorem recoverTaggedInterval_factor_sound {N L b d : ℕ} (alpha x : (ZMod N)ˣ)
    (h : recoverTaggedInterval alpha x L b=some (Sum.inl d)) : ProperDivisor N d := by
  unfold recoverTaggedInterval recoverTaggedJet at h
  dsimp only at h
  split_ifs at h with hp _ _ _
  · have hd := Sum.inl.inj (Option.some.inj h)
    subst d
    exact ⟨hp.1,hp.2,Nat.gcd_dvd_left _ _⟩
  · cases h
  · obtain ⟨e,he,heq⟩ := Option.map_eq_some_iff.mp h
    cases heq
    exact SemiprimeCartesianCompletion.recoverResidueBatch_sound he

/-- Every returned index is in the original interval and is verified
against the original global power equation. -/
theorem recoverTaggedInterval_index_sound {N L b k : ℕ} (alpha x : (ZMod N)ˣ)
    (h : recoverTaggedInterval alpha x L b=some (Sum.inr k)) :
    k<L ∧ (x : ZMod N)=(alpha : ZMod N)^k := by
  unfold recoverTaggedInterval recoverTaggedJet at h
  dsimp only at h
  split_ifs at h with _ _ _ hs
  · cases h
  · have he := Sum.inr.inj (Option.some.inj h)
    simpa only [he] using hs
  · obtain ⟨_,_,he⟩ := Option.map_eq_some_iff.mp h
    cases he

/-- A simple local root is preserved completely: the public controller
either returns a factor or returns that SAME original root index. Both
mixed-index saturation and a common global root are handled. -/
theorem recoverTaggedInterval_preserves_root {p q L b k : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (alpha x : (ZMod (p*q))ˣ) (hk : k<L) (hcover : L≤b^2)
    (hLP : L≤orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      (alpha : ZMod (p*q))))
    (hLQ : L≤orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      (alpha : ZMod (p*q))))
    (hroot : ZMod.castHom (dvd_mul_right p q) (ZMod p) (x : ZMod (p*q))=
      (ZMod.castHom (dvd_mul_right p q) (ZMod p) (alpha : ZMod (p*q)))^k) :
    (∃ d, recoverTaggedInterval alpha x L b=some (Sum.inl d)) ∨
      recoverTaggedInterval alpha x L b=some (Sum.inr k) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  have hLp : L<p := hLP.trans_lt (local_unit_period_lt_prime hp (dvd_mul_right p q) alpha)
  have hLq : L<q := hLQ.trans_lt (local_unit_period_lt_prime hq (dvd_mul_left q p) alpha)
  have hzP : ZMod.castHom (dvd_mul_right p q) (ZMod p)
      (intervalProduct (alpha : ZMod (p*q)) (x : ZMod (p*q)) L)=0 := by
    rw [intervalProduct_map,intervalProduct_zero_iff]
    exact ⟨k,hk,hroot⟩
  by_cases hz : intervalProduct (alpha : ZMod (p*q)) (x : ZMod (p*q)) L=0
  · have hu : IsUnit ((x : ZMod (p*q))*
        targetDerivative (alpha : ZMod (p*q)) (x : ZMod (p*q)) L) :=
      x.isUnit.mul (saturated_targetDerivative_isUnit hp hq _ _ hLP hLQ hz)
    let s := decodedIndex (alpha : ZMod (p*q)) (x : ZMod (p*q)) L hu.unit
    have hsP : ZMod.castHom (dvd_mul_right p q) (ZMod p) s=(k : ZMod p) :=
      decodedIndex_map_root _ _ _ _ hu.unit hu.unit_spec hk hroot
    have hzQ := congrArg (ZMod.castHom (dvd_mul_left q p) (ZMod q)) hz
    rw [intervalProduct_map,map_zero,intervalProduct_zero_iff] at hzQ
    obtain ⟨l,hl,hQ⟩ := hzQ
    have hsQ : ZMod.castHom (dvd_mul_left q p) (ZMod q) s=(l : ZMod q) :=
      decodedIndex_map_root _ _ _ _ hu.unit hu.unit_spec hl hQ
    by_cases hkl : k=l
    · have hglobal : (x : ZMod (p*q))=(alpha : ZMod (p*q))^k := by
        apply eq_of_prime_reductions hp hq hpq.ne
        · simpa only [map_pow] using hroot
        · simpa only [map_pow,hkl] using hQ
      have hs : s=(k : ZMod (p*q)) := by
        exact decodedIndex_map_root (RingHom.id _) _ _ _ hu.unit hu.unit_spec hk hglobal
      have hkn : k<p*q := by nlinarith only [hk,hLp,hq.one_lt,hp.pos]
      have hval : s.val=k := by rw [hs,ZMod.val_natCast,Nat.mod_eq_of_lt hkn]
      apply Or.inr
      unfold recoverTaggedInterval recoverTaggedJet
      dsimp only
      rw [hz,ZMod.val_zero,Nat.gcd_zero_right,if_neg (by omega)]
      simp only [ite_true,dif_pos hu]
      change (if s.val<L ∧ (x : ZMod (p*q))=(alpha : ZMod (p*q))^s.val
        then some (Sum.inr s.val) else (recoverIndex s b).map Sum.inl)=_
      rw [if_pos (by simpa only [hval] using And.intro hk hglobal),hval]
    · have hlarge : ¬s.val<L := by
        intro hs
        have hsk := index_eq_of_reduction (dvd_mul_right p q) s
          (hs.trans hLp) (hk.trans hLp) hsP
        have hsl := index_eq_of_reduction (dvd_mul_left q p) s
          (hs.trans hLq) (hl.trans hLq) hsQ
        exact hkl (hsk.symm.trans hsl)
      obtain ⟨d,hd⟩ := decodedIndex_recovers_distinct_roots hp hq hk hl
        hLq.le hcover hkl _ _ hu.unit hu.unit_spec hroot hQ
      apply Or.inl
      refine ⟨d,?_⟩
      unfold recoverTaggedInterval recoverTaggedJet
      dsimp only
      rw [hz,ZMod.val_zero,Nat.gcd_zero_right,if_neg (by omega)]
      simp only [ite_true,dif_pos hu]
      change (if s.val<L ∧ (x : ZMod (p*q))=(alpha : ZMod (p*q))^s.val
        then some (Sum.inr s.val) else (recoverIndex s b).map Sum.inl)=_
      rw [if_neg (fun h => hlarge h.1),hd]
      rfl
  · have hzQ : ZMod.castHom (dvd_mul_left q p) (ZMod q)
        (intervalProduct (alpha : ZMod (p*q)) (x : ZMod (p*q)) L)≠0 := by
      intro he
      exact hz (zero_of_prime_reductions hp hq hpq.ne _ hzP he)
    have hg := separating_residue_gcd hp hq _ hzP hzQ
    apply Or.inl
    refine ⟨p,?_⟩
    unfold recoverTaggedInterval recoverTaggedJet
    dsimp only
    rw [hg,if_pos]
    exact ⟨hp.one_lt,by nlinarith only [hq.one_lt,hp.pos]⟩

/-- The public target for the geometric wrap column at a fixed signed
short index. Its construction uses the cached descriptor and global base. -/
def wrapTarget {G : Type*} [CommGroup G] (g : G) (m t : ℕ)
    (s : ProgressionSeed G) (i : ℤ) : G := s.step^t*g^(-((m : ℤ)^2*i))

/-- The column root equation is exactly the original row-target hit,
including its full wrap and signed factor index. -/
theorem wrapTarget_eq_iff {G : Type*} [CommGroup G] (g : G) (m t k : ℕ)
    (s : ProgressionSeed G) (i : ℤ) :
    wrapTarget g m t s i=s.carryStep^k ↔ wrappedValue t k s=g^((m : ℤ)^2*i) := by
  simp only [wrapTarget,wrappedValue,zpow_neg,zpow_natCast,mul_inv_eq_iff_eq_mul]
  rw [mul_comm (s.carryStep^k)]

/-- Checked quadratic candidates are read without an assumed candidate
soundness theorem. Every returned integer is validated by a proper GCD. -/
def recoverCandidates (N : ℕ) : List ℤ → Option ℕ
  | [] => none
  | a::as => match checkedSignal N a.natAbs with
    | some d => some d
    | none => recoverCandidates N as

/-- The public candidate reader returns only proper divisors. -/
theorem recoverCandidates_sound {N d : ℕ} {xs : List ℤ}
    (h : recoverCandidates N xs=some d) : ProperDivisor N d := by
  induction xs with
  | nil => simp only [recoverCandidates] at h; cases h
  | cons a as ih =>
    simp only [recoverCandidates] at h
    split at h
    · rename_i e he
      cases h
      exact checkedSignal_sound he
    · exact ih h

/-- A proved positive proper divisor in the full integer-root list is
enough for the checked reader to succeed, even if another candidate is inexact. -/
theorem recoverCandidates_succeeds {N p : ℕ} {xs : List ℤ}
    (hp : ProperDivisor N p) (hmem : (p : ℤ)∈xs) :
    ∃ d, recoverCandidates N xs=some d := by
  have hc : checkedSignal N p=some p := by
    unfold checkedSignal
    rw [Nat.gcd_eq_right hp.2.2,if_pos ⟨hp.1,hp.2.1⟩]
  induction xs with
  | nil => simp only [List.not_mem_nil] at hmem
  | cons a as ih =>
    by_cases he : checkedSignal N a.natAbs=none
    · have htail : (p : ℤ)∈as := by
        rcases List.mem_cons.mp hmem with ha|ha
        · subst a
          simp only [Int.natAbs_natCast,hc,Option.some_ne_none] at he
        · exact ha
      obtain ⟨d,hd⟩ := ih htail
      exact ⟨d,by simpa only [recoverCandidates,he] using hd⟩
    · obtain ⟨d,hd⟩ := Option.ne_none_iff_exists'.mp he
      exact ⟨d,by simp only [recoverCandidates,hd]⟩

/-- Decode one whole wrap column from three scalars. A common wrap is
retained for the actual quadratic candidate list instead of being discarded. -/
noncomputable def recoverWrapColumn {N : ℕ} (g : (ZMod N)ˣ) (m t : ℕ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (i : ℤ) : Option ℕ :=
  match recoverTaggedInterval s.carryStep (wrapTarget g m t s i) (wrapCap m+1) (2*m) with
  | none => none
  | some (Sum.inl d) => some d
  | some (Sum.inr k) => recoverCandidates N (wrappedRecovery N m t k s i)

/-- One column returns only a checked proper factor, through either the
interval's separating index or the common wrap's exact quadratic. -/
theorem recoverWrapColumn_sound {N m t d : ℕ} (g : (ZMod N)ˣ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (i : ℤ)
    (h : recoverWrapColumn g m t s i=some d) : ProperDivisor N d := by
  unfold recoverWrapColumn at h
  split at h
  · cases h
  · rename_i e he
    cases h
    exact recoverTaggedInterval_factor_sound _ _ he
  · exact recoverCandidates_sound h

/-- The literal integer-root reader tests at most two candidates for
any recovered common wrap. This is a list-size charge, not a bit cost. -/
theorem wrappedRecovery_length_le_two {G : Type*} (N m t k : ℕ)
    (s : ProgressionSeed G) (i : ℤ) : (wrappedRecovery N m t k s i).length≤2 := by
  unfold wrappedRecovery integerRoots
  dsimp only
  split_ifs <;> simp

/-- The quadratic wrap interval is covered by the existing short-index
batch at width 2m. -/
theorem wrap_interval_cover {m : ℕ} (hm : 1<m) : wrapCap m+1≤(2*m)^2 := by
  unfold wrapCap
  nlinarith only [hm]

/-- The existing separating-index stage uses at most 2m roots, 2m
points and 4m GCD queries. Polynomial acquisition remains unpriced. -/
theorem wrap_index_stage_bounds {N m : ℕ} (s : ZMod N) :
    (indexRoots N (2*m)).length=2*m ∧
    (indexTargets s (2*m)).length=2*m ∧
    SemiprimeCartesianCompletion.recoveryGcdCount N
      (fun i => SemiprimeCartesianCompletion.residueLeaves (indexRoots N (2*m)).toFinset
        (i : ZMod N))
      (SemiprimeCartesianCompletion.evaluatedColumns (indexRoots N (2*m)).toFinset
        (indexTargets s (2*m)))≤4*m := by
  obtain ⟨hr,ht⟩ := index_input_lengths s (2*m)
  exact ⟨hr,ht,by simpa only [←Nat.mul_assoc,Nat.reduceMul] using index_recovery_gcd_bound s (2*m)⟩

/-- Normalize the original row difference by a public unit. This retains
its exact GCD, including a saturated or whole-modulus collision. -/
theorem wrap_residual_identity {N : ℕ} (g : (ZMod N)ˣ) (m t k : ℕ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (i : ℤ) :
    ((wrappedValue t k s : (ZMod N)ˣ) : ZMod N)-
      ((g^((m : ℤ)^2*i) : (ZMod N)ˣ) : ZMod N)=
      ((s.carryStep^(-(k : ℤ))*g^((m : ℤ)^2*i) : (ZMod N)ˣ) : ZMod N)*
        (((wrapTarget g m t s i : (ZMod N)ˣ) : ZMod N)-(s.carryStep : ZMod N)^k) := by
  let phase := s.carryStep^(-(k : ℤ))*g^((m : ℤ)^2*i)
  have ht : phase*wrapTarget g m t s i=wrappedValue t k s := by
    dsimp only [phase,wrapTarget,wrappedValue]
    calc
      s.carryStep^(-(k : ℤ))*g^((m : ℤ)^2*i)*(s.step^t*g^(-((m : ℤ)^2*i)))=
        s.step^t*s.carryStep^(-(k : ℤ))*(g^((m : ℤ)^2*i)*g^(-((m : ℤ)^2*i))) := by ac_rfl
      _=s.step^t*s.carryStep^(-(k : ℤ)) := by
        rw [←zpow_add,add_neg_cancel,zpow_zero,mul_one]
  have hb : phase*s.carryStep^k=g^((m : ℤ)^2*i) := by
    dsimp only [phase]
    simp only [zpow_neg,zpow_natCast]
    calc
      (s.carryStep^k)⁻¹*g^((m : ℤ)^2*i)*s.carryStep^k=
        g^((m : ℤ)^2*i)*((s.carryStep^k)⁻¹*s.carryStep^k) := by ac_rfl
      _=g^((m : ℤ)^2*i) := by rw [inv_mul_cancel,mul_one]
  have htval := congrArg (fun u : (ZMod N)ˣ => (u : ZMod N)) ht.symm
  have hbval := congrArg (fun u : (ZMod N)ˣ => (u : ZMod N)) hb.symm
  simp only [Units.val_mul] at htval
  simp only [Units.val_mul,Units.val_pow_eq_pow_val] at hbval
  calc
    _=(phase : ZMod N)*((wrapTarget g m t s i : (ZMod N)ˣ) : ZMod N)-
        (phase : ZMod N)*(s.carryStep : ZMod N)^k := congrArg₂ (·-·) htval hbval
    _=_ := by ring

/-- The repository's exact unit cancellation applies to the entire
widened row residual; no zero-union information is replaced by a sum. -/
theorem wrap_residual_gcd {N : ℕ} (g : (ZMod N)ˣ) (m t k : ℕ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (i : ℤ) :
    N.gcd (((wrappedValue t k s : (ZMod N)ˣ) : ZMod N)-
      ((g^((m : ℤ)^2*i) : (ZMod N)ˣ) : ZMod N)).val=
      N.gcd (((wrapTarget g m t s i : (ZMod N)ˣ) : ZMod N)-
        (s.carryStep : ZMod N)^k).val := by
  rw [wrap_residual_identity]
  exact SemiprimeRHCancellation.unit_mul_gcd_eq _ _

/-- A projected original hit is the corresponding simple local wrap
root. The factor map is used only in this proof, never by the controller. -/
theorem wrapTarget_map_root {G H : Type*} [CommGroup G] [CommGroup H]
    (φ : G→*H) (g : G) (m t k : ℕ) (s : ProgressionSeed G) (i : ℤ)
    (hhit : φ (wrappedValue t k s)=(φ g)^((m : ℤ)^2*i)) :
    φ (wrapTarget g m t s i)=(φ s.carryStep)^k := by
  simp only [wrappedValue,map_mul,zpow_neg,zpow_natCast,map_inv,map_pow,
    mul_inv_eq_iff_eq_mul] at hhit
  simp only [wrapTarget,map_mul,zpow_neg,map_inv,map_pow,map_zpow,mul_inv_eq_iff_eq_mul]
  simpa only [mul_comm] using hhit

/-- One fixed column preserves any proved exact row witness under its
simple-period certificates. It does not expand the quadratic wrap axis. -/
theorem recoverWrapColumn_succeeds_of_exact_hit {p q m t k : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : 1<m)
    (g : (ZMod (p*q))ˣ) (s : ProgressionSeed ((ZMod (p*q))ˣ)) (i : ℤ)
    (hk : k≤wrapCap m)
    (hLP : wrapCap m+1≤orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      (s.carryStep : ZMod (p*q))))
    (hLQ : wrapCap m+1≤orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      (s.carryStep : ZMod (p*q))))
    (hhit : (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom)
      (wrappedValue t k s)=
        ((Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom) g)^
          ((m : ℤ)^2*i))
    (hroot : (p : ℤ)∈wrappedRecovery (p*q) m t k s i) :
    ∃ d, recoverWrapColumn g m t s i=some d := by
  have hr := wrapTarget_map_root
    (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom) g m t k s i hhit
  have hrval := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hr
  simp only [Units.coe_map,Units.val_pow_eq_pow_val] at hrval
  have hd := recoverTaggedInterval_preserves_root hp hq hpq _ _ (by omega : k<wrapCap m+1)
    (wrap_interval_cover hm) hLP hLQ hrval
  rcases hd with ⟨d,hd⟩|hd
  · exact ⟨d,by simp only [recoverWrapColumn,hd]⟩
  · have hproper : ProperDivisor (p*q) p :=
      ⟨hp.one_lt,by nlinarith only [hq.one_lt,hp.pos],dvd_mul_right p q⟩
    obtain ⟨d,he⟩ := recoverCandidates_succeeds hproper hroot
    exact ⟨d,by simpa only [recoverWrapColumn,hd] using he⟩

/-- Every factor ratio after the actual complete prefix has a recoverable
column on the matched-width projected-long branch. All periods and the
exceptional-residue exclusion are proved from that routing certificate. -/
theorem exists_recoverable_wrapped_column {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : 1<m)
    (hcover : m^2<p*q) (hsize : p*q≤m^6)
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q) m=none)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    let h := projectedUnit g m
    ∃ (t : ℕ) (i : ℤ),
      progressionSeed h (p*q) m (p%m)∈progressionSeeds h (p*q) m ∧
      0<t ∧ t<m ∧ i.natAbs<2*m ∧
      ∃ d, recoverWrapColumn h m t (progressionSeed h (p*q) m (p%m)) i=some d := by
  have hprefix := SemiprimeStrassenPrefix.prefix_none_excludes_small_prime
    hcover hp (dvd_mul_right p q) hnone
  have hmm : m≤m^2 := by nlinarith only [hm]
  have hcop := SemiprimeStrassenPrefix.prefix_none_coprime_integer
    hcover hnone (by omega : 0<m) hmm
  have hjcop : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hcop.symm.of_dvd_right (dvd_mul_right p q)
  have hjpos : 0<p%m := by
    by_contra! hn
    have he : p%m=0 := by omega
    simp only [he,Nat.coprime_zero_left] at hjcop
    omega
  have hj : 1<p%m := by
    have he := long_true_residue_ne_one hp hpq.le hm hprefix.le hsize g hlong
    omega
  have hperiods := long_carry_periods hm hj (Nat.mod_lt p (by omega)) g hlong
  obtain ⟨t,k,i,hmem,ht,htm,hk,hi,hhit,hroot⟩ :=
    public_wrapped_after_prefix hm hp hpq.le hcover hsize hnone (projectedUnit g m)
  refine ⟨t,i,hmem,ht,htm,hi,?_⟩
  exact recoverWrapColumn_succeeds_of_exact_hit hp hq hpq hm _ _ _ hk
    hperiods.1 hperiods.2 hhit hroot

/-- The actual public row modulus has a recoverable widened column when
the public refinement is performed at that SAME modulus. The old route
at sixthWidth cannot silently substitute for this certificate. -/
theorem actual_public_recoverable_wrapped_column {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (g : (ZMod (p*q))ˣ)
    (hlong : LongData g (SemiprimeEuclidRowBudget.publicRowModulus (p*q))) :
    let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
    let h := projectedUnit g m
    ∃ (t : ℕ) (i : ℤ),
      progressionSeed h (p*q) m (p%m)∈progressionSeeds h (p*q) m ∧
      0<t ∧ t<m ∧ i.natAbs<2*m ∧
      ∃ d, recoverWrapColumn h m t (progressionSeed h (p*q) m (p%m)) i=some d := by
  have hN := Nat.mul_pos hp.pos hq.pos
  have hmBounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 1<SemiprimeEuclidRowBudget.publicRowModulus (p*q) := by omega
  have hbudget := (SemiprimeLehmanCoverage.sixthWidth_upper (p*q)).trans
    (Nat.pow_le_pow_left hmBounds.1 6)
  exact exists_recoverable_wrapped_column hp hq hpq hm
    (public_modulus_prefix_below_input hN hB) hbudget hnone g hlong

/-- The existing seed route only needs the complete prefix below the
input, rather than the selected width being its exact sixth root. This
permits the actual least-prime row modulus without changing the seed loop. -/
theorem seed_route_with_prefix_bound {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≤q) (hm : 4≤m)
    (hsize : p*q≤m^6) (hcover : m^2<p*q) :
    SemiprimeSeedLcm.GoodRoute (p*q) (2*m) (SemiprimeSeedLcm.routeByWidth (p*q) m) := by
  unfold SemiprimeSeedLcm.routeByWidth
  rw [if_neg (by omega)]
  cases hsquare : SemiprimeCommonOrder.recoverSquare (p*q) with
  | some d => exact SemiprimeCommonOrder.recoverSquare_sound hsquare
  | none =>
    dsimp only
    cases hprefix : SemiprimeStrassenPrefix.factorPrefix (p*q) m with
    | some d => exact SemiprimeStrassenPrefix.prefix_sound hprefix
    | none =>
      dsimp only
      apply SemiprimeSeedLcm.seedLoop_progress hp hq hpq (by omega) hsize
        hcover hprefix (by decide) (one_dvd _) (one_dvd _)
      simpa only [mul_one] using Nat.le_pow_clog (by decide : 1<2) m

/-- Run the existing N-only seed selection and refinement at the actual
row modulus, so the retained long certificate has the required width. -/
noncomputable def routeAtRowModulus (N : ℕ) : SemiprimeLocalOrderRouting.Route :=
  let m := SemiprimeEuclidRowBudget.publicRowModulus N
  match SemiprimeSeedLcm.routeByWidth N m with
  | .factor d => .factor d
  | .largeBase k => refineBase N m k
  | .unresolved => .unresolved

/-- The matched-width public route returns a proper factor, kernel
certificate or long certificate; there is no assumed base-selection oracle. -/
theorem routeAtRowModulus_semiprime {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q)) :
    SemiprimeLocalOrderRouting.GoodRoute p q
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)) (routeAtRowModulus (p*q)) := by
  have hN := Nat.mul_pos hp.pos hq.pos
  have hmBounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 4≤SemiprimeEuclidRowBudget.publicRowModulus (p*q) := by omega
  have hbudget := (SemiprimeLehmanCoverage.sixthWidth_upper (p*q)).trans
    (Nat.pow_le_pow_left hmBounds.1 6)
  have hseed := seed_route_with_prefix_bound hp hq hpq.le hm hbudget
    (public_modulus_prefix_below_input hN hB)
  unfold routeAtRowModulus
  dsimp only
  cases he : SemiprimeSeedLcm.routeByWidth (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)) with
  | factor d =>
    rw [he] at hseed
    exact hseed
  | largeBase a =>
    rw [he] at hseed
    obtain ⟨hc,hlarge⟩ := hseed
    exact refineBase_semiprime hp hq hpq.ne (by omega) hc hlarge
  | unresolved =>
    rw [he] at hseed
    exact hseed.elim

/-- An actual long outcome of the matched-width N-only route supplies
the recoverable column, including every factor ratio and global hits.
The successful column's acquisition is still a separate open task. -/
theorem long_public_route_recoverable_column {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      ∃ (t : ℕ) (i : ℤ),
        progressionSeed h (p*q) m (p%m)∈progressionSeeds h (p*q) m ∧
        0<t ∧ t<m ∧ i.natAbs<2*m ∧
        ∃ d, recoverWrapColumn h m t (progressionSeed h (p*q) m (p%m)) i=some d := by
  have hd := routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hd
  obtain ⟨hc,hlong⟩ := hd
  exact ⟨hc,actual_public_recoverable_wrapped_column hp hq hpq hB hnone _ hlong⟩

/-- Matching the row width changes the proved refinement GCD bound by
at most a constant factor. This does not price the seed or polynomial backend. -/
theorem actual_refinement_gcd_bound {N : ℕ} (hN : 0<N) (g : (ZMod N)ˣ) :
    SemiprimeLocalOrderRouting.refinementGcdCount g
      (SemiprimeEuclidRowBudget.publicRowModulus N)≤
        18*SemiprimeLehmanCoverage.sixthWidth N+1 := by
  have hc := SemiprimeLocalOrderRouting.refinementGcdCount_le g
    (SemiprimeEuclidRowBudget.publicRowModulus N)
  have hm := (SemiprimeEuclidRowBudget.publicRowModulus_bounds hN).2
  omega

/-- Acquire one exact wrap triple by the existing shared m-root
polynomials and normalized block points, followed by its complete tail. -/
noncomputable def wrapBlockedJet {R : Type*} [CommRing R]
    (alpha : Rˣ) (x : R) (m : ℕ) : R × R × R :=
  let L := wrapCap m+1
  SemiprimeSharedIntervalJet.combineJets
    (SemiprimeSharedIntervalJet.sharedBlockedJet alpha x m (L/m))
    (SemiprimeSharedIntervalJet.blockJet (alpha : R) x ((L/m)*m) (L%m))

/-- The blocked construction retains the SAME three wrap scalars over
every commutative ring, including zero products and nonunit targets. -/
theorem wrapBlockedJet_exact {R : Type*} [CommRing R]
    (alpha : Rˣ) (x : R) {m : ℕ} (hm : 0<m) :
    wrapBlockedJet alpha x m=
      (intervalProduct (alpha : R) x (wrapCap m+1),
        targetDerivative (alpha : R) x (wrapCap m+1),
        baseDerivative (alpha : R) x (wrapCap m+1)) := by
  let L := wrapCap m+1
  have he : (L/m)*m+L%m=L := by
    simpa only [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div L m
  unfold wrapBlockedJet
  dsimp only
  rw [SemiprimeSharedIntervalJet.sharedBlockedJet_exact alpha x hm]
  dsimp only [SemiprimeSharedIntervalJet.combineJets,SemiprimeSharedIntervalJet.blockJet]
  rw [←SemiprimeSharedIntervalJet.intervalProduct_split,
    ←SemiprimeSharedIntervalJet.targetDerivative_split,
    ←SemiprimeSharedIntervalJet.baseDerivative_split]
  change (intervalProduct (alpha : R) x ((L/m)*m+L%m),
    targetDerivative (alpha : R) x ((L/m)*m+L%m),
    baseDerivative (alpha : R) x ((L/m)*m+L%m))=_
  rw [he]

/-- One column has at most 2m+1 full normalized block points and two
tail factors. This is an input count; a fast polynomial bit backend is separate. -/
theorem wrap_block_dimensions {m : ℕ} (hm : 1<m) :
    (wrapCap m+1)/m≤2*m+1 ∧ (wrapCap m+1)%m≤2 := by
  have hm₀ : 0<m := by omega
  have he : wrapCap m+1=m*(2*m)+2 := by unfold wrapCap; ring
  rw [he,Nat.mul_add_div hm₀,Nat.mul_add_mod]
  have hd : 2/m<2 := (Nat.div_lt_iff_lt_mul hm₀).mpr (by omega)
  exact ⟨by omega,Nat.mod_le _ _⟩

/-- Shared roots, normalized points, literal tail and one constant
have a linear total input count for ONE fixed column. -/
theorem wrap_block_input_bound {m : ℕ} (hm : 1<m) :
    m+(wrapCap m+1)/m+(wrapCap m+1)%m+1≤3*m+4 := by
  obtain ⟨hJ,hT⟩ := wrap_block_dimensions hm
  omega

/-- The blocked three-scalar reader is a concrete alternative to
constructing the full wrap interval for one cached column. -/
noncomputable def recoverBlockedWrapColumn {N : ℕ} (g : (ZMod N)ˣ) (m t : ℕ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (i : ℤ) : Option ℕ :=
  let x := wrapTarget g m t s i
  match recoverTaggedJet s.carryStep x (wrapCap m+1) (2*m)
      (wrapBlockedJet s.carryStep (x : ZMod N) m) with
  | none => none
  | some (Sum.inl d) => some d
  | some (Sum.inr k) => recoverCandidates N (wrappedRecovery N m t k s i)

/-- Exact blocked acquisition gives precisely the proved original
tag-preserving controller, including both saturation cases. -/
theorem recoverBlockedWrapColumn_eq {N m t : ℕ} (hm : 0<m) (g : (ZMod N)ˣ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (i : ℤ) :
    recoverBlockedWrapColumn g m t s i=recoverWrapColumn g m t s i := by
  simp only [recoverBlockedWrapColumn,wrapBlockedJet_exact _ _ hm,
    recoverWrapColumn,recoverTaggedInterval]

/-- The actual matched-width public long outcome has a successful
BLOCKED column, with no full quadratic wrap list used by its recovery. -/
theorem long_public_route_recoverable_blocked_column {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      ∃ (t : ℕ) (i : ℤ),
        progressionSeed h (p*q) m (p%m)∈progressionSeeds h (p*q) m ∧
        0<t ∧ t<m ∧ i.natAbs<2*m ∧
        ∃ d, recoverBlockedWrapColumn h m t (progressionSeed h (p*q) m (p%m)) i=some d := by
  obtain ⟨hc,t,i,hmem,ht,htm,hi,d,hd⟩ :=
    long_public_route_recoverable_column hp hq hpq hB hnone hroute
  have hmBounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds (Nat.mul_pos hp.pos hq.pos)
  refine ⟨hc,t,i,hmem,ht,htm,hi,d,?_⟩
  rw [recoverBlockedWrapColumn_eq (by omega)]
  exact hd

/-- A factor returned by the blocked version is still a checked proper
divisor. No polynomial or inverse implementation is assumed sound. -/
theorem recoverBlockedWrapColumn_sound {N m t d : ℕ} (hm : 0<m) (g : (ZMod N)ˣ)
    (s : ProgressionSeed ((ZMod N)ˣ)) (i : ℤ)
    (h : recoverBlockedWrapColumn g m t s i=some d) : ProperDivisor N d := by
  rw [recoverBlockedWrapColumn_eq hm] at h
  exact recoverWrapColumn_sound _ _ _ h

/-- Pooling every denominator/short-index target at ONE residue into
the existing transposed interval norm has a quadratic input floor for
every block width. This restricts that representation, not all algorithms. -/
theorem qInputs_wrap_target_group_floor {m s : ℕ} (hm : 1<m) (hs : 0<s) :
    16*m^4<(SemiprimeQAggregate.qInputs (4*m*(m-1)) (wrapCap m+1) s)^2 := by
  have hmpos : 0<m := by omega
  have hmminus : 0<m-1 := by omega
  have hr : 0<4*m*(m-1) := by positivity
  have hf := SemiprimeQAggregate.qInputs_squared_floor hr hs (L:=wrapCap m+1)
  have hm' : m≤2*(m-1) := by omega
  have hmul := Nat.mul_le_mul_left (m^3) hm'
  have hlow : 16*m^4≤4*(4*m*(m-1))*(wrapCap m+1) := by
    unfold wrapCap
    nlinarith only [hmul]
  exact hlow.trans_lt hf

end RiemannGaussian.SemiprimeWrapIndexRecovery
