/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeWeightedRows
import RiemannGaussian.SemiprimeCommonOrder
import Mathlib.Data.List.Sort

/-!
# Period information retained by whole-modulus row coincidences

Original exponent labels and cached unit powers produce confirmed signed
differences whenever two whole-modulus values agree. Their integer GCD
is still a period multiple of the original base. This information survives
global deduplication and can support checked probes at other public bases.
The representative scan preserves exactly the full cached-pair relation
GCD. Public common-modulus checks also enable a bounded wrap scan on the
balanced branch. Neither a nonzero result, exact order, common modulus
without those checks nor universal sixth-root coverage is assumed.
-/

namespace RiemannGaussian.SemiprimeRowPeriods

open SemiprimeEuclidRowFamily SemiprimeCartesianCompletion

/-- Retain an exponent beside its already constructed original unit value. -/
structure TaggedPower (G : Type*) where
  /-- The complete original signed exponent label. -/
  exponent : ℤ
  /-- Its cached whole-modulus group value. -/
  value : G
deriving Repr

/-- Every cache entry is the power of the same original public base. -/
def TaggedCorrect {G : Type*} [Group G] (g : G) (rows : List (TaggedPower G)) : Prop :=
  ∀ w∈rows, w.value=g^w.exponent

/-- The nonnegative GCD of complete original signed relation labels. -/
def signedRelationGcd : List ℤ → ℕ
  | [] => 0
  | e::tail => e.natAbs.gcd (signedRelationGcd tail)

theorem nat_dvd_absolute_iff (k : ℕ) (e : ℤ) : k∣e.natAbs ↔ (k : ℤ)∣e := by
  simpa only [Int.natAbs_natCast] using
    (Int.natAbs_dvd_natAbs : (k : ℤ).natAbs∣e.natAbs ↔ (k : ℤ)∣e)

theorem dvd_signedRelationGcd (k : ℕ) (es : List ℤ) :
    k∣signedRelationGcd es ↔ ∀ e∈es, (k : ℤ)∣e := by
  induction es with
  | nil => simp [signedRelationGcd]
  | cons e tail ih =>
    simp only [signedRelationGcd,Nat.dvd_gcd_iff,nat_dvd_absolute_iff,ih,List.mem_cons]
    aesop

/-- Retain one reference exponent in each cached equality class. -/
def centeredRelationGcd (center : ℤ) (es : List ℤ) : ℕ :=
  signedRelationGcd (es.map fun e => e-center)

/-- The full pair construction is only a mathematical comparison carrier. -/
def pairRelationGcd (es : List ℤ) : ℕ :=
  signedRelationGcd (es.flatMap fun e => es.map fun f => e-f)

theorem dvd_centeredRelationGcd (k : ℕ) (center : ℤ) (es : List ℤ) :
    k∣centeredRelationGcd center es ↔ ∀ e∈es, (k : ℤ)∣e-center := by
  simp only [centeredRelationGcd,dvd_signedRelationGcd,List.mem_map]
  constructor
  · intro h e he
    exact h (e-center) ⟨e,he,rfl⟩
  · intro h v hv
    obtain ⟨e,he,rfl⟩ := hv
    exact h e he

theorem dvd_pairRelationGcd (k : ℕ) (es : List ℤ) :
    k∣pairRelationGcd es ↔ ∀ e∈es, ∀ f∈es, (k : ℤ)∣e-f := by
  simp only [pairRelationGcd,dvd_signedRelationGcd,List.mem_flatMap,List.mem_map]
  constructor
  · intro h e he f hf
    exact h (e-f) ⟨e,he,f,hf,rfl⟩
  · intro h v hv
    obtain ⟨e,he,f,hf,rfl⟩ := hv
    exact h e he f hf

/-- Every pair difference is a signed difference of two reference-star
edges. One edge per label retains exactly the full pair GCD information. -/
theorem centeredRelationGcd_eq_pair {es : List ℤ} {center : ℤ} (hc : center∈es) :
    centeredRelationGcd center es=pairRelationGcd es := by
  apply Nat.dvd_antisymm
  · apply (dvd_pairRelationGcd _ es).mpr
    intro e he f hf
    have h := (dvd_centeredRelationGcd _ center es).mp
      (dvd_refl (centeredRelationGcd center es))
    have hsub := dvd_sub (h e he) (h f hf)
    rw [show e-f=(e-center)-(f-center) by ring]
    exact hsub
  · apply (dvd_centeredRelationGcd _ center es).mpr
    intro e he
    exact (dvd_pairRelationGcd _ es).mp (dvd_refl (pairRelationGcd es)) e he center hc

/-- Matching cached values retain a confirmed exponent difference.
No further original giant powers are computed by this scan. -/
def collectPeriodGcd {G : Type*} [DecidableEq G] :
    List (TaggedPower G) → List (TaggedPower G) → ℕ → ℕ
  | [], _, d => d
  | x::tail, reps, d =>
    match reps.find? (fun y => decide (x.value=y.value)) with
    | none => collectPeriodGcd tail (x::reps) d
    | some y => collectPeriodGcd tail reps (d.gcd (x.exponent-y.exponent).natAbs)

/-- Integer GCD operations at matches; lookup and construction are separate. -/
def periodGcdCount {G : Type*} [DecidableEq G] :
    List (TaggedPower G) → List (TaggedPower G) → ℕ
  | [], _ => 0
  | x::tail, reps =>
    match reps.find? (fun y => decide (x.value=y.value)) with
    | none => periodGcdCount tail (x::reps)
    | some _ => 1+periodGcdCount tail reps

/-- All equal cached values have congruent original exponents modulo k.
This is an exact signed relation property, including the modulus zero. -/
def CachedRelationCongruent {G : Type*} (k : ℕ) (rows : List (TaggedPower G)) : Prop :=
  ∀ x∈rows, ∀ y∈rows, x.value=y.value → (k : ℤ)∣x.exponent-y.exponent

theorem cachedRelationCongruent_perm {G : Type*} (k : ℕ)
    {xs ys : List (TaggedPower G)} (hp : xs.Perm ys) :
    CachedRelationCongruent k xs ↔ CachedRelationCongruent k ys := by
  constructor
  · intro h x hx y hy he
    exact h x (hp.mem_iff.mpr hx) y (hp.mem_iff.mpr hy) he
  · intro h x hx y hy he
    exact h x (hp.mem_iff.mp hx) y (hp.mem_iff.mp hy) he

theorem cachedRelationCongruent_cons_iff {G : Type*} (k : ℕ)
    (x y : TaggedPower G) (rows : List (TaggedPower G))
    (hy : y∈rows) (hxy : x.value=y.value) :
    CachedRelationCongruent k (x::rows) ↔
      CachedRelationCongruent k rows ∧ (k : ℤ)∣x.exponent-y.exponent := by
  constructor
  · intro h
    exact ⟨fun a ha b hb he => h a (by simp [ha]) b (by simp [hb]) he,
      h x (by simp) y (by simp [hy]) hxy⟩
  · rintro ⟨hr,hd⟩
    have hstar (z : TaggedPower G) (hz : z∈rows) (hxz : x.value=z.value) :
        (k : ℤ)∣x.exponent-z.exponent := by
      rw [show x.exponent-z.exponent=
        (x.exponent-y.exponent)-(z.exponent-y.exponent) by ring]
      exact dvd_sub hd (hr z hz y hy (hxz.symm.trans hxy))
    intro a ha b hb he
    rcases List.mem_cons.mp ha with ha|ha
    · subst a
      rcases List.mem_cons.mp hb with hb|hb
      · subst b; simp
      · exact hstar b hb he
    · rcases List.mem_cons.mp hb with hb|hb
      · subst b
        rw [show a.exponent-x.exponent=-(x.exponent-a.exponent) by ring]
        exact dvd_neg.mpr (hstar a ha he.symm)
      · exact hr a ha b hb he

theorem cachedRelationCongruent_cons_new {G : Type*} (k : ℕ)
    (x : TaggedPower G) (rows : List (TaggedPower G))
    (hr : CachedRelationCongruent k rows) (hn : ∀ y∈rows, x.value≠y.value) :
    CachedRelationCongruent k (x::rows) := by
  intro a ha b hb he
  rcases List.mem_cons.mp ha with ha|ha
  · subst a
    rcases List.mem_cons.mp hb with hb|hb
    · subst b; simp
    · exact (hn b hb he).elim
  · rcases List.mem_cons.mp hb with hb|hb
    · subst b
      exact (hn a ha he.symm).elim
    · exact hr a ha b hb he

/-- The actual representative-cache scan retains every equal-value
pair congruence. Initial representatives need only be mutually congruent. -/
theorem collectPeriodGcd_divisibility {G : Type*} [DecidableEq G]
    (k : ℕ) (rows reps : List (TaggedPower G)) (d : ℕ)
    (hr : CachedRelationCongruent k reps) :
    k∣collectPeriodGcd rows reps d ↔ k∣d ∧ CachedRelationCongruent k (rows++reps) := by
  induction rows generalizing reps d with
  | nil => simp only [collectPeriodGcd,List.nil_append,and_iff_left hr]
  | cons x tail ih =>
    cases hf : reps.find? (fun y => decide (x.value=y.value)) with
    | none =>
      have hn : ∀ y∈reps, x.value≠y.value := by
        simpa only [List.find?_eq_none,decide_eq_true_eq] using hf
      have hr' := cachedRelationCongruent_cons_new k x reps hr hn
      rw [collectPeriodGcd,hf,ih (x::reps) d hr']
      have hp : (tail++x::reps).Perm ((x::tail)++reps) := by
        simpa only [List.cons_append] using (List.perm_middle (a:=x) (l₁:=tail) (l₂:=reps))
      rw [cachedRelationCongruent_perm k hp]
    | some y =>
      have hy : y∈reps := List.mem_of_find?_eq_some hf
      have he : x.value=y.value := of_decide_eq_true
        (List.find?_some (p:=fun (y : TaggedPower G) => decide (x.value=y.value)) hf)
      rw [collectPeriodGcd,hf,ih reps _ hr,Nat.dvd_gcd_iff,nat_dvd_absolute_iff,
        List.cons_append,cachedRelationCongruent_cons_iff k x y (tail++reps)
          (List.mem_append_right tail hy) he]
      tauto

/-- Equal whole group powers certify the absolute signed difference. -/
theorem period_of_equal_powers {G : Type*} [Group G] (g : G) {e f : ℤ}
    (he : g^e=g^f) : g^(e-f).natAbs=1 := by
  have hd : (orderOf g : ℤ)∣e-f := orderOf_dvd_sub_iff_zpow_eq_zpow.mpr he
  have hn : orderOf g∣(e-f).natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  exact orderOf_dvd_iff_pow_eq_one.mp hn

/-- GCD combines confirmed periods without factoring either integer. -/
theorem period_of_gcd {G : Type*} [Group G] (g : G) {d e : ℕ}
    (hd : g^d=1) (he : g^e=1) : g^(d.gcd e)=1 :=
  orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_gcd
    (orderOf_dvd_iff_pow_eq_one.mpr hd) (orderOf_dvd_iff_pow_eq_one.mpr he))

/-- A confirmed positive period reduces signed powers without an exact
order oracle. The original signed exponent remains in its cache tag. -/
theorem signed_power_reduce_of_period {G : Type*} [Group G] (g : G)
    {d : ℕ} (hd : 0<d) (hpow : g^d=1) (e : ℤ) :
    g^e=g^(e%(d : ℤ)).toNat := by
  have h := zpow_eq_zpow_emod' e hpow
  have hr : (((e%(d : ℤ)).toNat) : ℤ)=e%(d : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hd.ne'))
  rw [←hr,zpow_natCast] at h
  exact h

/-- The actual cache scan preserves its confirmed period invariant. -/
theorem collectPeriodGcd_certificate {G : Type*} [Group G] [DecidableEq G]
    (g : G) (rows reps : List (TaggedPower G)) (d : ℕ)
    (hr : TaggedCorrect g rows) (hs : TaggedCorrect g reps) (hd : g^d=1) :
    g^(collectPeriodGcd rows reps d)=1 := by
  induction rows generalizing reps d with
  | nil => exact hd
  | cons x tail ih =>
    have hx := hr x (by simp)
    have ht : TaggedCorrect g tail := fun y hy => hr y (by simp [hy])
    cases hf : reps.find? (fun y => decide (x.value=y.value)) with
    | none =>
      have hnew : TaggedCorrect g (x::reps) := by
        intro y hy
        rcases List.mem_cons.mp hy with he|he
        · subst y; exact hx
        · exact hs y he
      simpa [collectPeriodGcd,hf] using ih (x::reps) d ht hnew hd
    | some y =>
      have hy := hs y (List.mem_of_find?_eq_some hf)
      have he : x.value=y.value := of_decide_eq_true
        (List.find?_some (p:=fun (y : TaggedPower G) => decide (x.value=y.value)) hf)
      have hp : g^x.exponent=g^y.exponent := by rw [←hx,←hy]; exact he
      have hnew := period_of_gcd g hd (period_of_equal_powers g hp)
      simpa [collectPeriodGcd,hf] using ih reps _ ht hs hnew

theorem periodGcdCount_le {G : Type*} [DecidableEq G]
    (rows reps : List (TaggedPower G)) : periodGcdCount rows reps≤rows.length := by
  induction rows generalizing reps with
  | nil => simp [periodGcdCount]
  | cons x tail ih =>
    cases hf : reps.find? (fun y => decide (x.value=y.value)) with
    | none => simpa [periodGcdCount,hf] using (ih (x::reps)).trans (Nat.le_succ _)
    | some y => simpa [periodGcdCount,hf,Nat.add_comm] using Nat.succ_le_succ (ih reps)

/-- Extract the retained relation GCD; zero is an explicit uninformative case. -/
def retainedPeriod {G : Type*} [DecidableEq G] (rows : List (TaggedPower G)) : ℕ :=
  collectPeriodGcd rows [] 0

/-- No full pair matrix is needed to retain the complete equal-value
relation GCD, even for untrusted cached values or zero certificates. -/
theorem retainedPeriod_divisibility {G : Type*} [DecidableEq G]
    (k : ℕ) (rows : List (TaggedPower G)) :
    k∣retainedPeriod rows ↔ CachedRelationCongruent k rows := by
  have hr : CachedRelationCongruent k ([] : List (TaggedPower G)) := by
    simp [CachedRelationCongruent]
  simpa only [retainedPeriod,List.append_nil,dvd_zero, true_and] using
    collectPeriodGcd_divisibility k rows [] 0 hr

/-- Full cached-pair comparison GCD. Unequal values contribute zero.
This quadratic object is never constructed by the representative scan. -/
def cachedPairRelationGcd {G : Type*} [DecidableEq G]
    (rows : List (TaggedPower G)) : ℕ :=
  signedRelationGcd (rows.flatMap fun x => rows.map fun y =>
    if x.value=y.value then x.exponent-y.exponent else 0)

theorem dvd_cachedPairRelationGcd {G : Type*} [DecidableEq G]
    (k : ℕ) (rows : List (TaggedPower G)) :
    k∣cachedPairRelationGcd rows ↔ CachedRelationCongruent k rows := by
  rw [cachedPairRelationGcd,dvd_signedRelationGcd]
  constructor
  · intro h x hx y hy he
    have hm : (if x.value=y.value then x.exponent-y.exponent else 0)∈
        rows.flatMap (fun a => rows.map fun b =>
          if a.value=b.value then a.exponent-b.exponent else 0) :=
      List.mem_flatMap.mpr ⟨x,hx,List.mem_map.mpr ⟨y,hy,rfl⟩⟩
    simpa only [if_pos he] using h _ hm
  · intro h v hv
    obtain ⟨x,hx,hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hv
    by_cases he : x.value=y.value
    · simpa only [if_pos he] using h x hx y hy he
    · simp [he]

/-- Exact equality to the full pair matrix's relation GCD for the
actual cache algorithm, including arbitrary values and zero output. -/
theorem retainedPeriod_eq_cachedPairRelationGcd {G : Type*} [DecidableEq G]
    (rows : List (TaggedPower G)) : retainedPeriod rows=cachedPairRelationGcd rows := by
  apply Nat.dvd_antisymm
  · exact (dvd_cachedPairRelationGcd _ rows).mpr
      ((retainedPeriod_divisibility _ rows).mp (dvd_refl (retainedPeriod rows)))
  · exact (retainedPeriod_divisibility _ rows).mpr
      ((dvd_cachedPairRelationGcd _ rows).mp (dvd_refl (cachedPairRelationGcd rows)))

theorem retainedPeriod_certificate {G : Type*} [Group G] [DecidableEq G]
    (g : G) (rows : List (TaggedPower G)) (hr : TaggedCorrect g rows) :
    g^retainedPeriod rows=1 :=
  collectPeriodGcd_certificate g rows [] 0 hr (by simp [TaggedCorrect]) (by simp)

/-- The N-only packet constructor supplies its original exponent and power. -/
def publicTaggedRows {N : ℕ} (m : ℕ) (g : (ZMod N)ˣ) : List (TaggedPower (ZMod N)ˣ) :=
  (publicPackets N m).map fun w => ⟨packetExponent m w,g^packetExponent m w⟩

theorem publicTaggedRows_correct {N m : ℕ} (g : (ZMod N)ˣ) :
    TaggedCorrect g (publicTaggedRows m g) := by
  intro x hx
  obtain ⟨w,_,rfl⟩ := List.mem_map.mp hx
  rfl

/-- A public period certificate obtained entirely from the retained cache. -/
def publicRetainedPeriod {N : ℕ} (m : ℕ) (g : (ZMod N)ˣ) : ℕ :=
  retainedPeriod (publicTaggedRows m g)

theorem publicRetainedPeriod_certificate {N m : ℕ} (g : (ZMod N)ˣ) :
    g^publicRetainedPeriod m g=1 :=
  retainedPeriod_certificate g _ (publicTaggedRows_correct g)

theorem publicRetainedPeriod_gcd_bound {N m : ℕ} (g : (ZMod N)ˣ) :
    periodGcdCount (publicTaggedRows m g) []≤(publicPackets N m).length := by
  simpa [publicTaggedRows] using periodGcdCount_le (publicTaggedRows m g) []

/-- Equal cached natural values are consecutive after ordering. -/
def adjacentRelationGcd : List (TaggedPower ℕ) → ℕ
  | [] => 0
  | [_] => 0
  | x::y::tail =>
    if x.value=y.value then (x.exponent-y.exponent).natAbs.gcd (adjacentRelationGcd (y::tail))
    else adjacentRelationGcd (y::tail)

/-- The adjacent scan compares one cached value at each consecutive pair. -/
def adjacentComparisonCount : List (TaggedPower ℕ) → ℕ
  | [] => 0
  | [_] => 0
  | _::y::tail => 1+adjacentComparisonCount (y::tail)

theorem adjacentComparisonCount_eq (rows : List (TaggedPower ℕ)) :
    adjacentComparisonCount rows=rows.length-1 := by
  induction rows with
  | nil => rfl
  | cons x tail ih =>
    cases tail with
    | nil => rfl
    | cons y rest =>
      simp only [List.length_cons] at ih
      simp only [adjacentComparisonCount,List.length_cons]
      omega

/-- The only new integer GCDs in the adjacent scan occur at equal values. -/
def adjacentGcdCount : List (TaggedPower ℕ) → ℕ
  | [] => 0
  | [_] => 0
  | x::y::tail =>
    if x.value=y.value then 1+adjacentGcdCount (y::tail) else adjacentGcdCount (y::tail)

theorem adjacentGcdCount_le (rows : List (TaggedPower ℕ)) :
    adjacentGcdCount rows≤adjacentComparisonCount rows := by
  induction rows with
  | nil => rfl
  | cons x tail ih =>
    cases tail with
    | nil => rfl
    | cons y rest =>
      simp only [adjacentGcdCount,adjacentComparisonCount]
      split_ifs <;> omega

theorem cachedRelationCongruent_cons_fresh {G : Type*} (k : ℕ)
    (x : TaggedPower G) (rows : List (TaggedPower G)) (hn : ∀ y∈rows, x.value≠y.value) :
    CachedRelationCongruent k (x::rows) ↔ CachedRelationCongruent k rows := by
  constructor
  · intro h a ha b hb he
    exact h a (by simp [ha]) b (by simp [hb]) he
  · intro h
    exact cachedRelationCongruent_cons_new k x rows h hn

/-- Sorted adjacency retains every pair relation within each value block. -/
theorem adjacentRelationGcd_divisibility (k : ℕ) (rows : List (TaggedPower ℕ))
    (hs : rows.Pairwise (fun x y => x.value≤y.value)) :
    k∣adjacentRelationGcd rows ↔ CachedRelationCongruent k rows := by
  induction rows with
  | nil => simp [adjacentRelationGcd,CachedRelationCongruent]
  | cons x tail ih =>
    cases tail with
    | nil => simp [adjacentRelationGcd,CachedRelationCongruent]
    | cons y rest =>
      have hxt := (List.pairwise_cons.mp hs).1
      have htail := (List.pairwise_cons.mp hs).2
      have hih := ih htail
      by_cases he : x.value=y.value
      · rw [adjacentRelationGcd,if_pos he,Nat.dvd_gcd_iff,nat_dvd_absolute_iff,hih,
          cachedRelationCongruent_cons_iff k x y (y::rest) (by simp) he]
        tauto
      · have hn : ∀ z∈y::rest, x.value≠z.value := by
          intro z hz
          have hxy : x.value≤y.value := hxt y (by simp)
          have hyz : y.value≤z.value := by
            rcases List.mem_cons.mp hz with hz|hz
            · subst z; exact le_refl _
            · exact (List.pairwise_cons.mp htail).1 z hz
          omega
        rw [adjacentRelationGcd,if_neg he,hih,cachedRelationCongruent_cons_fresh k x (y::rest) hn]

/-- Sort complete tags by their cached natural values, retaining exponents. -/
def sortedTags (rows : List (TaggedPower ℕ)) : List (TaggedPower ℕ) :=
  rows.mergeSort (fun x y => decide (x.value≤y.value))

theorem sortedTags_pairwise (rows : List (TaggedPower ℕ)) :
    (sortedTags rows).Pairwise (fun x y => x.value≤y.value) := by
  have ht (a b c : TaggedPower ℕ) :
      decide (a.value≤b.value) → decide (b.value≤c.value) → decide (a.value≤c.value) := by
    simp only [decide_eq_true_eq]
    exact le_trans
  have hall (a b : TaggedPower ℕ) : decide (a.value≤b.value) || decide (b.value≤a.value) := by
    simp only [Bool.or_eq_true,decide_eq_true_eq]
    exact le_total _ _
  simpa only [sortedTags,decide_eq_true_eq] using List.pairwise_mergeSort ht hall rows

/-- A matrix-free ordered cache scan with no association-list lookup. -/
def sortedAdjacentPeriod (rows : List (TaggedPower ℕ)) : ℕ :=
  adjacentRelationGcd (sortedTags rows)

theorem sortedAdjacentPeriod_eq_retained (rows : List (TaggedPower ℕ)) :
    sortedAdjacentPeriod rows=retainedPeriod rows := by
  have hiff (k : ℕ) : k∣sortedAdjacentPeriod rows ↔ k∣retainedPeriod rows := by
    rw [sortedAdjacentPeriod,adjacentRelationGcd_divisibility k _ (sortedTags_pairwise rows),
      sortedTags,cachedRelationCongruent_perm k (List.mergeSort_perm rows _),
      retainedPeriod_divisibility]
  exact Nat.dvd_antisymm ((hiff _).mp (dvd_refl _)) ((hiff _).mpr (dvd_refl _))

theorem sortedAdjacentPeriod_scan_bound (rows : List (TaggedPower ℕ)) :
    adjacentComparisonCount (sortedTags rows)=rows.length-1 ∧
      adjacentGcdCount (sortedTags rows)≤rows.length-1 := by
  have hlen : (sortedTags rows).length=rows.length := List.length_mergeSort rows
  constructor
  · rw [adjacentComparisonCount_eq,hlen]
  · simpa only [adjacentComparisonCount_eq,hlen] using adjacentGcdCount_le (sortedTags rows)

/-- Fork the complete unit cache to its public canonical natural residues. -/
def naturalValueTags {N : ℕ} (rows : List (TaggedPower (ZMod N)ˣ)) : List (TaggedPower ℕ) :=
  rows.map fun x => ⟨x.exponent,((x.value : ZMod N).val)⟩

theorem naturalValueTags_congruent {N : ℕ} [NeZero N] (k : ℕ)
    (rows : List (TaggedPower (ZMod N)ˣ)) :
    CachedRelationCongruent k (naturalValueTags rows) ↔ CachedRelationCongruent k rows := by
  constructor
  · intro h x hx y hy he
    apply h ⟨x.exponent,(x.value : ZMod N).val⟩ (List.mem_map.mpr ⟨x,hx,rfl⟩)
      ⟨y.exponent,(y.value : ZMod N).val⟩ (List.mem_map.mpr ⟨y,hy,rfl⟩)
    exact congrArg (fun u : (ZMod N)ˣ => (u : ZMod N).val) he
  · intro h x hx y hy he
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
    apply h a ha b hb
    apply Units.ext
    exact ZMod.val_injective N he

theorem naturalValueTags_period_eq {N : ℕ} [NeZero N]
    (rows : List (TaggedPower (ZMod N)ˣ)) :
    retainedPeriod (naturalValueTags rows)=retainedPeriod rows := by
  have hiff (k : ℕ) : k∣retainedPeriod (naturalValueTags rows) ↔ k∣retainedPeriod rows := by
    rw [retainedPeriod_divisibility,naturalValueTags_congruent,retainedPeriod_divisibility]
  exact Nat.dvd_antisymm ((hiff _).mp (dvd_refl _)) ((hiff _).mpr (dvd_refl _))

/-- The N-only packet cache uses the actual sorted adjacent extractor. -/
def publicSortedRetainedPeriod {N : ℕ} (m : ℕ) (g : (ZMod N)ˣ) : ℕ :=
  sortedAdjacentPeriod (naturalValueTags (publicTaggedRows m g))

theorem publicSortedRetainedPeriod_eq {N : ℕ} [NeZero N] (m : ℕ) (g : (ZMod N)ˣ) :
    publicSortedRetainedPeriod m g=publicRetainedPeriod m g := by
  rw [publicSortedRetainedPeriod,sortedAdjacentPeriod_eq_retained,naturalValueTags_period_eq]
  rfl

theorem publicSortedRetainedPeriod_certificate {N : ℕ} [NeZero N] (m : ℕ) (g : (ZMod N)ˣ) :
    g^publicSortedRetainedPeriod m g=1 := by
  rw [publicSortedRetainedPeriod_eq]
  exact publicRetainedPeriod_certificate g

theorem publicSortedRetainedPeriod_scan_bound {N : ℕ} (m : ℕ) (g : (ZMod N)ˣ) :
    adjacentComparisonCount (sortedTags (naturalValueTags (publicTaggedRows m g)))=
      (publicPackets N m).length-1 ∧
    adjacentGcdCount (sortedTags (naturalValueTags (publicTaggedRows m g)))≤
      (publicPackets N m).length-1 := by
  simpa only [naturalValueTags,publicTaggedRows,List.length_map] using
    sortedAdjacentPeriod_scan_bound (naturalValueTags (publicTaggedRows m g))

/-- Check both original signs at each further public integer base. -/
def periodProbeLeaves (N d : ℕ) (bases : List ℕ) : List ℕ :=
  bases.flatMap fun (b : ℕ) => [(((b : ZMod N)^d)-1).val,(((b : ZMod N)^d)+1).val]

/-- Period probes return only separately checked proper divisors.
A zero relation GCD remains an explicit unresolved case. -/
def probePeriod (N d : ℕ) (bases : List ℕ) : Option ℕ :=
  if d=0 then none else scanProper N (periodProbeLeaves N d bases)

theorem probePeriod_sound {N d f : ℕ} {bases : List ℕ}
    (hf : probePeriod N d bases=some f) : SemiprimeGroupSelection.ProperDivisor N f := by
  unfold probePeriod at hf
  split_ifs at hf with hd
  exact scanProper_sound hf

theorem periodProbeLeaves_length (N d : ℕ) (bases : List ℕ) :
    (periodProbeLeaves N d bases).length=2*bases.length := by
  induction bases with
  | nil => rfl
  | cons b tail ih =>
    simp only [periodProbeLeaves,List.flatMap_cons,List.length_append,List.length_cons,
      List.length_nil] at *
    omega

/-- At most two factor-checking GCD queries per further public base. -/
def periodProbeGcdCount (N d : ℕ) (bases : List ℕ) : ℕ :=
  if d=0 then 0 else scanGcdCount N (periodProbeLeaves N d bases)

theorem periodProbeGcdCount_le (N d : ℕ) (bases : List ℕ) :
    periodProbeGcdCount N d bases≤2*bases.length := by
  unfold periodProbeGcdCount
  split_ifs
  · omega
  · simpa [periodProbeLeaves_length] using scanGcdCount_le N (periodProbeLeaves N d bases)

/-- Entire public-row period extraction followed by the checked base menu.
The known period, repeated-row witness and factors are not inputs. -/
def recoverPublicRowPeriods {N : ℕ} (m : ℕ) (g : (ZMod N)ˣ)
    (bases : List ℕ) : Option ℕ := probePeriod N (publicRetainedPeriod m g) bases

theorem recoverPublicRowPeriods_sound {N m f : ℕ} {g : (ZMod N)ˣ} {bases : List ℕ}
    (hf : recoverPublicRowPeriods m g bases=some f) :
    SemiprimeGroupSelection.ProperDivisor N f := probePeriod_sound hf

/-- Balanced factors need only a sixth-root-sized common modulus.
Retaining the sum's wrap label gives fewer than three sixth-root labels. -/
theorem balanced_wrap_label_bound {p q d B a b : ℕ}
    (hpq : p≤q) (hbalanced : q≤2*p) (hB : 0<B) (hbudget : p*q≤B^6)
    (hsize : B≤d) (hpa : p=d*a+1) (hqb : q=d*b+1) :
    (a+b)/d<3*B := by
  have hpp := Nat.mul_le_mul_left p hpq
  have hsq : p^2≤(B^3)^2 := by
    calc
      p^2≤p*q := by simpa only [pow_two] using hpp
      _≤B^6 := hbudget
      _=(B^3)^2 := by ring
  have hpB : p≤B^3 := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp hsq
  have hsum : p+q≤3*B^3 := by omega
  have hdiv := Nat.div_mul_le_self (a+b) d
  have hmul := Nat.mul_le_mul_left d hdiv
  have hd2 : B^2≤d^2 := Nat.pow_le_pow_left hsize 2
  by_contra hn
  have ht : 3*B≤(a+b)/d := by omega
  have htB := Nat.mul_le_mul_right (B^2) ht
  have htD := Nat.mul_le_mul_left ((a+b)/d) hd2
  have hB2 : 0<B^2 := pow_pos hB 2
  nlinarith

/-- The retained wrap scan recovers every balanced semiprime with an
actual common modulus at least B, using at most four B factor checks.
Its common-modulus premise is not supplied by a mere period multiple. -/
theorem recoverWrapped_balanced {p q d B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≤q) (hbalanced : q≤2*p) (hB : 0<B) (hbudget : p*q≤B^6)
    (hsize : B≤d) (hdp : d∣p-1) (hdq : d∣q-1) :
    ∃ f, SemiprimeCommonOrder.recoverWrapped (p*q) d (2*B)=some f := by
  have hd : 0<d := hB.trans_le hsize
  obtain ⟨a,b,_,_,hab,hpa,hqb⟩ :=
    SemiprimeCommonOrder.common_modulus_indices hp.one_lt hq.one_lt hd hpq hdp hdq
  have ht := balanced_wrap_label_bound hpq hbalanced hB hbudget hsize hpa hqb
  have ht4 : (a+b)/d<2*(2*B) := by omega
  have hc : SemiprimeCommonOrder.wrappedCandidate (p*q) d ((a+b)/d)=p := by
    rw [hpa,hqb]
    exact SemiprimeCommonOrder.wrappedCandidate_encoded hd hab
  cases hs : SemiprimeCommonOrder.recoverWrapped (p*q) d (2*B) with
  | some f => exact ⟨f,rfl⟩
  | none =>
    have hn : scanProper (p*q)
        ((List.range (2*(2*B))).map (SemiprimeCommonOrder.wrappedCandidate (p*q) d))=none := by
      simpa only [SemiprimeCommonOrder.recoverWrapped,if_pos hd] using hs
    have hmem : p∈(List.range (2*(2*B))).map
        (SemiprimeCommonOrder.wrappedCandidate (p*q) d) :=
      List.mem_map.mpr ⟨(a+b)/d,List.mem_range.mpr ht4,hc⟩
    have he := (scanProper_none_iff _ _).mp hn p hmem
    have hproper : 1<p ∧ p<p*q := ⟨hp.one_lt,by have hh:=hq.one_lt; nlinarith⟩
    rw [SemiprimeGroupSelection.checkedSignal,Nat.gcd_eq_right (dvd_mul_right p q),
      if_pos hproper] at he
    contradiction

/-- Reconstruct from the actual retained cache certificate, keeping
every candidate behind a proper-divisor GCD check. -/
def recoverPublicWrappedPeriod {N : ℕ} (B m : ℕ) (g : (ZMod N)ˣ) : Option ℕ :=
  SemiprimeCommonOrder.recoverWrapped N (publicRetainedPeriod m g) (2*B)

theorem recoverPublicWrappedPeriod_sound {N B m f : ℕ} {g : (ZMod N)ˣ}
    (hf : recoverPublicWrappedPeriod B m g=some f) :
    SemiprimeGroupSelection.ProperDivisor N f := SemiprimeCommonOrder.recoverWrapped_sound hf

/-- The complete public reconstruction uses the ordered adjacent cache. -/
def recoverPublicSortedWrappedPeriod {N : ℕ} (B m : ℕ) (g : (ZMod N)ˣ) : Option ℕ :=
  SemiprimeCommonOrder.recoverWrapped N (publicSortedRetainedPeriod m g) (2*B)

theorem recoverPublicSortedWrappedPeriod_eq {N : ℕ} [NeZero N] (B m : ℕ) (g : (ZMod N)ˣ) :
    recoverPublicSortedWrappedPeriod B m g=recoverPublicWrappedPeriod B m g := by
  rw [recoverPublicSortedWrappedPeriod,publicSortedRetainedPeriod_eq]
  rfl

theorem recoverPublicSortedWrappedPeriod_sound {N B m f : ℕ} {g : (ZMod N)ˣ}
    (hf : recoverPublicSortedWrappedPeriod B m g=some f) :
    SemiprimeGroupSelection.ProperDivisor N f := SemiprimeCommonOrder.recoverWrapped_sound hf

/-- Only reconstruction factor checks are counted here; row construction,
integer period GCDs and cache lookups remain separately charged. -/
theorem recoverPublicWrappedPeriod_gcd_bound {N : ℕ} (B m : ℕ) (g : (ZMod N)ˣ) :
    scanGcdCount N ((List.range (2*(2*B))).map
      (SemiprimeCommonOrder.wrappedCandidate N (publicRetainedPeriod m g)))≤4*B := by
  have h := SemiprimeCommonOrder.recoverWrapped_gcd_count N (publicRetainedPeriod m g) (2*B)
  omega

/-- Public prime-divisor checks upgrade the actual cached period multiple
to a common modulus. The annihilating power comes from the cache theorem. -/
theorem recoverPublicWrappedPeriod_of_checks {p q B m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≤q) (hbalanced : q≤2*p)
    (hB : 0<B) (hbudget : p*q≤B^6) (g : (ZMod (p*q))ˣ)
    (hsize : B≤publicRetainedPeriod m g)
    (hclear : ∀ r, r.Prime → r∣publicRetainedPeriod m g →
      (p*q).gcd (((g^(publicRetainedPeriod m g/r) : (ZMod (p*q))ˣ) : ZMod (p*q))-1).val=1) :
    ∃ f, recoverPublicWrappedPeriod B m g=some f := by
  obtain ⟨hdp,hdq⟩ := SemiprimeCommonOrder.common_modulus_of_public_checks hp hq g
    (hB.trans_le hsize) (publicRetainedPeriod_certificate g) hclear
  exact recoverWrapped_balanced hp hq hpq hbalanced hB hbudget hsize hdp hdq

/-- When the extracted period is prime, a single public check at g-1
certifies its common-modulus role. No local order or factor is advice. -/
theorem recoverPublicWrappedPeriod_of_prime_period {p q B m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≤q) (hbalanced : q≤2*p)
    (hB : 0<B) (hbudget : p*q≤B^6) (g : (ZMod (p*q))ˣ)
    (hsize : B≤publicRetainedPeriod m g) (hd : (publicRetainedPeriod m g).Prime)
    (hunit : (p*q).gcd (((g : ZMod (p*q))-1).val)=1) :
    ∃ f, recoverPublicWrappedPeriod B m g=some f := by
  apply recoverPublicWrappedPeriod_of_checks hp hq hpq hbalanced hB hbudget g hsize
  intro r hr hrD
  have he : r=publicRetainedPeriod m g := (Nat.prime_dvd_prime_iff_eq hr hd).mp hrD
  rw [he,Nat.div_self hd.pos,pow_one]
  exact hunit

/-- Literal original public base for the matched-order control. -/
def controlBase : (ZMod 2047)ˣ := ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 2047)

theorem control_order : orderOf controlBase=11 := by
  let : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · apply Units.ext
    norm_num only [controlBase,Units.val_pow_eq_pow_val,ZMod.coe_unitOfCoprime,Units.val_one]
    reduce_mod_char
  · decide +kernel

/-- Reduce arbitrary signed exponents to the certified finite cyclic carrier. -/
theorem control_power_reduce (e : ℤ) :
    controlBase^e=controlBase^(e%11).toNat := by
  have h := zpow_mod_orderOf controlBase e
  rw [control_order] at h
  norm_num only [Nat.cast_ofNat] at h
  have hr : ((e%11).toNat : ℤ)=e%11 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  rw [←hr,zpow_natCast] at h
  exact h.symm

set_option maxRecDepth 32768 in
/-- All original N-only packets supply the confirmed relation GCD eleven. -/
theorem control_public_period : publicRetainedPeriod 5 controlBase=11 := by
  unfold publicRetainedPeriod publicTaggedRows
  simp_rw [control_power_reduce]
  decide +kernel

/-- The complete public procedure recovers 23 by the fixed further base 3.
Neither the period eleven nor its repeated rows are algorithm inputs. -/
theorem control_public_period_recovers : recoverPublicRowPeriods 5 controlBase [3]=some 23 := by
  unfold recoverPublicRowPeriods
  rw [control_public_period]
  norm_num [probePeriod,periodProbeLeaves,scanProper,SemiprimeGroupSelection.checkedSignal,
    ZMod.val_ofNat]

theorem control_arithmetic : Nat.Prime 23 ∧ Nat.Prime 89 ∧ 23*89=2047 ∧
    Nat.Prime 5 ∧ Nat.Coprime 5 2047 ∧ (3 : ℕ)^6<2047 ∧ 2047≤(4 : ℕ)^6 := by
  norm_num [Nat.Coprime]

theorem control_power_represented (e : ℤ) :
    ∃ i : Fin 11, controlBase^e=controlBase^i.val := by
  have hlo : 0≤e%11 := Int.emod_nonneg _ (by decide)
  have hhi : e%11<11 := Int.emod_lt_of_pos _ (by decide)
  exact ⟨⟨(e%11).toNat,by omega⟩,control_power_reduce e⟩

set_option maxRecDepth 32768 in
/-- Every pair in the whole base-two cyclic carrier has no proper hit
in either original channel. This checks only 121 finite pairs. -/
theorem control_finite_pair_checks : ∀ i j : Fin 11,
    SemiprimeGroupSelection.checkedSignal 2047
      (((controlBase^i.val : (ZMod 2047)ˣ) : ZMod 2047)-
        ((controlBase^j.val : (ZMod 2047)ˣ) : ZMod 2047)).val=none ∧
    SemiprimeGroupSelection.checkedSignal 2047
      (((controlBase^i.val : (ZMod 2047)ˣ) : ZMod 2047)*
        ((controlBase^j.val : (ZMod 2047)ˣ) : ZMod 2047)-1).val=none := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem control_finite_endpoint_checks : ∀ i : Fin 11,
    SemiprimeGroupSelection.checkedSignal 2047
      (((controlBase^i.val : (ZMod 2047)ˣ) : ZMod 2047)-1).val=none ∧
    SemiprimeGroupSelection.checkedSignal 2047
      (((controlBase^i.val : (ZMod 2047)ˣ) : ZMod 2047)+1).val=none := by
  decide +kernel

/-- No choice of signed exponents repairs this fixed base's pair/endpoint
detector. This says nothing about other public bases or observables. -/
theorem control_any_power_rows_none (es : List ℤ) :
    SemiprimeGuardedTrace.guardedTraceRows (es.map fun e => controlBase^e)=none := by
  apply (SemiprimeGuardedTrace.guardedTraceRows_none_iff _).mpr
  constructor
  · apply (scanProper_none_iff _ _).mpr
    intro v hv
    unfold SemiprimeGuardedTrace.endpointLeaves at hv
    obtain ⟨x,hx,hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨i,hi⟩ := control_power_represented e
    rw [hi] at hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl
    · exact (control_finite_endpoint_checks i).1
    · exact (control_finite_endpoint_checks i).2
  · intro x hx y hy
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨f,_,rfl⟩ := List.mem_map.mp hy
    obtain ⟨i,hi⟩ := control_power_represented e
    obtain ⟨j,hj⟩ := control_power_represented f
    rw [hi,hj]
    exact control_finite_pair_checks i j

theorem control_public_original_none (m : ℕ) :
    SemiprimeGuardedTrace.publicGuardedTraceRows m controlBase=none := by
  simpa [SemiprimeGuardedTrace.publicGuardedTraceRows,SemiprimeGuardedTrace.publicUnitRows,
    publicExponents,List.map_map,Function.comp_def] using
      control_any_power_rows_none (publicExponents 2047 m)

theorem control_public_weighted_none (m : ℕ) :
    SemiprimeWeightedRows.recoverWeightedRows m controlBase=none := by
  exact control_any_power_rows_none (SemiprimeWeightedRows.publicWeightedExponents 2047 m)

/-- A balanced control whose smallest factor lies beyond the B-squared prefix. -/
def balancedControlBase : (ZMod 2304167)ˣ :=
  ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 2304167)

theorem balanced_control_order : orderOf balancedControlBase=29 := by
  let : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · apply Units.ext
    norm_num only [balancedControlBase,Units.val_pow_eq_pow_val,ZMod.coe_unitOfCoprime,
      Units.val_one]
    reduce_mod_char
  · decide +kernel

theorem balanced_control_power_reduce (e : ℤ) :
    balancedControlBase^e=balancedControlBase^(e%29).toNat := by
  have h := zpow_mod_orderOf balancedControlBase e
  rw [balanced_control_order] at h
  norm_num only [Nat.cast_ofNat] at h
  have hr : ((e%29).toNat : ℤ)=e%29 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  rw [←hr,zpow_natCast] at h
  exact h.symm

set_option maxRecDepth 32768 in
/-- The complete original N-only packet cache discovers period 29.
The period and the colliding packets are not supplied to the constructor. -/
theorem balanced_control_public_period : publicRetainedPeriod 13 balancedControlBase=29 := by
  unfold publicRetainedPeriod publicTaggedRows
  simp_rw [balanced_control_power_reduce]
  decide +kernel

set_option maxRecDepth 32768 in
/-- Changing to each further base from three through thirteen still fails
for the actual cached period. The reconstruction observable is separate. -/
theorem balanced_control_probe_menu_none :
    recoverPublicRowPeriods 13 balancedControlBase [3,4,5,6,7,8,9,10,11,12,13]=none := by
  unfold recoverPublicRowPeriods
  rw [balanced_control_public_period]
  norm_num [probePeriod,periodProbeLeaves,scanProper,SemiprimeGroupSelection.checkedSignal,
    ZMod.val_ofNat]

set_option maxRecDepth 32768 in
/-- Actual N-only cache acquisition followed by the bounded wrap scan
recovers the factor. Neither period 29 nor the correct wrap label is an input. -/
theorem balanced_control_public_wrapped_recovers :
    recoverPublicWrappedPeriod 13 13 balancedControlBase=some 1103 := by
  unfold recoverPublicWrappedPeriod
  rw [balanced_control_public_period]
  norm_num [SemiprimeCommonOrder.recoverWrapped,SemiprimeCommonOrder.wrappedCandidate,
    SemiprimeCommonOrder.indexSum,SemiprimeCommonOrder.indexProduct,
    SemiprimeCommonOrder.orderQuotient,scanProper,SemiprimeGroupSelection.checkedSignal,
    List.range_eq_range',List.range'_succ]

/-- The actual sorted full-cache constructor and bounded public recovery
give the same certified factor without association-list lookup. -/
theorem balanced_control_sorted_wrapped_recovers :
    recoverPublicSortedWrappedPeriod 13 13 balancedControlBase=some 1103 := by
  rw [recoverPublicSortedWrappedPeriod_eq]
  exact balanced_control_public_wrapped_recovers

theorem balanced_control_arithmetic : Nat.Prime 1103 ∧ Nat.Prime 2089 ∧
    1103*2089=2304167 ∧ 1103≤2089 ∧ 2089≤2*1103 ∧ (13 : ℕ)^2<1103 ∧
    2304167≤(13 : ℕ)^6 ∧ Nat.Prime 13 ∧ Nat.Coprime 13 2304167 ∧
    13≤29 ∧ Nat.Prime 29 ∧ ((2304167 : ℕ).gcd 1)=1 := by
  norm_num [Nat.Coprime]

/-- The generic guarantee applies to the actual discovered period,
discharging its primality, common-modulus check, size and balanced budget. -/
theorem balanced_control_from_public_certificate :
    ∃ f, recoverPublicWrappedPeriod 13 13 balancedControlBase=some f := by
  apply recoverPublicWrappedPeriod_of_prime_period (p:=1103) (q:=2089)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) balancedControlBase
  · rw [balanced_control_public_period]
    norm_num
  · rw [balanced_control_public_period]
    norm_num
  · norm_num [balancedControlBase,ZMod.val_ofNat,ZMod.val_one]
    decide +kernel

/-- A balanced input beyond the quadratic prefix with no nonzero cached relation. -/
def zeroControlBase : (ZMod 143)ˣ :=
  ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 143)

theorem zero_control_power : zeroControlBase^60=1 := by
  apply Units.ext
  norm_num only [zeroControlBase,Units.val_pow_eq_pow_val,ZMod.coe_unitOfCoprime,
    Units.val_one]
  reduce_mod_char

set_option maxRecDepth 32768 in
/-- The actual public packet cache can return zero on a balanced semiprime.
The other row observables are not ruled out on this input. -/
theorem zero_control_public_period : publicRetainedPeriod 3 zeroControlBase=0 := by
  unfold publicRetainedPeriod publicTaggedRows
  simp_rw [signed_power_reduce_of_period zeroControlBase (by decide : 0<60) zero_control_power]
  decide +kernel

theorem zero_control_probes_none (bases : List ℕ) :
    recoverPublicRowPeriods 3 zeroControlBase bases=none := by
  simp [recoverPublicRowPeriods,zero_control_public_period,probePeriod]

theorem zero_control_wrapped_none (B : ℕ) :
    recoverPublicWrappedPeriod B 3 zeroControlBase=none := by
  simp [recoverPublicWrappedPeriod,zero_control_public_period,SemiprimeCommonOrder.recoverWrapped]

theorem zero_control_sorted_wrapped_none (B : ℕ) :
    recoverPublicSortedWrappedPeriod B 3 zeroControlBase=none := by
  rw [recoverPublicSortedWrappedPeriod_eq]
  exact zero_control_wrapped_none B

theorem zero_control_arithmetic : Nat.Prime 11 ∧ Nat.Prime 13 ∧ 11*13=143 ∧
    11≤13 ∧ 13≤2*11 ∧ (3 : ℕ)^2<11 ∧ 143≤(3 : ℕ)^6 ∧ Nat.Coprime 3 143 := by
  norm_num [Nat.Coprime]

end RiemannGaussian.SemiprimeRowPeriods
