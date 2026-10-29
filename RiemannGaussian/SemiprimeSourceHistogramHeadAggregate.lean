/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramAcquiredSums
import RiemannGaussian.SemiprimeSourceHistogramPortKeys
import RiemannGaussian.SemiprimeSourceHistogramSquares
import RiemannGaussian.SemiprimeSourceHistogramFeatureBits

/-! # Original all-coordinate head count from one derived sparse histogram
The fixed/free lists and the fixed-vertex/coordinate occurrence list are derived
from actual original finite lists. No collision count is supplied as input.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeSourceHistogramHeadAggregate
open scoped BigOperators
open SemiprimeSourceHistogramGrouping SemiprimeSourceHistogramOriginalSums
open SemiprimeMaterializedScoreEnvironment

/-- The actual sparse squared multiplicities of an occurrence-label list. -/
def squares {A B : Type*} [DecidableEq B] (xs : List A) (label : A→B) : ℕ :=
  ∑ k∈(xs.map label).toFinset,(multiplicity label xs k)^2

/-- A physical byte map with exactly the original label equalities has the
original sparse collision count, including every repeated occurrence. -/
theorem collision_map_iff {A B : Type*} [DecidableEq B] (xs : List A)
    (bytes : A→List Bool) (label : A→B)
    (he : ∀a∈xs,∀b∈xs,bytes a=bytes b ↔ label a=label b) :
    SemiprimeSourceHistogramSquares.collisions (xs.map bytes)=squares xs label := by
  rw [SemiprimeSourceHistogramSquares.collisions,SemiprimeSourceHistogramFeatureBits.pairs_map]
  calc
    _=pairs xs (fun a b => if label a=label b then (1:ℕ) else 0) := by
      unfold pairs
      congr 1
      apply List.map_congr_left
      intro a ha
      congr 1
      apply List.map_congr_left
      intro b hb
      dsimp only
      simp only [he a ha b hb]
    _= _ := pair_grouping label xs

/-- Exact list sum restricted by an actual Boolean filter. -/
theorem filter_sum {A R : Type*} [AddCommMonoid R] (xs : List A) (p : A→Bool) (f : A→R) :
    ((xs.filter p).map f).sum=(xs.map (fun a => if p a then f a else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h:p a <;> simp [h,ih]

/-- Filtering both ordered pair coordinates does not lose list multiplicities. -/
theorem pairs_filter {A R : Type*} [AddCommMonoid R] (xs : List A) (p : A→Bool) (f : A→A→R) :
    pairs (xs.filter p) f=pairs xs (fun a b => if p a && p b then f a b else 0) := by
  unfold pairs
  rw [filter_sum]
  simp_rw [filter_sum]
  congr 1
  apply List.map_congr_left
  intro a _
  cases h:p a <;> simp

/-- Actual zero/one filter-weight sum is the filtered occurrence count. -/
theorem filter_ones {A : Type*} (xs : List A) (p : A→Bool) :
    (xs.map (fun a => if p a then (1:ℚ) else 0)).sum=((xs.filter p).length:ℚ) := by
  rw [←filter_sum]
  simp

/-- With injective keys, a weighted collision sum has only actual list diagonals. -/
theorem injective_squares {A B R : Type*} [DecidableEq A] [DecidableEq B] [CommSemiring R]
    (xs : List A) (hn : xs.Nodup) (label : A→B) (hi : Function.Injective label) (w : A→R) :
    (∑ k∈(xs.map label).toFinset,(bucket label xs w k)^2)=(xs.map (fun a => (w a)^2)).sum := by
  rw [←weighted_pair_grouping]
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [←List.sum_toFinset _ hn]
  simp only [hi.eq_iff]
  simp [ha,pow_two]

/-- Zero/one occurrence weights select precisely the actual filtered collisions. -/
theorem masked_squares {A B : Type*} [DecidableEq B] (xs : List A) (label : A→B) (p : A→Bool) :
    (∑ k∈(xs.map label).toFinset,
      (bucket label xs (fun a => if p a then (1:ℚ) else 0) k)^2)=
      ((pairs (xs.filter p) (fun a b => if label a=label b then (1:ℕ) else 0):ℕ):ℚ) := by
  rw [←weighted_pair_grouping,cast_pairs,pairs_filter]
  unfold pairs
  congr 1
  apply List.map_congr_left
  intro a _
  congr 1
  apply List.map_congr_left
  intro b _
  dsimp only
  cases ha:p a <;> cases hb:p b <;> by_cases he:label a=label b <;> simp [he]

/-- Fixed original vertices in their actual ascending source order. -/
def fixedVertices (n : ℕ) (remaining : List ℕ) : List (Fin n) :=
  (List.finRange n).filter (fun v => decide (v.val∉remaining))

/-- Free original vertices in their actual ascending source order. -/
def freeVertices (n : ℕ) (remaining : List ℕ) : List (Fin n) :=
  (List.finRange n).filter (fun v => decide (v.val∈remaining))


/-- Fixed-colour collision pairs at one actual original coordinate. -/
def fixedCollision (n r Q : ℕ) (q : Fin Q) (remaining : List ℕ) (env : Environment r Q) : ℕ :=
  pairs (fixedVertices n remaining) (fun v w => if denote env v.val q=denote env w.val q then 1 else 0)

/-- Original vertices have injective variable keys, so the free-key squared
histogram equals the actual number of free vertices. -/
theorem free_squares (n : ℕ) (remaining : List ℕ) :
    (∑ k∈((List.finRange n).map Fin.val).toFinset,
      (bucket Fin.val (List.finRange n)
        (fun v => if v.val∈remaining then (1:ℚ) else 0) k)^2)=
      ((freeVertices n remaining).length:ℚ) := by
  rw [injective_squares (List.finRange n) (List.nodup_finRange n) Fin.val Fin.val_injective]
  have hi : (fun v : Fin n => ((if v.val∈remaining then (1:ℚ) else 0)^2))=
      (fun v : Fin n => if v.val∈remaining then (1:ℚ) else 0) := by
    funext v
    by_cases h : v.val∈remaining <;> simp [h]
  rw [hi]
  simpa only [freeVertices,decide_eq_true_eq] using
    filter_ones (List.finRange n) (fun v => decide (v.val∈remaining))

/-- The fixed-colour weighted histogram is the literal fixed-vertex pair count. -/
theorem fixed_squares (n r Q : ℕ) (q : Fin Q) (remaining : List ℕ) (env : Environment r Q) :
    (∑ c∈((List.finRange n).map (fun v => denote env v.val q)).toFinset,
      (bucket (fun v => denote env v.val q) (List.finRange n)
        (fun v => if v.val∈remaining then (0:ℚ) else 1) c)^2)=
      (fixedCollision n r Q q remaining env:ℚ) := by
  simpa only [fixedCollision,fixedVertices,decide_eq_true_eq,ite_not] using
    masked_squares (List.finRange n) (fun v => denote env v.val q)
      (fun v => decide (v.val∉remaining))

/-- The fixed-mask sum is the actual fixed-list count. -/
theorem fixed_sum (n : ℕ) (remaining : List ℕ) :
    ((List.finRange n).map (fun v => if v.val∈remaining then (0:ℚ) else 1)).sum=
      ((fixedVertices n remaining).length:ℚ) := by
  simpa only [fixedVertices,decide_eq_true_eq,ite_not] using
    filter_ones (List.finRange n) (fun v => decide (v.val∉remaining))

/-- One-coordinate original histogram with injective source vertices simplified. -/
theorem headHistogram_simplified (n r Q : ℕ) (q : Fin Q) (remaining : List ℕ) (env : Environment r Q) :
    headHistogram (List.finRange n) Fin.val r Q q remaining env=
      (((r^Q)^4:ℕ):ℚ)*(fixedCollision n r Q q remaining env:ℚ)+
      ((r^(4*Q-1):ℕ):ℚ)*((n:ℚ)^2-((fixedVertices n remaining).length:ℚ)^2)+
      ((((r^Q)^4:ℕ):ℚ)-((r^(4*Q-1):ℕ):ℚ))*((freeVertices n remaining).length:ℚ) := by
  unfold headHistogram
  dsimp only
  rw [fixed_squares,free_squares,fixed_sum]
  simp


/-- Two literal list sums commute, preserving every occurrence on either side. -/
theorem sum_comm {A B R : Type*} [AddCommMonoid R] (xs : List A) (ys : List B) (f : A→B→R) :
    (xs.map (fun a => (ys.map (f a)).sum)).sum=
      (ys.map (fun b => (xs.map (fun a => f a b)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.map_cons,List.sum_cons,ih,List.sum_map_add]

/-- A literal coordinate row selects exactly its one matching original coordinate. -/
theorem coordinate_row {n r Q : ℕ} (qs : List (Fin Q)) (hn : qs.Nodup)
    (env : Environment r Q) (v w : Fin n) (q : Fin Q) (hq : q∈qs) :
    (qs.map (fun t => if (q.val,(denote env v.val q).val)=(t.val,(denote env w.val t).val)
      then (1:ℕ) else 0)).sum=
      if denote env v.val q=denote env w.val q then 1 else 0 := by
  have he : (fun t => if (q.val,(denote env v.val q).val)=(t.val,(denote env w.val t).val)
      then (1:ℕ) else 0)=
      (fun t => if q=t then (if denote env v.val q=denote env w.val q then 1 else 0) else 0) := by
    funext t
    by_cases ht : q=t
    · subst t
      simp only [Prod.mk.injEq,Fin.val_inj,true_and,ite_true]
    · simp only [Prod.mk.injEq,Fin.val_inj,ht,false_and,ite_false]
  rw [he,←List.sum_toFinset _ hn]
  simp [hq]

/-- Joint coordinate/colour collisions have no cross-coordinate aliases.
The source Cartesian list may be fixed-major although the original sum is q-major. -/
theorem coordinate_pairs {n r Q : ℕ} (vertices : List (Fin n)) (qs : List (Fin Q))
    (hn : qs.Nodup) (env : Environment r Q) :
    pairs (vertices.product qs) (fun a b =>
      if (a.2.val,(denote env a.1.val a.2).val)=(b.2.val,(denote env b.1.val b.2).val)
      then (1:ℕ) else 0)=
      (qs.map (fun q => pairs vertices (fun v w => if denote env v.val q=denote env w.val q then 1 else 0))).sum := by
  calc
    _=(vertices.map (fun v => (qs.map (fun q =>
      (vertices.map (fun w => if denote env v.val q=denote env w.val q then (1:ℕ) else 0)).sum)).sum)).sum := by
      unfold pairs
      rw [SemiprimeSourceHistogramOriginalSums.sum_product]
      congr 1
      apply List.map_congr_left
      intro v _
      congr 1
      apply List.map_congr_left
      intro q hq
      dsimp only
      rw [SemiprimeSourceHistogramOriginalSums.sum_product]
      congr 1
      apply List.map_congr_left
      intro w _
      exact coordinate_row qs hn env v w q hq
    _= _ := sum_comm vertices qs _

/-- The actual fixed-major head occurrence list. -/
def headOccurrences (n Q : ℕ) (remaining : List ℕ) : List (Fin n×Fin Q) :=
  (fixedVertices n remaining).product (List.finRange Q)

/-- Original coordinate/colour key, using literal finite values. -/
def colourKey {n r Q : ℕ} (env : Environment r Q) (z : Fin n×Fin Q) : ℕ×ℕ :=
  (z.2.val,(denote env z.1.val z.2).val)

/-- Derived sparse head collision count; never an input answer. -/
def collisionCount (n r Q : ℕ) (remaining : List ℕ) (env : Environment r Q) : ℕ :=
  squares (headOccurrences n Q remaining) (colourKey env)

/-- The one actual joint-key histogram is the sum of every original coordinate's
fixed collision count, including Q0 and empty fixed lists. -/
theorem collisionCount_coordinates (n r Q : ℕ) (remaining : List ℕ) (env : Environment r Q) :
    collisionCount n r Q remaining env=
      ((List.finRange Q).map (fun q => fixedCollision n r Q q remaining env)).sum := by
  unfold collisionCount squares
  rw [←pair_grouping]
  exact coordinate_pairs (fixedVertices n remaining) (List.finRange Q) (List.nodup_finRange Q) env


/-- Actual fixed/free vertex lists partition the complete original vertex list. -/
theorem fixed_free_length (n : ℕ) (remaining : List ℕ) :
    (fixedVertices n remaining).length+(freeVertices n remaining).length=n := by
  have h (xs : List (Fin n)) :
      (xs.filter (fun v => decide (v.val∉remaining))).length+
      (xs.filter (fun v => decide (v.val∈remaining))).length=xs.length := by
    induction xs with
    | nil => rfl
    | cons v xs ih =>
      by_cases hv : v.val∈remaining <;> simp [hv] at * <;> omega
  simpa only [fixedVertices,freeVertices,List.length_finRange] using h (List.finRange n)

/-- Subtraction-free free off-diagonal count, valid also when f=0. -/
theorem free_offdiag (f : ℕ) : f*(f-1)+f=f^2 := by
  cases f with
  | zero => rfl
  | succ f => simp only [Nat.add_one_sub_one];ring

/-- Summing the actual coordinate histograms yields one joint C and two counts. -/
theorem coordinate_histogram_sum (n r Q : ℕ) (remaining : List ℕ) (env : Environment r Q) :
    ((List.finRange Q).map (fun q => headHistogram (List.finRange n) Fin.val r Q q remaining env)).sum=
      (((r^Q)^4:ℕ):ℚ)*(collisionCount n r Q remaining env:ℚ)+
      (Q:ℚ)*(((r^(4*Q-1):ℕ):ℚ)*((n:ℚ)^2-((fixedVertices n remaining).length:ℚ)^2)+
        ((((r^Q)^4:ℕ):ℚ)-((r^(4*Q-1):ℕ):ℚ))*((freeVertices n remaining).length:ℚ)) := by
  simp_rw [headHistogram_simplified]
  have hc : ((List.finRange Q).map (fun q => (fixedCollision n r Q q remaining env:ℚ))).sum=
      (collisionCount n r Q remaining env:ℚ) := by
    rw [collisionCount_coordinates,Nat.cast_list_sum,List.map_map]
    rfl
  simp only [List.sum_map_add,List.sum_map_mul_left,List.map_const',List.sum_replicate,
    List.length_finRange,nsmul_eq_mul]
  rw [hc]
  ring

/-- The full positive original head-count expression from one derived sparse C. -/
def total (n r Q : ℕ) (remaining : List ℕ) (env : Environment r Q) : ℕ :=
  let p := (fixedVertices n remaining).length
  let f := (freeVertices n remaining).length
  (r^Q)^4*(collisionCount n r Q remaining env+Q*f)+
    r^(4*Q-1)*Q*(2*p*f+f*(f-1))

/-- The rational histogram identity equals the exact nonnegative integer formula. -/
theorem coordinate_sum_total (n r Q : ℕ) (remaining : List ℕ) (env : Environment r Q) :
    ((List.finRange Q).map (fun q => headHistogram (List.finRange n) Fin.val r Q q remaining env)).sum=
      (total n r Q remaining env:ℚ) := by
  rw [coordinate_histogram_sum]
  let p := (fixedVertices n remaining).length
  let f := (freeVertices n remaining).length
  have hnp : (n:ℚ)=(p:ℚ)+(f:ℚ) := by
    have h:=fixed_free_length n remaining
    exact_mod_cast h.symm
  have hoff : (f:ℚ)*((f-1:ℕ):ℚ)=(f:ℚ)^2-(f:ℚ) := by
    have h:=congrArg (fun z : ℕ => (z:ℚ)) (free_offdiag f)
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow] at h
    linarith
  change (((r^Q)^4:ℕ):ℚ)*(collisionCount n r Q remaining env:ℚ)+
    (Q:ℚ)*(((r^(4*Q-1):ℕ):ℚ)*((n:ℚ)^2-(p:ℚ)^2)+
      ((((r^Q)^4:ℕ):ℚ)-((r^(4*Q-1):ℕ):ℚ))*(f:ℚ))=
    (((r^Q)^4*(collisionCount n r Q remaining env+Q*f)+
      r^(4*Q-1)*Q*(2*p*f+f*(f-1)):ℕ):ℚ)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  rw [hnp,hoff]
  ring

/-- ACTUAL original compiled head lane, from original public arity/owner metadata.
Its only collision scalar is the derived fixed-vertex/coordinate histogram above. -/
theorem original_head_lane (n F r Q : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (remaining : List ℕ) (env : Environment r Q) (hn : remaining.Nodup) :
    let old := SemiprimeSourceWordIdMetadata.acquire n F Q arity
    (SemiprimeSourceScoreCountsObjective.evaluateCounts (SemiprimeFiniteEnumerations.words r Q).values
      (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst old.indices old.terms).value
      remaining env).value.head=total n r Q remaining env := by
  have h:=(SemiprimeSourceHistogramAcquiredSums.acquired_original_lanes
    n F r Q arity owner (NeZero.pos r) remaining env hn).2
  have hv : (SemiprimeSourceHistogramMetadata.acquire n F Q arity).vertices=List.finRange n := by
    simp only [SemiprimeSourceHistogramMetadata.acquire,SemiprimeSourceHistogramMetadata.finFast_value]
  have hq : (SemiprimeSourceHistogramMetadata.acquire n F Q arity).coordinates=List.finRange Q := by
    simp only [SemiprimeSourceHistogramMetadata.acquire,SemiprimeSourceHistogramMetadata.finFast_value]
  have hk : (fun v : Fin n => OAI.Algorithms.SubexponentialSAT.LocalExpectation.indexCode
      (SemiprimeSourceHistogramMetadata.acquire n F Q arity).indices (.inl v))=Fin.val := by
    funext v
    exact SemiprimeSourceHistogramPortKeys.indexCode_inl n F Q arity v
  rw [hv,hq,hk,coordinate_sum_total] at h
  exact_mod_cast h

end RiemannGaussian.SemiprimeSourceHistogramHeadAggregate
