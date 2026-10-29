import Mathlib
import RiemannGaussian.SemiprimeSourceHeadCountFormula
set_option autoImplicit false
namespace SparseCollisionHistogram
open scoped BigOperators

/-- Actual list multiplicity, not cardinality of deduplicated ports. -/
def multiplicity {α β : Type*} [DecidableEq β] (label : α → β) (xs : List α) (k : β) : ℕ :=
  xs.countP (fun a => decide (label a=k))

/-- Literal indicator scan equals the list predicate count. -/
theorem indicator_sum {α β : Type*} [DecidableEq β]
    (label : α → β) (xs : List α) (k : β) :
    (xs.map (fun a => if label a=k then (1:ℕ) else 0)).sum=multiplicity label xs k := by
  induction xs with
  | nil => simp [multiplicity]
  | cons a xs ih =>
    simp only [List.map_cons,List.sum_cons,multiplicity,List.countP_cons] at *
    by_cases h : label a=k <;> simp [h,ih,Nat.add_comm]

/-- Multiplicity is the ordinary count in the actually derived key list. -/
theorem multiplicity_map {α β : Type*} [DecidableEq β]
    (label : α → β) (xs : List α) (k : β) :
    multiplicity label xs k=(xs.map label).count k := by
  induction xs with
  | nil => simp [multiplicity]
  | cons a xs ih =>
    simp only [multiplicity,List.countP_cons,List.map_cons,List.count_cons] at *
    by_cases h : label a=k <;> simp [h,ih]

/-- Exact sparse pair grouping over actual list occurrences, including duplicates. -/
theorem pair_grouping {α β : Type*} [DecidableEq β]
    (label : α → β) (xs : List α) :
    (xs.map (fun a => (xs.map (fun b => if label a=label b then (1:ℕ) else 0)).sum)).sum=
      ∑ k∈(xs.map label).toFinset,(multiplicity label xs k)^2 := by
  have hi (a : α) :
      (xs.map (fun b => if label a=label b then (1:ℕ) else 0)).sum=
        (xs.map label).count (label a) := by
    simpa only [eq_comm,multiplicity_map] using indicator_sum label xs (label a)
  simp_rw [hi,multiplicity_map]
  have hs:=Finset.sum_list_map_count (xs.map label) (fun k => (xs.map label).count k)
  simpa [List.map_map,Function.comp_def,nsmul_eq_mul,pow_two] using hs

/-- Joint head/slot incidence labels require no injectivity or port deduplication. -/
theorem joint_pair_grouping {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (head : α → β) (slot : α → γ) (xs : List α) :
    (xs.map (fun a => (xs.map (fun b =>
      if head a=head b ∧ slot a=slot b then (1:ℕ) else 0)).sum)).sum=
      ∑ k∈(xs.map (fun a => (head a,slot a))).toFinset,
        (multiplicity (fun a => (head a,slot a)) xs k)^2 := by
  simpa only [Prod.mk.injEq] using pair_grouping (fun a => (head a,slot a)) xs


/-- Sparse regrouping for arbitrary occurrence weights and an explicitly covering key set. -/
theorem regroup {α β R : Type*} [DecidableEq β] [AddCommMonoid R]
    (label : α→β) (xs : List α) (keys : Finset β) (weight : α→R)
    (hk : ∀ a∈xs,label a∈keys) :
    (xs.map weight).sum=∑ k∈keys,(xs.map (fun a => if label a=k then weight a else 0)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha:=hk a List.mem_cons_self
    have ht:=ih (fun b hb => hk b (List.mem_cons_of_mem a hb))
    simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib]
    rw [← ht]
    simp [ha]

/-- The bucket value is acquired from the literal occurrence list, not supplied. -/
def bucket {α β R : Type*} [DecidableEq β] [AddCommMonoid R]
    (label : α→β) (xs : List α) (weight : α→R) (k : β) : R :=
    (xs.map (fun a => if label a=k then weight a else 0)).sum

/-- Weighted collision grouping, valid also for signed/rational weights. -/
theorem weighted_pair_grouping {α β R : Type*} [DecidableEq β] [CommSemiring R]
    (label : α→β) (xs : List α) (weight : α→R) :
    (xs.map (fun a => (xs.map (fun b =>
      if label a=label b then weight a*weight b else 0)).sum)).sum=
      ∑ k∈(xs.map label).toFinset,(bucket label xs weight k)^2 := by
  have hi (a : α) : (xs.map (fun b =>
      if label a=label b then weight a*weight b else 0)).sum=
      weight a*bucket label xs weight (label a) := by
    unfold bucket
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro b _
    by_cases h : label a=label b <;> simp [h,Ne.symm]
  simp_rw [hi]
  rw [regroup label xs (xs.map label).toFinset
    (fun a => weight a*bucket label xs weight (label a))
    (fun a ha => List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,ha,rfl⟩))]
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_two]
  change _ = (xs.map (fun a => if label a=k then weight a else 0)).sum * bucket label xs weight k
  rw [← List.sum_map_mul_right]
  congr 1
  apply List.map_congr_left
  intro a _
  by_cases h : label a=k <;> simp [h]


/-- Ordered double list scan, preserving every repeated occurrence. -/
def pairs {α R : Type*} [AddCommMonoid R] (xs : List α) (f : α→α→R) : R :=
  (xs.map (fun a => (xs.map (f a)).sum)).sum

theorem pairs_add {α R : Type*} [AddCommMonoid R] (xs : List α) (f g : α→α→R) :
    pairs xs (fun a b => f a b+g a b)=pairs xs f+pairs xs g := by
  simp only [pairs,List.sum_map_add]

theorem pairs_sub {α R : Type*} [AddCommGroup R] (xs : List α) (f g : α→α→R) :
    pairs xs (fun a b => f a b-g a b)=pairs xs f-pairs xs g := by
  have hs (u v : α→R) : (xs.map (fun a => u a-v a)).sum=
      (xs.map u).sum-(xs.map v).sum := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp only [List.map_cons,List.sum_cons,ih];abel
  unfold pairs
  simp_rw [hs]

theorem pairs_scale {α R : Type*} [Semiring R] (xs : List α) (c : R) (f : α→α→R) :
    pairs xs (fun a b => c*f a b)=c*pairs xs f := by
  simp only [pairs,List.sum_map_mul_left]

theorem pairs_product {α R : Type*} [Semiring R] (xs : List α) (f g : α→R) :
    pairs xs (fun a b => f a*g b)=(xs.map f).sum*(xs.map g).sum := by
  simp only [pairs,List.sum_map_mul_left,List.sum_map_mul_right]

/-- Exact partial-prefix head grouping. Fixed weights select anchored occurrences;
free-key buckets retain aliases among repeated ports, not merely their colours. -/
theorem head_prefix_grouping {α κ γ R : Type*} [DecidableEq κ] [DecidableEq γ]
    [CommRing R] (xs : List α) (key : α→κ) (colour : κ→γ) (active : κ→Prop)
    [DecidablePred active] (A B : R) :
    pairs xs (fun a b => if key a=key b then A
      else if active (key a) ∨ active (key b) then B
      else if colour (key a)=colour (key b) then A else 0)=
      A*(∑ c∈(xs.map (fun a => colour (key a))).toFinset,
        (bucket (fun a => colour (key a)) xs
          (fun a => if active (key a) then (0:R) else 1) c)^2)+
      B*(((xs.map (fun _ => (1:R))).sum)^2-
        ((xs.map (fun a => if active (key a) then (0:R) else 1)).sum)^2)+
      (A-B)*(∑ k∈(xs.map key).toFinset,
        (bucket key xs (fun a => if active (key a) then (1:R) else 0) k)^2) := by
  let fixed : α→R := fun a => if active (key a) then 0 else 1
  let free : α→R := fun a => if active (key a) then 1 else 0
  have point (a b : α) :
      (if key a=key b then A else if active (key a) ∨ active (key b) then B
        else if colour (key a)=colour (key b) then A else 0)=
      A*(if colour (key a)=colour (key b) then fixed a*fixed b else 0)+
      B*((1:R)-fixed a*fixed b)+
      (A-B)*(if key a=key b then free a*free b else 0) := by
    by_cases hk : key a=key b
    · by_cases ha : active (key a)
      · simp [← hk,ha,fixed,free]
      · simp [← hk,ha,fixed,free]
    · by_cases ha : active (key a) <;> by_cases hb : active (key b) <;>
        by_cases hc : colour (key a)=colour (key b) <;> simp [hk,ha,hb,hc,fixed]
  have hp : (fun a b => if key a=key b then A
      else if active (key a) ∨ active (key b) then B
      else if colour (key a)=colour (key b) then A else 0)=
      (fun a b => A*(if colour (key a)=colour (key b) then fixed a*fixed b else 0)+
        B*((1:R)-fixed a*fixed b)+(A-B)*(if key a=key b then free a*free b else 0)) := by
    funext a b
    exact point a b
  rw [hp,pairs_add,pairs_add,pairs_scale,pairs_scale,pairs_scale,pairs_sub]
  have hf:=weighted_pair_grouping (fun a => colour (key a)) xs fixed
  have hfree:=weighted_pair_grouping key xs free
  change pairs xs (fun a b => if colour (key a)=colour (key b) then fixed a*fixed b else 0)=_ at hf
  change pairs xs (fun a b => if key a=key b then free a*free b else 0)=_ at hfree
  rw [hf,hfree,pairs_product]
  have hone : pairs xs (fun _ _ => (1:R))=((xs.map (fun _ => (1:R))).sum)^2 := by
    simpa only [one_mul,pow_two] using pairs_product xs (fun _ => (1:R)) (fun _ => (1:R))
  rw [hone]
  simp only [fixed,free,pow_two]


/-- Actual original padded head-pair list reduces pointwise to the histogram kernel.
Composing this with head_prefix_grouping gives the full partial-prefix histogram. -/
theorem original_head_pairs {α : Type*} (xs : List α) (key : α→ℕ)
    (r Q : ℕ) (q : Fin Q) (remaining : List ℕ)
    (env : RiemannGaussian.SemiprimeMaterializedScoreEnvironment.Environment r Q)
    (hn : remaining.Nodup) :
    pairs xs (fun a b => ((RiemannGaussian.SemiprimeSourceScoreCountsPadding.paddedLocal
      (RiemannGaussian.SemiprimeFiniteEnumerations.words r Q).values
      (.head q (key a) (key b)) remaining env).value : ℤ))=
    pairs xs (fun a b => if key a=key b then (((r^Q)^4:ℕ):ℤ)
      else if key a∈remaining ∨ key b∈remaining then ((r^(4*Q-1):ℕ):ℤ)
      else if RiemannGaussian.SemiprimeMaterializedScoreEnvironment.denote env (key a) q=
          RiemannGaussian.SemiprimeMaterializedScoreEnvironment.denote env (key b) q
        then (((r^Q)^4:ℕ):ℤ) else 0) := by
  unfold pairs
  congr 1
  apply List.map_congr_left
  intro a _
  congr 1
  apply List.map_congr_left
  intro b _
  dsimp only
  rw [RiemannGaussian.SemiprimeSourceHeadCountFormula.head_padded_original r Q q
    (key a) (key b) remaining env hn]
  split_ifs <;> rfl


/-- The derived sparse key set never exceeds the actual occurrence-list length. -/
theorem sparse_keys_card {α β : Type*} [DecidableEq β] (label : α→β) (xs : List α) :
    (xs.map label).toFinset.card≤xs.length := by
  simpa only [List.length_map] using List.toFinset_card_le (xs.map label)

end SparseCollisionHistogram
