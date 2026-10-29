/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramGrouping
import RiemannGaussian.SemiprimeSourceIncidenceCountFormula

/-! # Sixteen sparse features for the actual conditional incidence count
No full pair list or incidence-matrix oracle is an input. Histogram bins and
weights derive from the actual occurrence list, retaining parallel incidences.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceIncidenceHistogram
open scoped BigOperators
open SemiprimeSourceHistogramGrouping SemiprimeSourceIncidencePairAverage
open SemiprimeSourceIncidenceCountFormula
open SemiprimeMaterializedScoreEnvironment

/-- Four equality features: constant, free-key diagonal, fixed-label bucket,
and fixed-constant correction. -/
abbrev Feature := Fin 4

/-- Signed coefficients of L times the exact equality kernel. -/
def coefficient (L : ℚ) (f : Feature) : ℚ := ![1,L-1,L,-1] f

/-- Actual per-key eligibility; fixed-label reads are needed only for feature 2. -/
def featureWeight (remaining : List ℕ) (f : Feature) (a : ℕ) : ℚ :=
  if f=0 then 1 else if f=1 then if a∈remaining then 1 else 0
  else if a∈remaining then 0 else 1

/-- Each feature has one derived equality key, not a supplied histogram. -/
def featureKey {W : Type*} (ω : ℕ → W) (f : Feature) (a : ℕ) : ℕ ⊕ W :=
  if f=1 then .inl a else if f=2 then .inr (ω a) else .inl 0

/-- Actual weighted same-feature collision of two original keys. -/
def featurePair {W : Type*} [DecidableEq W] (remaining : List ℕ) (ω : ℕ → W)
    (f : Feature) (a c : ℕ) : ℚ :=
  if featureKey ω f a=featureKey ω f c then
    featureWeight remaining f a*featureWeight remaining f c else 0

/-- Scaled original conditional kernel, using no unknown inverse. -/
def kernel {W : Type*} [DecidableEq W] (L : ℚ) (remaining : List ℕ)
    (ω : ℕ → W) (a c : ℕ) : ℚ :=
  if a=c then L else if a∈remaining ∨ c∈remaining then 1
  else if ω a=ω c then L else 0

/-- Pointwise four-feature identity; aliases and all fixed/free cases are exact. -/
theorem kernel_expansion {W : Type*} [DecidableEq W] (L : ℚ)
    (remaining : List ℕ) (ω : ℕ → W) (a c : ℕ) :
    kernel L remaining ω a c=∑ f : Feature,coefficient L f*featurePair remaining ω f a c := by
  classical
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  by_cases he : a=c
  · subst c
    by_cases ha : a∈remaining <;>
      simp [kernel,coefficient,featurePair,featureKey,featureWeight,ha]
  · by_cases ha : a∈remaining <;> by_cases hc : c∈remaining <;>
      by_cases hw : ω a=ω c <;>
      simp [kernel,coefficient,featurePair,featureKey,featureWeight,he,ha,hc,hw]

/-- Scaling by the known positive menu length matches the existing potential. -/
theorem kernel_potential {W : Type*} [DecidableEq W] (L : ℕ) (hL : 0<L)
    (remaining : List ℕ) (ω : ℕ → W) (a c : ℕ) :
    kernel (L:ℚ) remaining ω a c=(L:ℚ)*pairPotential L remaining ω a c := by
  have hn : (L:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hL
  by_cases he : a=c <;> by_cases hf : a∈remaining ∨ c∈remaining <;>
    by_cases hw : ω a=ω c <;> simp [kernel,pairPotential,he,hf,hw,hn]

/-- Two-feature joint port key; it is computed from each actual port. -/
def jointKey {I W : Type*} (ω : ℕ → W) (owner factor : I → ℕ)
    (f g : Feature) (i : I) : (ℕ ⊕ W) × (ℕ ⊕ W) :=
  (featureKey ω f (owner i),featureKey ω g (factor i))

/-- Literal per-port zero/one mask selects eligible feature records. -/
def jointWeight {I : Type*} (remaining : List ℕ) (owner factor : I → ℕ)
    (f g : Feature) (i : I) : ℚ :=
  featureWeight remaining f (owner i)*featureWeight remaining g (factor i)

/-- One sparse feature histogram: at most one derived key per original port.
Zero-weight records may be omitted by an implementation. -/
def histogram {I W : Type*} [DecidableEq W] (xs : List I) (remaining : List ℕ)
    (ω : ℕ → W) (owner factor : I → ℕ) (f g : Feature) : ℚ :=
  ∑ k∈(xs.map (jointKey ω owner factor f g)).toFinset,
    (bucket (jointKey ω owner factor f g) xs (jointWeight remaining owner factor f g) k)^2

/-- The complete sixteen-feature scalar is derived from the original ports. -/
def histogramSum {I W : Type*} [DecidableEq W] (L : ℚ) (xs : List I)
    (remaining : List ℕ) (ω : ℕ → W) (owner factor : I → ℕ) : ℚ :=
  ∑ f : Feature,∑ g : Feature,coefficient L f*coefficient L g*
    histogram xs remaining ω owner factor f g

/-- Every feature has at most as many sparse keys as actual port occurrences. -/
theorem histogram_keys_bound {I W : Type*} [DecidableEq W] (xs : List I)
    (ω : ℕ → W) (owner factor : I → ℕ) (f g : Feature) :
    (xs.map (jointKey ω owner factor f g)).toFinset.card ≤ xs.length :=
  sparse_keys_card _ xs

/-- Joint grouping is exactly the product of the two feature collision kernels. -/
theorem feature_grouping {I W : Type*} [DecidableEq W] (xs : List I)
    (remaining : List ℕ) (ω : ℕ → W) (owner factor : I → ℕ) (f g : Feature) :
    pairs xs (fun i j => featurePair remaining ω f (owner i) (owner j)*
      featurePair remaining ω g (factor i) (factor j))=
      histogram xs remaining ω owner factor f g := by
  have h := weighted_pair_grouping (jointKey ω owner factor f g) xs
    (jointWeight remaining owner factor f g)
  change pairs xs (fun i j => if jointKey ω owner factor f g i=jointKey ω owner factor f g j then
      jointWeight remaining owner factor f g i*jointWeight remaining owner factor f g j else 0)=_ at h
  unfold histogram
  rw [← h]
  unfold pairs
  congr 1
  apply List.map_congr_left
  intro i _
  congr 1
  apply List.map_congr_left
  intro j _
  dsimp only
  by_cases ho : featureKey ω f (owner i)=featureKey ω f (owner j) <;>
    by_cases hf : featureKey ω g (factor i)=featureKey ω g (factor j) <;>
    simp [featurePair,jointKey,jointWeight,ho,hf]
  ring

/-- Finite feature sums commute with the actual ordered occurrence-pair sum. -/
theorem pairs_sum {I A : Type*} [DecidableEq A] (xs : List I) (s : Finset A)
    (F : A → I → I → ℚ) :
    pairs xs (fun i j => ∑ a∈s,F a i j)=∑ a∈s,pairs xs (F a) := by
  induction s using Finset.induction_on with
  | empty => simp [pairs]
  | @insert a s ha ih => simp only [Finset.sum_insert ha,pairs_add,ih]

/-- The original pair sum contracts to sixteen actual sparse histograms. -/
theorem kernel_pairs {I W : Type*} [DecidableEq W] (L : ℚ) (xs : List I)
    (remaining : List ℕ) (ω : ℕ → W) (owner factor : I → ℕ) :
    pairs xs (fun i j => kernel L remaining ω (owner i) (owner j)*
      kernel L remaining ω (factor i) (factor j))=
      histogramSum L xs remaining ω owner factor := by
  simp_rw [kernel_expansion]
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [pairs_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [pairs_sum]
  apply Finset.sum_congr rfl
  intro g _
  have hp : (fun i j => (coefficient L f*featurePair remaining ω f (owner i) (owner j))*
      (coefficient L g*featurePair remaining ω g (factor i) (factor j)))=
      (fun i j => (coefficient L f*coefficient L g)*
        (featurePair remaining ω f (owner i) (owner j)*
          featurePair remaining ω g (factor i) (factor j))) := by
    funext i j
    ring
  rw [hp,pairs_scale,feature_grouping]

/-- Pointwise original padded count is L² times the two scaled equality kernels. -/
theorem padded_kernel (r Q : ℕ) (hr : 0<r) (a b c d : ℕ)
    (remaining : List ℕ) (env : Environment r Q) (hn : remaining.Nodup)
    (hab : a≠b) (had : a≠d) (hcb : c≠b) (hcd : c≠d) :
    ((SemiprimeSourceScoreCountsPadding.paddedLocal
      (SemiprimeFiniteEnumerations.words r Q).values (.incidence a b c d) remaining env).value:ℚ)=
      ((r^Q:ℕ):ℚ)^2*kernel ((r^Q:ℕ):ℚ) remaining (denote env) a c*
        kernel ((r^Q:ℕ):ℚ) remaining (denote env) b d := by
  have hL : 0<r^Q := pow_pos hr Q
  have hv := paddedLocal_formula r Q hr a b c d remaining env hn hab had hcb hcd
  simp only [SemiprimeSourceHeadCountFormula.alphabet] at hv
  rw [hv,kernel_potential (r^Q) hL,kernel_potential (r^Q) hL]
  have hp := classified_probability (r^Q) hL remaining (denote env) a b c d
  have hden : (((r^Q:ℕ):ℚ)^4)≠0 := pow_ne_zero _ (by exact_mod_cast Nat.ne_of_gt hL)
  have he := (eq_div_iff hden).mp hp
  rw [← he]
  ring

/-- Exact ORIGINAL padded incidence sum, from the actual arbitrary port list.
Cross-namespace separation follows from original complete index encoding;
parallel incidences and repeated owners/factors remain separate occurrences. -/
theorem original_incidence_pairs {I : Type*} (xs : List I) (owner factor : I → ℕ)
    (r Q : ℕ) (hr : 0<r) (remaining : List ℕ) (env : Environment r Q)
    (hn : remaining.Nodup)
    (hcross : ∀ i∈xs,∀ j∈xs,owner i≠factor j) :
    pairs xs (fun i j => ((SemiprimeSourceScoreCountsPadding.paddedLocal
      (SemiprimeFiniteEnumerations.words r Q).values
      (.incidence (owner i) (factor i) (owner j) (factor j)) remaining env).value:ℚ))=
      ((r^Q:ℕ):ℚ)^2*histogramSum ((r^Q:ℕ):ℚ) xs remaining (denote env) owner factor := by
  have he : pairs xs (fun i j => ((SemiprimeSourceScoreCountsPadding.paddedLocal
        (SemiprimeFiniteEnumerations.words r Q).values
        (.incidence (owner i) (factor i) (owner j) (factor j)) remaining env).value:ℚ))=
      ((r^Q:ℕ):ℚ)^2*pairs xs (fun i j =>
        kernel ((r^Q:ℕ):ℚ) remaining (denote env) (owner i) (owner j)*
          kernel ((r^Q:ℕ):ℚ) remaining (denote env) (factor i) (factor j)) := by
    rw [← pairs_scale]
    unfold pairs
    congr 1
    apply List.map_congr_left
    intro i hi
    congr 1
    apply List.map_congr_left
    intro j hj
    dsimp only
    have hv := padded_kernel r Q hr (owner i) (factor i) (owner j) (factor j)
      remaining env hn (hcross i hi i hi) (hcross i hi j hj)
        (hcross j hj i hi) (hcross j hj j hj)
    simpa only [mul_assoc] using hv
  rw [he,kernel_pairs]

/-- Every feature mask is a literal zero or one, independently of labels. -/
theorem featureWeight_zero_one (remaining : List ℕ) (f : Feature) (a : ℕ) :
    featureWeight remaining f a=0 ∨ featureWeight remaining f a=1 := by
  fin_cases f <;> by_cases ha : a∈remaining <;> simp [featureWeight,ha]

/-- Joint port eligibility has no fractional or signed weight. -/
theorem jointWeight_zero_one {I : Type*} (remaining : List ℕ) (owner factor : I → ℕ)
    (f g : Feature) (i : I) :
    jointWeight remaining owner factor f g i=0 ∨ jointWeight remaining owner factor f g i=1 := by
  rcases featureWeight_zero_one remaining f (owner i) with h|h <;>
    rcases featureWeight_zero_one remaining g (factor i) with h'|h' <;>
    simp [jointWeight,h,h']

/-- The actual eligible original ports; no free-label read determines this filter. -/
def eligiblePorts {I : Type*} (xs : List I) (remaining : List ℕ) (owner factor : I → ℕ)
    (f g : Feature) : List I :=
  xs.filter (fun i => decide (jointWeight remaining owner factor f g i=1))

/-- A zero/one weighted bucket is the actual filtered occurrence multiplicity. -/
theorem masked_bucket {I K : Type*} [DecidableEq K] (xs : List I) (label : I → K)
    (weight : I → ℚ) (hw : ∀i,weight i=0 ∨ weight i=1) (k : K) :
    bucket label xs weight k=
      ((multiplicity label (xs.filter (fun i => decide (weight i=1))) k:ℕ):ℚ) := by
  induction xs with
  | nil => simp [bucket,SemiprimeSourceHistogramGrouping.multiplicity]
  | cons i xs ih =>
    rcases hw i with hi|hi <;> by_cases hk : label i=k <;>
      simp [bucket,SemiprimeSourceHistogramGrouping.multiplicity,hi,hk] at ih ⊢ <;> linarith

/-- Every sparse term is literally a square-count histogram of its filtered
original port list, not an advised weighted matrix or a rational normalizer. -/
theorem histogram_filtered {I W : Type*} [DecidableEq W] (xs : List I)
    (remaining : List ℕ) (ω : ℕ → W) (owner factor : I → ℕ) (f g : Feature) :
    histogram xs remaining ω owner factor f g=
      ∑ k∈((eligiblePorts xs remaining owner factor f g).map
          (jointKey ω owner factor f g)).toFinset,
        ((multiplicity (jointKey ω owner factor f g)
          (eligiblePorts xs remaining owner factor f g) k:ℕ):ℚ)^2 := by
  classical
  let selected := eligiblePorts xs remaining owner factor f g
  let label := jointKey ω owner factor f g
  have hb (k) := masked_bucket xs label (jointWeight remaining owner factor f g)
    (jointWeight_zero_one remaining owner factor f g) k
  change histogram xs remaining ω owner factor f g=
    ∑k∈(selected.map label).toFinset,((multiplicity label selected k:ℕ):ℚ)^2
  change (∑k∈(xs.map label).toFinset,
    (bucket label xs (jointWeight remaining owner factor f g) k)^2)=_
  simp_rw [hb]
  change (∑k∈(xs.map label).toFinset,((multiplicity label selected k:ℕ):ℚ)^2)=_
  have hs : (selected.map label).toFinset ⊆ (xs.map label).toFinset := by
    intro k hk
    rcases List.mem_map.mp (List.mem_toFinset.mp hk) with ⟨i,hi,rfl⟩
    have hix : i∈xs := (List.mem_filter.mp hi).1
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,hix,rfl⟩)
  symm
  apply Finset.sum_subset hs
  intro k _ hk
  have hn : k∉selected.map label := by simpa only [List.mem_toFinset] using hk
  have hz : multiplicity label selected k=0 := by
    unfold SemiprimeSourceHistogramGrouping.multiplicity
    apply List.countP_eq_zero.mpr
    intro i hi
    simp only [decide_eq_true_eq]
    intro he
    exact hn (List.mem_map.mpr ⟨i,hi,he⟩)
  rw [hz]
  norm_num

end RiemannGaussian.SemiprimeSourceIncidenceHistogram
