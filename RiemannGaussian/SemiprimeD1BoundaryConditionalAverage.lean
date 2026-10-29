/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryPotential
import RiemannGaussian.SemiprimeD1BoundaryColourWords

/-! # Marginal identities for the executed local conditional expectation
The inactive-coordinate case retains precisely the same local samples and
success count after the next vertex is assigned.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1BoundaryConditionalAverage
open SemiprimeD1BoundaryPlan

/-- The local enumerator has exactly the advertised number of assignments. -/
theorem colourWords_length (k n : Nat) : (colourWords k n).length = k ^ n := by
  induction n with
  | zero => simp [colourWords]
  | succ n ih => simp [colourWords, List.length_flatMap, ih, Nat.pow_succ, Nat.mul_comm]

/-- Splitting the first local coordinate partitions the executed success count. -/
theorem colourWords_successes (k n : Nat) (p : List Nat → Bool) :
    ((List.range k).map (fun c =>
      ((colourWords k n).filter (fun sample => p (c :: sample))).length)).sum =
      ((colourWords k (n + 1)).filter p).length := by
  simp [colourWords, List.filter_flatMap, List.filter_map, List.length_flatMap, Function.comp_def]

/-- Inserting a local sample coordinate commutes with endpoint lookup. -/
theorem getD_idxOf_insert (before after sample : List Nat) (t c v : Nat)
    (ht : t ∉ before) (hlen : before.length ≤ sample.length) :
    (sample.take before.length ++ c :: sample.drop before.length).getD
        ((before ++ t :: after).idxOf v) 0 =
      if v = t then c else sample.getD ((before ++ after).idxOf v) 0 := by
  induction before generalizing sample with
  | nil =>
    simp only [List.length_nil, List.take_zero, List.drop_zero, List.nil_append]
    by_cases hv : v = t
    · subst v
      simp
    · rw [List.idxOf_cons_ne _ (Ne.symm hv)]
      simp [hv]
  | cons a before ih =>
    cases sample with
    | nil => simp at hlen
    | cons s sample =>
      have hat : t ≠ a := fun hh => ht (by simp [hh])
      have htail : t ∉ before := fun hh => ht (List.mem_cons_of_mem a hh)
      have hl : before.length ≤ sample.length := by simpa using hlen
      by_cases hv : v = a
      · subst v
        simp [Ne.symm hat]
      · simp only [List.length_cons, List.take_succ_cons, List.drop_succ_cons,
          List.cons_append, List.idxOf_cons_ne _ (Ne.symm hv), List.getD_cons_succ]
        exact ih sample htail hl

/-- An arbitrary-position local coordinate can be moved into the fixed prefix. -/
theorem readColour_insert (fixed before after sample : List Nat) (c v : Nat)
    (ht : fixed.length ∉ before) (hlen : before.length ≤ sample.length) :
    readColour (fixed ++ [c]) (before ++ after) sample v =
      readColour fixed (before ++ fixed.length :: after)
        (sample.take before.length ++ c :: sample.drop before.length) v := by
  unfold readColour
  simp only [List.length_append, List.length_singleton]
  by_cases h : v < fixed.length
  · rw [ite_eq_left (by omega), ite_eq_left h, List.getD_append _ _ _ _ h]
  · rw [ite_eq_right h, getD_idxOf_insert before after sample fixed.length c v ht hlen]
    by_cases he : v = fixed.length
    · subst v
      rw [ite_eq_left (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp
    · rw [ite_eq_right (by omega), ite_eq_right he]

/-- Moving the first unknown endpoint into the prefix preserves all reads. -/
theorem readColour_first_unknown (fixed unknown sample : List Nat) (c v : Nat) :
    readColour (fixed ++ [c]) unknown sample v =
      readColour fixed (fixed.length :: unknown) (c :: sample) v := by
  unfold readColour
  simp only [List.length_append, List.length_singleton]
  by_cases h : v < fixed.length
  · rw [ite_eq_left (by omega), ite_eq_left h, List.getD_append _ _ _ _ h]
  · rw [ite_eq_right h]
    by_cases he : v = fixed.length
    · subst v
      rw [ite_eq_left (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp
    · rw [ite_eq_right (by omega), List.idxOf_cons_ne _ (Ne.symm he)]
      rfl

/-- Fixing the next vertex deletes precisely that vertex from local unknowns. -/
theorem unknown_append_eq_filter (fixed : List Nat) (c : Nat) (es : List (Nat × Nat)) :
    (endpoints es).filter (fun v => !(v < (fixed ++ [c]).length)) =
      ((endpoints es).filter (fun v => !(v < fixed.length))).filter
        (fun v => v != fixed.length) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro v _
  simp only [List.length_append, List.length_singleton]
  by_cases h : v < fixed.length
  · have hh : v < fixed.length + 1 := by omega
    simp [h, hh]
  · by_cases he : v = fixed.length
    · subst v
      simp
    · have hh : ¬ v < fixed.length + 1 := by omega
      simp [h, he, hh]

/-- The executable first-occurrence endpoint catalogue has no repetitions. -/
theorem eraseDups_nodup (xs : List Nat) : xs.eraseDups.Nodup := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => simp
    | cons a xs =>
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro hm
        have hh := List.mem_filter.mp (List.mem_eraseDups.mp hm)
        simpa using hh.2
      · apply ih ((xs.filter (fun b => !(b == a))).length)
          (by have := List.length_filter_le (fun b => !(b == a)) xs; simp only [List.length_cons] at hn; omega)
          _ rfl

/-- Once the next vertex leads the unknown list, fixing it leaves its tail. -/
theorem unknown_append_of_first (fixed unknown : List Nat) (c : Nat)
    (es : List (Nat × Nat))
    (hbefore : (endpoints es).filter (fun v => !(v < fixed.length)) =
      fixed.length :: unknown) :
    (endpoints es).filter (fun v => !(v < (fixed ++ [c]).length)) = unknown := by
  have hnd : (endpoints es).Nodup := eraseDups_nodup _
  have htail : fixed.length ∉ unknown := by
    have hh := hnd.filter (fun v => !(v < fixed.length))
    rw [hbefore] at hh
    exact (List.nodup_cons.mp hh).1
  rw [unknown_append_eq_filter, hbefore]
  simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, reduceIte]
  apply List.filter_eq_self.mpr
  intro v hv
  have hn : v ≠ fixed.length := fun he => htail (he ▸ hv)
  simpa using hn

/-- The active first-coordinate marginal follows from the executed catalogue.
The premises describe endpoint lists, rather than assuming an averaging identity. -/
theorem localExpectation_average_first (scale k : Nat) (fixed unknown : List Nat)
    (load : Load) (es : List (Nat × Nat))
    (hbefore : (endpoints es).filter (fun v => !(v < fixed.length)) =
      fixed.length :: unknown)
    (hscale : unknown.length + 1 ≤ scale) :
    ((List.range k).map (fun c =>
      (localExpectation scale k (fixed ++ [c]) load es).value)).sum =
      k * (localExpectation scale k fixed load es).value := by
  let p : List Nat → Bool := fun sample => es.all (fun e =>
    indicator load (readColour fixed (fixed.length :: unknown) sample e.1)
      (readColour fixed (fixed.length :: unknown) sample e.2))
  have hchild (c : Nat) : (localExpectation scale k (fixed ++ [c]) load es).value =
      ((colourWords k unknown.length).filter (fun sample => p (c :: sample))).length *
        k ^ (scale - unknown.length) := by
    unfold localExpectation
    simp only [unknown_append_of_first fixed unknown c es hbefore]
    congr 3
    funext sample
    simp only [p, readColour_first_unknown]
  have hexp : scale - unknown.length = scale - (unknown.length + 1) + 1 := by omega
  simp_rw [hchild]
  rw [List.sum_map_mul_right, colourWords_successes]
  unfold localExpectation
  simp only [hbefore, List.length_cons]
  change _ = k * (((colourWords k (unknown.length + 1)).filter p).length *
    k ^ (scale - (unknown.length + 1)))
  rw [hexp, Nat.pow_succ]
  ring

/-- Appending a colour leaves every other endpoint read unchanged. -/
theorem readColour_append_of_ne (fixed unknown sample : List Nat) (c v : Nat)
    (hv : v ≠ fixed.length) :
    readColour (fixed ++ [c]) unknown sample v = readColour fixed unknown sample v := by
  unfold readColour
  by_cases h : v < fixed.length
  · simp only [List.length_append, List.length_singleton]
    rw [ite_eq_left (by omega), ite_eq_left h, List.getD_append _ _ _ _ h]
  · simp only [List.length_append, List.length_singleton]
    rw [ite_eq_right (by omega), ite_eq_right h]

/-- The local unknown list changes only when the newly fixed vertex occurs. -/
theorem unknown_append_of_absent (fixed : List Nat) (c : Nat) (es : List (Nat × Nat))
    (ha : fixed.length ∉ endpoints es) :
    (endpoints es).filter (fun v => !(v < (fixed ++ [c]).length)) =
      (endpoints es).filter (fun v => !(v < fixed.length)) := by
  apply List.filter_congr
  intro v hv
  have hn : v ≠ fixed.length := fun h => ha (h ▸ hv)
  simp only [List.length_append, List.length_singleton]
  have hh : (v < fixed.length + 1) ↔ (v < fixed.length) := by omega
  simp only [hh]

/-- An inactive endpoint coordinate preserves the literal scaled value. -/
theorem localExpectation_append_of_absent (scale k : Nat) (fixed : List Nat)
    (c : Nat) (load : Load) (es : List (Nat × Nat))
    (ha : fixed.length ∉ endpoints es) :
    (localExpectation scale k (fixed ++ [c]) load es).value =
      (localExpectation scale k fixed load es).value := by
  have hu := unknown_append_of_absent fixed c es ha
  have hn : ∀ e ∈ es, e.1 ≠ fixed.length ∧ e.2 ≠ fixed.length := by
    intro e he
    constructor
    · intro h
      apply ha
      apply List.mem_eraseDups.mpr
      apply List.mem_flatMap.mpr
      exact ⟨e, he, by simp [h]⟩
    · intro h
      apply ha
      apply List.mem_eraseDups.mpr
      apply List.mem_flatMap.mpr
      exact ⟨e, he, by simp [h]⟩
  unfold localExpectation
  simp only [hu]
  congr 3
  funext sample

  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor <;> intro h e he
  · simpa only [readColour_append_of_ne fixed _ sample c e.1 (hn e he).1,
      readColour_append_of_ne fixed _ sample c e.2 (hn e he).2] using h e he
  · simpa only [readColour_append_of_ne fixed _ sample c e.1 (hn e he).1,
      readColour_append_of_ne fixed _ sample c e.2 (hn e he).2] using h e he

/-- Exact executed averaging for a coordinate absent from this local factor. -/
theorem localExpectation_average_of_absent (scale k : Nat) (fixed : List Nat)
    (load : Load) (es : List (Nat × Nat))
    (ha : fixed.length ∉ endpoints es) :
    ((List.range k).map (fun c =>
      (localExpectation scale k (fixed ++ [c]) load es).value)).sum =
      k * (localExpectation scale k fixed load es).value := by
  have he : (List.range k).map (fun c =>
      (localExpectation scale k (fixed ++ [c]) load es).value) =
      (List.range k).map (fun _ => (localExpectation scale k fixed load es).value) := by
    apply List.map_congr_left
    intro c _
    exact localExpectation_append_of_absent scale k fixed c load es ha
  rw [he]
  simp

/-- Fixing an arbitrary-position unknown deletes exactly that local coordinate. -/
theorem unknown_append_of_split (fixed before after : List Nat) (c : Nat)
    (es : List (Nat × Nat))
    (hb : (endpoints es).filter (fun v => !(v < fixed.length)) =
      before ++ fixed.length :: after) :
    fixed.length ∉ before ∧
      (endpoints es).filter (fun v => !(v < (fixed ++ [c]).length)) = before ++ after := by
  have hn := (eraseDups_nodup (es.flatMap (fun e => [e.1, e.2]))).filter
    (fun v => !(v < fixed.length))
  change ((endpoints es).filter (fun v => !(v < fixed.length))).Nodup at hn
  rw [hb] at hn
  have hp := List.nodup_append.mp hn
  have hbefore : fixed.length ∉ before := fun hm =>
    hp.2.2 fixed.length hm fixed.length (by simp) rfl
  have hafter : fixed.length ∉ after := (List.nodup_cons.mp hp.2.1).1
  refine ⟨hbefore, ?_⟩
  rw [unknown_append_eq_filter, hb, List.filter_append]
  have he (xs : List Nat) (hh : fixed.length ∉ xs) :
      xs.filter (fun v => v != fixed.length) = xs := by
    apply List.filter_eq_self.mpr
    intro v hv
    have : v ≠ fixed.length := fun he => hh (he ▸ hv)
    simpa using this
  simp [he before hbefore, he after hafter]

/-- Exact executed marginal at an arbitrary position in the endpoint catalogue. -/
theorem localExpectation_average_split (scale k : Nat) (fixed before after : List Nat)
    (load : Load) (es : List (Nat × Nat))
    (hb : (endpoints es).filter (fun v => !(v < fixed.length)) =
      before ++ fixed.length :: after)
    (hs : before.length + after.length + 1 ≤ scale) :
    ((List.range k).map (fun c =>
      (localExpectation scale k (fixed ++ [c]) load es).value)).sum =
      k * (localExpectation scale k fixed load es).value := by
  let n := before.length + after.length
  let p : List Nat → Bool := fun sample => es.all (fun e =>
    indicator load (readColour fixed (before ++ fixed.length :: after) sample e.1)
      (readColour fixed (before ++ fixed.length :: after) sample e.2))
  have hchild (c : Nat) : (localExpectation scale k (fixed ++ [c]) load es).value =
      ((colourWords k n).filter (fun sample =>
        p (sample.take before.length ++ [c] ++ sample.drop before.length))).length *
          k ^ (scale - n) := by
    obtain ⟨ht, hu⟩ := unknown_append_of_split fixed before after c es hb
    unfold localExpectation
    simp only [hu]
    simp only [List.length_append]
    congr 2
    apply List.filter_congr
    intro sample hm
    have hl := SemiprimeD1BoundaryColourWords.member_length k n sample hm
    have hle : before.length ≤ sample.length := by dsimp [n] at hl; omega
    simp only [p]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor <;> intro h e he
    · simpa only [readColour_insert fixed before after sample c e.1 ht hle,
        readColour_insert fixed before after sample c e.2 ht hle, List.append_assoc, List.singleton_append] using h e he
    · simpa only [readColour_insert fixed before after sample c e.1 ht hle,
        readColour_insert fixed before after sample c e.2 ht hle, List.append_assoc, List.singleton_append] using h e he
  simp_rw [hchild]
  rw [List.sum_map_mul_right, SemiprimeD1BoundaryColourWords.successes_insert k n before.length p
    (by dsimp [n]; omega)]
  unfold localExpectation
  simp only [hb, List.length_append, List.length_cons]
  change _ = k * (((colourWords k (n + 1)).filter p).length * k ^ (scale - (n + 1)))
  have he : scale - n = scale - (n + 1) + 1 := by dsimp [n] at *; omega
  rw [he, Nat.pow_succ]
  ring

/-- Literal local conditional expectations satisfy exact averaging.
No graph colouring or probabilistic premise is supplied to this theorem. -/
theorem localExpectation_average (scale k : Nat) (fixed : List Nat)
    (load : Load) (es : List (Nat × Nat))
    (hs : (endpoints es).length ≤ scale) :
    ((List.range k).map (fun c =>
      (localExpectation scale k (fixed ++ [c]) load es).value)).sum =
      k * (localExpectation scale k fixed load es).value := by
  by_cases ha : fixed.length ∈ endpoints es
  · have hu : fixed.length ∈ (endpoints es).filter (fun v => !(v < fixed.length)) := by
      simp [ha]
    obtain ⟨before, after, hb⟩ := List.mem_iff_append.mp hu
    apply localExpectation_average_split scale k fixed before after load es hb
    have hh := List.length_filter_le (fun v => !(v < fixed.length)) (endpoints es)
    rw [hb] at hh
    simp only [List.length_append, List.length_cons] at hh
    omega
  · exact localExpectation_average_of_absent scale k fixed load es ha

/-- First-occurrence deletion cannot increase the catalogue length. -/
theorem eraseDups_length_le (xs : List Nat) : xs.eraseDups.length ≤ xs.length := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => simp
    | cons a xs =>
      rw [List.eraseDups_cons]
      have hf := List.length_filter_le (fun b => !(b == a)) xs
      have hh := ih ((xs.filter (fun b => !(b == a))).length)
        (by simp only [List.length_cons] at hn; omega) _ rfl
      simp only [List.length_cons]
      simp only [List.length_cons] at hn
      omega

/-- Every endpoint catalogue contains at most two vertices per occurrence. -/
theorem endpoints_length_le (es : List (Nat × Nat)) :
    (endpoints es).length ≤ 2 * es.length := by
  apply Nat.le_trans (eraseDups_length_le _)
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
    omega

/-- Exact averaging of every single-edge local term used by the potential. -/
theorem single_average (k : Nat) (fixed : List Nat) (load : Load) (e : Nat × Nat) :
    ((List.range k).map (fun c =>
      (localExpectation 2 k (fixed ++ [c]) load [e]).value)).sum =
      k * (localExpectation 2 k fixed load [e]).value := by
  apply localExpectation_average
  simpa using endpoints_length_le [e]

/-- Exact averaging includes diagonal and parallel ordered edge pairs. -/
theorem pair_average (k : Nat) (fixed : List Nat) (load : Load) (e f : Nat × Nat) :
    ((List.range k).map (fun c =>
      (localExpectation 4 k (fixed ++ [c]) load [e, f]).value)).sum =
      k * (localExpectation 4 k fixed load [e, f]).value := by
  apply localExpectation_average
  simpa using endpoints_length_le [e, f]

/-- Exact scaled averaging as a property of a prefix-dependent integer term. -/
def Averages (k : Nat) (f : List Nat → Int) : Prop :=
  ∀ fixed, ((List.range k).map (fun c => f (fixed ++ [c]))).sum = (k : Int) * f fixed

/-- Constant terms obey the same marginal identity. -/
theorem averages_const (k : Nat) (a : Int) : Averages k (fun _ => a) := by
  intro fixed
  simp

/-- The marginal identity is preserved by addition. -/
theorem averages_add (k : Nat) (f g : List Nat → Int)
    (hf : Averages k f) (hg : Averages k g) : Averages k (fun xs => f xs + g xs) := by
  intro fixed
  rw [List.sum_map_add, hf, hg]
  ring

/-- The marginal identity is preserved by subtraction. -/
theorem averages_sub (k : Nat) (f g : List Nat → Int)
    (hf : Averages k f) (hg : Averages k g) : Averages k (fun xs => f xs - g xs) := by
  intro fixed
  have he : (List.range k).map (fun c => f (fixed ++ [c]) - g (fixed ++ [c])) =
      (List.range k).map (fun c => f (fixed ++ [c]) + -1 * g (fixed ++ [c])) := by
    congr 1
    funext c
    ring
  rw [he, List.sum_map_add, List.sum_map_mul_left, hf, hg]
  ring

/-- Integer scaling commutes with marginalization. -/
theorem averages_mul (k : Nat) (a : Int) (f : List Nat → Int)
    (hf : Averages k f) : Averages k (fun xs => a * f xs) := by
  intro fixed
  rw [List.sum_map_mul_left, hf]
  ring

/-- Exact interchange of finite integer sums. -/
theorem int_sum_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Int) :
    (xs.map (fun x => (ys.map (f x)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.sum_map_add, ih]

/-- Original occurrence sums retain exact averaging without a distinctness premise. -/
theorem averages_sum {α : Type} (k : Nat) (xs : List α) (f : α → List Nat → Int)
    (hf : ∀ x ∈ xs, Averages k (f x)) :
    Averages k (fun fixed => (xs.map (fun x => f x fixed)).sum) := by
  intro fixed
  rw [int_sum_swap]
  have he : xs.map (fun x => ((List.range k).map (fun c => f x (fixed ++ [c]))).sum) =
      xs.map (fun x => (k : Int) * f x fixed) := by
    apply List.map_congr_left
    intro x hx
    exact hf x hx fixed
  rw [he, List.sum_map_mul_left]

/-- Integer coercion of every single-edge marginal. -/
theorem averages_single (k : Nat) (load : Load) (e : Nat × Nat) :
    Averages k (fun fixed => ((localExpectation 2 k fixed load [e]).value : Int)) := by
  intro fixed
  have h := congrArg (fun n : Nat => (n : Int)) (single_average k fixed load e)
  simpa only [Nat.cast_list_sum, List.map_map, Nat.cast_mul, Function.comp_def] using h

/-- Integer coercion of every ordered-pair marginal. -/
theorem averages_pair (k : Nat) (load : Load) (e f : Nat × Nat) :
    Averages k (fun fixed => ((localExpectation 4 k fixed load [e, f]).value : Int)) := by
  intro fixed
  have h := congrArg (fun n : Nat => (n : Int)) (pair_average k fixed load e f)
  simpa only [Nat.cast_list_sum, List.map_map, Nat.cast_mul, Function.comp_def] using h

/-- The executed quadratic potential satisfies exact conditional averaging. -/
theorem potential_average (g : Graph) (k : Nat) (fixed : List Nat) :
    ((List.range k).map (fun c => (potential g k (fixed ++ [c])).value)).sum =
      (k : Int) * (potential g k fixed).value := by
  have hp (load : Load) : Averages k (fun fixed =>
      (g.edges.map (fun e => (g.edges.map (fun f =>
        ((localExpectation 4 k fixed load [e, f]).value : Int))).sum)).sum) := by
    apply averages_sum
    intro e _
    apply averages_sum
    intro f _
    exact averages_pair k load e f
  have hs (load : Load) : Averages k (fun fixed =>
      (g.edges.map (fun e => ((localExpectation 2 k fixed load [e]).value : Int))).sum) := by
    apply averages_sum
    intro e _
    exact averages_single k load e
  have h := averages_sum k (loads k) (fun load fixed =>
    (g.edges.map (fun e => (g.edges.map (fun f =>
      ((localExpectation 4 k fixed load [e, f]).value : Int))).sum)).sum -
    2 * (meanNumerator g.edges.length k load : Int) *
      (g.edges.map (fun e => ((localExpectation 2 k fixed load [e]).value : Int))).sum +
    (meanNumerator g.edges.length k load : Int)^2)
    (fun load _ => averages_add k _ _
      (averages_sub k _ _ (hp load) (averages_mul k _ _ (hs load)))
      (averages_const k _)) fixed
  simpa only [potential, List.map_map, Function.comp_def, Nat.cast_list_sum,
    List.map_flatMap, List.flatMap, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def] using h

/-- List and finset range summation use the same occurrence order and values. -/
theorem sum_range_eq (k : Nat) (f : Nat → Int) :
    ((List.range k).map f).sum = ∑ c ∈ Finset.range k, f c := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.range_succ, Finset.sum_range_succ, ih]

/-- The selected actual colour never increases the executed potential. -/
theorem selected_potential_le (g : Graph) (k : Nat) (fixed : List Nat) (hk : 0 < k) :
    (potential g k (fixed ++ [(leastCandidate g k fixed).value])).value ≤
      (potential g k fixed).value := by
  apply SemiprimeD1BoundaryChoice.selected_le_current g k fixed hk
  simpa only [sum_range_eq] using potential_average g k fixed

/-- Every executed extension has a nonincreasing literal potential. -/
theorem extend_potential_le (g : Graph) (k n : Nat) (fixed : List Nat) (hk : 0 < k) :
    (potential g k (extend g k n fixed).value).value ≤ (potential g k fixed).value := by
  apply SemiprimeD1BoundaryChoice.extend_potential_le g k n fixed hk
  intro current _ _
  simpa only [sum_range_eq] using potential_average g k current

/-- Closed acquisition attains at most its own initial executed potential. -/
theorem acquire_potential_le (g : Graph) :
    (potential g (acquire g).k (acquire g).colours).value ≤
      (potential g (acquire g).k []).value := by
  change (potential g (chooseK g) (extend g (chooseK g) g.vertices []).value).value ≤
    (potential g (chooseK g) []).value
  apply extend_potential_le
  have h := (SemiprimeD1BoundaryChoice.chooseK_bounds g).1
  omega

end RiemannGaussian.SemiprimeD1BoundaryConditionalAverage
