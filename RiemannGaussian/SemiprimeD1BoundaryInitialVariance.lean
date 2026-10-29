/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryConditionalAverage

/-! # Proof-only complete catalogue formula for the initial potential
The executable algorithm still generates only local endpoint samples. The
complete assignment catalogue occurs exclusively in the following identities.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1BoundaryInitialVariance
open SemiprimeD1BoundaryPlan SemiprimeD1BoundaryConditionalAverage

/-- Repeated exact marginals recover the proof-only complete finite catalogue. -/
theorem catalogue_marginal (k n : Nat) (f : List Nat → Int) (hf : Averages k f)
    (fixed : List Nat) :
    ((colourWords k n).map (fun sample => f (fixed ++ sample))).sum =
      (k : Int)^n * f fixed := by
  induction n generalizing fixed with
  | zero => simp [colourWords]
  | succ n ih =>
    have he : ((colourWords k (n + 1)).map (fun sample => f (fixed ++ sample))).sum =
        ((List.range k).map (fun c => ((colourWords k n).map
          (fun sample => f ((fixed ++ [c]) ++ sample))).sum)).sum := by
      simp [colourWords, List.flatMap, List.map_flatten,
        List.sum_flatten, List.map_map, Function.comp_def, List.append_assoc]
    rw [he]
    simp_rw [ih]
    rw [List.sum_map_mul_left, hf, pow_succ]
    ring

/-- The initial executed potential is exactly a finite mean of literal squares.
No global assignment enumeration is executed by the runtime partitioner. -/
theorem initial_catalogue (g : Graph) (k : Nat)
    (hg : SemiprimeD1BoundaryPotential.Valid g) :
    (k : Int)^g.vertices * (potential g k []).value =
      ((colourWords k g.vertices).map (fun colours => ((loads k).map (fun load =>
        ((k : Int)^2 * (loadValue g colours load : Int) -
          (meanNumerator g.edges.length k load : Int))^2)).sum)).sum := by
  have ha : Averages k (fun fixed => (potential g k fixed).value) :=
    potential_average g k
  rw [← catalogue_marginal k g.vertices _ ha []]
  simp only [List.nil_append]
  apply congrArg List.sum
  apply List.map_congr_left
  intro colours hc
  apply SemiprimeD1BoundaryPotential.potential_fixed
  have hl := SemiprimeD1BoundaryColourWords.member_length k g.vertices colours hc
  intro e he
  have hh := hg e he
  omega

/-- Complete local words factor exactly at any consecutive coordinate cut. -/
theorem colourWords_add (k n m : Nat) :
    colourWords k (n + m) = (colourWords k n).flatMap (fun xs =>
      (colourWords k m).map (fun ys => xs ++ ys)) := by
  induction n with
  | zero => simp [colourWords]
  | succ n ih =>
    simp [Nat.succ_add, colourWords, ih, List.flatMap_assoc, List.flatMap_map,
      List.map_flatMap, List.map_map, Function.comp_def]

/-- Counts of independent finite catalogue factors multiply, retaining duplicates. -/
theorem successes_product {α β : Type} (xs : List α) (ys : List β)
    (p : α → Bool) (q : β → Bool) :
    ((xs.flatMap (fun x => ys.map (fun y => (x, y)))).filter
      (fun xy => p xy.1 && q xy.2)).length =
      (xs.filter p).length * (ys.filter q).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.filter_append, List.length_append, List.filter_cons]
    have he : ((ys.map (fun y => (x, y))).filter
        (fun xy => p xy.1 && q xy.2)).length =
        if p x then (ys.filter q).length else 0 := by
      rw [List.filter_map]
      cases hp : p x <;> simp [hp, Function.comp_def]
    rw [he, ih]
    cases hp : p x <;> simp [Nat.add_mul, Nat.add_comm]

/-- Exact two-colour event count independent of endpoint names. -/
def eventCount (k : Nat) (load : Load) : Nat :=
  ((colourWords k 2).filter (fun sample =>
    indicator load (sample.getD 0 0) (sample.getD 1 0))).length

/-- Every nonloop single-edge initial expectation has the same event count. -/
theorem single_initial (k a b : Nat) (load : Load) (hab : a ≠ b) :
    (localExpectation 2 k [] load [(a, b)]).value = eventCount k load := by
  simp [localExpectation, endpoints, List.eraseDups_cons, hab, Ne.symm hab,
    readColour, eventCount]

/-- A local edge event count lies between zero and the two-coordinate catalogue. -/
theorem eventCount_le (k : Nat) (load : Load) : eventCount k load ≤ k^2 := by
  unfold eventCount
  apply Nat.le_trans (List.length_filter_le _ _)
  exact le_of_eq (colourWords_length k 2)

/-- Exact weighted count for one distinguished value in an occurrence list. -/
theorem sum_special (xs : List Nat) (t k : Nat) :
    ((xs.map (fun a => if a == t then k else 1)).sum) + xs.count t =
      xs.count t * k + xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    by_cases ha : a = t
    · subst a
      simp only [List.map_cons, List.sum_cons, beq_self_eq_true, reduceIte,
        List.count_cons_self, List.length_cons, Nat.add_mul, one_mul]
      omega
    · simp only [List.map_cons, List.sum_cons, beq_eq_false_iff_ne.mpr ha, Bool.false_eq_true,
        reduceIte, List.count_cons, Nat.add_zero,
        List.length_cons]
      omega

/-- A bucket event has exactly the literal unconditional numerator. -/
theorem eventCount_bucket (k t : Nat) (ht : t < k) :
    eventCount k (.bucket t) = 2 * k - 1 := by
  have hi (a : Nat) :
      (((List.range k).map (fun b => [a, b])).filter (fun sample =>
        indicator (.bucket t) (sample.getD 0 0) (sample.getD 1 0))).length =
      if a == t then k else 1 := by
    rw [List.filter_map]
    by_cases ha : a = t
    · subst a
      simp [indicator, Function.comp_def]
    · simp [indicator, Function.comp_def, beq_eq_false_iff_ne.mpr ha, List.filter_beq, List.count_range, ht]
  have he : colourWords k 2 = (List.range k).flatMap (fun a =>
      (List.range k).map (fun b => [a, b])) := by
    simp [colourWords, ← List.map_eq_flatMap, Function.comp_def]
  unfold eventCount
  rw [he, List.filter_flatMap, List.length_flatMap]
  simp_rw [hi]
  have hh := sum_special (List.range k) t k
  simp only [List.count_range, ht, reduceIte, List.length_range, one_mul] at hh
  omega

/-- A disjoint ordered edge pair reads exactly four independent local coordinates. -/
theorem pair_initial_disjoint_coordinates (k a b c d : Nat) (load : Load)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (localExpectation 4 k [] load [(a, b), (c, d)]).value =
      ((colourWords k 4).filter (fun sample =>
        indicator load (sample.getD 0 0) (sample.getD 1 0) &&
          indicator load (sample.getD 2 0) (sample.getD 3 0))).length := by
  simp [localExpectation, endpoints, List.eraseDups_cons, readColour,
    hab, hac, had, hbc, hbd, hcd, Ne.symm hab, Ne.symm hac, Ne.symm had,
    Ne.symm hbc, Ne.symm hbd, Ne.symm hcd]

/-- Constant successful weights sum exactly over a filtered occurrence list. -/
theorem sum_success_weight {α : Type} (xs : List α) (p : α → Bool) (w : Nat) :
    ((xs.map (fun x => if p x then w else 0)).sum) = (xs.filter p).length * w := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x <;> simp [hp, ih, Nat.add_mul, Nat.add_comm]

/-- Independence of the two consecutive two-colour blocks in the local catalogue. -/
theorem fourCount_eq_square (k : Nat) (load : Load) :
    ((colourWords k 4).filter (fun sample =>
      indicator load (sample.getD 0 0) (sample.getD 1 0) &&
        indicator load (sample.getD 2 0) (sample.getD 3 0))).length =
      eventCount k load * eventCount k load := by
  rw [show 4 = 2 + 2 from rfl, colourWords_add, List.filter_flatMap, List.length_flatMap]
  have hi (xs : List Nat) (hx : xs ∈ colourWords k 2) :
      (((colourWords k 2).map (fun ys => xs ++ ys)).filter (fun sample =>
        indicator load (sample.getD 0 0) (sample.getD 1 0) &&
          indicator load (sample.getD 2 0) (sample.getD 3 0))).length =
      if indicator load (xs.getD 0 0) (xs.getD 1 0) then eventCount k load else 0 := by
    have hl := SemiprimeD1BoundaryColourWords.member_length k 2 xs hx
    rw [List.filter_map, List.length_map]
    have he : (fun ys =>
        indicator load ((xs ++ ys).getD 0 0) ((xs ++ ys).getD 1 0) &&
          indicator load ((xs ++ ys).getD 2 0) ((xs ++ ys).getD 3 0)) =
        (fun ys => indicator load (xs.getD 0 0) (xs.getD 1 0) &&
          indicator load (ys.getD 0 0) (ys.getD 1 0)) := by
      funext ys
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega)]
      simp only [hl]
    change ((colourWords k 2).filter (fun ys =>
      indicator load ((xs ++ ys).getD 0 0) ((xs ++ ys).getD 1 0) &&
        indicator load ((xs ++ ys).getD 2 0) ((xs ++ ys).getD 3 0))).length = _
    rw [he]
    cases hb : indicator load (xs.getD 0 0) (xs.getD 1 0) <;> simp [eventCount]
  have he : (colourWords k 2).map (fun xs =>
      (((colourWords k 2).map (fun ys => xs ++ ys)).filter (fun sample =>
        indicator load (sample.getD 0 0) (sample.getD 1 0) &&
          indicator load (sample.getD 2 0) (sample.getD 3 0))).length) =
      (colourWords k 2).map (fun xs =>
        if indicator load (xs.getD 0 0) (xs.getD 1 0) then eventCount k load else 0) := by
    apply List.map_congr_left
    exact hi
  rw [he, sum_success_weight]
  rfl

/-- Disjoint-edge covariance cancels exactly in the executed initial potential. -/
theorem pair_initial_disjoint (k a b c d : Nat) (load : Load)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (localExpectation 4 k [] load [(a, b), (c, d)]).value =
      eventCount k load * eventCount k load := by
  rw [pair_initial_disjoint_coordinates k a b c d load hab hac had hbc hbd hcd,
    fourCount_eq_square]

/-- A pair event is pointwise dominated by its first single event. -/
theorem pair_initial_le_single (g : Graph) (k : Nat) (load : Load) (e f : Nat × Nat)
    (hk : 0 < k) (he : e ∈ g.edges) (hf : f ∈ g.edges)
    (hg : SemiprimeD1BoundaryPotential.Valid g) :
    ((localExpectation 4 k [] load [e, f]).value : Int) ≤
      (k : Int)^2 * ((localExpectation 2 k [] load [e]).value : Int) := by
  let term : List Nat → Int := fun fixed =>
    (k : Int)^2 * ((localExpectation 2 k fixed load [e]).value : Int) -
      ((localExpectation 4 k fixed load [e, f]).value : Int)
  have ha : Averages k term := averages_sub k _ _
    (averages_mul k _ _ (averages_single k load e)) (averages_pair k load e f)
  have hm := catalogue_marginal k g.vertices term ha []
  have hn : 0 ≤ ((colourWords k g.vertices).map (fun sample => term ([] ++ sample))).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨colours, hc, rfl⟩ := List.mem_map.mp hx
    have hl := SemiprimeD1BoundaryColourWords.member_length k g.vertices colours hc
    have hge := hg e he
    have hgf := hg f hf
    have hle : e.1 < colours.length ∧ e.2 < colours.length := by omega
    have hlf : f.1 < colours.length ∧ f.2 < colours.length := by omega
    dsimp only [term]
    simp only [List.nil_append,
      SemiprimeD1BoundaryPotential.single_fixed k colours load e hle,
      SemiprimeD1BoundaryPotential.pair_fixed k colours load e f hle hlf,
      SemiprimeD1BoundaryPotential.atom]
    split_ifs <;> simp_all [pow_succ]
    nlinarith [sq_nonneg (k : Int)]
  rw [hm] at hn
  have hp : (0 : Int) < (k : Int)^g.vertices := pow_pos (by exact_mod_cast hk) _
  dsimp only [term] at hn
  nlinarith

/-- Each ordered edge covariance is bounded above by one quarter of the scale. -/
theorem covariance_quarter (g : Graph) (k : Nat) (load : Load) (e f : Nat × Nat)
    (hk : 0 < k) (he : e ∈ g.edges) (hf : f ∈ g.edges)
    (hg : SemiprimeD1BoundaryPotential.Valid g) :
    4 * (((localExpectation 4 k [] load [e, f]).value : Int) -
      (eventCount k load : Int)^2) ≤ (k : Int)^4 := by
  have hb := pair_initial_le_single g k load e f hk he hf hg
  rw [single_initial k e.1 e.2 load (hg e he).2.2] at hb
  nlinarith [sq_nonneg ((k : Int)^2 - 2 * (eventCount k load : Int))]

end RiemannGaussian.SemiprimeD1BoundaryInitialVariance
