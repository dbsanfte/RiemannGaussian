/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeUniversalSourceExecution
import RiemannGaussian.SemiprimeBinomialExecutionTracked

/-! # Paid recursive universal source numerator acquisition
All branches of finite differences and all subset-list construction are executed.
The clock counts scalar/register/finite-list operations, not bit operations.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeMaterializedSourceUniversal
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes Subexp.MatrixSupport SqrtLog
variable {r Q R : ℕ}

/-- A value together with the finite operations executed to acquire it. -/
structure Run (α : Type*) where
  /-- Acquired value. -/
  value : α
  /-- Scalar/register/list operations. -/
  work : ℕ

/-- Full coordinate equality scan; both coordinates and all tails are evaluated. -/
def equalWord : (q : ℕ) → (Fin q → Fin r) → (Fin q → Fin r) →
    (Fin q → Fin r) → (Fin q → Fin r) → Run Bool
  | 0,_,_,_,_ => ⟨true,1⟩
  | q+1,a,b,c,d =>
      let tail := equalWord q (fun i => a i.succ) (fun i => b i.succ)
        (fun i => c i.succ) (fun i => d i.succ)
      ⟨decide (a 0=c 0) && decide (b 0=d 0) && tail.value,tail.work+7⟩

theorem equalWord_value (q : ℕ) (a b c d : Fin q → Fin r) :
    (equalWord q a b c d).value=true ↔ ∀ i, a i=c i ∧ b i=d i := by
  induction q with
  | zero => simp [equalWord]
  | succ q ih =>
    simp only [equalWord,Bool.and_eq_true,decide_eq_true_eq,ih]
    constructor
    · rintro ⟨⟨ha,hb⟩,ht⟩ i
      exact Fin.cases ⟨ha,hb⟩ ht i
    · intro h
      exact ⟨⟨(h 0).1,(h 0).2⟩,fun i => h i.succ⟩

theorem equalWord_work (q : ℕ) (a b c d : Fin q → Fin r) :
    (equalWord q a b c d).work=7*q+1 := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [equalWord,ih]; omega

/-- Literal register delta, using the paid equality scan rather than a function-equality oracle. -/
def delta (y u : UniversalType r Q 1) : Run ℤ :=
  let eq := equalWord Q u.head (u.slot 0) y.head (y.slot 0)
  ⟨if eq.value then 1 else 0,eq.work+1⟩

theorem delta_value (y u : UniversalType r Q 1) :
    (delta y u).value=LayoutNumerator.integerDelta y u := by
  have he : (equalWord Q u.head (u.slot 0) y.head (y.slot 0)).value=true ↔ u=y := by
    rw [equalWord_value]
    constructor
    · intro h
      cases u with | mk uh us =>
        cases y with | mk yh ys =>
          have hh : uh=yh := funext (fun i => (h i).1)
          have hs : us=ys := by
            funext i t
            have hi : i=0 := Subsingleton.elim _ _
            subst i
            exact (h t).2
          cases hh; cases hs; rfl
    · intro h
      subst u
      exact fun _ => ⟨rfl,rfl⟩
  simp only [delta,LayoutNumerator.integerDelta]
  simp only [he]

theorem delta_work (y u : UniversalType r Q 1) : (delta y u).work=7*Q+2 := by
  simp only [delta,equalWord_work]

/-- Full two-branch difference tree. Swapped register addresses are actual arguments. -/
def difference (positions : List (Fin Q)) (y u : UniversalType r Q 1) : Run ℤ :=
  match positions with
  | [] => delta y u
  | a::as =>
      let left := difference as y u
      let right := difference as y (swapPositions 0 {a} u)
      ⟨left.value-right.value,left.work+right.work+(4*Q+3)⟩

theorem difference_value (positions : List (Fin Q)) (y u : UniversalType r Q 1) :
    (difference positions y u).value=
      LayoutNumerator.integerDifference 0 positions (LayoutNumerator.integerDelta y) u := by
  induction positions generalizing u with
  | nil => exact delta_value y u
  | cons a as ih => simp only [difference,LayoutNumerator.integerDifference,ih]

/-- Exact two-branch recursion accounting, including all register swaps. -/
theorem difference_work_exact (positions : List (Fin Q)) (y u : UniversalType r Q 1) :
    (difference positions y u).work+(4*Q+3)=2^positions.length*(11*Q+5) := by
  induction positions generalizing u with
  | nil => simp only [difference,delta_work,List.length_nil,pow_zero,one_mul]; omega
  | cons a as ih =>
    simp only [difference,List.length_cons,pow_succ]
    have hl := ih u
    have hr := ih (swapPositions 0 {a} u)
    nlinarith

/-- Each leaf is a full equality scan; internal swaps and subtraction are retained. -/
theorem difference_work (positions : List (Fin Q)) (y u : UniversalType r Q 1) :
    (difference positions y u).work ≤ 2^positions.length*(11*Q+5) := by
  have h := difference_work_exact positions y u
  omega

/-- Generate every subset as a finite set by two actual recursive list branches. -/
def subsets {α : Type*} [DecidableEq α] : List α → Run (List (Finset α))
  | [] => ⟨[∅],1⟩
  | a::as =>
      let old := subsets as
      ⟨old.value ++ old.value.map (insert a),old.work+old.value.length*(as.length+3)+1⟩

@[simp] theorem subsets_length {α : Type*} [DecidableEq α] (xs : List α) :
    (subsets xs).value.length=2^xs.length := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [subsets,List.length_append,List.length_map,ih,List.length_cons,pow_succ]; omega

theorem subsets_mem {α : Type*} [DecidableEq α] (xs : List α) (s : Finset α) :
    s∈(subsets xs).value ↔ s⊆xs.toFinset := by
  induction xs generalizing s with
  | nil => simp [subsets]
  | cons a as ih =>
    simp only [subsets,List.mem_append,List.mem_map,ih,List.toFinset_cons]
    constructor
    · rintro (hs|⟨b,hb,rfl⟩)
      · exact hs.trans (Finset.subset_insert _ _)
      · exact Finset.insert_subset_insert _ hb
    · intro h
      by_cases ha : a∈s
      · right
        refine ⟨s.erase a,?_,Finset.insert_erase ha⟩
        intro x hx
        have := h (Finset.mem_of_mem_erase hx)
        rcases Finset.mem_insert.mp this with he|he
        · exact False.elim ((Finset.mem_erase.mp hx).1 he)
        · exact he
      · left
        intro x hx
        rcases Finset.mem_insert.mp (h hx) with he|he
        · exact False.elim (ha (he ▸ hx))
        · exact he

/-- No duplicates are created when the original position list has no duplicates. -/
theorem subsets_nodup {α : Type*} [DecidableEq α] (xs : List α) (hx : xs.Nodup) :
    (subsets xs).value.Nodup := by
  induction xs with
  | nil => simp [subsets]
  | cons a as ih =>
    have ha := (List.nodup_cons.mp hx).1
    have hold := ih (List.nodup_cons.mp hx).2
    have hnot : ∀ s∈(subsets as).value, a∉s := by
      intro s hs hmem
      exact ha (List.mem_toFinset.mp ((subsets_mem as s).mp hs hmem))
    apply List.nodup_append.mpr
    refine ⟨hold,hold.map_on (fun x hx y hy he => ?_),?_⟩
    · have hh := congrArg (fun s : Finset α => s.erase a) he
      simpa only [Finset.erase_insert (hnot x hx),Finset.erase_insert (hnot y hy)] using hh
    · intro x hx y hy he
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hy
      have heq : x=insert a z := he
      exact hnot x hx (heq ▸ Finset.mem_insert_self _ _)

/-- The generated list denotes exactly the finite powerset. -/
theorem subsets_finset {α : Type*} [DecidableEq α] (xs : List α) :
    (subsets xs).value.toFinset=xs.toFinset.powerset := by
  ext s
  simp only [List.mem_toFinset,subsets_mem,Finset.mem_powerset]

/-- Constructing the subset list is polynomial in its explicit output size and input width. -/
theorem subsets_work {α : Type*} [DecidableEq α] (xs : List α) :
    (subsets xs).work ≤ 2^xs.length*(xs.length+3) := by
  induction xs with
  | nil => norm_num [subsets]
  | cons a as ih =>
    simp only [subsets,subsets_length,List.length_cons,pow_succ]
    have hp : 1≤2^as.length := Nat.one_le_pow _ _ (by decide)
    nlinarith

/-- Every coordinate position in canonical order; subset membership is explicitly scanned. -/
def positions (s : Finset (Fin Q)) : List (Fin Q) :=
  (List.finRange Q).filter (fun i => decide (i∈s))

theorem positions_perm (s : Finset (Fin Q)) : (positions s).Perm s.toList := by
  apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange Q).filter _) s.nodup_toList).mpr
  intro i
  simp

theorem positions_length (s : Finset (Fin Q)) : (positions s).length=s.card := by
  exact (positions_perm s).length_eq.trans s.length_toList

/-- Positive powers are acquired by actual repeated scalar multiplication. -/
def powerTwo : ℕ → Run ℤ
  | 0 => ⟨1,1⟩
  | k+1 => let old := powerTwo k; ⟨old.value*2,old.work+2⟩

theorem powerTwo_value (k : ℕ) : (powerTwo k).value=(2 : ℤ)^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [powerTwo,ih,pow_succ]

theorem powerTwo_work (k : ℕ) : (powerTwo k).work=2*k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [powerTwo,ih]; omega

/-- Execute every callback in an actual finite list, retaining all callback clocks. -/
def sumRuns {α : Type*} (f : α → Run ℤ) : List α → Run ℤ
  | [] => ⟨0,1⟩
  | a::as =>
      let first := f a
      let tail := sumRuns f as
      ⟨first.value+tail.value,first.work+tail.work+2⟩

theorem sumRuns_value {α : Type*} (f : α → Run ℤ) (xs : List α) :
    (sumRuns f xs).value=(xs.map (fun a => (f a).value)).sum := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [sumRuns,List.map_cons,List.sum_cons,ih]

theorem sumRuns_work {α : Type*} (f : α → Run ℤ) (xs : List α) (B : ℕ)
    (h : ∀ a∈xs, (f a).work≤B) :
    (sumRuns f xs).work≤xs.length*(B+2)+1 := by
  induction xs with
  | nil => simp [sumRuns]
  | cons a as ih =>
    have hh := h a (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [sumRuns,List.length_cons]
    nlinarith

/-- One subset contribution, including acquisition of its scalar power and difference tree. -/
def contribution (c : Fin R → ℤ) (j : Fin R) (t : Fin Q)
    (y u : UniversalType r Q 1) (s : Finset (Fin Q)) : Run ℤ :=
  if s.card=j.val then
    let power := powerTwo (R-1-j.val)
    let diff := difference (positions s) y (swapPositions 0 (activePositions t) u)
    ⟨c j*power.value*diff.value,power.work+diff.work+(Q+1)*(Q+1)+2*Q+6⟩
  else ⟨0,Q+2⟩

theorem contribution_value (c : Fin R → ℤ) (j : Fin R) (t : Fin Q)
    (y u : UniversalType r Q 1) (s : Finset (Fin Q)) :
    (contribution c j t y u s).value=
      if s.card=j.val then c j*2^(R-1-j.val)*
        LayoutNumerator.integerDifference 0 s.toList (LayoutNumerator.integerDelta y)
          (swapPositions 0 (activePositions t) u) else 0 := by
  unfold contribution
  split_ifs
  · simp only [powerTwo_value,difference_value]
    rw [SemiprimeUniversalNumeratorExecution.integerDifference_perm 0 (positions_perm s)]
  · rfl

/-- Active positions are acquired by the actual canonical finite filter. -/
def active (t : Fin Q) : List (Fin Q) :=
  (List.finRange Q).filter (fun a => decide (a≠t))

theorem active_finset (t : Fin Q) : (active t).toFinset=activePositions t := by
  ext a
  simp [active,activePositions]

/-- Paid universal entry with a cached subset list shared by every parity index. -/
def entry (c : Fin R → ℤ) (t : Fin Q) (u y : UniversalType r Q 1) : Run ℤ :=
  let ss := subsets (active t)
  let out := sumRuns (fun j : Fin R => sumRuns (contribution c j t y u) ss.value) (List.finRange R)
  ⟨out.value,out.work+ss.work+(Q+1)*(Q+1)⟩

/-- The acquired entry equals the original source numerator from the SAME parity data. -/
theorem entry_value (A : ℕ) (c : Fin R → ℤ)
    (hc : c=BinomialInterpolation.parityCoefficients (K:=ℤ) A R)
    (t : Fin Q) (u y : UniversalType r Q 1) :
    (entry c t u y).value=LayoutNumerator.entry 0 t A R u y := by
  have hn : (subsets (active t)).value.Nodup := subsets_nodup _ ((List.nodup_finRange Q).filter _)
  simp only [entry,sumRuns_value]
  rw [← List.sum_toFinset _ (List.nodup_finRange R)]
  simp only [List.toFinset_finRange]
  rw [← SemiprimeUniversalNumeratorExecution.entry_eq A c hc]
  unfold SemiprimeUniversalNumeratorExecution.entry
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [← List.sum_toFinset _ hn,subsets_finset,active_finset]
  simp_rw [contribution_value]
  rw [← Finset.sum_filter]
  rw [← Finset.powersetCard_eq_filter]
  simp only [BinomialInterpolation.extendCoefficients, j.isLt, dite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [SemiprimeUniversalNumeratorExecution.integerDifference_perm 0 (Finset.sort_perm_toList _ _)]

/-- Explicit bound for every subset callback, including rejected cardinalities. -/
def contributionBudget (Q R : ℕ) : ℕ :=
  2*R+1+2^Q*(11*Q+5)+(Q+1)*(Q+1)+2*Q+6

theorem contribution_work (c : Fin R → ℤ) (j : Fin R) (t : Fin Q)
    (y u : UniversalType r Q 1) (s : Finset (Fin Q)) :
    (contribution c j t y u s).work≤contributionBudget Q R := by
  have hs : s.card≤Q := s.card_le_univ.trans_eq (by simp)
  have hp : 2^(positions s).length≤2^Q := by
    rw [positions_length]
    exact Nat.pow_le_pow_right (by decide) hs
  have hd := difference_work (positions s) y (swapPositions 0 (activePositions t) u)
  have hm := Nat.mul_le_mul_right (11*Q+5) hp
  unfold contribution
  split_ifs
  · simp only [powerTwo_work]
    unfold contributionBudget
    have hk : R-1-j.val≤R := Nat.sub_le _ _ |>.trans (Nat.sub_le _ _)
    omega
  · dsimp only
    unfold contributionBudget
    omega

/-- Bound for the entire entry run, including subset-list construction and both finite sums. -/
def entryBudget (Q R : ℕ) : ℕ :=
  R*(2^Q*(contributionBudget Q R+2)+3)+1+2^Q*(Q+3)+(Q+1)*(Q+1)

theorem active_length_le (t : Fin Q) : (active t).length≤Q :=
  (List.length_filter_le _ _).trans_eq List.length_finRange

theorem entry_work (c : Fin R → ℤ) (t : Fin Q) (u y : UniversalType r Q 1) :
    (entry c t u y).work≤entryBudget Q R := by
  have hlen := active_length_le t
  have hp : 2^(active t).length≤2^Q := Nat.pow_le_pow_right (by decide) hlen
  have hs := subsets_work (active t)
  have hsw : (subsets (active t)).work≤2^Q*(Q+3) :=
    hs.trans (Nat.mul_le_mul hp (Nat.add_le_add_right hlen 3))
  have inner (j : Fin R) :
      (sumRuns (contribution c j t y u) (subsets (active t)).value).work≤
        2^Q*(contributionBudget Q R+2)+1 := by
    have h := sumRuns_work (contribution c j t y u) (subsets (active t)).value
      (contributionBudget Q R) (fun s _ => contribution_work c j t y u s)
    rw [subsets_length] at h
    exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hp) 1)
  have outer := sumRuns_work
    (fun j : Fin R => sumRuns (contribution c j t y u) (subsets (active t)).value)
    (List.finRange R) (2^Q*(contributionBudget Q R+2)+1) (fun j _ => inner j)
  rw [List.length_finRange] at outer
  unfold entry
  dsimp only
  calc
    _ ≤ (R*(2^Q*(contributionBudget Q R+2)+1+2)+1)+2^Q*(Q+3)+(Q+1)*(Q+1) := by omega
    _ = entryBudget Q R := by unfold entryBudget; ring

/-- A literal polynomial envelope after the universal alphabet pays the exponential subsets. -/
def entryPolynomial (Q R : ℕ) : ℕ :=
  R*((11*Q+5)+(2*R+1+(Q+1)*(Q+1)+2*Q+8)+3)+1+(Q+3)+(Q+1)*(Q+1)

theorem entryBudget_polynomial (Q R D : ℕ) (hD : 2^(2*Q)≤D) :
    entryBudget Q R≤D*entryPolynomial Q R := by
  have hx : 1≤2^Q := Nat.one_le_pow _ _ (by decide)
  have hxx : 2^Q*2^Q≤D := by simpa only [← pow_add,← two_mul] using hD
  have hsingle : 2^Q≤D := (Nat.le_mul_of_pos_right _ (by omega)).trans hxx
  have hone : 1≤D := hx.trans hsingle
  have hthree : 3≤D*3 := by omega
  have hlast : (Q+1)*(Q+1)≤D*((Q+1)*(Q+1)) :=
    by simpa only [one_mul] using Nat.mul_le_mul_right ((Q+1)*(Q+1)) hone
  calc
    entryBudget Q R = R*((2^Q*2^Q)*(11*Q+5)+
      2^Q*(2*R+1+(Q+1)*(Q+1)+2*Q+8)+3)+1+2^Q*(Q+3)+(Q+1)*(Q+1) := by
        unfold entryBudget contributionBudget
        ring
    _ ≤ R*(D*(11*Q+5)+D*(2*R+1+(Q+1)*(Q+1)+2*Q+8)+D*3)+
      D+D*(Q+3)+D*((Q+1)*(Q+1)) := by gcongr
    _ = D*entryPolynomial Q R := by unfold entryPolynomial; ring

/-- Native r>=2 makes the complete universal alphabet large enough for that polynomial bound. -/
theorem entry_work_native (hr : 2≤r) (c : Fin R → ℤ) (t : Fin Q)
    (u y : UniversalType r Q 1) :
    (entry c t u y).work≤r^(2*Q)*entryPolynomial Q R :=
  (entry_work c t u y).trans (entryBudget_polynomial Q R _ (Nat.pow_le_pow_left hr _))

/-- Cache paid callbacks in an actual list, retaining every value and every callback clock. -/
def collect {α β : Type*} (f : α → Run β) : List α → Run (List β)
  | [] => ⟨[],1⟩
  | a::as =>
      let first := f a
      let tail := collect f as
      ⟨first.value::tail.value,first.work+tail.work+2⟩

theorem collect_value {α β : Type*} (f : α → Run β) (xs : List α) :
    (collect f xs).value=xs.map (fun a => (f a).value) := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [collect,ih,List.map_cons]

theorem collect_work {α β : Type*} (f : α → Run β) (xs : List α) (B : ℕ)
    (h : ∀ a∈xs, (f a).work≤B) :
    (collect f xs).work≤xs.length*(B+2)+1 := by
  induction xs with
  | nil => simp [collect]
  | cons a as ih =>
    have hh := h a (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [collect,List.length_cons]
    nlinarith

/-- Cache every source numerator at every actual universal row/column and position. -/
def table (A R : ℕ) (words : List (UniversalType r Q 1)) : Run (List (List (List ℤ))) :=
  let parity := SemiprimeBinomialExecutionTracked.acquireParity A R
  let c := fun j : Fin R => SemiprimeBinomialExecution.coeff parity.coefficients j.rev.val
  let out := collect (fun t : Fin Q => collect (fun u => collect
    (fun y => entry c t u y) words) words) (List.finRange Q)
  ⟨out.value,out.work+parity.arithmetic+parity.reads+1⟩

/-- Full acquired table values, with parity supplied only by the actual cached solver. -/
theorem table_value (A R : ℕ) (words : List (UniversalType r Q 1)) :
    (table A R words).value=(List.finRange Q).map (fun t => words.map (fun u =>
      words.map (fun y => LayoutNumerator.entry 0 t A R u y))) := by
  unfold table
  simp only [collect_value]
  congr 1
  funext t
  congr 1
  funext u
  congr 1
  funext y
  exact entry_value A _ (SemiprimeBinomialExecutionTracked.acquiredParity_eq A R) t u y

/-- Every table call and row/column list allocation is retained. -/
def tableBudget (A R Q D : ℕ) : ℕ :=
  Q*(D*(D*(entryBudget Q R+2)+3)+3)+1+
    (A*(R+1)+A+R+R^2)+(2*A*(R+1)+R^2)+1

theorem table_work (A R : ℕ) (words : List (UniversalType r Q 1)) :
    (table A R words).work≤tableBudget A R Q words.length := by
  let parity := SemiprimeBinomialExecutionTracked.acquireParity A R
  let c := fun j : Fin R => SemiprimeBinomialExecution.coeff parity.coefficients j.rev.val
  have inner (t : Fin Q) (u : UniversalType r Q 1) :
      (collect (fun y => entry c t u y) words).work≤words.length*(entryBudget Q R+2)+1 :=
    collect_work _ _ _ (fun y _ => entry_work c t u y)
  have middle (t : Fin Q) :
      (collect (fun u => collect (fun y => entry c t u y) words) words).work≤
        words.length*(words.length*(entryBudget Q R+2)+3)+1 := by
    have h := collect_work (fun u => collect (fun y => entry c t u y) words) words
      (words.length*(entryBudget Q R+2)+1) (fun u _ => inner t u)
    exact h
  have outer := collect_work
    (fun t : Fin Q => collect (fun u => collect (fun y => entry c t u y) words) words)
    (List.finRange Q) (words.length*(words.length*(entryBudget Q R+2)+3)+1)
    (fun t _ => middle t)
  rw [List.length_finRange] at outer
  have hp := SemiprimeBinomialExecutionTracked.acquireParity_work A R
  unfold table
  dsimp only
  rw [hp.1,hp.2]
  unfold tableBudget
  have he : Q*(words.length*(words.length*(entryBudget Q R+2)+3)+1+2)+1=
    Q*(words.length*(words.length*(entryBudget Q R+2)+3)+3)+1 := by ring
  rw [he] at outer
  dsimp only [c,parity] at outer
  omega

end RiemannGaussian.SemiprimeMaterializedSourceUniversal
