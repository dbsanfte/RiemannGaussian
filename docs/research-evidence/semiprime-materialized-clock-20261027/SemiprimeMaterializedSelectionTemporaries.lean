/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedSelectionHeight
import RiemannGaussian.SemiprimeRationalBits

/-! # Actual RREF scalar-expression temporary heights

Expression leaves are cached actual state or input scalars. Finite residual
sums are expanded once per coordinate, not through the earlier row history.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
namespace RiemannGaussian.SemiprimeMaterializedSelectionTemporaries
open scoped BigOperators
open SemiprimeRowSelectionExecution SemiprimeRowSelectionTracked
open SemiprimeMaterializedSelectionHeight

/-- Both canonical magnitudes of an actual rational value. -/
def Bounded (q : ℚ) (B : ℕ) : Prop := q.num.natAbs≤B ∧ q.den≤B

/-- Enlarging a literal canonical envelope is safe. -/
theorem bounded_mono {q : ℚ} {A B : ℕ} (h : Bounded q A) (hab : A≤B) : Bounded q B :=
  ⟨h.1.trans hab,h.2.trans hab⟩

/-- A tested integer fraction supplies canonical bounds after actual reduction. -/
theorem bounded_fraction (a b : ℤ) (hb : b≠0) (B : ℕ)
    (ha : a.natAbs≤B) (hd : b.natAbs≤B) : Bounded ((a : ℚ)/(b : ℚ)) B := by
  have h := reduced_fraction_bounds ((a : ℚ)/(b : ℚ)) a b hb rfl
  exact ⟨h.1.trans ha,h.2.trans hd⟩

/-- Products multiply the two operand envelopes, not their circuit histories. -/
theorem bounded_mul {q r : ℚ} {A B : ℕ} (hq : Bounded q A) (hr : Bounded r B) :
    Bounded (q*r) (A*B) := by
  rw [← Rat.num_div_den q,← Rat.num_div_den r]
  rw [div_mul_div_comm,← Int.cast_mul,← Nat.cast_mul]
  apply bounded_fraction _ _ (by positivity)
  · simpa only [Int.natAbs_mul] using Nat.mul_le_mul hq.1 hr.1
  · simpa only [Int.natAbs_mul,Int.natAbs_natCast] using Nat.mul_le_mul hq.2 hr.2

/-- Addition's one extra bit is explicit, including unreduced numerator growth. -/
theorem bounded_add {q r : ℚ} {A B : ℕ} (hq : Bounded q A) (hr : Bounded r B) :
    Bounded (q+r) (2*A*B) := by
  have hqd : (q.den : ℚ)≠0 := by positivity
  have hrd : (r.den : ℚ)≠0 := by positivity
  have he : q+r=((q.num*(r.den : ℤ)+r.num*(q.den : ℤ) : ℤ) : ℚ)/
      ((q.den*r.den : ℕ) : ℚ) := by
    rw [Int.cast_add,Int.cast_mul,Int.cast_mul,Int.cast_natCast,Int.cast_natCast,Nat.cast_mul]
    nth_rw 1 [← Rat.num_div_den q,← Rat.num_div_den r]
    field_simp
  rw [he]
  apply bounded_fraction _ _ (by positivity)
  · have h := Int.natAbs_add_le (q.num*(r.den : ℤ)) (r.num*(q.den : ℤ))
    simp only [Int.natAbs_mul,Int.natAbs_natCast] at h
    have h1 := Nat.mul_le_mul hq.1 hr.2
    have h2 := Nat.mul_le_mul hr.1 hq.2
    nlinarith
  · simp only [Int.natAbs_natCast]
    have h := Nat.mul_le_mul hq.2 hr.2
    nlinarith

/-- Sign change does not increase either canonical magnitude. -/
theorem bounded_neg {q : ℚ} {A : ℕ} (hq : Bounded q A) : Bounded (-q) A := by
  simpa only [Bounded,Rat.neg_num,Int.natAbs_neg,Rat.neg_den] using hq

/-- Subtraction uses the same explicit extra bit as addition. -/
theorem bounded_sub {q r : ℚ} {A B : ℕ} (hq : Bounded q A) (hr : Bounded r B) :
    Bounded (q-r) (2*A*B) := by
  simpa only [sub_eq_add_neg] using bounded_add hq (bounded_neg hr)

/-- Reciprocal exchanges numerator and denominator; the zero convention is
handled explicitly, rather than assuming a future pivot is nonzero. -/
theorem bounded_inv {q : ℚ} {A : ℕ} (hq : Bounded q A) : Bounded q⁻¹ A := by
  by_cases hz : q=0
  · subst q
    simpa only [inv_zero] using hq
  · have hn : q.num≠0 := by
      intro h
      have he := Rat.num_div_den q
      simp [h] at he
      exact hz he.symm
    have he : q⁻¹=((q.den : ℤ) : ℚ)/(q.num : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den q,inv_div]
      rfl
    rw [he]
    exact bounded_fraction _ _ hn A (by simpa using hq.2) hq.1

/-- Division never needs a larger envelope than a product of canonical bounds. -/
theorem bounded_div {q r : ℚ} {A B : ℕ} (hq : Bounded q A) (hr : Bounded r B) :
    Bounded (q/r) (A*B) := by
  simpa only [div_eq_mul_inv] using bounded_mul hq (bounded_inv hr)

/-- The actual finite arithmetic syntax of one RREF scalar coordinate. -/
inductive Expr where
  | scalar (value : ℚ)
  | add (left right : Expr)
  | sub (left right : Expr)
  | mul (left right : Expr)
  | divide (left right : Expr)

/-- Literal rational execution of the scalar syntax. -/
def Expr.eval : Expr → ℚ
  | .scalar q => q
  | .add a b => a.eval+b.eval
  | .sub a b => a.eval-b.eval
  | .mul a b => a.eval*b.eval
  | .divide a b => a.eval/b.eval

/-- Actual operands and operation results, in execution order. -/
def Expr.trace : Expr → List ℚ
  | .scalar q => [q]
  | .add a b => a.trace++b.trace++[a.eval+b.eval]
  | .sub a b => a.trace++b.trace++[a.eval-b.eval]
  | .mul a b => a.trace++b.trace++[a.eval*b.eval]
  | .divide a b => a.trace++b.trace++[a.eval/b.eval]

/-- All leaves are cached inputs, whose height comes from the actual run. -/
def Expr.LeavesBounded (B : ℕ) : Expr → Prop
  | .scalar q => Bounded q B
  | .add a b | .sub a b | .mul a b | .divide a b => a.LeavesBounded B ∧ b.LeavesBounded B

/-- A linear syntax budget: cached leaves cost one, each binary operation one. -/
def Expr.nodes : Expr → ℕ
  | .scalar _ => 1
  | .add a b | .sub a b | .mul a b | .divide a b => a.nodes+b.nodes+1

/-- Literal tracked arithmetic is recovered from the expression data path. -/
def Expr.run : Expr → ScalarRun
  | .scalar q => SemiprimeRowSelectionTracked.scalar q
  | .add a b => SemiprimeRowSelectionTracked.add a.run b.run
  | .sub a b => SemiprimeRowSelectionTracked.sub a.run b.run
  | .mul a b => SemiprimeRowSelectionTracked.mul a.run b.run
  | .divide a b => SemiprimeRowSelectionTracked.divide a.run b.run

/-- Erasure gives the exact returned scalar, not a supplied answer. -/
theorem Expr.run_value (e : Expr) : e.run.value=e.eval := by
  induction e <;> simp_all [Expr.run,Expr.eval,SemiprimeRowSelectionTracked.scalar,SemiprimeRowSelectionTracked.add,
    SemiprimeRowSelectionTracked.sub,SemiprimeRowSelectionTracked.mul,SemiprimeRowSelectionTracked.divide]

/-- Every finite expression returns a trace member. -/
theorem Expr.eval_mem_trace (e : Expr) : e.eval∈e.trace := by
  cases e <;> simp [Expr.eval,Expr.trace]

/-- Local rational expressions have bit exponents additive in their ACTUAL
finite syntax, not exponential in the number of prior selector steps. -/
theorem Expr.eval_bounded (e : Expr) (bits : ℕ) (h : e.LeavesBounded (2^bits)) :
    Bounded e.eval (2^((bits+1)*e.nodes)) := by
  induction e with
  | scalar q =>
    exact bounded_mono h (by simp only [Expr.nodes]; gcongr; omega)
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | divide a b iha ihb =>
    rcases h with ⟨ha,hb⟩
    have hA := iha ha
    have hB := ihb hb
    first
    | apply bounded_mono (bounded_add hA hB)
    | apply bounded_mono (bounded_sub hA hB)
    | apply bounded_mono (bounded_mul hA hB)
    | apply bounded_mono (bounded_div hA hB)
    all_goals
      simp only [Expr.nodes]
      first
      | calc
          2*2^((bits+1)*a.nodes)*2^((bits+1)*b.nodes)=
            2^((bits+1)*a.nodes+(bits+1)*b.nodes+1) := by
              simp only [pow_add,pow_one]; ring
          _≤_ := Nat.pow_le_pow_right (by decide) (by nlinarith)
      | rw [← Nat.pow_add]
        exact Nat.pow_le_pow_right (by decide) (by nlinarith)

/-- Every operand and result in the actual scalar evaluation obeys the same
polynomial syntax-height envelope. -/
theorem Expr.trace_bounded (e : Expr) (bits : ℕ) (h : e.LeavesBounded (2^bits)) :
    ∀ q∈e.trace,Bounded q (2^((bits+1)*e.nodes)) := by
  induction e with
  | scalar q =>
    intro z hz
    simp only [Expr.trace,List.mem_singleton] at hz
    subst z
    exact Expr.eval_bounded _ bits h
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | divide a b iha ihb =>
    intro q hq
    rcases h with ⟨ha,hb⟩
    simp only [Expr.trace,List.mem_append,List.mem_singleton] at hq
    rcases hq with (hqa|hqb)|hq
    · apply bounded_mono (iha ha q hqa)
      apply Nat.pow_le_pow_right (by decide)
      simp only [Expr.nodes]
      nlinarith
    · apply bounded_mono (ihb hb q hqb)
      apply Nat.pow_le_pow_right (by decide)
      simp only [Expr.nodes]
      nlinarith
    · subst q
      first
      | exact Expr.eval_bounded (.add a b) bits ⟨ha,hb⟩
      | exact Expr.eval_bounded (.sub a b) bits ⟨ha,hb⟩
      | exact Expr.eval_bounded (.mul a b) bits ⟨ha,hb⟩
      | exact Expr.eval_bounded (.divide a b) bits ⟨ha,hb⟩

/-- Finite summation syntax matching the executed sumRun recursion. -/
def sumExpr : {n : ℕ} → (Fin n → Expr) → Expr
  | 0,_ => .scalar 0
  | _+1,f => .add (f 0) (sumExpr (f ∘ Fin.succ))

/-- This is the SAME finite summation data path as the tracked selector. -/
theorem sumExpr_run {n : ℕ} (f : Fin n → Expr) :
    (sumExpr f).run=sumRun (fun i => (f i).run) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumExpr,Expr.run,sumRun,ih,Function.comp_def]

/-- Polynomial finite-sum syntax size. -/
theorem sumExpr_nodes {n bound : ℕ} (f : Fin n → Expr) (h : ∀ i,(f i).nodes≤bound) :
    (sumExpr f).nodes≤n*(bound+1)+1 := by
  induction n with
  | zero => simp [sumExpr,Expr.nodes]
  | succ n ih =>
    have ht := ih (f ∘ Fin.succ) (fun i => h i.succ)
    have hh := h 0
    simp only [sumExpr,Expr.nodes]
    nlinarith

/-- Bounded cached terms give bounded leaves in the actual finite sum. -/
theorem sumExpr_leaves {n B : ℕ} (f : Fin n → Expr) (h : ∀ i,(f i).LeavesBounded B)
    (hB : 1≤B) : (sumExpr f).LeavesBounded B := by
  induction n with
  | zero => simpa [sumExpr,Expr.LeavesBounded,Bounded] using hB
  | succ n ih => exact ⟨h 0,ih (f ∘ Fin.succ) (fun i => h i.succ)⟩

/-- Actual scalar coordinate used by residualRun. -/
def residualExpr {m n : ℕ} (s : State m n) (row : Row n) (v : Fin n) : Expr :=
  .sub (.scalar (row v)) (sumExpr (fun c : Fin n => if s.active c then
    .mul (.scalar (row c)) (.scalar (s.rows c v)) else .scalar 0))

/-- Exact match to the frozen selector residual coordinate, including its
literal multiplication and finite-sum recursion. -/
theorem residualExpr_run {m n : ℕ} (s : State m n) (row : Row n) (v : Fin n) :
    (residualExpr s row v).run=
      sub (scalar (row v)) (sumRun (fun c =>
        if s.active c then mul (scalar (row c)) (scalar (s.rows c v)) else scalar 0)) := by
  simp only [residualExpr,Expr.run,sumExpr_run]
  congr 2
  funext c
  cases s.active c <;> rfl

/-- Cached finite row construction returns this exact scalar syntax value. -/
theorem residualExpr_value {m n : ℕ} (s : State m n) (row : Row n) (v : Fin n) :
    (residualExpr s row v).eval=(residualRun s row).row v := by
  rw [← Expr.run_value,residualExpr_run]
  simp only [residualRun,buildRow_value]

/-- No hidden expansion through earlier selector history: one residual
coordinate has at most 4n+3 cached scalar syntax nodes. -/
theorem residualExpr_nodes {m n : ℕ} (s : State m n) (row : Row n) (v : Fin n) :
    (residualExpr s row v).nodes≤4*n+3 := by
  have h := sumExpr_nodes (bound := 3)
    (fun c : Fin n => if s.active c then
      Expr.mul (.scalar (row c)) (.scalar (s.rows c v)) else .scalar 0)
    (by intro c; cases s.active c <;> norm_num [Expr.nodes])
  simp only [residualExpr,Expr.nodes]
  omega

/-- Actual per-coordinate normalization syntax reads the computed residual
cache; the residual computation is charged separately, not recursively hidden. -/
def normalizeExpr {n : ℕ} (row : Row n) (p v : Fin n) : Expr :=
  .divide (.scalar (row v)) (.scalar (row p))

/-- Normalization syntax is exactly the tracked division result. -/
theorem normalizeExpr_value {n : ℕ} (row : Row n) (p v : Fin n) :
    (normalizeExpr row p v).eval=(normalizeRun row p).row v := by
  simp only [normalizeExpr,Expr.eval,normalizeRun_value]

/-- Actual back-elimination syntax with the computed normalized row cached. -/
def updateExpr {m n : ℕ} (s : State m n) (p : Fin n) (row : Row n) (c v : Fin n) : Expr :=
  if c=p then .scalar (row v) else if s.active c then
    .sub (.scalar (s.rows c v)) (.mul (.scalar (s.rows c p)) (.scalar (row v))) else .scalar 0

/-- Back update syntax equals the actual materialized matrix coordinate. -/
theorem updateExpr_value {m n : ℕ} (s : State m n) (p : Fin n) (row : Row n) (c v : Fin n) :
    (updateExpr s p row c v).eval=(updateRun s p row).rows c v := by
  rw [updateRun_value]
  unfold updateExpr
  split_ifs <;> rfl

/-- Polynomial exponent for cached leaves of an actual residual stage. -/
def leafBits (n bits : ℕ) : ℕ := n*(n+bits)+bits

/-- Polynomial exponent for all residual arithmetic temporaries. -/
def residualBits (n bits : ℕ) : ℕ := (leafBits n bits+1)*(4*n+3)

/-- Polynomial exponent for all normalization arithmetic temporaries. -/
def normalizeBits (n bits : ℕ) : ℕ := (residualBits n bits+1)*3

/-- Polynomial exponent for all back-elimination arithmetic temporaries. -/
def updateBits (n bits : ℕ) : ℕ := (n*(n+bits)+normalizeBits n bits+1)*5

/-- Actual integer-input cached row magnitudes have the canonical envelope. -/
theorem original_bounded {m n : ℕ} (C : Fin m → Fin n → ℤ) (bits : ℕ)
    (hC : ∀ j v,|C j v|≤(2^bits : ℕ)) (j : Fin m) (v : Fin n) :
    Bounded (originalRow C j v) (2^bits) := by
  constructor
  · simpa only [originalRow,Rat.num_intCast] using
      (show (C j v).natAbs≤2^bits by exact_mod_cast (show ((C j v).natAbs : ℤ)≤(2^bits : ℕ) by
        simpa only [Int.natCast_natAbs] using hC j v))
  · simp only [originalRow,Rat.den_intCast]
    exact Nat.one_le_two_pow

/-- All residual leaves come from proved actual state/input bounds. -/
theorem residual_leaves {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v|≤(2^bits : ℕ)) (j : Fin m) (v : Fin n) :
    (residualExpr (run C ids) (originalRow C j) v).LeavesBounded (2^leafBits n bits) := by
  have hin (c : Fin n) : Bounded (originalRow C j c) (2^leafBits n bits) :=
    bounded_mono (original_bounded C bits hC j c) (by unfold leafBits; gcongr; omega)
  refine ⟨hin v,?_⟩
  apply sumExpr_leaves
  · intro c
    cases hc : (run C ids).active c with
    | false => simp [Expr.LeavesBounded,Bounded,Nat.one_le_two_pow]
    | true =>
      refine ⟨hin c,?_⟩
      exact bounded_mono (state_binary_bounds C ids bits hC c v)
        (by unfold leafBits; gcongr; omega)
  · exact Nat.one_le_two_pow

/-- EVERY actual residual scalar temporary has polynomial binary height. -/
theorem residual_trace_bounds {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v|≤(2^bits : ℕ)) (j : Fin m) (v : Fin n) :
    ∀ q∈(residualExpr (run C ids) (originalRow C j) v).trace,
      Bounded q (2^residualBits n bits) := by
  intro q hq
  have h := Expr.trace_bounded _ (leafBits n bits) (residual_leaves C ids bits hC j v) q hq
  apply bounded_mono h
  apply Nat.pow_le_pow_right (by decide)
  unfold residualBits
  exact Nat.mul_le_mul_left _ (residualExpr_nodes _ _ _)

/-- EVERY normalization temporary reads only the actual residual cache. -/
theorem normalize_trace_bounds {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v|≤(2^bits : ℕ)) (j : Fin m) (p v : Fin n) :
    ∀ q∈(normalizeExpr (residualRun (run C ids) (originalRow C j)).row p v).trace,
      Bounded q (2^normalizeBits n bits) := by
  apply Expr.trace_bounded
  constructor
  · rw [← residualExpr_value]
    exact residual_trace_bounds C ids bits hC j v _ (Expr.eval_mem_trace _)
  · rw [← residualExpr_value]
    exact residual_trace_bounds C ids bits hC j p _ (Expr.eval_mem_trace _)

/-- EVERY back-elimination scalar temporary reads actual cached operands. -/
theorem update_trace_bounds {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v|≤(2^bits : ℕ)) (j : Fin m) (p c v : Fin n) :
    ∀ q∈(updateExpr (run C ids) p
      (normalizeRun (residualRun (run C ids) (originalRow C j)).row p).row c v).trace,
      Bounded q (2^updateBits n bits) := by
  let row := (normalizeRun (residualRun (run C ids) (originalRow C j)).row p).row
  have hs (k v : Fin n) : Bounded ((run C ids).rows k v)
      (2^(n*(n+bits)+normalizeBits n bits)) :=
    bounded_mono (state_binary_bounds C ids bits hC k v) (by gcongr; omega)
  have hr (v : Fin n) : Bounded (row v) (2^(n*(n+bits)+normalizeBits n bits)) := by
    have hn := normalize_trace_bounds C ids bits hC j p v _ (Expr.eval_mem_trace _)
    rw [normalizeExpr_value] at hn
    exact bounded_mono hn (by gcongr; omega)
  intro q hq
  have hn : (updateExpr (run C ids) p row c v).nodes≤5 := by
    unfold updateExpr
    split_ifs <;> norm_num [Expr.nodes]
  have hl : (updateExpr (run C ids) p row c v).LeavesBounded
      (2^(n*(n+bits)+normalizeBits n bits)) := by
    unfold updateExpr
    split_ifs
    · exact hr v
    · exact ⟨hs c v,hs c p,hr v⟩
    · simp only [Expr.LeavesBounded,Bounded,Rat.num_zero,Int.natAbs_zero,Rat.den_zero]
      exact ⟨Nat.zero_le _,Nat.one_le_two_pow⟩
  apply bounded_mono (Expr.trace_bounded _ _ hl q hq)
  apply Nat.pow_le_pow_right (by decide)
  unfold updateBits
  exact Nat.mul_le_mul_left _ hn

/-- One fixed polynomial width covers all actual scalar-stage temporaries. -/
def selectorWidth (n bits : ℕ) : ℕ :=
  leafBits n bits+residualBits n bits+normalizeBits n bits+updateBits n bits+1

/-- A non-strict canonical power bound automatically supplies a strict
physical-word fit after one additional bit. -/
theorem bounded_fits {q : ℚ} {e W : ℕ} (h : Bounded q (2^e)) (he : e<W) :
    SemiprimeRationalBits.Fits q W := by
  have hp : 2^e<2^W := Nat.pow_lt_pow_right (by decide) he
  exact ⟨h.1.trans_lt hp,h.2.trans_lt hp⟩

/-- Actual residual products, finite-sum prefixes and subtraction results fit
the same acquired polynomial width. -/
theorem residual_trace_fits {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v|≤(2^bits : ℕ)) (j : Fin m) (v : Fin n) :
    ∀ q∈(residualExpr (run C ids) (originalRow C j) v).trace,
      SemiprimeRationalBits.Fits q (selectorWidth n bits) := by
  intro q hq
  exact bounded_fits (residual_trace_bounds C ids bits hC j v q hq) (by unfold selectorWidth; omega)

/-- Actual normalization operands and division outputs require no fit advice. -/
theorem normalize_trace_fits {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v|≤(2^bits : ℕ)) (j : Fin m) (p v : Fin n) :
    ∀ q∈(normalizeExpr (residualRun (run C ids) (originalRow C j)).row p v).trace,
      SemiprimeRationalBits.Fits q (selectorWidth n bits) := by
  intro q hq
  exact bounded_fits (normalize_trace_bounds C ids bits hC j p v q hq) (by unfold selectorWidth; omega)

/-- Back multiplication/subtraction operands and outputs likewise fit. -/
theorem update_trace_fits {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v|≤(2^bits : ℕ)) (j : Fin m) (p c v : Fin n) :
    ∀ q∈(updateExpr (run C ids) p
      (normalizeRun (residualRun (run C ids) (originalRow C j)).row p).row c v).trace,
      SemiprimeRationalBits.Fits q (selectorWidth n bits) := by
  intro q hq
  exact bounded_fits (update_trace_bounds C ids bits hC j p c v q hq) (by unfold selectorWidth; omega)

/-- Physical normalization really inverts the supplied denominator words and
multiplies the supplied numerator words; clocks come from both bit routines. -/
def normalizeWords (a b : SemiprimeRationalBits.RationalWord) (template : List Bool) :
    SemiprimeRationalBits.RationalReport :=
  let inverse := SemiprimeRationalBits.executeOperation .inv b SemiprimeRationalBits.zeroWord template
  let result := SemiprimeRationalBits.executeOperation .mul a inverse.word template
  ⟨result.word,inverse.clock+result.clock+2⟩

/-- Actual cached residual word inputs refine the literal normalization step;
all output and reciprocal fits are DERIVED from the run-state bounds. The clock
is the sum of the executed physical instructions, not a clock annotation. -/
theorem normalizeWords_correct_cost {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v|≤(2^bits : ℕ)) (j : Fin m) (p v : Fin n)
    (a b : SemiprimeRationalBits.RationalWord) (template : List Bool)
    (ht : template.length=selectorWidth n bits)
    (ha : a.Valid) (hb : b.Valid)
    (haw : SemiprimeRationalBits.Width a template.length)
    (hbw : SemiprimeRationalBits.Width b template.length)
    (hav : a.value=(residualRun (run C ids) (originalRow C j)).row v)
    (hbv : b.value=(residualRun (run C ids) (originalRow C j)).row p) :
    (normalizeWords a b template).word.value=
      (normalizeRun (residualRun (run C ids) (originalRow C j)).row p).row v ∧
    (normalizeWords a b template).word.Valid ∧
    SemiprimeRationalBits.Width (normalizeWords a b template).word template.length ∧
    (normalizeWords a b template).clock≤40002*(template.length+1)^3 := by
  let W := template.length
  have hW : 1≤W := by dsimp [W]; rw [ht]; unfold selectorWidth; omega
  have hzv : SemiprimeRationalBits.zeroWord.Valid := by
    change 0<1
    decide
  have hzw : SemiprimeRationalBits.Width SemiprimeRationalBits.zeroWord W := by
    change 0≤W ∧ 1≤W
    exact ⟨Nat.zero_le _,hW⟩
  have hbb : Bounded b.value (2^residualBits n bits) := by
    rw [hbv,← residualExpr_value]
    exact residual_trace_bounds C ids bits hC j p _ (Expr.eval_mem_trace _)
  have hif : SemiprimeRationalBits.Fits b.value⁻¹ W :=
    bounded_fits (bounded_inv hbb) (by dsimp [W]; rw [ht]; unfold selectorWidth; omega)
  have hi := SemiprimeRationalBits.executeOperation_correct .inv b SemiprimeRationalBits.zeroWord template hb hzv hif
  have hic := SemiprimeRationalBits.executeOperation_cost .inv b SemiprimeRationalBits.zeroWord template hbw hzw le_rfl
  have hqf : SemiprimeRationalBits.Fits
      (a.value*(SemiprimeRationalBits.executeOperation .inv b SemiprimeRationalBits.zeroWord template).word.value) W := by
    rw [hi.1,hav,hbv]
    change SemiprimeRationalBits.Fits
      ((residualRun (run C ids) (originalRow C j)).row v/
        (residualRun (run C ids) (originalRow C j)).row p) W
    rw [← normalizeRun_value]
    have h := normalize_trace_fits C ids bits hC j p v _ (Expr.eval_mem_trace _)
    rw [normalizeExpr_value] at h
    simpa only [W,ht] using h
  have hm := SemiprimeRationalBits.executeOperation_correct .mul a
    (SemiprimeRationalBits.executeOperation .inv b SemiprimeRationalBits.zeroWord template).word template ha hi.2.1 hqf
  have hmc := SemiprimeRationalBits.executeOperation_cost .mul a
    (SemiprimeRationalBits.executeOperation .inv b SemiprimeRationalBits.zeroWord template).word template haw hi.2.2 le_rfl
  refine ⟨?_,hm.2.1,hm.2.2,?_⟩
  · simpa only [normalizeWords,SemiprimeRationalBits.Operation.value,hi.1,hav,hbv,
      normalizeRun_value,div_eq_mul_inv] using hm.1
  · dsimp only [normalizeWords]
    have hp : 1≤(template.length+1)^3 := Nat.one_le_pow _ _ (by omega)
    have hs := Nat.add_le_add_right (Nat.add_le_add hic hmc) 2
    apply hs.trans
    omega

end RiemannGaussian.SemiprimeMaterializedSelectionTemporaries
