/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Literal binary upper carries at a moving dyadic scale

The original central-binomial carries above `H=2^k` transport exactly to
the quotient `n/H`. Their binary digit parity is a block Thue--Morse code.
All integer heads and every finite prefix are retained. These finite
identities and prefix bounds provide no actual-prime estimate or source.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option warningAsError true
noncomputable section
open scoped BigOperators
namespace OpenAIReview.DigitalCarry

/-- The literal central-binomial carry at one denominator. -/
def carry (n d : ℕ) : ℕ := (2*n)/d-2*(n/d)

/-- Sum of the literal base-two digits, with empty digits at zero. -/
def digitSum (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- Binary digit parity as an integer sign. -/
def epsilon (n : ℕ) : ℤ := (-1)^digitSum n

/-- The high-digit sign at the literal moving dyadic quotient. -/
def highCode (k n : ℕ) : ℤ := epsilon (n/2^k)

/-- Every original carry strictly above the dyadic cutoff transports
to the corresponding carry of the quotient, including zero quotients. -/
theorem carry_upper_transport (n k j : ℕ) (hj : 0<j) :
    carry n (2^(k+j)) = carry (n/2^k) (2^j) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  unfold carry
  rw [pow_add, pow_succ']
  have hcancel : 2*n/(2^k*(2*2^j)) = n/(2^k*2^j) := by
    rw [show 2^k*(2*2^j)=2*(2^k*2^j) by ring]
    exact Nat.mul_div_mul_left n _ (by norm_num)
  rw [hcancel, Nat.mul_div_mul_left _ _ (by norm_num : 0<2)]
  simp only [Nat.div_div_eq_div_mul]

/-- Doubling appends a zero binary digit; the zero head is explicit. -/
theorem digitSum_double (n : ℕ) : digitSum (2*n)=digitSum n := by
  by_cases hn : n=0
  · simp [hn,digitSum]
  · simp [digitSum, Nat.digits_base_mul (by norm_num : 1<2) (Nat.pos_of_ne_zero hn)]

/-- An odd input appends a one binary digit. -/
theorem digitSum_double_add_one (n : ℕ) : digitSum (2*n+1)=digitSum n+1 := by
  rw [show 2*n+1=1+2*n by omega]
  unfold digitSum
  rw [Nat.digits_add 2 (by norm_num) 1 n (by norm_num)
    (Or.inl (by norm_num : (1 : ℕ)≠0))]
  simp [Nat.add_comm]

/-- Kummer's exact valuation specializes to the sum of binary digits. -/
theorem central_padicValNat (n : ℕ) :
    padicValNat 2 ((2*n).choose n)=digitSum n := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_one_mul_padicValNat_choose_eq_sub_sum_digits'
    (p := 2) (n := n) (k := n)
  change (2-1)*padicValNat 2 ((n+n).choose n)=
    digitSum n+digitSum n-digitSum (n+n) at h
  simp only [Nat.reduceSub, one_mul, ← two_mul, digitSum_double] at h
  omega

/-- The same equality uses the actual prime factorization of the integer
central binomial coefficient, not an abstract carry surrogate. -/
theorem central_factorization (n : ℕ) :
    ((2*n).choose n).factorization 2=digitSum n := by
  rw [Nat.factorization_def _ Nat.prime_two, central_padicValNat]

/-- A literal central carry is its exact threshold indicator. -/
theorem carry_eq_indicator (n d : ℕ) (hd : 0<d) :
    carry n d=if d≤n%d+n%d then 1 else 0 := by
  unfold carry
  rw [two_mul,Nat.add_div hd]
  split_ifs <;> omega

/-- Full finite Kummer carry sum on the actual central binomial integer. -/
theorem central_factorization_eq_carry_sum (n B : ℕ)
    (hB : Nat.log 2 (2*n)<B) :
    ((2*n).choose n).factorization 2=
      ∑ j∈Finset.Ico 1 B,carry n (2^j) := by
  have hc:=Nat.factorization_choose' (p := 2) (n := n) (k := n) (b := B)
    Nat.prime_two (by simpa only [← two_mul] using hB)
  rw [show 2*n=n+n by omega,hc]
  simp only [carry_eq_indicator n _ (Nat.two_pow_pos _),Finset.sum_boole]
  simp

/-- Every retained high digit comes from an original literal carry layer;
the finite window endpoint is required to cover the quotient. -/
theorem upper_carry_window_eq_digitSum (n k B : ℕ)
    (hB : Nat.log 2 (2*(n/2^k))<B) :
    (∑ j∈Finset.Ico 1 B,carry n (2^(k+j)))=digitSum (n/2^k) := by
  calc
    _ = ∑ j∈Finset.Ico 1 B,carry (n/2^k) (2^j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact carry_upper_transport n k j (Finset.mem_Ico.mp hj).1
    _ = ((2*(n/2^k)).choose (n/2^k)).factorization 2 :=
      (central_factorization_eq_carry_sum _ _ hB).symm
    _ = _ := central_factorization _

/-- The high code is exactly parity of the original retained carry window. -/
theorem highCode_eq_upper_carry_sign (n k B : ℕ)
    (hB : Nat.log 2 (2*(n/2^k))<B) :
    highCode k n=(-1 : ℤ)^(∑ j∈Finset.Ico 1 B,carry n (2^(k+j))) := by
  rw [upper_carry_window_eq_digitSum n k B hB]
  rfl

/-- The zero central binomial has positive sign. -/
@[simp] theorem epsilon_zero : epsilon 0=1 := by simp [epsilon,digitSum]

/-- Doubling preserves the literal central-binomial parity sign. -/
@[simp] theorem epsilon_double (n : ℕ) : epsilon (2*n)=epsilon n := by
  simp only [epsilon,digitSum_double]

/-- An odd successor negates that same parity sign. -/
@[simp] theorem epsilon_double_add_one (n : ℕ) : epsilon (2*n+1)= -epsilon n := by
  simp only [epsilon,digitSum_double_add_one,pow_succ]
  ring

/-- The first nonzero central-binomial parity sign is negative. -/
@[simp] theorem epsilon_one : epsilon 1= -1 := by
  simpa using epsilon_double_add_one 0

/-- The full first block, including the zero head, has positive sign. -/
theorem highCode_first_block {k n : ℕ} (hn : n<2^k) : highCode k n=1 := by
  simp only [highCode,Nat.div_eq_of_lt hn,epsilon_zero]

/-- The next block begins with the literal negative sign. -/
@[simp] theorem highCode_at_cutoff (k : ℕ) : highCode k (2^k)= -1 := by
  simp [highCode]

/-- Every sign has absolute value one. -/
@[simp] theorem abs_epsilon (n : ℕ) : |epsilon n|=1 := by
  simp [epsilon,abs_pow]

/-- Exact adjacent-pair cancellation before any estimate. -/
theorem epsilon_pair (n : ℕ) : epsilon (2*n)+epsilon (2*n+1)=0 := by simp

/-- The phase is exactly the parity of the integer's prime factorization. -/
theorem epsilon_eq_central_factorization (n : ℕ) :
    epsilon n=(-1 : ℤ)^(((2*n).choose n).factorization 2) := by
  rw [central_factorization]
  rfl

/-- Every complete adjacent pair prefix cancels exactly. -/
theorem sum_epsilon_even (q : ℕ) : ∑ n∈Finset.range (2*q),epsilon n=0 := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show 2*(q+1)=2*q+2 by omega,Finset.sum_range_add]
      simp [Finset.sum_range_succ,ih]

/-- A partial literal block has constant quotient, without dropping its head. -/
theorem sum_partial_block (H q r : ℕ) (hH : 0<H) (hr : r≤H) :
    ∑ n∈Finset.range r,epsilon ((H*q+n)/H)=(r : ℤ)*epsilon q := by
  have he : ∀ n∈Finset.range r,(H*q+n)/H=q := by
    intro n hn
    have hnH : n<H := (Finset.mem_range.mp hn).trans_le hr
    rw [Nat.add_comm,Nat.add_mul_div_left _ _ hH,Nat.div_eq_of_lt hnH,zero_add]
  calc
    _ = ∑ n∈Finset.range r,epsilon q :=
      Finset.sum_congr rfl (fun n hn => by rw [he n hn])
    _ = _ := by simp

/-- All complete quotient blocks are retained with their exact multiplicity. -/
theorem sum_complete_blocks (H q : ℕ) (hH : 0<H) :
    ∑ n∈Finset.range (H*q),epsilon (n/H)=(H : ℤ)*∑ n∈Finset.range q,epsilon n := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show H*(q+1)=H*q+H by ring,Finset.sum_range_add,ih,
        sum_partial_block H q H hH le_rfl,Finset.sum_range_succ]
      ring

/-- Exact quotient/remainder prefix formula, including the boundary block. -/
theorem sum_block_prefix (H q r : ℕ) (hH : 0<H) (hr : r≤H) :
    ∑ n∈Finset.range (H*q+r),epsilon (n/H)=
      (H : ℤ)*(∑ n∈Finset.range q,epsilon n)+(r : ℤ)*epsilon q := by
  rw [Finset.sum_range_add,sum_complete_blocks H q hH,sum_partial_block H q r hH hr]

/-- Uniform exact partial-block bound, including odd quotient boundaries. -/
theorem abs_sum_block_prefix (H q r : ℕ) (hH : 0<H) (hr : r≤H) :
    |∑ n∈Finset.range (H*q+r),epsilon (n/H)|≤(H : ℤ) := by
  rw [sum_block_prefix H q r hH hr]
  let u:=q/2
  have hq : q=2*u ∨ q=2*u+1 := by
    have hm:=Nat.mod_add_div q 2
    have hb:=Nat.mod_lt q (by norm_num : 0<2)
    dsimp [u]
    omega
  rcases hq with hq | hq
  · rw [hq,sum_epsilon_even,epsilon_double]
    simp only [mul_zero,zero_add,abs_mul,abs_epsilon,mul_one]
    rw [abs_of_nonneg (Nat.cast_nonneg r)]
    exact_mod_cast hr
  · rw [hq,Finset.sum_range_succ,sum_epsilon_even]
    simp only [epsilon_double,epsilon_double_add_one,zero_add]
    rw [show (H : ℤ)*epsilon u+(r : ℤ)* -epsilon u=
        ((H : ℤ)-r)*epsilon u by ring,abs_mul,abs_epsilon,mul_one]
    have hrZ : (r : ℤ)≤H := by exact_mod_cast hr
    rw [abs_of_nonneg (sub_nonneg.mpr hrZ)]
    omega

/-- A block code has prefix discrepancy at most its block length, uniformly
in both the length and the physical cutoff. -/
theorem abs_sum_quotient_prefix_le (H N : ℕ) (hH : 0<H) :
    |∑ n∈Finset.range N,epsilon (n/H)|≤(H : ℤ) := by
  have hN : N=H*(N/H)+N%H := by have he:=Nat.mod_add_div N H; omega
  calc
    _ = |∑ n∈Finset.range (H*(N/H)+N%H),epsilon (n/H)| := by rw [← hN]
    _ ≤ _ := abs_sum_block_prefix H (N/H) (N%H) hH (Nat.mod_lt N hH).le

/-- The moving dyadic code has the exact uniform bound needed by the
growing-scale source audit. No prime weights occur in this statement. -/
theorem abs_sum_highCode_prefix_le (k N : ℕ) :
    |∑ n∈Finset.range N,highCode k n|≤(2^k : ℕ) :=
  abs_sum_quotient_prefix_le (2^k) N (Nat.two_pow_pos k)

/-- The two adjacent moving dyadic blocks cancel before any norm. -/
theorem highCode_adjacent_blocks (k q : ℕ) :
    ∑ n∈Finset.range (2*(2^k)),highCode k (2^k*(2*q)+n)=0 := by
  rw [show 2*(2^k)=2^k+2^k by omega,Finset.sum_range_add]
  unfold highCode
  rw [sum_partial_block _ _ _ (Nat.two_pow_pos k) le_rfl]
  have hs : (∑ n∈Finset.range (2^k),epsilon ((2^k*(2*q)+(2^k+n))/2^k))=
      (2^k : ℕ)*epsilon (2*q+1) := by
    rw [show (fun n => epsilon ((2^k*(2*q)+(2^k+n))/2^k))=
        (fun n => epsilon ((2^k*(2*q+1)+n)/2^k)) by funext n; congr 2; ring]
    exact sum_partial_block _ _ _ (Nat.two_pow_pos k) le_rfl
  rw [hs]
  simp

end OpenAIReview.DigitalCarry

#lint+ in OpenAIReview.DigitalCarry

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty digital-carry audit."
  logInfo m!"Digital-carry audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-digital-carry-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-digital-carry-gate/axioms.json"
    (Json.mkObj [("scope",toJson "literal moving dyadic central carries and binary parity; no prime/source estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
