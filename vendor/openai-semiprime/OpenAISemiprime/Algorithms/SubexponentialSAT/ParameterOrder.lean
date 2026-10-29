import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Effective selection of fixed parameters

The searches below take supplied Boolean tests. `select` uses the executable
least-number search `Nat.find`; the existence proof is used only to prove
termination. Executability is relative to the supplied test until its own
computability has been established. The bounded scan gives a separate finite
execution and counts calls to the test, not bit operations or Turing-machine
transitions.

The power-threshold application discharges its existence hypothesis explicitly.
The manuscript's binomial-tail and sparsification tests require their own
mathematical eventual-validity theorems before using the generic interface.
-/

namespace SubexponentialSAT.ParameterOrder

/-- A finite scan of the interval `[start, start + fuel)`, recording test calls. -/
def scanFrom (test : ℕ → Bool) (start : ℕ) : ℕ → Option ℕ × ℕ
  | 0 => (none, 0)
  | fuel + 1 =>
      if test start then (some start, 1)
      else
        let rest := scanFrom test (start + 1) fuel
        (rest.1, rest.2 + 1)

theorem scanFrom_calls_le (test : ℕ → Bool) (start fuel : ℕ) :
    (scanFrom test start fuel).2 ≤ fuel := by
  induction fuel generalizing start with
  | zero => simp [scanFrom]
  | succ fuel ih =>
      cases ht : test start <;> simp [scanFrom, ht]
      exact ih (start + 1)

theorem scanFrom_sound (test : ℕ → Bool) {start fuel result : ℕ}
    (h : (scanFrom test start fuel).1 = some result) :
    test result = true ∧ start ≤ result ∧ result < start + fuel := by
  induction fuel generalizing start with
  | zero => simp [scanFrom] at h
  | succ fuel ih =>
      cases ht : test start with
      | false =>
          have hr : (scanFrom test (start + 1) fuel).1 = some result := by
            simpa [scanFrom, ht] using h
          obtain ⟨htrue, hstart, hend⟩ := ih hr
          exact ⟨htrue, by omega, by omega⟩
      | true =>
          have heq : start = result := by simpa [scanFrom, ht] using h
          subst result
          exact ⟨ht, le_rfl, by omega⟩

theorem scanFrom_complete (test : ℕ → Bool) {start fuel witness : ℕ}
    (hstart : start ≤ witness) (hend : witness < start + fuel)
    (htrue : test witness = true) :
    ∃ result, (scanFrom test start fuel).1 = some result := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
      cases ht : test start with
      | false =>
          have hne : start ≠ witness := by
            intro heq
            subst witness
            simp [ht] at htrue
          obtain ⟨result, hr⟩ := ih (start := start + 1) (by omega) (by omega)
          exact ⟨result, by simpa [scanFrom, ht] using hr⟩
      | true => exact ⟨start, by simp [scanFrom, ht]⟩

/-- No smaller number in the scanned interval passes the test. -/
theorem scanFrom_min (test : ℕ → Bool) {start fuel result : ℕ}
    (h : (scanFrom test start fuel).1 = some result) :
    ∀ m, start ≤ m → m < result → test m = false := by
  induction fuel generalizing start with
  | zero => simp [scanFrom] at h
  | succ fuel ih =>
      cases ht : test start with
      | false =>
          have hr : (scanFrom test (start + 1) fuel).1 = some result := by
            simpa [scanFrom, ht] using h
          intro m hstart hm
          by_cases heq : m = start
          · simpa [heq] using ht
          · exact ih hr m (by omega) hm
      | true =>
          have heq : start = result := by simpa [scanFrom, ht] using h
          intro m hstart hm
          omega

/-- A successful scan checks each integer through its returned witness once. -/
theorem scanFrom_calls_eq (test : ℕ → Bool) {start fuel result : ℕ}
    (h : (scanFrom test start fuel).1 = some result) :
    (scanFrom test start fuel).2 = result - start + 1 := by
  induction fuel generalizing start with
  | zero => simp [scanFrom] at h
  | succ fuel ih =>
      cases ht : test start with
      | false =>
          have hr : (scanFrom test (start + 1) fuel).1 = some result := by
            simpa [scanFrom, ht] using h
          have hc := ih hr
          have hs := (scanFrom_sound test hr).2.1
          simp only [scanFrom, ht, Bool.false_eq_true, ↓reduceIte, hc]
          omega
      | true =>
          have heq : start = result := by simpa [scanFrom, ht] using h
          subst result
          simp [scanFrom, ht]

/-- Executable least-number search. Only the Boolean test is inspected at run time. -/
def select (test : ℕ → Bool) (exists_good : ∃ m, test m = true) : ℕ :=
  Nat.find exists_good

theorem select_spec (test : ℕ → Bool) (h : ∃ m, test m = true) :
    test (select test h) = true :=
  Nat.find_spec h

theorem select_le (test : ℕ → Bool) (h : ∃ m, test m = true) {m : ℕ}
    (hm : test m = true) : select test h ≤ m :=
  Nat.find_min' h hm

theorem select_min (test : ℕ → Bool) (h : ∃ m, test m = true) {m : ℕ}
    (hm : m < select test h) : test m = false := by
  have hn : test m ≠ true := Nat.find_min h hm
  cases ht : test m <;> simp_all

/-- The total search is witnessed by a bounded scan with at most `select + 1`
Boolean predicate evaluations. This is not a bit-complexity assertion. -/
theorem select_finite_execution (test : ℕ → Bool) (h : ∃ m, test m = true) :
    (scanFrom test 0 (select test h + 1)).1 = some (select test h) ∧
      (scanFrom test 0 (select test h + 1)).2 ≤ select test h + 1 := by
  obtain ⟨result, hr⟩ := scanFrom_complete test (start := 0)
    (fuel := select test h + 1) (witness := select test h)
    (Nat.zero_le _) (by omega) (select_spec test h)
  obtain ⟨htrue, _, hend⟩ := scanFrom_sound test hr
  have heq : result = select test h := by
    have hleast := select_le test h htrue
    omega
  subst result
  exact ⟨hr, scanFrom_calls_le test 0 (select test h + 1)⟩

/-- Any successful upper bound permits an entirely bounded implementation of
the same least-number search; the exact number of predicate calls is recorded. -/
theorem select_bounded_execution (test : ℕ → Bool) (h : ∃ m, test m = true)
    {N : ℕ} (hN : test N = true) :
    scanFrom test 0 (N + 1) = (some (select test h), select test h + 1) := by
  obtain ⟨result, hr⟩ := scanFrom_complete test (start := 0)
    (fuel := N + 1) (witness := N) (Nat.zero_le _) (by omega) hN
  have htrue := (scanFrom_sound test hr).1
  have hleft := select_le test h htrue
  have hright : result ≤ select test h := by
    by_contra hn
    have hfalse := scanFrom_min test hr (select test h) (Nat.zero_le _) (by omega)
    rw [select_spec test h] at hfalse
    contradiction
  have heq : result = select test h := Nat.le_antisymm hright hleft
  subst result
  apply Prod.ext hr
  simpa using scanFrom_calls_eq test hr

/-- An eventual bound supplies termination without extracting that bound as data. -/
theorem exists_good_of_eventual (test : ℕ → Bool)
    (h : ∃ N, ∀ m ≥ N, test m = true) : ∃ m, test m = true := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, hN N le_rfl⟩

/-- Search using an eventual-validity proof. No classical choice is used. -/
def selectEventually (test : ℕ → Bool)
    (h : ∃ N, ∀ m ≥ N, test m = true) : ℕ :=
  select test (exists_good_of_eventual test h)

theorem selectEventually_spec (test : ℕ → Bool)
    (h : ∃ N, ∀ m ≥ N, test m = true) :
    test (selectEventually test h) = true :=
  select_spec test _

theorem selectEventually_le_bound (test : ℕ → Bool)
    (h : ∃ N, ∀ m ≥ N, test m = true) {N : ℕ}
    (hN : ∀ m ≥ N, test m = true) : selectEventually test h ≤ N :=
  select_le test _ (hN N le_rfl)

/-- Interface for asymptotic proofs stated using the natural-number `atTop` filter. -/
def selectAtTop (test : ℕ → Bool)
    (h : ∀ᶠ m in Filter.atTop, test m = true) : ℕ :=
  selectEventually test (Filter.eventually_atTop.mp h)

theorem selectAtTop_spec (test : ℕ → Bool)
    (h : ∀ᶠ m in Filter.atTop, test m = true) :
    test (selectAtTop test h) = true :=
  selectEventually_spec test _

/-- Tests defining the same admissible set give the same chosen constant,
regardless of the proofs used to certify termination. -/
theorem select_congr (test₁ test₂ : ℕ → Bool)
    (h₁ : ∃ m, test₁ m = true) (h₂ : ∃ m, test₂ m = true)
    (htest : ∀ m, test₁ m = test₂ m) : select test₁ h₁ = select test₂ h₂ := by
  apply Nat.le_antisymm
  · apply select_le test₁ h₁
    rw [htest]
    exact select_spec test₂ h₂
  · apply select_le test₂ h₂
    rw [← htest]
    exact select_spec test₁ h₁

/-- If a test is independent of the input size, its least successful parameter
is independent too, even when the supplied existence proofs were indexed by it. -/
theorem select_input_independent (test : ℕ → ℕ → Bool) (fixedTest : ℕ → Bool)
    (h : ∀ n, ∃ m, test n m = true)
    (hfixed : ∀ n m, test n m = fixedTest m) (n₁ n₂ : ℕ) :
    select (test n₁) (h n₁) = select (test n₂) (h n₂) := by
  apply select_congr
  intro m
  rw [hfixed n₁ m, hfixed n₂ m]

/-- One effective choice for each width. There is deliberately no input-size
argument: only the width indexes the supplied Boolean test. -/
def parameterFamily (test : ℕ → ℕ → Bool)
    (h : ∀ k, ∃ N, ∀ m ≥ N, test k m = true) (k : ℕ) : ℕ :=
  selectEventually (test k) (h k)

theorem parameterFamily_spec (test : ℕ → ℕ → Bool)
    (h : ∀ k, ∃ N, ∀ m ≥ N, test k m = true) (k : ℕ) :
    test k (parameterFamily test h k) = true :=
  selectEventually_spec (test k) (h k)

/-- Euclid's theorem supplies termination for a direct primality search.
The test itself is decidable natural arithmetic and primality. -/
theorem large_prime_exists (bound : ℕ) :
    ∃ p, decide (bound ≤ p ∧ 3 ≤ p ∧ Nat.Prime p) = true := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max bound 3)
  refine ⟨p, decide_eq_true_eq.mpr ?_⟩
  exact ⟨le_trans (Nat.le_max_left _ _) hp,
    le_trans (Nat.le_max_right _ _) hp, hprime⟩

/-- The least prime at least three and at least the requested bound.
In particular, the manuscript can fix `largePrime (2 ^ 4096)` before reading
any formula. -/
def largePrime (bound : ℕ) : ℕ :=
  select (fun p => decide (bound ≤ p ∧ 3 ≤ p ∧ Nat.Prime p))
    (large_prime_exists bound)

theorem largePrime_spec (bound : ℕ) :
    bound ≤ largePrime bound ∧ 3 ≤ largePrime bound ∧ Nat.Prime (largePrime bound) := by
  exact decide_eq_true_eq.mp
    (select_spec (fun p => decide (bound ≤ p ∧ 3 ≤ p ∧ Nat.Prime p))
      (large_prime_exists bound))

theorem largePrime_one_lt (bound : ℕ) : 1 < largePrime bound := by
  have h := (largePrime_spec bound).2.1
  omega

/-- Fixing a prime above `2 ^ minBits` supplies the manuscript's required
Boolean chunk capacity without any dependence on the input size. -/
theorem largePrime_log_bound (minBits : ℕ) :
    minBits ≤ Nat.log 2 (largePrime (2 ^ minBits)) :=
  Nat.le_log_of_pow_le (by decide) (largePrime_spec (2 ^ minBits)).1

theorem largePrime_power_interval (bound : ℕ) :
    2 ^ Nat.log 2 (largePrime bound) ≤ largePrime bound ∧
      largePrime bound < 2 ^ (Nat.log 2 (largePrime bound) + 1) := by
  constructor
  · apply Nat.pow_log_le_self
    have h := largePrime_one_lt bound
    omega
  · exact Nat.lt_pow_succ_log_self (by decide) _

/-- A concrete eventual bound for the extension-size search. It uses
`m < p^m`, so `target` itself suffices as an exponent bound. -/
theorem power_threshold_eventual (p target : ℕ) (hp : 1 < p) :
    ∃ N, ∀ m ≥ N, decide (target ≤ p ^ m - 1) = true := by
  refine ⟨target, ?_⟩
  intro m hm
  apply decide_eq_true_eq.mpr
  have hpow : m < p ^ m := Nat.lt_pow_self hp
  omega

/-- Find an extension exponent whose number of nonzero field elements meets
an arbitrary prescribed natural-number threshold. -/
def powerExponent (p target : ℕ) (hp : 1 < p) : ℕ :=
  selectEventually (fun m => decide (target ≤ p ^ m - 1))
    (power_threshold_eventual p target hp)

theorem powerExponent_spec (p target : ℕ) (hp : 1 < p) :
    target ≤ p ^ powerExponent p target hp - 1 := by
  exact decide_eq_true_eq.mp
    (selectEventually_spec (fun m => decide (target ≤ p ^ m - 1))
      (power_threshold_eventual p target hp))

theorem powerExponent_le (p target : ℕ) (hp : 1 < p) :
    powerExponent p target hp ≤ target := by
  apply select_le
  apply decide_eq_true_eq.mpr
  have hpow : target < p ^ target := Nat.lt_pow_self hp
  omega

/-- Combining independently proved eventual requirements remains effective;
the maximum of their thresholds proves termination of the combined search. -/
theorem and_eventual (test₁ test₂ : ℕ → Bool)
    (h₁ : ∃ N, ∀ m ≥ N, test₁ m = true)
    (h₂ : ∃ N, ∀ m ≥ N, test₂ m = true) :
    ∃ N, ∀ m ≥ N, (test₁ m && test₂ m) = true := by
  obtain ⟨N₁, hN₁⟩ := h₁
  obtain ⟨N₂, hN₂⟩ := h₂
  refine ⟨max N₁ N₂, ?_⟩
  intro m hm
  simp [hN₁ m (le_trans (Nat.le_max_left _ _) hm),
    hN₂ m (le_trans (Nat.le_max_right _ _) hm)]

/-- A computable family of tests with a proof of pointwise success has a
computable least-witness function. The success proof is not a truth oracle. -/
theorem computable_select {α : Type*} [Primcodable α]
    (test : α → ℕ → Bool) (htest : Computable₂ test)
    (h : ∀ a, ∃ m, test a m = true) :
    Computable (fun a => select (test a) (h a)) := by
  apply (Partrec.rfind htest.partrec₂).of_eq_tot
  intro a
  apply Nat.mem_rfind.mpr
  constructor
  · exact Part.mem_some_iff.mpr (select_spec (test a) (h a)).symm
  · intro m hm
    exact Part.mem_some_iff.mpr (select_min (test a) (h a) hm).symm

/-- Width-indexed fixed parameters are a computable family when their
admissibility test is computable and the eventuality theorem is proved. -/
theorem computable_parameterFamily (test : ℕ → ℕ → Bool)
    (htest : Computable₂ test)
    (h : ∀ k, ∃ N, ∀ m ≥ N, test k m = true) :
    Computable (parameterFamily test h) := by
  exact computable_select test htest
    (fun k => exists_good_of_eventual (test k) (h k))

/-- The natural power-threshold predicate used above is primitive recursive. -/
theorem primrec_power_test (p : ℕ) :
    Primrec₂ (fun target m : ℕ => decide (target ≤ p ^ m - 1)) := by
  have hpow : Primrec₂ (fun a b : ℕ => a ^ b) :=
    Primrec₂.unpaired'.mp Nat.Primrec.pow
  exact (Primrec.nat_le.comp Primrec.fst
    (Primrec.nat_sub.comp
      (hpow.comp (Primrec.const p) Primrec.snd) (Primrec.const 1))).decide

/-- For each fixed base at least two, the least successful extension exponent
is a computable function of the requested size threshold. -/
theorem computable_powerExponent (p : ℕ) (hp : 1 < p) :
    Computable (fun target => powerExponent p target hp) := by
  exact computable_select
    (fun target m => decide (target ≤ p ^ m - 1))
    (primrec_power_test p).to_comp
    (fun target => exists_good_of_eventual _ (power_threshold_eventual p target hp))

/-- Bounded trial division, used to prove primality testing computable. -/
def largestProperDivisor (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m => m ∣ n ∧ m < n) n

theorem prime_iff_largestProperDivisor (n : ℕ) :
    Nat.Prime n ↔ 2 ≤ n ∧ largestProperDivisor n = 1 := by
  constructor
  · intro hp
    refine ⟨hp.two_le, ?_⟩
    apply Nat.findGreatest_eq_iff.mpr
    refine ⟨by have := hp.two_le; omega, ?_, ?_⟩
    · intro _
      exact ⟨one_dvd n, hp.one_lt⟩
    · intro m hm _ hdiv
      have heq : m = 1 := (Nat.prime_def_lt.mp hp).2 m hdiv.2 hdiv.1
      omega
  · rintro ⟨hn, heq⟩
    apply Nat.prime_def_lt.mpr
    refine ⟨hn, ?_⟩
    intro m hmn hdiv
    have hbound : m ≤ largestProperDivisor n :=
      Nat.le_findGreatest (Nat.le_of_lt hmn) ⟨hdiv, hmn⟩
    have hnonzero : m ≠ 0 := by
      intro hz
      subst m
      have hz := zero_dvd_iff.mp hdiv
      omega
    rw [heq] at hbound
    omega

/-- The manuscript's primality test has a primitive-recursive implementation. -/
theorem primrec_prime : PrimrecPred Nat.Prime := by
  have hmod : PrimrecRel (fun n m : ℕ => n % m = 0) :=
    Primrec.eq.comp Primrec.nat_mod (Primrec.const 0)
  have hdvd : PrimrecRel (fun n m : ℕ => m ∣ n) :=
    PrimrecRel.of_eq hmod (fun n m => Nat.dvd_iff_mod_eq_zero.symm)
  have hproper : PrimrecRel (fun n m : ℕ => m ∣ n ∧ m < n) :=
    PrimrecPred.and hdvd (Primrec.nat_lt.comp Primrec.snd Primrec.fst)
  have hlargest : Primrec largestProperDivisor :=
    Primrec.nat_findGreatest Primrec.id hproper
  have hchar : PrimrecPred (fun n => 2 ≤ n ∧ largestProperDivisor n = 1) :=
    (Primrec.nat_le.comp (Primrec.const 2) Primrec.id).and
      (Primrec.eq.comp hlargest (Primrec.const 1))
  exact hchar.of_eq (fun n => (prime_iff_largestProperDivisor n).symm)

theorem primrec_largePrime_test :
    Primrec₂ (fun bound p : ℕ => decide (bound ≤ p ∧ 3 ≤ p ∧ Nat.Prime p)) := by
  exact (PrimrecPred.and Primrec.nat_le
    ((Primrec.nat_le.comp (Primrec.const 3) Primrec.snd).and
      (primrec_prime.comp Primrec.snd))).decide

/-- The prime is selected uniformly from the requested numerical lower bound. -/
theorem computable_largePrime : Computable largePrime := by
  exact computable_select
    (fun bound p => decide (bound ≤ p ∧ 3 ≤ p ∧ Nat.Prime p))
    primrec_largePrime_test.to_comp large_prime_exists

end SubexponentialSAT.ParameterOrder

end OAI.Algorithms
