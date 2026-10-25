# Family103: quantitative derandomization bridge and sixth-rate scope

Research date: 2026-10-22. Scratch analysis only; no repository mutation or build. The entire 108-page primary manuscript was accessible and read at the relevant interfaces. This is an applicability analysis conditional on the correctness of that manuscript, not independent certification of its extraordinary theorem or its Lean implementation.

Primary manuscript: [Exact Derandomization of Logarithmic Space: L = RL = BPL](https://github.com/openai/math/blob/main/preprints/Exact-Derandomization-of-Logarithmic-Space-L-equals-RL-equals-BPL-September-23-2026/paper.pdf). Downloaded PDF SHA256 `15030fab23d31a4d91bd944100a547c3e9eff6da8330a4fb94ea999f071fadfc`. Printed and PDF page numbers agree. No direct quotations are used below.

## Result

The paper gives more than the class-equality theorem inspected in the previous audit: a source-specific effective compiler with explicit, very loose time exponents (Theorem 13.1, pp.98–105), and a fixed universal capped interpreter from which a general `poly(T,2^S,n)` simulation can be derived. Neither gives an exponent-preserving simulation. For an ordinary factoring algorithm storing even one full-size residue, its workspace is already proportional to `log N`; the available universal constants then do not certify `N^(1/6)`. The real quantitative obstruction is the exponent multiplying workspace, rather than the fact that the original running time is superpolynomial in binary input length.

A positive conditional target is precise: a fixed randomized factoring witness procedure with `log T=o(log N)` **and** total live workspace `S=o(log N)` could be derandomized to `N^o(1)` using the manuscript. No such factoring procedure is supplied or established here. Merely having polynomial space in the input bitlength is insufficient.

## Primary interface inventory

Theorem 1.2 (p.2; proof pp.96–97) approximates a fixed source's acceptance probability to `2^-q` in space `O(log(n+2)+q)` and time `(n+2)^O(1)2^O(q)`, with machine-dependent constants. Lemma 13.2 (pp.100–101) fixes one interpreter whose length-m input caps source time at m and each work coordinate at `floor(ceil(log₂(m+2))/(100(d+1)^3))`, where d is encoded program length. Section 13.2 fixes a total deterministic separator A for that interpreter. Section 13.3 (p.102) pads a source bounded by `(n+2)^a` time and `b ceil(log₂(n+2))` work bits, using `P=1000(d+2)^4(a+b+2)` and virtual length `2^(P ceil(log₂(n+2)))`. Section 13.5 (pp.104–105) returns the finite-syntax bounds displayed below. Corollary 12.4 (pp.97–98) supplies certified accepting runs by greedy continuation-value estimation.

## 1. Exact effective-compiler exponent

Use distinct names to avoid confusing the paper's compiler bookkeeping variable S with the source workspace. Let:

- `d>=1` be the source program's encoded length;
- `t` be the generated deterministic machine's number of work tapes;
- `g>=2` bound its work alphabet sizes;
- `q_D` count its finite control states;
- `u>=1` dominate its transition-table bitlength, alphabet sizes, states and tape count.

The compiler supplies

```
P = 1000(d+2)^4(a+b+2)
rho = 100(P+2)
Sigma = 1 + (t+1)(2 rho+1)(g+2)
K = 4 Sigma
c = 2 Sigma+1
H = 2^((u+100)^2) (q_D+1)
space <= K log₂(n+2)
time_bit <= H (n+2)^c.
```

These are computable once a concrete valid finite library A is fixed. The PDF establishes existence of that fixed finite transition list; it does not print or instantiate its table, t, g, u or the resulting integer exponent for a factoring source. In particular one cannot read a usable small numerical overhead out of Theorem 1.2's big-O notation.

The generated program has four auxiliary counter tapes (p.103), so `t>=4`. Even with d, t and g at their smallest possible values, its *certified exponent* obeys

```
Sigma >= 1+20(200(P+2)+1) = 4000P+8021
c >= 8000P+16043
  >= 648000000(a+b+2)+16043.
```

This lower bound describes the magnitude of this deliberately loose reported **upper-bound exponent**. It is not a runtime lower bound and does not exclude a faster implementation or analysis.

## 2. Why external padding cannot improve that certificate

Write `ell=log₂ N`. Suppose a fixed randomized procedure on N has time `T` and workspace `S_alg`. Put it on a virtual input of length `m=N^delta`, allowing the input symbols to be regenerated from N. A polynomial-time/logspace hypothesis then requires, up to ceilings and fixed additive constants,

```
a >= log₂T/(delta ell)
b >= S_alg/(delta ell).
```

The compiler certifies time `H(m+2)^c=N^(delta c+o(1))`. If `S_alg>=sigma ell`, its printed formulas imply

```
delta c >= 648000000 delta b >= 648000000 sigma.
```

Taking a longer pad makes b smaller but multiplies the output exponent by delta; taking a shorter pad increases b. Neither maneuver makes this certificate approach 1/6. Similarly its dependence on a fails to preserve any source time exponent. Constants H and the actual machine syntax can only make the concrete threshold harder to certify.

This is a quantitative strengthening of the old audit, not a refutation of the paper: its objective is polynomial time in the enlarged input, rather than preserving a number-theoretic exponent.

Letting delta, a or b vary with N while invoking a separately compiled theorem at each N is not automatically one uniform factoring algorithm. It would require uniform access to those generated programs, and their compilation and syntax sizes must be charged. The fixed-interpreter construction below is the legitimate way to discuss variable budgets.

## 3. A stronger useful bridge derived from the fixed interpreter

Fix a source program z of length d. Let n denote its actual input length. Suppose we know worst-case budgets T>=1 and S_alg for the particular input length, and can compute their encodings within the claimed resources. Count all work cells, counters, arithmetic registers and suspended calls. Put

```
D = 100(d+1)^3
L_pre = (d+1)(n+2)
Lambda = max(ceil(log₂(T+1)),
             D(S_alg+2),
             ceil(log₂(L_pre+1)), d, 2)
m = 2^Lambda.
```

Supply the interpreter the prefix `1^d 0 z 1^n 0 E_d(x)` followed virtually by zeros. Its encoded program eligibility test passes. Its coordinate cap is at least `S_alg+2`, so local work-tape motion cannot leave the permitted strips: reaching a coordinate requires traversing the intervening counted cells. Its time cap m exceeds T, and its input contains the entire prefix. Thus it has exactly the source acceptance probability.

The fixed separator A from section 13.2 now acts on a virtual length-m input; symbol regeneration costs polynomial time in n+Lambda and requires O(n-independent counters plus Lambda) bits. No physical pad is written.

There is a slightly sharper way to expose the library constant than applying the coarse compiler formulas. Let t_A, g_A, q_A be the fixed separator's number of work tapes, maximum alphabet size and control-state count in its blocked convention (13.4). For `m=2^Lambda`, `lambda_m=Lambda+1`, and its work heads lie in `[-Lambda-2,Lambda+2]`. Its number of complete configurations is at most

```
q_A (m+2) (2Lambda+5)^t_A g_A^(t_A(2Lambda+5)).
```

Totality means that it never repeats a complete configuration. Finite-symbol bit simulation adds a fixed factor; regenerating each virtual symbol adds `poly(n,Lambda)`. Consequently, with

```
kappa = 1+2t_A log₂ g_A,
```

we obtain the derived upper bound

```
time <= poly(n,Lambda) 2^(kappa Lambda+O(log Lambda))
space = O(Lambda)
      = O(S_alg+log T+log n),
```

where all hidden constants depend only on the fixed source and fixed library. Equivalently this is `poly(n,T,2^S_alg)`. The term `log T` is not multiplied by the source workspace. This is a real quantitative improvement over stating only L=BPL, but kappa is not numerically instantiated in the manuscript. Even the displayed kappa is >=3 when A has at least one binary work tape.

For a decision procedure satisfying

```
log₂T <= tau ell + o(ell)
S_alg <= sigma ell + o(ell),
```

the derived certificate is

```
time <= N^(kappa max(tau,D sigma)+o(1)).
```

Thus a sufficient strict condition for an eventual sixth-rate bound is

```
kappa max(tau,D sigma) < 1/6.
```

The coefficient D is already at least 800 in this particular universal wrapper. A source-specific capped wrapper might reduce this artificial interpreter constant, but would replace it with other source-dependent separator constants that the manuscript does not instantiate. For tau=o(1) and a full ell-bit work register (sigma>=1), this generic simulation certificate is far above the target. This again is a limitation of the available certified construction, not a theorem that all deterministic simulations are slow.

The robust asymptotic useful regime avoids needing numerical kappa: if `S_alg=o(ell)` and `log T=o(ell)`, then `Lambda=o(ell)`, so the derived time is `N^o(1)` and hence at most `N^(1/6)` for all sufficiently large N. The finite range can in principle be handled by any exact fallback after a concrete threshold is obtained. Without instantiated library constants there is no practical or explicit numerical crossover threshold.

## 4. Search and worst-case time are additional, payable requirements

An expected-time Las Vegas factor routine can be truncated at a fixed multiple of its proved expectation. Markov's inequality yields constant success probability and a worst-case clock on every tape; charge its clock counter in S_alg. A correctness-checking source must accept only after emitting a valid nontrivial factor. Expected time alone cannot be fed into the theorem unchanged.

A factor routine's output bits need not individually have a bounded-error gap: several valid factors can have different bits. Therefore independently derandomizing each output bit is invalid in general. Corollary 12.4's accepting-run method supplies the right construction. If initial accepting probability is gamma>=2/3, choose each coin transition using deterministic estimates of successor continuation probabilities to error at most `gamma/(8T)`. Each chosen step decreases continuation probability by at most twice that error, so after T steps its terminal value is positive and hence it is an accepting run. Repeat the choices to emit the verified witness.

The needed precision is `q=O(log T)`, rather than the bitlength ell of a whole putative factor. A universal continuation interpreter and Theorem 1.2 therefore keep the bound `2^O(S_alg+log T+log n)` and add at most a polynomial factor in T. Its workspace includes current and candidate source configurations, remaining-time counters, approximation scratch and virtual addresses. This does not change the useful `S_alg,log T=o(ell)` implication, but it does not fix existing full-precision arithmetic storage.

For balanced semiprimes, an alternative canonical normalization of a returned factor is `min(d,N/d)`. Successful runs then agree on the smaller prime, so constant-success amplification can produce bounded-error bit decisions. That normalization, amplification and output verification must also be paid in the chosen machine model.

## 5. Succinctness and restricted machines

The paper already uses an implicitly presented time-layered configuration graph (Lemma 2.1, p.7). An address records the source work contents as well as time, heads and state. Its length is `O(S_alg+log T+log n)`. Supplying local successor/predecessor ports succinctly avoids writing the exponentially many vertices; it does not remove S_alg from each configuration address or from the deterministic separator's exponent. Replacing that graph by a polynomial-size circuit does not license invoking a theorem for a smaller graph. A new quotient would need to preserve acceptance probabilities, support local port computations and reduce the live configuration information; none is supplied here.

A restricted source could help in either of two demonstrable ways: a genuinely sublinear-in-ell workspace witness routine, or a new structure-specific deterministic probability evaluator with quantified sufficiently small constants. Restricting the source to constant degree, fresh coins or layered transitions does not itself help, because those properties are already built into the construction. A zero-space local query oracle is not free: work and time of its evaluation must be charged, and an oracle containing factoring information would be circular.

## Verification scope and prior audit

Read current AGENTS tail and archived `logspace-scope.md`, `Equality.lean`, and `Deterministic.lean`. The archived formal theorem exports membership in L, with no clock relation; its configuration-count lemma contains exponent `h+w+2cw`. No Lean build or proof dependency audit was performed. The manuscript's effective quantitative section is additional primary evidence, and does not invalidate the old claim that the **formal theorem interface** alone supplies no sixth-rate factoring algorithm.

This note proves a conditional resource bridge and a precise failure of two padding certificates. It does not prove that every possible reduction fails, does not establish a lower bound for integer factoring, and does not claim a new factoring algorithm or exponent.
