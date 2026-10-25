# Rigorous randomized factoring and sublinear bitspace

2026-10-22. Binary input N, n=ceil(log2(N+1)). Read the inherited `docs/research-evidence/semiprime-direct-frontier-20261016/repo-delta/logspace-scope.md`; no repeat of the family103 audit. This memo records primary sources, an implementation inference, and the remaining constructive gap.

## Result

No rigorous factoring theorem was located with BOTH bounded T=2^{o(n)} and S=o(n) bit workspace on ordinary read-only binary input. This is a search result, not a space lower bound or proof of nonexistence. There is a good rigorous source with suitable time and plausible O(n) workspace: Lenstra–Pila–Pomerance genus-2 HECM. It does not currently supply sublinear bitspace.

## Primary literature

**Lenstra–Pomerance (1992), A rigorous time bound for factoring integers**, JAMS 5, 483–516. [Primary PDF](https://www.cs.umd.edu/~gasarch/TOPICS/factoring/rigorous.pdf), [DOI](https://doi.org/10.1090/S0894-0347-1992-1137100-0).

The introduction gives complete factorization in expected L_N[1/2,1+o(1)] bit time. More relevant here: the remark on **p.509**, immediately after Theorem10.3, explicitly gives storage at most L_N[1/2,1/2+o(1)] for Algorithm10.1, referring to Wiedemann [34]. This is a subexponential storage upper bound, not O(n). A single quadratic form takes only O(n) bits, but the growing relation system remains. Sparse linear algebra does not imply constant-register workspace. The remark also says changing its smoothness parameter y cannot improve that algorithm's time exponent. Neither observation rules out another streamed algorithm.

Section12, **p.513**, specifies independent fair random bits at unit cost. Thus a computation stopped after T bit operations uses at most T random bits. The expected-time theorem does not itself guarantee a fixed successful deterministic run.

**Lenstra–Pila–Pomerance (1993), A hyperelliptic smoothness test. I**, Philosophical Transactions A345, 397–408. [Author primary PDF](https://math.dartmouth.edu/~carlp/hyperI.pdf), [DOI](https://doi.org/10.1098/rsta.1993.0138).

**Theorem1.1, p.397:** effectively computable constants c0,N0 exist such that every N>=N0 that is not a prime power yields a nontrivial divisor in expected time `L_p[2/3,c0](log N)^2`, where p is the least prime divisor.

**Corollary1.2, same page:** for N>=N0 and v>=3 a bounded-time algorithm uses at most `L_v[2/3,c0](log N)^3` time and obtains all prime factors p<=v with probability at least1/2. Thus a primary bounded-time statement already handles the expected-time issue. Setting v=ceil(sqrt N) covers a factor of every composite N and yields `log2 T=O(n^(2/3)(log n)^(1/3))=o(n)`. Semiprime squares can also be detected separately by integer square root; distinct-prime semiprimes are not prime powers. The effective finite small-N range can be hardcoded.

**p.398** labels the standard ECM exponent1/2 estimate conjectural and gives a separate conjectural exponent1/2 for HECM. The rigorous HECM theorem here has exponent2/3. The size of fixed c0 is irrelevant to logT=o(n), but may matter for practical ranges.

**Lenstra–Pila–Pomerance (2002), A hyperelliptic smoothness test, II**, PLMS84,105–146. [Author primary preprint](https://people.maths.ox.ac.uk/pila/HyperII.pdf), [DOI](https://doi.org/10.1112/plms/84.1.105).

Theorem1.1 gives a uniform prime-by-prime group-order distribution: for prime p>=8100, all but at most p integers z in `[p^2-(1/2)p^(3/2),p^2+(1/2)p^(3/2)]` occur as Jacobian orders of at least `p^(9/2)/(24000(log p)^2(loglog p)^2)` nonsingular quintics over F_p. The introduction explains combination with PartI's short-interval smoothness theorem. This is not an average-case-over-N estimate.

The introduction refers algorithm details to a forthcoming PartIII. I did not locate PartIII in the author sources searched. PartsI–II support the stated theorem and its analytic input, but do not themselves provide a machine-level workspace theorem or a numerical workspace coefficient. That limits the claim about a concrete implementation.

**Bernstein, Circuits for integer factorization: a proposal** (2001/2002). [Primary paper](https://cr.yp.to/papers/nfscircuit-20011109-retypeset20220327.pdf), parallel ECM/HECM discussion.

Bernstein distinguishes conjectural ECM from rigorous HECM smoothness testing and states HECM time `exp((log y)^(2/3+o(1)))`, negligible failure, and memory `y^o(1)` in that parameter regime. This supports low memory relative to a sieve; it does NOT imply o(log y) bits, since even (log y)^100 is y^o(1).

**Lenstra (1987), Factoring integers with elliptic curves**, Annals126,649–673. [Primary publisher abstract](https://annals.math.princeton.edu/1987/126-3/p09), [DOI](https://doi.org/10.2307/1971363). The abstract explicitly calls its subexponential expected-time estimate conjectural. Small memory does not make the required uniform success estimate rigorous.

**Geffert–Pardubska (2013), Factoring and testing primes in small space**, RAIRO ITA47,241–259. [Primary PDF](https://www.numdam.org/item/10.1051/ita/2013038.pdf), [DOI](https://doi.org/10.1051/ita/2013038).

This tempting search hit uses UNARY input plus a pebble, or a special alternating-space condition. The candidate divisor is represented by the pebble's input position. A unary input has N positions and this position carries Theta(log N) bits; simulating it on the binary input pays Theta(n). Its residual-arithmetic lemmas demonstrate that materializing an entire modulus is unnecessary, but they do not generate factor candidates for binary input in the desired ordinary workspace.

## Plausible O(n)-space HECM route: an inference, not a quoted theorem

Fixed genus2 means fixed-degree polynomial arithmetic and a fixed number of curve/group coordinates. Conventional implementation retains a fixed number of residues modulo N. Schoolbook multiplication, modular GCD/division, and fixed-degree polynomial operations can use O(n) bit workspace and polynomial(n) time per group operation. Replacing fast arithmetic by these routines preserves T=2^{o(n)}.

Do not store the enormous smoothness exponent M. Stream its prime-power factors, successively updating the point. The bound B in the rigorous2/3 regime has `log B=O(n^(2/3)(log n)^(1/3))`. Generating candidate primes by trial division instead of saving a sieve adds only a fixed power of B, still 2^{o(n)} time, and counters use o(n) bits. A bounded clock similarly uses logT=o(n) space.

This removes a relation matrix and sieve storage but retains N-bit coordinates. A constant number of residues is not a constant number of bits. This is an upper-bound analysis for conventional representations, not a lower bound for every representation. PartsI–II have not been turned into a full bit-machine proof here, so O(n) should be presented as a concrete implementation route, not an explicit published workspace theorem.

## Truncation, random bits, search/output

If a Las Vegas search has E[tau]<=mu(N), stopping after4mu gives failure probability<=1/4 by Markov. Use any fixed effective subexponential upper bound for mu; the exact expectation need not be computed. A verified returned divisor stays correct. The clock costs logmu=o(n) bits. Alternatively, repeat bounded Corollary1.2 independently r times to get failure<=2^(-r), time multiplied by r, with sequential workspace.

Under the source's unit-coin convention, truncation provides R<=T random bits. It DOES NOT provide an O(logT)-bit seed. Enumerating all R-bit tapes costs2^T, far beyond the budget. Conventional random curve sampling takes Theta(n) fresh bits per trial and potentially subexponentially many trials; no smaller sufficient enumerable seed was established.

On the semiprime promise, a verified nontrivial d determines canonical `p=min(d,N/d)` and `q=N/p`. For a decision-only simulator, the source can accept iff bit i of p is1 and map timeout to0. Correct bit1 instances accept with high probability; correct bit0 instances never accept if timeout is the only failure and returned divisors are checked. O(n) bit queries reconstruct p, at only polynomial(n) time overhead. Output storage is still charged; a write-only output tape cannot be reused as free work memory. Also, the semiprime-promise version of the separator/derandomization theorem, or a suitable total-language extension, must be stated. Promise correctness is not automatically a total BPL witness.

## Why streaming/recomputation has not closed the gap

Read-only arithmetic operands can often be streamed in much less than n space; the modulus alone is not a lower-bound argument. The troublesome operands are the evolving group point and previous residues. Asking recursively for bits of the preceding state creates recomputation through the whole scalar-multiplication sequence.

The straightforward expansion of K sequential group operations has depth proportional to K and repeated uses of earlier state. Its formula expansion may cost exp(O(K)) time. Here K itself may be exp(Theta(n^(2/3)(log n)^(1/3))), so that generic expansion is far beyond2^{o(n)}. This rejects only the naive construction, not every specialized addition-chain, division-polynomial, circuit-balancing, or state-compression method. No explicit S=n^(1-epsilon), T=2^{o(n)} construction was found.

CRT does not make the modular reduction free: updating a coordinate modulo N is not generally equivalent to independently updating its reductions modulo unrelated small primes. The reduction quotient depends on the full intermediate value. An arithmetic-circuit representation needs a paid bit-access/evaluation algorithm. The same warning applies to keeping an n-bit randomized state on an allegedly free read-only random tape: standard small-space coin access must be respected.

## Conditional family103 exponent accounting

Take from the separate quantitative audit the conditional fixed-source bound

`D(N)<=2^{K(S(N)+log2 T(N)+log2 n+O(1))}`

with fixed K including interpreter, separator, and machine-encoding constants. This memo does not re-establish that bound.

If BOTH S=o(n) and logT=o(n), then D=2^{o(n)}=N^{o(1)}, also after O(n) output-bit calls, and thus asymptotically below N^(1/6).

LP's published subexponential storage bound does not certify S=o(n). HECM supplies logT=o(n), but conventional S<=a n+o(n) gives only D<=N^{Ka+o(1)}. Certifying the sixth-rate target from this accounting requires Ka<=1/6 (strict inequality if additional exponent-bearing work remains). The factoring literature supplies neither the numerical a nor the simulator's K. O(n) workspace is insufficient evidence for that inequality. Tape-alphabet compression does not shrink BITspace freely, and padding cannot erase the original n-bit live state.

The constructive remaining obligation is specific: give a rigorous bounded HECM-like or other factoring source with sublinear-bitspace representation and subexponential bit-access/update cost. Existing primary sources supply uniform success and the time scale, not that representation.
