# Quantitative randomness bridge and original-query follow-ups

No new whole-family acquisition bound or guaranteed factoring exponent is
established here. The useful new result is a conditional resource reduction:
the exact quantitative derandomization manuscript would turn a rigorous
fresh-coin factorizer with subexponential time and sublinear bit workspace
into deterministic subexponential factoring. No such source algorithm has
been acquired. This changes the representation to seek on this alternative
branch; it does not discharge the original collision query.

## A precise sufficient resource bound

Write n=ceil(log2(N+1)). For a fixed randomized source, let T and S be
computable worst-case time and simultaneous writable-bit bounds, including
its counters, arithmetic and suspended calls. The fixed capped interpreter
and probability estimator in the [OpenAI manuscript, Sections 12–13](https://github.com/openai/math/blob/main/preprints/Exact-Derandomization-of-Logarithmic-Space-L-equals-RL-equals-BPL-September-23-2026/paper.pdf)
give the following derived bound, conditional on that manuscript:

    deterministic time = 2^O(S + log T + log n).

A virtual padding length 2^Lambda with
Lambda=O(S+log T+log n) supplies the interpreter's time and workspace
budgets. Its symbols are regenerated from the actual input, so writing
the padding is unnecessary. The fixed deterministic library has only
2^O(Lambda) configurations and halts. This proves the displayed resource
implication; it does not make the hidden constant small.

Consequently S=o(n) and log T=o(n) suffice for deterministic N^o(1),
eventually below N^(1/6). The greedy accepting-run construction needs
probability precision O(log T). Alternatively, on the semiprime promise,
proved canonical-factor bit circuits can emit the answer one bit at a
time. Neither method may hide an n-bit candidate in uncharged memory.
The total probability estimator handles promise gaps without requiring
a total bounded-error factoring language.

The older audit correctly said that the exported L=BPL equality alone
does not preserve a running-time exponent. The new primary reading
inspects the stronger quantitative compiler. Its deliberately loose
printed exponent is at least 648000000(a+b+2)+16043 for source clock
(n+2)^a and workspace b*ceil(log2(n+2)). This is a bound on the size of
the **supplied upper-bound exponent**, not a runtime lower bound.
Padding cannot erase its contribution from S=Theta(log N).

Details: [quantitative derivation](reports/logspace-quantitative.md),
[composition review](composition-review.md).

## What the factoring sources actually supply

[Lenstra–Pila–Pomerance, Part I, Corollary 1.2](https://math.dartmouth.edu/~carlp/hyperI.pdf)
supplies a rigorous bounded hyperelliptic smoothness search. Taking its
factor bound to be ceil(sqrt N) gives log T=O(n^(2/3)(log n)^(1/3))
and constant success probability. The conventional fixed-genus
implementation retains full-size residues; a sublinear-bitspace
implementation is not supplied by the primary theorem. Merely using a
constant number of arithmetic registers is insufficient.

The rigorous Lenstra–Pomerance class-group algorithm explicitly permits
subexponential storage. Neither source currently satisfies the new
workspace target. This is a statement about the available constructions,
not a lower bound for factoring. See the [primary-source survey](reports/lowspace-factoring.md).

## A circuit representation, and the exact randomness condition

For a uniform binary circuit of depth D and size Z with R random inputs,
depth-first evaluation can store a path and completed sibling bits,
reconstructing each gate address. With local uniformity costs U_S,U_T,

    S = O(D + log Z + log R + U_S),
    T <= 2^O(D) * poly(D,log Z,n) * U_T * R.

This is a proved representation bound with a reusable, two-way random
tape. It does not turn repeated references to one random bit into
independent fresh coins.

A proposed shallow Dixon construction with smoothness bound
B=exp(n^alpha) balances the anticipated trial-selection depth
O(n^(1-alpha) log n) against linear-algebra depth O(n^(2alpha)). The
balance alpha=1/3 suggests S+log T+log n=soft O(n^(2/3)). The complete
uniform circuit, its success proof and canonical output costs remain
obligations; this is a conditional design estimate.

[Cheng–Wu v3, Corollary 6](https://arxiv.org/html/2609.23603v3#S10.SS4)
supplies a relevant separate theorem. If a reusable-random-tape machine
visits each random cell at most v times, deterministic probability
estimation costs

    2^O(v*(S + log(n+T))) * poly(n,T,1/epsilon).

Thus v*(S+log T+log n)=o(n) would suffice for this route, independently
of the OpenAI manuscript. At the proposed balanced parameters, the
needed visit bound is o(n^(1/3)/polylog n), with the logarithmic factor
matched to the actual circuit bound. Ordinary circuit unfolding gives
no such guarantee. Transit across random-tape cells counts as visits.
An oblivious recursion stack does not provide free random-bit replay.

See [the constructive evaluator and missing conditions](reports/circuit-space.md).
A short seed preserving the success of the *whole factorizer* would
also suffice, but no such seed construction is supplied. Preserving
only smoothness marginals is not enough.

## Original-query follow-ups retained from the interrupted turn

These three reports preserve the earlier scratch work without claiming
another acquisition advance:

- [Adaptive localization](reports/adaptive-localization.md): an acquired
  original gcd locator would suffice, but the first restricted product
  in the proposed adaptive algorithm still costs soft O(sqrt(JL)).
- [Hensel geometry](reports/hensel-support-contraction.md): the exact
  m-adic square-image identity shows that higher precision constrains
  only the critical residue channel. All critical channels can be
  queried together in soft O(m), using the inherited common-product
  machinery. The remaining unit-square palettes have no additional
  restriction from these separate Hensel masks.
- [Small symmetric trace](reports/cubic-small-trace.md): acquiring
  P+Q modulo r gives at most two factor residues; acquiring P^2+Q^2
  gives at most four. At r=Theta(N^(1/18)), either datum feeds the
  existing sparse-residue consumer within the sixth-rate budget.
  Paid dense N-power tables still lack a guaranteed trace decoder.

## Root review and research boundary

Root checked the virtual interpreter's cap, simultaneous space accounting,
compiler-exponent arithmetic, accepting-path precision, and the exact
fresh-coin/read-many distinction against the primary texts. The Hensel
identity and common critical-channel product retain the original scalar
indices and carry terms. The small-trace reduction uses the existing
consumer at modulus r directly; no gratuitous r-squared lift is required.
An additional composition review confirms the conditional scope.

The next substantive work on this branch must construct a source with
the stated workspace/randomness bounds, or a tailored short-seed
distribution with proved full factoring success. Implementing the
compiler or formalizing another supplied-data consumer would not meet
that obligation. The strongest original bounded scalar controller and
its unpaid soft-O(m) long query remain the main arithmetic alternative.
Complete executable and Lean bit-complexity integration also remain.

No Lean build, finite coverage campaign, commit or push was performed.
Source fingerprints and verbatim report provenance are recorded in
source-pins.json. Validation records preservation of all 187 preceding
frozen entries; archive integrity is not mathematical coverage evidence.
