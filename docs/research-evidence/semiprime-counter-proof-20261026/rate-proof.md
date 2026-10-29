# Compiled growing-arity counter rate and numerical guard progress

New owned repository source: `/home/dbsanfte/riemann/formal/RiemannGaussian/SemiprimeCounterRate.lean`. Namespace `RiemannGaussian.SemiprimeCounterRate`. No existing source, frozen evidence packet, AGENTS file, journal, or external checkout was edited. No external build was restarted.

## Exact schedule contact

The definitions implement the frozen `shared_parameters.py` integer formulas:

- `lam=Nat.clog 2 n`, `nu=Nat.clog 2 lam` (mathematical ceiling binary logarithms);
- `scheduledGroupCount lam = Nat.sqrt lam / nu^2`, the lower-case group count **r**, not the degree R;
- `scheduledPointCount lam = lam / (128*nu)`, the point count Q;
- `scheduledCeilSqrt lam = sqrt(lam) + if sqrt(lam)^2=lam then 0 else 1`;
- `scheduledDegree lam = 4*scheduledCeilSqrt lam`, the actual degree budget R;
- `scheduledDimension n = r^(2Q)`;
- `intervalStart r Q R = (Q*(r-1)-r*(R-1))/(2*r)`.

The exact integer budget theorem proves `(r^(2Q))^128<=2^lam` from `r^2<=2^nu` and `128*nu*Q<=lam`. Both premises are discharged for the scheduled floor/square-root formulas. With `lam=clog_2 n` and n>1, it follows that **D^128<2n**. The real consequence **D^2<=2*n^(1/64)** is then proved rather than supplied as an assumption.

For every fixed C>=0, the actual incidence test

`2*(2+w)*D^2<=2n`

holds eventually for **every** w with `w<=C*n^(3/4)`. Its proof evaluates the normalized load using negative powers n^(-63/64) and n^(-15/64), and composes that decay with the proved scheduled-D budget. This is not a transport theorem assuming eventual guard acceptance or assuming D's asymptotic budget.

The actual group-balance test `2*Q*r^2<=n` is proved for all n>2^16, using a direct integer induction `2*k^2<=2^(k-1)` for k>=16. No probability estimate is used.

An independent exact induction proves `65536*nu^4<=2^(nu-1)` for nu>=64. Together with `2^(nu-1)<lam`, this gives the explicit scheduled range tests:

`r>=2`, `R>=32`, `6R<=Q`, hence `R<Q`.

The double integer ceiling logarithm tends to infinity, so these conditions hold eventually for the actual schedule. The parameter threshold is deliberately huge; this is no practical threshold claim.

Under those range tests, the centered interval numerator is nonnegative. Thus its natural-number subtraction coincides with the signed numerator in the Python floor formula; no negative-floor exception is being silently discarded. `interval_contained` proves A0+R<=Q+1. A combined theorem `eventually_non_tail_schedule_checks` packages r>=2, R>=32, 6R<=Q, R<Q, tau denominator r*lam>=2, both balance inequalities, and interval containment for actual growing arity.

**Remaining numerical guard obligation:** exact binomial-tail acceptance is NOT asserted. The combined theorem is explicitly named non-tail. It does not assume the full guard succeeds, and it does not insert a tail estimate as an axiom. The external `SpectralTail` pattern concerns Q-1 and a different constant; it was read only as a pattern and was not silently imported or equated to this schedule.

## Analytic envelope

`rho(x)=(log(log x))^2/sqrt(log x)` tends to zero. Mathlib's little-o logarithm/power theorem supplies this with exponent 1/2, composed with log tending to infinity.

The module proves, for arbitrary fixed real constants C,d,A,B and every epsilon>0, eventual absorption of

`C*x^d*exp(A*x*rho(x)+B*x^(3/4)) <= exp(epsilon*x)`.

The proof explicitly charges the polynomial log term, fixed leading constant and growing-arity exponent; the latter uses x^(-1/4)->0. Substitution x=log N gives the corresponding positive-power bound N^epsilon, including the displayed sixth-rate specialization. These are bounds on explicit analytic envelopes; **they are not a claim that a supplied implementation has already been proved to obey that envelope**.

The following remain separate: formal correctness/cost of every streamed counter operation, precise integer schedule-to-runtime estimates (including tail), linear network-size substitution into the runtime envelope, machine compilation, prefix factor recovery and a complete all-input factoring theorem. This module removes specific genuine numerical/analytic obligations, not those remaining interfaces.

## Verification

Strict command:

`lake env lean -DwarningAsError=true -o .lake/build/lib/lean/RiemannGaussian/SemiprimeCounterRate.olean RiemannGaussian/SemiprimeCounterRate.lean`

The executable uses `/home/dbsanfte/.elan/bin/lake`; log in `rate-build.log`. All imports are Mathlib; no unaudited external SAT source is imported. Ordinary-root import audit and scoped lint are in `rate-root-audit.lean` / `.log`, with axiom reports for every public theorem. Source/object hashes and verified report counts are recorded separately after that audit finishes.

Final verification: strict compile PASS; ordinary-root import and scoped namespace lint PASS; all 23 public theorem axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`. `rate-verification.json` records the final source/object and audit hashes. A scratch source copy is retained for review.
