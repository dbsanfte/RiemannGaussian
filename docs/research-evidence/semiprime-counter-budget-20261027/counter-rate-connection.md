# Exact counter budget to the actual retained-report rate

## Actual execution and derived budget

The endpoint remains `SemiprimeFullSetupScheduledController.run N`; this packet does not replace its algorithm. `FullSetupBudget.count_work_eq_setup_add_native` is an exact additive identity for its internal full counter. The setup part literally includes acquired enumeration, original source, raw metadata/integer family and every physical design report. Only after design values are proved equal does `FullCounterBudget.native_work_eq_indexed` transport the native phase's work expression. Setup is kept separately, so evaluating old design comparison terms in a proof supplies no free runtime selection.

`FullSetupBudget.setup_work_bound` bounds setup by an explicit fixed polynomial in original dimensions, the two source alphabet sizes and the DERIVED bit capacity `B+2+2R(Q+3)`. The large measurement magnitude is not used as a polynomial setup dimension. `NativeCounterBudget.count_work` retains the actual support count, actual summary box, head tables, local truth-table traversal and Hermite work. `FullCounterBudget.count_work` joins these against the actual acquired report.

For a public input, write n=wireCount N, r=groups N, Q=points N, R=degree N, J=precision N, lambda=Nat.clog 2 n. The public theorem uses

    H = ceil(3*n/(2*r))
    W = measurementBound 2 Q R
    Y = (2*n*W+1)^(floor(4*n/(r*lambda))).

The selected rank sum obeys `(sum_g m_g)*(r*lambda) <= 4*n`. Head and rank bounds come from the generic source constructor instantiated at `FiniteEnumerations.indexed`, the actual executed enumeration. Prior `defaultEnumerations` layouts can choose different ties; no equality is assumed. The denominator is proved positive from the actual guard. The individual selected measurement bound `m_g <= 4*n` is used only polynomially, while the summary exponent uses the total rank.

`PublicCounterBudget.counter_work` discharges every original occurrence, head, rank, summary and terminal callback premise. Its bound is uniform over prefixes of length <=n. `run_work` then closes the public fast-controller bound without the former unexplained B hypothesis; `eventually_run_work` uses the already proved eventual guard. The factor graph count itself is proved <=n, rather than inferred from occurrence two for a generic graph that might have empty scopes.

## Fixed-polynomial composition

`PublicReportPolynomial.resources N` sums all literal scalar dimensions plus the four large resources:

    weightedCount n (J-1), Y, 2^H, 2^scopeBound(bitLength N).

Its scalar part retains all separately executed source menus, prefix entry and decoder envelopes. `ScheduledScalarBudget.scalarResources_le` bounds it by

    20*n + 2*n^2 + 5 + entryEnvelope(n) + scopeEnvelope(n) + decoderEnvelope(n).

Both source menu sizes r^Q and r^(2Q) are bounded from the ACTUAL integer guard. Coarse polynomial bounds on H and scope are used only in the scalar part; their exponential terms keep the sharper bounds.

The diagonal setup/native envelopes are explicit fixed arithmetic expressions. `ReportPolynomialGrowth.Bound` constructs constants/exponents by constant, identity, sum, product and fixed-power closure. Its small tactic builds ordinary proof terms from those lemmas; it is not an axiom, a native-decide proof, or a supplied cost witness. `PublicReportGrowth.scalar_monomial` and `controller_monomial` provide fixed constants before quantifying over all resource sizes.

`PublicCounterResources` proves Y <= the established real summary envelope, 2^H <= the head envelope (including the ceiling), and 2^actualScope <= the actual growing-scope envelope. It identifies J-1 exactly with the existing inclusive cutoff. `FullReportRate.resources_le` combines these with the scalar monomial bound. `run_le_rate_budget` bounds the ACTUAL controller report by one fixed polynomial of `MaterializedRate.budget`; `run_report_subpower` invokes the existing public input-size rate theorem. No new family coverage or asymptotic arithmetic hypothesis is assumed.

## Scope of the new theorem

The complete mixed report now has a uniform, proved eventual N^epsilon bound for every positive epsilon. This closes the prior actual-counter B and report-to-rate obligations. It does not prove that every executed instruction costs one bit operation, nor that all original-input and memory acquisition has been instrumented. Existing physical selector and local bit subroutines are real components, but other operations still use scalar arithmetic or declared metadata/cache allowances.

Remaining physical refinements include original graph/scopes/coordinate and schedule/guard construction; source score/interpolation arithmetic and word extraction; every native rational/Hermite intermediate and floor operation; finite indexing/addressing and metadata/control; and the complete decoder/fallback composition. In particular the source array reader's enumeration inverse remains a finite index search, not a free bit read. Appropriate bit-height theorems and existing primitive components must be attached to the actual executed path, with memory permitted to be subexponential. The final primitive clock must be proved a fixed polynomial in the SAME resources before the rate theorem proves the requested whole bit-runtime guarantee.
