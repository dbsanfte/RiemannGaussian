# Actual incidence classifier work

NEW `SemiprimeSourceIncidenceCountBitsBounds` attaches original finite-resource bounds to the actual physical two-edge classifier. It supplies `acquired_payload`, `edge_work`, `count_work_cached`, `count_work`, numerical monotonicity for both budgets, and `countBudget_monomial` with constants quantified before all original inputs.

Let L=r^Q. The conservative budget is

```
edgeBudget L N s =
  4N+2 + 2 keyBudget(N)
  + 2 readBudget(N+1,N,2L,s) + eqBudget(2L+1) + 9
countBudget r Q L N s = 2 edgeBudget(L,N,s) + 4 Powers.width(r,Q) + 11
Powers.width r Q = 8Q(r+1)+1.
```

The only original premises are actual acquired-ID membership of the stored environment, fixed prefix length ≤N, override length ≤s, stored key lengths ≤N+1, remaining list length ≤N and the original descriptor keys ≤N. In particular there is no truth/count, intermediate fit, encoded-word answer, unknown order, source score or callback-work premise. Bank acquisition itself proves candidate-ID payload lengths ≤2L; `read_valid` proves returned IDs stay in the acquired menu. `read_work` pays both actual fixed/override scans, physical key construction, key comparisons and payload copies. `equalID_work` pays the real signed physical equality on those payloads. The two membership scans and shorter loop/free branches are retained exactly.

The generic cached-powers form takes actual payload length caps only; the original `CountPowers.acquire_length` discharges them without a value-to-width assumption. The wrapper `count_work` applies that actual cache. It does not count the cache's acquisition automatically: the caller must acquire/copy/cache powers once and retain its separate `.clock`. Similarly the acquired word bank is a caller setup report; no row lookup occurs inside incidence classification.

No L^m completion loop, unary L^4 construction or global 2^n traversal occurs in this runtime path. The coarse 2L ID width appears only in the original ID read/equality budgets. The native descriptor equality, natural-index membership and finite report/list-control stages remain explicitly scoped as such; this is not a claim that their unbounded natural equality or physical tape/address costs have already been composed into the full public primitive machine clock.

Strict/root15/all-generated standard-three-axiom and separate output-path recompile evidence is pinned in `incidence-bits-bounds-verification.json`. Earlier sources were read only.
