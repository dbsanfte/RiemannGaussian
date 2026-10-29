# Actual original histogram-query width and retained clock

`SourceHistogramQueryBounds` bounds the actual `Query.score` applied to `Setup.acquire n F r Q lam arity owner`. The only query-prefix premise is membership of its actual physical IDs in the actual acquired compact bank. All intermediate callback, payload, histogram, width and clock obligations are discharged by original constructors and executed invariants; no Fits/output/count/clock oracle is an input.

Write M=sum arity and L=r^Q. `baseWidth n M r Q lam` is one plus the sum of the original compact-width caps for L,L²,L⁴,r^(4Q−1),n²lambda²L⁴,4M²,M²,(Qn)²,Q, and n (the last uses clog₂(n+2)). `laneWidth=grow(baseWidth,20)` and `outputWidth=grow(laneWidth,2)` use the fixed-depth physical arithmetic theorem `grow(W,d)=4^d*(W+2)`. Thus output size depends on original logarithmic count/scale caps, not native score magnitude or an encoded answer. All coefficients and raw signed intermediates, including L−1 and subtraction in the head formula, are covered. Denominator-one validity remains the already proved actual Query invariant, with no rational GCD/reduction in this path.

The literal closed query bound is:

```
scoreBudget n F M r Q lambda k =
 prefixBudget(L,k)
 +16*FeatureBitsBounds.budget(n+F,L,M)
 +HeadBounds.budget(r,Q,keyWidth(n),n)
 +90*ArithmeticBounds.unitBudget(baseWidth)
 +3*ArithmeticBounds.unitBudget(laneWidth)
 +k+10.
```

Here `prefixBudget(L,k)=k*100*(clog₂(L+1)+clog₂(k+2)+2)+1` is the actual Prefix.acquire theorem at original acquired-ID width. Every feature producer retains its actual original record scan, dictionary reads, framing and sparse-square fold. The literal sixteen-term arithmetic list sum is bounded using its proved length sixteen. The head producer retains its actual prefix reads, one all-coordinate row query per fixed vertex, free/fixed physical increments, key appends and sparse-square fold. Its selected cached colour widths are logarithmic in r, not the old raw colour width. The 90 and 3 unit budgets are the proved fixed-depth lane and weighting operations; each unit budget is quadratic in its fixed-level word-width envelope. All lower producer clocks stay in the sum.

Consequently the explicit report has a scan contribution linear in M, nQ and selected-prefix length k, up to the displayed logarithmic key/counter widths, and a fixed polynomial in the original logarithmic arithmetic widths. This is a bound on the actual retained mixed report, not a separately assumed complexity interface or a complete primitive-machine asymptotic theorem. There is no M²+Qn² descriptor construction in this query. Quadratic occurrence-count caps occur inside logarithmic histogram/weight width bounds; no pair loop executes to acquire histogram outputs. The cached 4M² weight is acquired by physical multiplication, not an occurrence-pair scan.

`score_bound`, `score_clock` and `score_width` are the actual original constructor endpoints. `scoreBudget_prefix_mono` enlarges a reachable prefix length only, for controller integration. `indexed_clock` explicitly retains the actual once-acquired setup report. `indexed_clock_closed` additionally applies Quantum's proved SetupBounds.acquire_clock, giving a closed original-dimension setup budget plus this actual query budget. Cached selectors pay setup once rather than once per candidate.

The scope is physical Boolean arithmetic/copies/trie visits plus explicit native finite-index, interval, constructor/control and immutable-reference stages. Setup conservatively pays original native r/lambda/index encoders, finite metadata and the actual complete coordinate bank; no near-linear setup claim is made. Complete pointer/tape execution, replacement of every old downstream source caller, and a whole-public primitive-bit rate remain open. The new bounds do not infer a machine runtime from old report equality.

Canonical strict compilation uses autoImplicit=false and warningAsError=true. Ordinary-root namespace15 lint and every-generated transitive axiom audit pass with only propext/Classical.choice/Quot.sound: 26 declarations and 21 theorem constants. Independent isolated compilation is byte-identical. The module is proof/budget code over previously tested runtime; no new finite factoring campaign was added. Exact pins/logs are in histogram-query-bounds-verification.json.
