# Actual original scale and compact-weight acquisition

Three NEW modules close the original count/scale setup data path:

* `SourceHistogramCountInput.count xs` traverses actual list cells and physically increments a compact counter; it never encodes a supplied native length answer;
* `SourceHistogramScales.acquire r Q lam records vertices` executes the complete compact power/product/weight cache;
* `SourceHistogramScalesBounds` derives all actual setup work and compact query-operand bounds from those original inputs.

The Cache fields are exactly `alphabet`, `square`, `fourth`, `head`, `weights`, `clock`. Runtime consumes only original native r,Q,lambda and actual generic record/vertex lists, not M/n answers, histogram counts, encoded powers or fit/clock certificates.

## Actual operations and values

The actual record and vertex list spines acquire compact M/n bit counters. The original native r and lambda parameters use the explicitly paid existing natBits encoder, followed IMMEDIATELY by a physical trim. Their potentially magnitude-linear encodings are never fed untrimmed to powers or query weights.

A physical power of compact r produces L=r^Q and is trimmed. Actual multiplication L*L produces L² and is trimmed; its square produces L⁴ and is trimmed. A second physical power produces G=r^(4Q−1) and is trimmed. No unary L, U=L² or L⁴ materialization is executed. Q=0 gives the natural-subtraction exponent 0 for G, which is harmless because the actual head sum is empty.

The existing actual seven-product weight constructor consumes the ACQUIRED compact M/n counters, compact lambda, and compact L². Both physical weight outputs are trimmed and their trim reports retained. Exact values are

```
alphabet=r^Q; square=(r^Q)^2; fourth=(r^Q)^4; head=r^(4Q−1);
weights.incidence=vertices.length²*lambda²*(r^Q)^4;
weights.head=4*records.length².
```

These are precisely the original denominator-cleared incidence/head weights with U=L². Every count/power/product/weight equality follows its executed physical arithmetic; no output integer was encoded to create these fields. `acquire_compact` and `acquire_lengths` prove all six payloads are Compact and bounded by clog2(actual value+1). Both weights become [] when their actual value is zero.

## Work and original-derived widths

Each actual list-driven count costs at most

```
length * (30*(clog2(length+1)+2)+20) + 1.
```

The physical count loop ignores payload values and inspects every actual list constructor; input list construction remains separately caller-paid.

The r/lambda native boundary is explicit:

```
naturalBudget(x)=20*(x+1)^2+6*(x+1)+6.
```

The complete `acquire_clock` theorem adds both original list counts, both native encoders/trims, the physical L/G powers, L²/L⁴ products, the actual seven-product weight constructor, both weight trims and setup control. All lower report fields are retained once. The actual power/product inputs are compact before their consumers.

The input width used to bound query-weight construction is

```
clog2(M+1)+clog2(n+1)+clog2(lambda+1)
 +3*(2*Q*clog2(r+1)+1).
```

`acquire_weight_input_widths` derives it from ACTUAL list-count compactness, actual compact lambda and the physical L² multiplier. It is not a padded M/n width or a desired intermediate fit premise.

`acquire_clock_monomial` also proves a uniform conservative polynomial envelope: constants C,k precede every original dimension, every list element type and every actual record/vertex list. Given only r,Q,lambda and the two list lengths <=S, actual cache clock <=C(S+1)^k. Its proof first bounds known logarithms by S+1 and expands the numeric budget into a fixed polynomial. This coarse SETUP envelope does not replace the sharper compact query-operand theorem or reintroduce padded M/n runtime encodings.

## Scope

No positivity is needed for the acquisition/value/compactness theorems, including empty records/vertices, r=1, Q=0 and zero lambda. The original score-order consumer separately requires its established positive r/lambda hypotheses. Record and vertex lists preserve all their actual occurrences; the original caller must instantiate them with its acquired original metadata lists, whose cardinality equalities are separately available.

Native r/lambda acquisition, exponent/control arithmetic, report metadata arithmetic, list construction and immutable references remain explicit native/scalar interfaces. This module does not claim a logarithmic-time native parameter encoder, literal full address/TM simulation, or that the old public controller has already been replaced. The cached physical data is now available for the new histogram query. The caller must retain Cache.clock once; per-query arithmetic may reuse its payloads without pretending acquisition was free or charging it anew.

## Evidence

Canonical strict builds, all fifteen root linters and all-generated standard-three-axiom audits pass: CountInput21 declarations/14 theorems, Scales44/21, Bounds43/34 (108/69 total). Independent output-path recompiles are byte-identical; pins are in `histogram-scales-verification.json`.

The tiny actual-list smoke with three records, two vertices, r=2,Q=2,lambda=3 returns values `[4,16,256,128,9216,36]`. Empty lists with r=1,Q=0,lambda=0 return `[1,1,1,1,0,0]`. These are structural arithmetic controls, not factoring examples or performance measurements.
