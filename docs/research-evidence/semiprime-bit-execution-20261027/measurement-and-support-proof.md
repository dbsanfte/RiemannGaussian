# Physical measurements and the actual scheduled support count

This report covers the new `SemiprimeMeasurementBits`, `SemiprimeSupportRate`,
and `SemiprimeScheduledSupportRate` modules. All previous modules are preserved.

## Measurement semantics and execution

`dot`, `equal`, and `test` operate on explicit signed Boolean words. Signed
integer values occur in their specifications, not as hidden arithmetic inputs
to the implementation. Each visited matrix entry is physically copied; selected
entries use the existing Boolean signed-addition routine. Equality subtracts
the actual signed words and scans every result bit, so opposite signed-zero
representations compare equal. The suffix result is retained once.

`dot_value`, `equal_correct`, and `test_correct` prove the resulting flags are
exactly the original integer measurement equations. No output-fit premise is
needed: integers have variable-width signed words, and `dot_width` derives the
scratch bound W+row.length from the physical input widths alone.

For at most n entries of width W, the actual arithmetic ledger is at most
`n*50*(W+n+1)+4` per dot. For m rows with targets of width at most W+n,
`test_cost` bounds the full ledger by

```
m*(n*50*(W+n+1)+60*(W+n+2)+9)+4.
```

The indexed adapter preserves the existing measurement flags exactly.
`findBits_found_congr` transports this equality through false-first search;
`representative_found` therefore proves that the physical tests select precisely
the same witness as the previous integer implementation. Its ledger is bounded
by the same polynomial per visited search leaf, with at most 2^n leaves. The n
here is the input dimension of this representative search; the caller still
needs to instantiate it with its bounded group dimension.

These are concrete arithmetic routines and scoped ledgers. Matrix/target word
acquisition, constructing the finite callback lists, closure access, binary
address arithmetic, and compiling the surrounding traversal to a physical
machine are still separate. This theorem does not yet bound the whole counter.

The execution control checks signed zero, cancellation 3-3+2=2, a failing target,
the actual selected vector [false,false,true], and an inconsistent matrix.
The output is `true, 2, true, false, some [false,false,true], none`. It checks
executable data flow rather than supplying evidence for an asymptotic rate.

## Literal support count

The actual inclusive callback menu has size

\[
C(n,q)=\sum_{j=0}^{q}2^j\binom nj.
\]

For 0<n and q<=n, the new theorem derives

\[
C(n,q)\le(n+1)\exp\{nH(q/n)\},\qquad
H(a)=a\log8-a\log a.
\]

The apparent singularity at zero is removed using continuity of a log a.
Consequently q(n)/n -> 0 implies, for every positive epsilon, eventually
`C(n,q(n)) <= exp(epsilon*n)`. The proof includes q=0 and does not assume the
previously unpinned numerical aggregate constant 16435.

For the actual integer schedule Q(lambda)=floor(lambda/(128*clog2(lambda)))
and R(lambda)=4*ceil(sqrt(lambda)), the proof retains both rounding operations:

\[
\frac{2R(\lambda)}{Q(\lambda)}
\le4096\frac{\operatorname{clog}_2\lambda}{\sqrt\lambda}\longrightarrow0.
\]

It follows that the exact cutoff `floor(2*n*R(clog2 n)/Q(clog2 n))` has a
vanishing ratio to n, and the literal support menu is subexponential. This
closes a counting estimate. It does not by itself bound the cost of each
callback, charge preprocessing, or prove the public factoring execution time.

## Remaining composition

Combine the actual source-generated measurement words with the physical test,
instantiate group dimensions, and attach the support theorem to the same
physical group/fibre/interpolation run. The public wrapper's actual incidence
identity must identify its precision with this cutoff. Only after all source,
control, storage and arithmetic costs are attached can these component bounds
be used as a theorem about the all-input factoring algorithm.
