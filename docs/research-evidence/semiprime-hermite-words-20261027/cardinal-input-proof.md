# Cardinal input word acquisition

`SemiprimeCardinalInputBits.acquire Q J t` obtains the target index once, enumerates the actual `Fin Q` list, computes each unique nonself slope with signed Boolean subtraction and raw word reciprocal, and copies each slope J times in the original node-major order. The self slope is literal zero. The negative evaluation point toggles the acquired target sign. No rational slope or evaluation point is synthesized and fed to a scalar rational encoder.

`slopes_value` proves exact equality to `HermiteArrayHeight.cardinalSlopes Q J t.val`; `slopes_length` gives QJ. `slopes_valid`, `slopes_bounded` and `slopes_representation` give valid words, width Q+2, and the original common representation with denominator and numerator bound Q!. `x_value`, `x_valid`, `x_bounded`, `x_natAbs_le` give the negative integer point, valid width Q+2, and magnitude at most Q. No inverse-validity oracle is assumed: distinct finite nodes yield the nonzero physical denominator.

The attached clock retains index digits, finite enumeration, unique slope operations, repeated physical bit-list copies, and output traversal. `acquire_clock` proves the explicit polynomial bound

```
slopeBudget Q = 4(Q+1)+3+41(Q+2)+7
budget Q J = 4(Q+1)+3+3(Q+1)^2
 + Q*(slopeBudget Q+J*(6(Q+2)+7)+4)+1+QJ+Q+7.
```

This is a mixed scalar-digit/control and physical-word ledger. Nat index comparisons and division/remainder digit extraction remain explicit scalar operations, rather than a proved single-tape bit implementation. The claim is physical arithmetic/copy correctness and the stated attached ledger, not complete primitive bit time for original source production or the whole factorer.

Strict compilation, ordinary-root 15-linter checks and every-generated-declaration transitive standard-axiom audit pass: 108 declarations, 60 theorem constants. An independent strict object is byte-identical to the canonical object; pins are in `cardinal-input-verification.json`. The structural runtime diagnostic Q=3,J=2,t=1 executes the actual constructor and returns slopes `[1,1,0,0,-1,-1]`, point `-2`, clock 394. This diagnostic is not a factoring experiment.
