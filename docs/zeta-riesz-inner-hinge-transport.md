# Cross-count cancellation on the literal inner hinge

The independent `-79/1000-o(1)` floor remains **open**. This slice proves
a finite signed estimate on two original arithmetic labels. It does not
prove enough admissible partners, pay their total mismatch, or bound the
unmatched many-bin population.

## The count-independent coefficient

Write a squarefree label as `n=p*q*b`, where `p,q` are distinct primes
coprime to the squarefree composite `b`, and put `tau=log(p*b)-L`.
The literal inner-hinge conditions are

```
log(q*b) <= L,
log b <= log(p*q*b)-L,
0 <= tau <= log(minFac b).
```

All nonunit divisors of `b` are then outside the surviving hinge. Exact
prime deletion and the saturated response of the composite `b` give

```
response(L,log p+log(q*b),q*b) = -tau,
originalAtom(p*q*b) = mu(b) * tau * phaseWeight(q*b,p).
```

These are `response_inner` and `literal_inner_atom` in
[`ZetaRieszInnerHingeTransport.lean`](../RiemannGaussian/ZetaRieszInnerHingeTransport.lean).
The latter retains the original `residualCoefficient`, factorial kernel,
`1-boundedShare` and full phase. It holds at arbitrary counts allowed by
its hypotheses, including count56+. It does not assert that all remaining
many-bin labels satisfy the inner-hinge inequalities.

## Pairing original labels across parity

Replace the owner prime `p` by two actual, distinct primes `p',r`, with
`r` coprime to `b`; retain `q,b`. Assume the new label also satisfies the
literal inner-hinge conditions and all required coprimality. The total
prime count increases by one. Set

```
n  = p*q*b,
n' = p'*q*r*b,
tau' = log(p'*r*b)-L,
W  = v  * phaseWeight(A, L,N,y, q*b,  p),
W' = v' * phaseWeight(A',L,N,y, q*r*b,p').
```

Here `v,v'` are the **original signed population/funding multipliers**.
Each label retains its own allocation and phase; neither is replaced by
the other's. `inserted_pair_eq` proves

```
v*originalAtom(n) + v'*originalAtom(n')
  = mu(b) * (tau*W - tau'*W').
```

Thus `inserted_pair_floor` gives the actual finite one-sided inequality

```
Re(v*originalAtom(n) + v'*originalAtom(n'))
  >= -abs(Re(tau*W - tau'*W')).
```

The amplitudes are joined **before** their difference is priced. The
count-free mismatch estimate `norm_linear_pair_le` is

```
norm(mu(b)*(tau*W-tau'*W'))
  <= abs(tau-tau')*norm(W) + abs(tau')*norm(W-W').
```

There is no `2^omega` divisor allowance. The exact cutoff and total-log
gap is `tau'-tau=log(p'*r)-log p`, proved by `cutoff_gap_eq`. The common
cofactor contributes no extra phase displacement. Allocation and funding
differences are still present in `W-W'` and must be paid.

## What a whole-sum application needs

`matching_floor_with_signed_rest` reuses the existing disjoint matching
on the **original label set** `S`. For a matching `E` with proved pair
costs, it gives

```
Re(sum_(n in S) f(n))
  >= -sum_(e in E) cost(e)
     + Re(sum_(n in S \ matchedVertices(E)) f(n)).
```

The unmatched rest stays signed. The function `f` may retain all original
radial, allocation, count, owner, physical and funding weights. No weight
or mask removal is implicit in this theorem. Each actual matched label
must belong to `S`, and each pair is spent once.

The remaining global tasks are concrete:

1. Prove enough opposite-parity partners inside the native support. The
   many-bin condition alone supplies neither this capacity nor weighted
   coverage. Choosing `r<minFac b` gives a canonical least-prime inverse,
   but existence with the physical masks is not proved here.
2. Bound the total **actual** weighted mismatch at source scale, including
   allocation and signed funding differences. A small relative per-pair
   error is not enough against an exponentially growing positive envelope.
3. Bound the signed unmatched population and the original supply charge
   within the same whole funded ledger.

No global matching, fixed power saving, cofinal floor, ceiling or zero
exclusion is claimed.

## Optional numerical regression

`scripts/probe_riesz_inner_hinge_transport.py` tests 114 finite cases at
orders32,64,128,256,512, heights54,65,100 and counts4/5 through12/13.
It uses actual integer labels, exact integer rounding of the native moving
length at `u=10001/20000`, the literal unpaid factorial orders in the
allocation, all subset signs of the Riesz coefficient and the full complex
phase. Prime tests above `2^64` are probable-prime tests, not Lean
certificates. Floating near-equalities and small log gaps are diagnostics,
not certified intervals or rate theorems.

With equal population multipliers, pair norm divided by the two separate
norms ranges from approximately `0.00084131` to `0.0449282`. This measures
only those finite pairs. It is not a fraction of the asymptotic floor gap.
Changing the multipliers to `1,-0.1` makes that ratio essentially one;
signed ledger weights cannot be omitted. In these samples allocation
differences are much larger than the total-log transport gap.

Two finite owner cells of integer width8192 have 235 original primes and
266 distinct opposite-parity candidates at order32, and 110 versus155 at
order64. This is a numerical local capacity check, not native weighted
matching coverage or a certified prime-count theorem.

The inserted primes2,3,5,7 violate the **older fixed parity packet's**
all-leg rough-prime threshold. That threshold is not a mask on the current
whole core: its physical prime restriction is an upper cutoff, while
`N^2` controls allocation eligibility. Small insertions are not excluded
from the whole core merely by their size. These samples still do not
certify the unpaid count56+ many-bin population or the original
dyadic/funding witness. The probe retains allocation eligibility; native
membership and weighted coverage require separate proofs. It runs only
when explicitly invoked:

```
../.venv/bin/python scripts/probe_riesz_inner_hinge_transport.py \
  --output .lake/riesz-inner-hinge-probe.json
```

## Local proof audit

All seven public theorems pass direct Lean with warnings as errors, the
targeted module build, the working root import, all14 namespace linters
and transitive axiom checks. Their only axioms are `propext`,
`Classical.choice`, and `Quot.sound`.
[`riesz-inner-hinge-transport-audit.json`](riesz-inner-hinge-transport-audit.json)
records the exact validation scope. README/default explorer endpoints,
earlier positive results/no-go audits and unrelated staged work are
preserved. Wider publication checks and generated assets remain deferred.
