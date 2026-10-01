# A joined low-offset floor for the retained hinge

[ZetaRieszLowOffsetPairFloor](../RiemannGaussian/ZetaRieszLowOffsetPairFloor.lean)
proves a new independent sector inequality: joining two opposite original
four-divisor blocks costs at most **two thirds** of their separate real-part
allowance. This region includes near-balanced seven-prime geometries that
miss the previous overlap selector. The theorem is connected directly to
the current `polynomialCentralRemaining` floor ledger. The aggregate sector
cost, unselected signed sum, whole `-79/1000` floor and contradiction remain
**open**.

Fix the original squarefree cofactor `a`, prime owner `p`, three distinct
cofactor primes `r < s < q <= p`, and `e | a/(rsq)`. All eight incidences
keep the **same original label `pa`**, allocation, factorial observation and
complex phase. Set

```math
\alpha=\log r,\quad \beta=\log s,\quad v=\log q,\quad P=\log p,
\quad D=\log(a/e)-L,\quad S=\alpha+\beta+v.
```

On `0 <= D <= alpha` and `P+D <= alpha+beta`, the two old blocks have exact
responses

```math
Z_1=w(pa)\mu(a/e)X,\qquad Z_2=-w(pa)\mu(a/e)Y,
\qquad X=\alpha+\beta-P-2D,\quad Y=P+D-v.
```

Their sum is therefore

```math
Z_1+Z_2=w(pa)\mu(a/e)(S-2P-3D).
```

Both original hinges are included. The adjacent block crosses the **first**
hinge even though it lies below the cofactor hinge. Discarding that block as
an affine zero would be incorrect.

If `X <= 5Y` and `Y <= 5X`, both amplitudes are nonnegative and Lean proves

```math
\operatorname{Re}(Z_1+Z_2)
\ge-\frac23\bigl(|\operatorname{Re}Z_1|+|\operatorname{Re}Z_2|\bigr).
```

This is independent of the height and sign of the complex observation.
It is an allowance saving **on the matched eight-incidence sector**, not a
one-third reduction of the whole floor deficit. There is no prime-density,
exposed-zero or unproved bilinear cancellation premise.

`low_offset_prime_row_eq` also keeps the actual retained prime row joined:

```math
\mu(a/e)\bigl[(S-3D)M_0(P_{\rm literal})-2M_{\log}(P_{\rm literal})\bigr].
```

The prime mask may have its original endpoints and holes. This identity
does not bound its aggregate numerical price or license a completion.

`low_offset_pair_subset_retained` proves that strict `P+D < alpha+beta`
puts both blocks in the **current** antidiagonal after the earlier affine
zero deletions. Squarefreeness makes the two old blocks disjoint; different
original labels remain different outer summands. `global_retained_low_offset_floor`
retains every unselected label and divisor incidence signed. The terminal
`eventually_remaining_low_offset_floor` uses the original dyadic schedule,
the reduced count crop and the allocation payment, leaving all previous
credits and geometric errors unchanged and spent once. Its `LowOffsetData`
witnesses are only explicit finite prime/divisor/log geometry.

The optional [actual-label probe](../scripts/probe_riesz_low_offset_pair.py)
uses seven distinct primes and all original core masks at `(N,K)=(640,16)`
and `(1536,32)`. The joined/separate allowance ratios are about `0.437` and
`0.553`. Neither sample lies in the earlier overlap selector. Both satisfy
the new arithmetic balance. Their individual source amplitudes underflow;
the probe records this and never interprets a floating zero as cancellation.

The separate large-order scan uses **ideal log coordinates only** and gives
ratios approaching `0.651`. It constructs no primes and proves no population
bound. Seven factors lie below the newly paid count threshold once `K>1792`,
but the small literal samples are not below it. The eventual count payment
does not certify their finite-order bound either. These qualifications
prevent the small numerical regressions from being represented as an
estimate for the surviving cofinal mass.

The [proof audit](riesz-low-offset-pair-audit.json) records 15 public proofs,
focused warning-as-error compilation, namespace lint and transitive axioms.
Work remains local; the published README and explorer endpoint are unchanged.
The next unpaid quantity is the combined signed prime/cofactor moment over
these and the other retained rows. This slice proves no numerical floor,
source decay, starting order or zero exclusion for that whole sum.
