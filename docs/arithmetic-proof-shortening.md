# An arithmetic route to a shorter proof

The published principal-character proof uses 165,070 archive modules. The independent route below uses 27 selected Alpöge modules for the analytic implication from arithmetic to RH, together with native Lean and Mathlib dependencies. Its outstanding step is a bound on finite sums of the ordinary Möbius function. The total dependency count of a completed arithmetic proof is unknown. [Published proof and module accounting](research-evidence/alpoge-archive-rh/README.md) · [Source selection and pins](../vendor/alpoge-zeta/README.md).

## The quantity to bound

For each integer $n\ge2$, set $N=n^4$ and give each ordinary prime in $(N/4,N)$ a weight that rises from zero at $N/4$ to one at $N/2$ and falls to zero at $N$. Let $D(N)$ be $N\log(2)/2$ minus the sum of those weights times $\log p$. A positive value means a shortage of primes. The window test sums the positive parts with weights $1/n^3$, so a surplus at one sample cannot erase a shortage at another. [Prime weights and window criterion](../scripts/CheckAlpogeFixedPrimeBand.lean).

Put $U=n^2$. Two applications of Möbius inversion give a signed quadratic sum
```math
Q_N(V)=\sum_{1\le a,b\le V}\mu(a)\mu(b)
       \sum_{1\le j\le N/(ab)} F\!\left(\frac{N}{abj}\right),
```
where $F$ is the explicit centered kernel in the Lean source. With $V=U$, the error $|D(N)+Q_N(U)|$ is at most a constant times $n^2$, including the contribution from proper prime powers. Dividing by $n^3$ and summing costs at most a logarithm. Large **negative** values of the quadratic sum therefore correspond to prime shortfalls. [Centered kernel, inversion and error estimate](../scripts/CheckAlpogeFixedPrimeBandCentered.lean).

## How far the cutoff can move

* **An unconditional trim.** Take $s_n=n-\lfloor(n/8)^{1/3}\rfloor$ and $V=s_n^2$. We proved that the same $O(n^2)$ error holds at this smaller cutoff. An exact convolution identity evaluates $Q_N(s_n^2)$ as a polynomial of degree at most four in the values $\mu(1),\ldots,\mu(s_n)$. This reduces the input list while preserving the square-window criterion. [Cutoff and error](../scripts/CheckAlpogeFixedPrimeBandCorner.lean) · [Exact evaluation from the shorter list](../scripts/CheckAlpogeFixedPrimeBandShortInverse.lean).
* **A cutoff chosen at each sample.** Choose an integer $0\le L\le U/4$, put $V=U-L$, and write $M_V(j)=\sum_{V<d\le j}\mu(d)$. Double summation by parts bounds the contribution with both indices above $V$ by $(27/V)\sum_{V<j\le U+2L}M_V(j)^2$. This replaces those pairs by a bound involving one-dimensional partial sums. At the largest cutoff removal the quadratic sum uses indices through about $3U/4$, and the partial sums reach about $3U/2$. [Corner estimate and cutoff score](../scripts/CheckAlpogeFixedPrimeBandCorner.lean).

## Discarding the early multiples

There is also a cutoff on the contributing integer $k=abj$. For
$V\le K\le V^2$, the coefficient of the centered kernel at each $k\le K$
in the quadratic form is $\mu(k)$ when $k\le V$ and $-\mu(k)$ when $V<k\le K$.
Completing both divisor sums gives this identity because two omitted divisors
would have product greater than $V^2$. Consequently the contribution through
$K$ costs at most a constant times $K^2(1+\log N)/N$. At the fourth power
$N=n^4$, take $K_n=\lfloor n^3/\lceil\sqrt{1+\log n}\rceil\rfloor$ to make
that error $O(n^2)$ simultaneously for every allowed $V$. [Coefficient identity and error bound](../scripts/CheckAlpogeFixedPrimeBandCentered.lean).

The late part of the quadratic form equals the outer corner minus the linear tail
```math
T_n=\sum_{K_n<k\le n^4}\mu(k)F(n^4/k).
```
The energy allowance is at least the outer corner for every allowed cutoff.
Both are zero at $L=0$, so the minimum of the late-multiple scores is exactly
$T_n$ at every sample. The cutoff on $k$ is distinct from the shorter input
cutoff on the divisors $a,b$. [Exact adaptive minimum](../scripts/CheckAlpogeFixedPrimeBandCorner.lean).

## Removing the upper half of the linear tail

Let $L$ be the triangular lattice sum and put $G(y)=L(y)-2L(y/2)$.
Finite Möbius inversion gives $\sum_{k\le N}\mu(k)G(x/k)=0$ for $8\le x\le N$.
The linear main terms of the two lattice sums cancel, giving $|G(y)|\le300/y$.
These two properties let us change the kernel throughout the tail. Put
$c=1-\gamma$ and define

```math
J(y)=cG(y)-\int_1^2 (1+1/t)G(y/t)\,dt.
```

For $N\ge16$ the complete Möbius sum of $J(N/k)$ vanishes exactly, since
every scale $N/t$ in the integral is at least eight. On $1\le y\le2$,
$G(y)=y-1$ and the integral equals $(y-1)\log y$, so $J(y)=F(y)$.
The replacement weight $F-J$ therefore vanishes at every $k>N/2$.
The correction on the already discarded prefix costs at most $1500K^2/N$,
by $|J(y)|\le1500/y$. This gives a shorter linear statistic

```math
U_n=\sum_{K_n<k\le\lfloor n^4/2\rfloor}\mu(k)(F-J)(n^4/k),
\qquad |T_n-U_n|\le1500n^2.
```

Lean proves that the positive-part window masses differ by at most
$1500(1+\log B)$ on every $[m,B]$ with $m\ge2$. Their logarithmic
square-window criteria are equivalent. A signed bound for $U_n$ on
arbitrarily late windows would thus close the arithmetic route.
[Correction, error and forward implication](../scripts/CheckAlpogeFixedPrimeBandFirstQuotient.lean).

On the next quotient block, Lean proves $(F-J)(N/k)\ge1/5$ for
$2N/5\le k\le4N/9$. For an interval of length $D$ there, at most
$D/j^2+1$ integers are multiples of $j^2$. Summing over $2\le j\le\sqrt N$
leaves at least $D/4-\sqrt N$ squarefree indices. Lean uses this count to
prove that the retained absolute term sum is at least $n^4/2000$ for every
$n\ge32$. On **every** square window with $m\ge32$ this gives

```math
\sum_{n=m}^{m^2}\frac{1}{n^3}
  \sum_{K_n<k\le n^4/2}\big|\mu(k)(F-J)(n^4/k)\big|
  \ \ge\ \frac{m^4}{8000}.
```

The open criterion takes the positive part after the signed inner sum. Taking
absolute values term by term would exceed its logarithmic budget even on
arbitrarily selected late windows. [Unsigned lower bound from the second block](../scripts/CheckAlpogeFixedPrimeBandFirstQuotient.lean).

## Cancellation across quotient blocks

Write $M(k)=\sum_{a\le k}\mu(a)$ and $w_n(k)=F(n^4/k)$. Taking the same
endpoint weight on both sides of each quotient boundary makes the boundary
terms cancel exactly under summation by parts. Lean proves that $T_n$ differs
from the shared-prefix sum below by at most a constant times $n^2$.

```math
\sum_{k=K_n}^{n^4-1} M(k)\bigl(w_n(k)-w_n(k+1)\bigr).
```

The upper endpoint vanishes because $F(1)=0$. The lower endpoint costs
$O(n^2)$ by the cutoff estimate. This keeps the signed contributions from
the quotient blocks together before taking the positive part. The window
bound on that combined sum remains open. [Summation by parts and endpoint bound](../scripts/CheckAlpogeFixedPrimeBandCentered.lean).

## The remaining estimate

For each $n$, let $S_n$ be the minimum over the allowed $L$ of the prefix-square bound above minus $Q_N(U-L)$. The uncut choice $L=0$ is included. Lean proves that RH is equivalent to the existence of one $C\ge0$ such that, for arbitrarily large integers $m$,
```math
\sum_{n=m}^{m^2}\frac{\max(S_n,0)}{n^3}\le C(1+2\log m).
```
A uniform lower bound $Q_N(n^2)\ge -K n^2$ would pay for the window term by term through the harmonic sum. The window criterion also allows exceptional samples. The trimmed statistic $-Q_N(s_n^2)$ gives the same equivalence. Fixing $L=\lfloor U/4\rfloor$ instead gives a sufficient condition. A proof of any of these bounds **from arithmetic** would close this route. [Exact Lean statements](../scripts/CheckAlpogeFixedPrimeBandCenteredBounds.lean).

The same logarithmic bound with $T_n$ in place of $S_n$ is equivalent to RH.
The forward proof for $T_n$ uses the linear Möbius tail and its error bound.
It is in `CheckAlpogeFixedPrimeBandCentered`. [Forward statement](../scripts/CheckAlpogeFixedPrimeBandCentered.lean) · [Converse](../scripts/CheckAlpogeFixedPrimeBandCenteredBounds.lean).

The signed off-diagonal terms of the square give a sufficient estimate.
Write $T_n=\sum_k a_{n,k}$ with
$a_{n,k}=\mu(k)F(n^4/k)$ on the late range. Lean bounds the diagonal
$\sum_k a_{n,k}^2$ by a constant times $n^4$, so its weighted window cost
with weight $1/n^5$ is at most logarithmic. The inequality
$2\max(T_n/n^2,0)\le (T_n/n^2)^2+1$ then shows that a logarithmic upper
bound for $\sum_{n=m}^{m^2}n^{-5}\sum_{k\ne l}a_{n,k}a_{n,l}$ suffices on
arbitrarily late windows. The signs of the pairs enter before the sum is
bounded. [Diagonal budget and forward implication](../scripts/CheckAlpogeFixedPrimeBandCentered.lean).

For a pair of distinct multiples, write the smaller and larger indices as
$ga,gb$ with $\gcd(a,b)=1$ and $a<b$. We proved a uniform logarithmic window
bound for the **absolute** contribution of every pair with $b\ge a^3$.
To see the saving, put $N=n^4$. The kernel at $ga$ is $O((N/(ga))^{-3/4})$.
Since $gb\le N$ and $a\le b^{1/3}$, this is $O(b^{-1/2})$. For fixed $b$
there are at most $b^{1/3}$ choices of $a$ and $N/b$ choices of $g$.
The resulting bound is $O(N\sum_{b\ge1}b^{-7/6})$ per sample. With weight
$n^{-5}$ it sums to $O(1+\log B)$ on every window $[m,B]$ with $m\ge2$.
All integer ratios are included. On the same original tail, fix $H$ and
select at most $H\lfloor N/l\rfloor^2$ earlier partners for each larger
index $l$. Both kernel factors are $O((N/l)^{-3/4})$. Each row costs
$O(H\sqrt{N/l})$ in absolute value, hence all rows together cost $O(HN)$.
In particular, it suffices to bound the signed sum over pairs with both
$a<b<a^3$ and $l-k>H\lfloor N/l\rfloor^2$.
[Reduced-ratio and nearby-pair window bounds](../scripts/CheckAlpogeFixedPrimeBandRatios.lean).

Baiying Liu’s checked zero-free half-plane gives a power bound for the trimmed and minimum statistics. For each $\alpha>1.499828077680395788$ there is a fixed $0<\delta\le1$ and arbitrarily large $m$ with window mass at most $m^\alpha$ up to $\lceil m^{1+\delta}\rceil$. Both the growth rate and the window endpoint matter when comparing this with the target. [Liu specialization](../scripts/CheckAlpogeFixedPrimeBandLiu.lean) · [Source pin and adapter](../scripts/verify_liu_suzuki.py).

## An exact rational window test

At $N=n^4$, group the tail by $j=\lfloor N/k\rfloor$. For a cutoff $K$,
the $j$th block is
$\max(K,\lfloor N/(j+1)\rfloor)<k\le\lfloor N/j\rfloor$.
Write $z=1-jk/N$. Each reciprocal ramp is affine in $N/k$ on this block.
The variable part of the log is $-\log(1-z)$, with $0\le z<1/(j+1)$.
Keeping $p=1+\lfloor\log_{j+1}(n^2)\rfloor$ terms of its series costs
at most $4n^2$ per sample. The block score then uses only the sums of
$\mu(k)z^i$ and $\mu(k)z^i/k$ for $0\le i\le p$.
[Quotient moments and error bound](../scripts/CheckAlpogeFixedPrimeBandMoments.lean).

Use the integer cutoff
$K=\lfloor n^3/(1+\lfloor\sqrt{1+\lfloor\log_2n\rfloor}\rfloor)\rfloor$.
If $r=1+\lfloor\log_2(n^2)\rfloor$, the harmonic number $H_{2^rj}$
approximates $\log j+\gamma+r\log 2$. A rational partial sum for $\log 2$
then gives rational coefficients for all of the moments at an additional
cost of at most $8n^2$ per sample. With $P_n$ the sum of these rational
block scores, the arithmetic statement is that one integer $C$ works
on arbitrarily late square windows.

```math
\sum_{n=m}^{m^2}\frac{\max(P_n,0)}{n^3}
\le C\bigl(1+\lfloor\log_2m\rfloor\bigr).
```

Lean checks both directions of this criterion. Every finite inequality uses
integer and rational operations. [Rational forward theorem](../scripts/CheckAlpogeFixedPrimeBandMoments.lean) · [Exact equivalence](../scripts/CheckAlpogeFixedPrimeBandCenteredBounds.lean).

## The rational test with fewer Möbius inputs

The same rational approximation gives a uniform per-multiple error of at
most $12/n^2$. For $V^2\le N\le2V^2$, double Möbius inversion bounds the
change in the whole quadratic sum by $4NE$ whenever each weight changes by
at most $E$. Three linear sums contribute at most $NE$ each. In the
remaining corner both divisors lie in $(V,2V]$, and each pair contributes
at most one multiple. Thus the corner contributes at most $V^2 E\le NE$.
With $N=n^4$ and $V=s_n^2$, replacing all the weights costs at most $48n^2$.
[Perturbation bound](../scripts/CheckAlpogeFixedPrimeBandCentered.lean) · [Rational weights](../scripts/CheckAlpogeFixedPrimeBandMoments.lean).

One inverse step under Dirichlet convolution evaluates both factors in the
rational quadratic sum. The result is a rational polynomial of degree at
most four in just $\mu(1),\ldots,\mu(s_n)$. Lean proves that its negative-part
window mass differs from the original prime-deficit mass by $O(1+\log b)$
on $[m,b]$. The integer logarithmic criterion for this mass is equivalent
to the preceding rational test. [Evaluation and window equivalence](../scripts/CheckAlpogeFixedPrimeBandShortInverse.lean).

## The import saving in the forward implication

The forward proof of the logarithmic criterion now uses **5,339 modules**. It used **10,777** at commit `f04c60e9`. Replacing `import Mathlib` in two archive headers with specific imports removes **5,438 modules** from that same implication. The module with both directions uses **15,563** because the converse imports the larger native zero-free library. These totals include the proof module itself and all toolchain and package dependencies. The published principal-character proof counts archive modules. [Forward proofs and import report](../scripts/CheckAlpogeFixedPrimeBandCorner.lean) · [Equivalences and import report](../scripts/CheckAlpogeFixedPrimeBandCenteredBounds.lean).

The direct tail implication uses **5,337 modules** and the adaptive cutoff
implication uses **5,339**. Each uses 27 Alpöge modules and two native library
modules. The direct tail imports three local proof scripts. The adaptive
case adds the corner proof and Mathlib’s natural root lemmas. The Liu
comparison is optional. The exact rational implication adds one script to the
direct tail and uses **5,338 modules**. The half-length linear tail and
reduced-ratio implications each use **5,338 modules**. The short-input rational implication uses **5,341
modules**. [Pinned sources and the two import headers](../vendor/alpoge-zeta/README.md).

Alpöge’s `zeroFree_of_rpow_window` consumes a pointwise bound on the smoothed
prime sum. The existing path uses the archive’s `landau_window` directly and
therefore accepts the integrated bound from the fourth-power samples.
`mertens_upper` bounds a global von Mangoldt sum by `log y + 2`.
`Formalism.ZF.gzPNT` bounds the smoothed prime error at the scale
`y * exp (-c * sqrt (log y))`. The first result leaves the window bound
as an input, and both unconditional estimates are too weak to pay for the
logarithmic mass. [Pointwise window lemma](../vendor/alpoge-zeta/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean) · [Integrated Landau theorem](../vendor/alpoge-zeta/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean).

## Verify the arithmetic slice

From the repository root with the pinned Lean 4.34.1 toolchain, the first command checks the forward implication. The second also checks the converse, block cancellation and exact evaluation from the shorter input list.

```sh
python3 scripts/verify_alpoge_mined_bounds.py --fixed-prime-sieve
python3 scripts/verify_alpoge_mined_bounds.py --fixed-prime-bounds --fixed-prime-block --fixed-prime-short-inverse
```

Each command builds the native prerequisites, checks the selected Alpöge sources and local proofs, and invokes the standalone kernel checker. To include the quantitative comparison, first run `python3 scripts/verify_liu_suzuki.py /path/to/pinned/liu/checkout`, then add `--fixed-prime-liu` to the command above.

The forward selection contains **35** archive and repository modules.
The combined run with Liu replayed **43 modules**, comprising the 27 pinned
Alpöge modules, twelve local fixed-band proof modules and four native modules.
A final kernel check replayed the centered, reduced-ratio and half-tail modules
after the unsigned lower bound was added.
The axiom guards allow only `propext`, `Classical.choice` and `Quot.sound`.
The published archive proof has its own Lean 4.33.1 verifier and receipt.
[Arithmetic verifier](../scripts/verify_alpoge_mined_bounds.py) · [Archive proof verification](research-evidence/alpoge-archive-rh/README.md).
