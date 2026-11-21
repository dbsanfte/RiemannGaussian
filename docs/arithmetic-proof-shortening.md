# An arithmetic route to a shorter proof

The published principal-character proof uses 165,070 archive modules. The independent route below uses 27 selected Alpöge modules for the analytic implication from arithmetic to RH, together with native Lean and Mathlib dependencies. Its outstanding step is a bound on finite sums of the ordinary Möbius function. The total dependency count of a completed arithmetic proof is unknown. [Published proof and module accounting](research-evidence/alpoge-archive-rh/README.md) · [Source selection and pins](../vendor/alpoge-zeta/README.md).

## The quantity to bound

For each integer $n\ge2$, set $N=n^4$ and give each ordinary prime in $(N/4,N)$ a weight that rises from zero at $N/4$ to one at $N/2$ and falls to zero at $N$. Let $D(N)$ be $N\log(2)/2$ minus the sum of those weights times $\log p$. A positive value means a shortage of primes. The window test sums the positive parts with weights $1/n^3$, so a surplus at one sample cannot erase a shortage at another. [Prime weights and window criterion](../scripts/CheckAlpogeFixedPrimeBand.lean).

Crossley gives a related RH criterion for every fixed positive integer power. At fourth powers it uses the same ordinary-prime deficit $D$ and requires $D(n^4)\ge 0$ at every integer $m\le n\le m^2$ on arbitrarily late blocks. [A prime-window criterion for RH on perfect powers](https://doi.org/10.5281/zenodo.24411621).

Put $U=n^2$. Two applications of Möbius inversion give a signed quadratic sum
```math
Q_N(V)=\sum_{1\le a,b\le V}\mu(a)\mu(b)
       \sum_{1\le j\le N/(ab)} F\!\left(\frac{N}{abj}\right),
```
where $F$ is the explicit centered kernel in the Lean source. With $V=U$, the error $|D(N)+Q_N(U)|$ is at most a constant times $n^2$, including the contribution from proper prime powers. Dividing by $n^3$ and summing costs at most a logarithm. Large **negative** values of the quadratic sum therefore correspond to prime shortfalls. [Centered kernel, inversion and error estimate](../scripts/CheckAlpogeFixedPrimeBandCentered.lean).

## How far the cutoff can move

* **An unconditional trim.** Take $s_n=n-\lfloor(n/8)^{1/3}\rfloor$ and $V=s_n^2$. We proved that the same $O(n^2)$ error holds at this smaller cutoff. An exact convolution identity evaluates $Q_N(s_n^2)$ as a polynomial of degree at most four in the values $\mu(1),\ldots,\mu(s_n)$. This reduces the input list while preserving the square-window criterion. [Cutoff and error](../scripts/CheckAlpogeFixedPrimeBandCorner.lean) · [Exact evaluation from the shorter list](../scripts/CheckAlpogeFixedPrimeBandShortInverse.lean).
* **A cutoff chosen at each sample.** Choose an integer $0\le L\le U/4$, put $V=U-L$, and write $M_V(j)=\sum_{V<d\le j}\mu(d)$. Double summation by parts bounds the contribution with both indices above $V$ by $(27/V)\sum_{V<j\le U+2L}M_V(j)^2$. This replaces those pairs by a bound involving one-dimensional partial sums. At the largest cutoff removal the quadratic sum uses indices through about $3U/4$, and the partial sums reach about $3U/2$. [Corner estimate and cutoff score](../scripts/CheckAlpogeFixedPrimeBandCorner.lean).

## The remaining estimate

For each $n$, let $S_n$ be the minimum over the allowed $L$ of the prefix-square bound above minus $Q_N(U-L)$. The uncut choice $L=0$ is included. Lean proves that RH is equivalent to the existence of one $C\ge0$ such that, for arbitrarily large integers $m$,
```math
\sum_{n=m}^{m^2}\frac{\max(S_n,0)}{n^3}\le C(1+2\log m).
```
A uniform lower bound $Q_N(n^2)\ge -K n^2$ would pay for the window term by term through the harmonic sum. The window criterion also allows exceptional samples. The trimmed statistic $-Q_N(s_n^2)$ gives the same equivalence. Fixing $L=\lfloor U/4\rfloor$ instead gives a sufficient condition. A proof of any of these bounds **from arithmetic** would close this route. [Exact Lean statements](../scripts/CheckAlpogeFixedPrimeBandCenteredBounds.lean).

Baiying Liu’s checked zero-free half-plane gives a power bound for the trimmed and minimum statistics. For each $\alpha>1.499828077680395788$ there is a fixed $0<\delta\le1$ and arbitrarily large $m$ with window mass at most $m^\alpha$ up to $\lceil m^{1+\delta}\rceil$. Both the growth rate and the window endpoint matter when comparing this with the target. [Liu specialization](../scripts/CheckAlpogeFixedPrimeBandLiu.lean) · [Source pin and adapter](../scripts/verify_liu_suzuki.py).

## The import saving in the forward implication

The forward proof of the logarithmic criterion can be imported on its own. Lean reports **10,777 modules** when a fresh file imports `CheckAlpogeFixedPrimeBandCorner`, compared with **15,562** for the file that proves both directions. Moving the sufficient condition into the smaller module removes **4,785 imports** from this conditional step. Both totals include the proof module itself and the pinned toolchain, Mathlib and package dependencies. The published principal-character proof uses a different counting convention for its archive modules. [Forward proofs and import report](../scripts/CheckAlpogeFixedPrimeBandCorner.lean) · [Equivalences and import report](../scripts/CheckAlpogeFixedPrimeBandCenteredBounds.lean).

Of the 10,777 modules, 27 come from Alpöge’s selection. Four are local proof scripts and two are native library modules. These six repository modules construct the ordinary-prime criterion, rewrite it using Möbius inversion, and bound the omitted corner. The reverse implication uses the larger native zero-free library. The Liu comparison is optional.

## Verify the arithmetic slice

From the repository root with the pinned Lean 4.34.1 toolchain, the first command checks the forward implication. The second also checks the converse, block cancellation and exact evaluation from the shorter input list.

```sh
python3 scripts/verify_alpoge_mined_bounds.py --fixed-prime-sieve
python3 scripts/verify_alpoge_mined_bounds.py --fixed-prime-bounds --fixed-prime-block --fixed-prime-short-inverse
```

Each command builds the native prerequisites, checks the selected Alpöge sources and local proofs, and invokes the standalone kernel checker. To include the quantitative comparison, first run `python3 scripts/verify_liu_suzuki.py /path/to/pinned/liu/checkout`, then add `--fixed-prime-liu` to the command above.

The forward-only standalone run replayed all **33** selected archive and repository modules. The combined run replayed **41 modules**, comprising the 27 pinned Alpöge modules, nine local fixed-band proof modules and five native modules. The axiom guards on the new window theorems allow only `propext`, `Classical.choice` and `Quot.sound`. The published archive proof has its own Lean 4.33.1 verifier and receipt. [Arithmetic verifier](../scripts/verify_alpoge_mined_bounds.py) · [Archive proof verification](research-evidence/alpoge-archive-rh/README.md).
