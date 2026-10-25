# Independent composite integration review

22 October 2026. Read `composite-colour-catalog.md` and `composite-gauss-supply.md`; checked against the amended `../semiprime-composite-modulus-20261022/composite-modulus-source.md` (actual absolute source is `/tmp/semiprime-composite-modulus-20261022/composite-modulus-source.md`). Verdict: arithmetic/construction PASS with the two narrow integration clarifications below. No repository edits, new backend, examples or agents.

## All-input source and public screens

The retained P,Q>16m², P<=Q and N<=m^6 give P<=m³ and Q<m⁴/16. With a<m and |ellrow|<3m², the exact own-tag index obeys

    13<I<(17/16)m²+3<4m², m>=3.

Hence no balanced-input caveat is needed for source coverage on the retained branch. The original exact row/Fermat identity needs only unit tags, not prime m. The nonzero scalar leaf bound follows from N>256m⁴ and L<=4m² and is unchanged by composite colors.

Use the stronger public screen: factor m publicly and test gcd(N,p) for each prime p|m, plus gcd(N,ell). Each gcd is 1 or a proper factor because N is composite and the tested integer is prime. This avoids any gcd(N,ell*m)=N saturation and eliminates a finite-input exception in that screen. Both reviewed reports currently phrase their screen as the combined product followed by asymptotic/finite handling; that is mathematically valid as stated, but the separate-prime version gives the cleaner unconditional input contract and should replace it in integration. Factoring public m is paid within soft m regardless of whether the sieve already supplies its factors.

## Catalog and boundary proof

The exact mask kappa+(4aj)^-1 Squares(Z/m) follows by the bijection h->b+2ah, including zero and nonunit discriminants. For each odd prime power p^e, even valuations and square units give the stated count; multiplication by a local nonsquare makes the two nonzero images disjoint and shares only zero. CRT independent local signs classify ALL unit multiplier squareclasses, including their action on nonunit squares. No Jacobi-only shortcut is used.

The total colored output is product_p 2|Squares(Z/p^e)| <=m product_p(1+p^-e)<=m H_m. This charges cross-color repeated zeros and partial-zero components. Enumerating local square images costs sum p^e<=m, deduplicates within each color, and the incremental colored CRT lists have sizes bounded by the final output. Deterministic sorting, local nonsquare search, CRT constants and per-row color assignment all fit soft O(m+J). Thus this is actual acquired output, not only a descriptor bound.

The A/B/C translated-mask boundary equations require only an ordered residue set, so they survive unchanged with unequal palette sizes. Per-depth TOTAL degree is bounded by the summed colored output, and each row requests nodes only in its assigned palette. Joint monic MPE therefore costs soft O(m+J), including all colors, repeats and requested outputs. K=0 symbolic cancellation is retained. Proper and saturated boundary gcds retain original scalar exponent ledgers; no root-difference division or unlicensed cancellation occurs. The stated large-order/source promises must still be supplied by the preparation/controller, as the report explicitly says.

## Supply and aggregate exceptions

Selecting prime ell=3 modulo 4 above 2u, u=ceil(N^(1/6)), and then m=(ell-1)/2 guarantees odd m>=u and ell=2m+1. A fixed progression prime-existence bound and a paid growing sieve yield ell,m=Theta(u); no growing-modulus least-prime theorem or primality of m is assumed. This review checks the mathematical implication and work accounting; it does not independently reverify the numerical constants transcribed from the inspected explicit-PNT source. Root/source author verification of that primary theorem remains the cited supply evidence. The proof also works with a fixed-modulus asymptotic PNT and a finite effective constant.

The packed primitive accepts arbitrary character order dividing ell-1. Its E_a projectors correctly handle proper-divisor character components and nonunit intermediate exponents. Restricting native tags j to units is ESSENTIAL: then chi^j is nontrivial iff chi is nontrivial, every component has odd order and chi(-1)=1. Thus g_j g_-j=D=E0+(1-E0)ell and the reciprocal C_N identity hold even on nonprimitive nontrivial components. E0 selects only the trivial component. Exact integer a_-j=a_j and centered carries survive; all sums/products must be over units and pair count is phi(m)/2. Three common vectors plus scalar/index metadata remain a paid representation; expanding all pair arrays is not claimed.

## Remaining assumptions and actual progress

The ell-first supply and explicit composite palette construction remove the earlier prescribed-prime-progression gap and prime-row-mask restriction for these ACQUIRED objects. Prepared gamma and its decoder contract remain inherited obligations; a paid small-q-order screen can factor, supply an annihilator, or certify the required q-order lower bounds without assuming gcd(m,orders)=1. Existing prime-field low-fiber/denominator-rich Lean theorems do not automatically generalize.

No order/recovery guarantee is transferred to ell or a Gauss-derived seed. No whole family of rank-m Gauss targets is expanded at soft m cost. The long H_c products, restriction-stable difference aggregate and universal sixth-rate acquisition remain uncomputed. The reviewed supply and catalog are genuine positive construction repairs, not an H-zero evaluator or a finished factoring algorithm.
