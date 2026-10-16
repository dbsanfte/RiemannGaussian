# Independent final short-annihilator extractor review A

Verdict: PASS. No correction requested. This is an independent mathematical and source-contract review of the exact final bytes; no numerical experiment, native edit, build, or literature-priority certification is claimed.

## Exact targets and evidence

- short-annihilator-extractor.md10375 bytes; SHA256433d10d8c413ad8cbe7ecb09bbafe0794559afa8b2b535e3667b9491950c1131.
- small-order-separator.md5679 bytes; SHA2565fd92268584613b0ffe9b1c12e076dd3ef93a52d53cb3d76c799b2a747793109.
- uniform-preprocessing.md8770 bytes; SHA256375460025deb024f03c3bc3415fc7990ca9a50b16cc9e272a19b17dd08d2e4fd.
- uniform-primary-pins.json190 bytes; SHA2562afdb1fed3d05a2fab7560a0927cf1b476056156d6b7e0259a5304b34293436b.

Lau--Wu primary PDF221207 bytes SHA2564cc9dba73064795de434d6b42baca0743347313b6a242f5439c9ed979ddd4368; regenerated layout text53442 bytes SHA25699d222b33b06d55c1ac00637eb67db393417439e8305e1493bab58e40df5a8d5. The copies under primary/ match my independently downloaded and inspected originals. Primary URL https://hkumath.hku.hk/~imr/IMRPreprintSeries/2007/IMR2007-4.pdf . Theorem1 printedp2 and its composite-modulus proof Section2 printedpp4--6 were inspected, not merely a search summary. My earlier separate Burgess audit remains frozen5513/6a8e3e1518b022bf1427cb383b1382375ed5dee6fcd1fdd9593bb7a626fad8a5.

Harvey--Hittmeir primary PDF412025 bytes SHA2560e957bacebc0b74f363436ab09b70085f4ad83c45dee93bda8aef19fbfdcbff0; inspected Theorem1.1 printedp3 and deterministic multitape model printedp2. Its fingerprint matches uniform-primary-pins.json. This external theorem concerns large GLOBAL order; the preprocessing proof separately handles the local implications.

## Algebra and separator

The root extractor needs only odd local orders with integer indices<m. No primality, distinctness, coprimality or lower order magnitude is silently used. After removing the2-part of nonzero K, its odd part remains divisible by both odd local orders. Equation(4), b^v=(a^(P−1))^(K0/r_P)=1, proves the local trial order divides v even when r_P and v share factors. The Q argument is identical. Odd powering preserves each local order's full2-primary factor. All powers use known units and polylog-bit exponents, and no order factorization is required.

The separator's exact-common-order guarantee is sufficient and necessary for the case split. Its self-contained monic product/remainder construction, increasing-row scan and descending larger-i-first localization inspect increasing positive exponents. An earlier unit product certifies every factor unit. A saturated leaf, with all earlier exponents certified units, forces BOTH exact local orders to equal that leaf exponent. Unequal local orders therefore cause a proper gcd rather than a spurious common-lcm output. NoHit is impossible when both local orders divide indices<m; outside this promise it certifies both orders exceed the actual H² search cap. Repeated nodes and zero divisors cause no inversion gap. The soft-sqrtm bit cost includes row gcds and O(H)-total-degree sibling evaluation.

## Burgess applicability and algorithmic branches

Lau--Wu Theorem1 applies to all nonprincipal characters modulo cubefree q, not only prime moduli or almost-all characters. The Jacobi character for distinct odd primes N=P Q is nonprincipal (indeed primitive), and N is squarefree. Thus its least character nonresidue has value−1. A gcd discovered during enumeration is already a proper factor. The Legendre character for either hidden prime is a second legitimate instance.

Fix any positive epsilon<5/32−1/(4sqrt(e)). The strict margin absorbs the primary implied constant in a cutoff N^(5/32). Balanced hidden primes ell<=C sqrtN yield the strict half-exponent margin needed for N^(5/64), including the fixed C. This concerns the prime with larger2-adic valuation, which need not be numerically larger. No GRH, quasi-RH or prime-order property is involved.

The initial scan performs ONLY gcd and Jacobi computation per candidate and invokes the separator once after finding Jacobi−1. If the2-adic valuations of P−1,Q−1 were equal, the opposite Legendre signs would force different local2-primary orders after odd powering. Therefore an exact equality return certifies unequal valuations. In phase2, a nonresidue at the larger-valuation prime has its full2-part, strictly above the maximum possible2-part in the other field. The separator must then return a factor. Its common-order outputs at intermediate bases may safely be skipped. All cases are exhaustive under the promises.

## Bit cost, totality and uniform composition

The first scan costs soft N^(5/32) plus one soft-sqrtm separator. The second has at most ceil(N^(5/64)) bases, each costing soft-sqrtm; all K reads, stripping, gcds and modular powers are included in fixed logarithmic factors. The arithmetic identity5/64+1/12=31/192<1/6 and5/32=30/192 is correct. The explicit m=Theta(N^(1/6)) assumption is present where substituted. The more general first bound is retained if m lacks that upper comparison. Polylogarithmically many bits of K are allowed; its multiplier need not be bounded.

Both rational-power cutoffs are exactly computable by fixed integer powers and roots. Under a uniform fixed balance constant and the theorem promises, Burgess guarantees success beyond a finite N threshold. Ordinary deterministic factoring after a failed bounded scan therefore makes the algorithm total without the algorithm knowing this threshold. The finite exceptional costs are absorbed by an asymptotic constant; no explicit Burgess threshold or practical improvement is claimed. Unexpected NoHit likewise has an explicit fallback; it cannot occur under the exact order promises.

The separately supplied uniform-preprocessing proof returns a factor or a base with odd local orders>16m² and indices<m, at soft-m bit cost. It invokes the primary large-GLOBAL-order theorem correctly only when16m²<N−1; the other branch has affordable trial division. Its universal detector and common-order squaring argument recover a common full order r>16m² or a factor; r²|phi(N) then recovers P+Q as (N+1) modr². Therefore combining preprocessing and this extractor gives a uniform conditional soft-m route on the stated balanced range, provided a short nonzero annihilator of the chosen base is supplied. No prime or disjoint local-order promise is needed.

This composition does NOT acquire K. It does NOT transfer the original strong-global-order collision-coverage/controller theorems to the redesigned base. It does NOT prove the original long-query acquisition or the Lean/full-bit sixth-rate theorem. The positive result is the expanded supplied-certificate recovery interface, with the acquisition gap explicitly retained.
