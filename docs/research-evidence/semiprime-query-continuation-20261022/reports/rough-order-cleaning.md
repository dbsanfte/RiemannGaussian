# Paid rough-order cleaning, including saturated recovery

2026-10-22. Compatibility recheck against strong-order-route.md. The smooth projection, collapse recovery, and prime/semiprime rough-order shape are inherited from the October 2 work and the October 16 constructive-frontier index. This is not a new acquisition advance. The remaining prime/semiprime-order branch is not a complete factoring algorithm; see order-cleaning-independent-review.md for provenance and the newer setup dependencies.

## Inputs and public exponent

Start with the existing prepared unit beta for N=PQ, P<=Q, N<=m^6. Its local orders r_P,r_Q are odd, coprime, and exceed B=16m². Choose public real threshold H=Cm with fixed C>=1 (integer rounding is harmless). Sieve the primes ell<=H. For each choose the least e_ell with ell^e_ell>=N; this is found by exact integer multiplication, not floating logs. Put

 f_ell=ell^e_ell,       M=product_(ell<=H) f_ell.

Every f_ell has at most log2N+log2H bits. Even the elementary count of at most H primes gives log2M=O(H logN); the sieve, exact powers, balanced product tree and explicit integer M therefore cost soft O(m) bits. Its complete prime-power factorization is acquired. Every ell-adic valuation of any r<N is at most e_ell.

Compute b=beta^M mod N, costing soft O(log M * log N)=soft O(m). The local orders of b are exactly the parts of r_P,r_Q supported on primes>H. They remain odd and coprime.

## Saturation is recovered in soft m without Burgess

If b=1 modulo N, both original local orders divide M. For every public prime-power leaf f_ell, acquire

 z_ell=beta^(M/f_ell) modulo N.

This is NOT done by independently exponentiating each quotient of size log M. Use the acquired balanced product tree. For a node with leaf product A and sibling products A_left,A_right, retain v=beta^(M/A). The children receive v^(A_right) and v^(A_left). Root v=beta. At each tree depth, the sum of bitlengths of the sibling exponents is O(log M + number_of_nodes). Thus the total modular-power bit work is soft O(log M * log N), with only O(log number_of_leaves) levels. Node storage, exponent products and all gcds are soft O(m). No modular reduction by an unknown group order is used.

Because r_P>1, choose any prime ell dividing r_P. Coprimality implies ell does not divide r_Q. Since r_Q divides M, it divides M/f_ell; hence z_ell=1 modulo Q. Removing the entire ell^e factor makes r_P NOT divide M/f_ell; hence z_ell!=1 modulo P. Therefore gcd(z_ell−1,N)=Q, a proper factor. The algorithm scans ALL acquired leaf gcds, so the proof's hidden choice is not an algorithmic input. This also handles r_P or r_Q having repeated prime factors. No factorization of either order is supplied.

It is valid to start with gcd(b−1,N): a proper result immediately factors, while gcd=N triggers the quotient tree. If gcd=1, both surviving local orders are nontrivial.

## Restore the full prepared contract

Run the exact-first-nonunit detector on b through B. A proper factor finishes. A common order<=B must equal1 by coprimality; thus b=1, already handled above (or can be handled by the same quotient tree if not checked earlier). NoHit retains both local orders>B, with every prime factor>H and global order>B².

Screen b^(m²) through B as in the existing setup. A common order1 would force both b orders to divide m², impossible since they exceed B; otherwise this screen factors or certifies the q-order interface. Thus the original canonical source and bounded-leaf recovery apply unchanged to b.

This costs only a fixed number of soft-m detectors plus the public exponent/tree work. In particular M need NOT have polylog bitlength; its saturation branch is resolved by its acquired factorization and original coprime-order separation, rather than by invoking the polylog-annihilator theorem outside its contract.

## Combination with (N−1)-cleaning

First apply the proved short-exponent cleaning with A=N−1. Its saturated branch is closed by the inherited short-annihilator extractor; otherwise both surviving orders are coprime to N−1. Apply the present smooth-order removal to that retained base. Dividing orders preserves this coprimality. On the final branch each local order is therefore prime to the OTHER FULL FIELD order, as well as being H-rough and large. All intermediate input bases are publicly acquired units; no change of base loses native canonical coverage.

## What the stronger branch really says

The smaller prime P satisfies P<=m³. Its retained order r divides P−1<m³. With H>=m, r has at most TWO prime factors counted WITH MULTIPLICITY: three primes each>m would give r>m³. Thus

 r is a prime, or a product ell_1 ell_2 (possibly ell_1=ell_2),
 r>16m²,       ell_i>H,       (P−1)/r<m/16.

This is a genuine uniform reduction, not a density statement or a supplied factorization. If it has two factors, one is at most sqrt(r)<m^(3/2); neither factor is acquired by the proof. The larger-prime order need not have only two factors: Q<m^4/16 permits up to three prime factors>m. Do not silently impose balance.

A fixed larger C or a polylogarithmically larger H remains soft-m but does not force the smaller order to be prime. Raising H above m^(3/2) would force primality but the explicit M acquisition no longer fits soft-m. This observation concerns this constructor's bit ledger, not a lower bound on different order-cleaning methods.

## Attempted actionable continuation and remaining premise

The retained small coindex t=(P−1)/r<m/16 and prime/semiprime shape suggest P=tr+1. However neither t nor r is numerically known, and enumerating t does not supply r or a residue modulus for P. The already-paid known-modulus residue algorithms require an acquired divisor of P−1; existence of a large rough divisor is not that input. Similarly generic order-finding searches up to P, whose square-root clock can reach m^(3/2), not m. The acquired quotient-exponent tree cannot expose a retained ell because it intentionally excludes all ell>H.

The new sparse norms operate on public cyclic ranks and known-support coefficients; no exact identity was found converting this retained prime/semiprime order shape into a numerical relation of beta. A public exponent family guaranteed to contain one of these retained primes with total acquired bitlength soft-m, or another acquired order relation that separates a local component, would complete a direct route. Neither the present proof nor the existing norm primitive supplies that guarantee.

Accordingly this pass proves the smooth-removal exponent, its fully paid saturated-factor recovery, restoration of all canonical promises, and a universal prime/semiprime reduction for the smaller local order. It does not yet bypass the original collision query or prove sixth-rate factorization.
