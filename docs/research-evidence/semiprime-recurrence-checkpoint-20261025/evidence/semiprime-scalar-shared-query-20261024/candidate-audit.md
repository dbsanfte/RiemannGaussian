# Supplied large global order: one executed factoring candidate

The strongest directly relevant recent primary candidate I checked is Gao–Feng–Hu–Pan, *On Factoring and Power Divisor Problems via Rank-3 Lattices and the Second Vector*, arXiv:2512.19076v1 (22 December 2025), https://arxiv.org/abs/2512.19076. It provides a useful exact residue-to-factor interface, but applying it to the current acquired scalar catalogue does not shorten the query. This is an application audit, not a new factoring result.

## Exact usable theorem and initialization

Theorem 3.1, with its power parameter equal to one, takes explicit integers N,s,m with 0<s,m<N and gcd(m,N)=1, and finds every divisor p of N satisfying p=s modulo m in

    O(ceil(N^(1/4)/m) log^(7+3 epsilon) N)

bit operations, for fixed positive epsilon. The modulus here is an arithmetic residue modulus, not a multiplicative order. One supplied residue suffices; there is no need to know which prime obeys it. A failed gcd(m,N) already factors the semiprime. The theorem is unconditional and uses integer lattice/root computation, so importing it requires no field pivot or unknown-prime oracle.

Execute it at our scale N<=k^6 with a public modulus m=ceil(sqrt(k)). Given the correct explicit residue s, the charge is soft(k), including integer root extraction and checking candidate divisors. But enumerating every residue s costs soft(m+N^(1/4))=soft(k^(3/2)) in the balanced N=Theta(k^6) regime. Early success is allowed; this is the scheduled full-residue budget, not an all-input runtime lower bound. Thus this theorem is a valid consumer for an acquired coarse residue, and does not acquire that residue from a scalar collision family.

Our supplied beta has global order greater than 256k^4 and both local odd orders greater than 16k^2. Neither certificate supplies p modulo m. In particular, the order certificate is an inequality, not an explicit divisor of p-1 from which such a residue could be inferred. The already available nonzero-annihilator consumer likewise starts only after a global equality beta^K=1 has actually been acquired. Feeding it a guessed K, or a merely local collision, changes its hypotheses.

## Testing the paper's complete factoring algorithm instead

Algorithm 4.8 and Proposition 4.9 retain the N^(1/5) exponent (with improved logarithms) in the stated fixed multiplicative prime-size bin. The algorithm explicitly supplies a modulus m of size soft(N^(1/5)), constructs a seed satisfying gcd(alpha^(m^2 i)-1,N)=1 for every i up to its specified search length, and performs the main search. A large *global* order alone does not certify these local gcd conditions. Our existing seed screen concerns powers beta^(k^2), rather than this new m^2; it cannot be silently reused. Even granting the required preparation for free, the published main search still has the stated one-fifth exponent, not a bound decreasing with excess global order. Its second-vector lattice and Coppersmith interface therefore do not instantiate a soft(k) algorithm on the current scalar catalogue.

## Search conclusion and preservation

I found no primary exact compressed-input q-product or selected-resultant theorem in this search that improves the current soft(J+sqrt(Jh))=soft(k^(5/4)) query. This is a search conclusion, not a lower bound. The recent Harvey–Hittmeir large-order result (arXiv:2601.11131v2, 5 June 2026) improves order *preparation*, already used in the scalar controller; it does not state the missing scalar query. The official OpenAI mathematics overview was also inspected: its prime-field polynomial-factorization entry takes a supplied prime and dense polynomial coefficients, so it does not supply a modular integer-factorization or implicit geometric-product input interface.

The useful initialized conclusion is specifically the soft(k) coarse-residue consumer above. It agrees with the existing partial-tag route and does not count as new acquisition. The scalar catalogue, its zero-row deletion, and its general nonzero integer-annihilator recovery remain unchanged.

## Primary pin

Cached PDF: `sources/gao-feng-hu-pan-2512.19076v1.pdf`
SHA256: `dd71520d86c5a6b0a3bfa8dad495fcf26dfabee64c8e2b580e50cb0a9dc57c51`.
Theorem 3.1 and Corollary 3.2 are on printed page 10; Algorithm 4.8 and Proposition 4.9 are on printed page 18. The cached primary PDF was read directly. The existing identical cache in the paired-weighted-query packet is credited; this copy creates no new theorem or independent proof.
