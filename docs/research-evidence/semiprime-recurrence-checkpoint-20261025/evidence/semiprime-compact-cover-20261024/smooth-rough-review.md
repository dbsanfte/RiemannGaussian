# Independent square-LCM smooth/rough cover review

2026-10-24. **PASS. No required fixes.** Read-only mathematical and cost audit; no source/repository edits or examples.

Reviewed source: `/tmp/semiprime-compact-cover-20261024/smooth-rough-cover.md`

Exact SHA256: `1111187524344b96671b0b800e899e7b71bec74d5f21d04bd23a8057189572c0`

The prior journal's shared product-exchange constructor around line 37630, its rough-purification attribution and factored-kernel/order-peeling context were inspected before this audit. The source correctly credits those old mechanisms. The positive refinement being checked is the square-LCM self-certificate, not first discovery of smooth projection or the unresolved rough cover.

## Square-LCM certificate

For p<=m and b=floor(log_p m)>=1, m<p^(b+1)<=p^(2b), so the displayed strict p^(2b)>m inequality is correct. If p survives in d/gcd(d,M), its removed p-primary factor already exceeds m. Therefore d<m^3 implies residual order<m^2 whenever any small prime survives. NoHit above 16m^2 excludes that case and certifies m-roughness. The proof needs no actual order or hidden factorization.

Sieve/factor acquisition and even log K<=m log m suffice for soft-m bit length. A single beta^M exponentiation costs its ACTUAL O(m polylog N)-bit exponent length, and is charged. M is not powered independently at every small prime.

## Complete old factored-kernel closure

The input beta orders are already coprime, odd and nontrivial. Their divisors after any public power remain coprime. On gcd(beta^M-1,N)=N, the invariant u^A=1 with both orders nontrivial/coprime is correct.

Splitting A=A_left*A_right gives exactly the stated transitions. A saturated u^A_left retains u,A_left. A unit gcd retains v=u^A_left,A_right, with both v orders nontrivial and still coprime. A proper gcd factors. At a single prime-power leaf two nontrivial coprime orders cannot both divide that exponent, so a proper factor must have appeared earlier. Only one tree path is used; subtree exponent-bit lengths plus depth fit soft(bit M). No unrelated outside-power list or long-annihilator oracle is required.

On the initial unit-gcd branch, the inherited first-nonunit detector through C has no unresolved common-order outcome: common order would be one by coprimality, contradicting both components being nonidentity. Thus every kernel or short-residual branch is paid in soft m, and the only continuing outcome certifies both residual orders>C.

## Exact smaller-prime rough part and larger-prime limitation

The smaller residual rP is m-rough by the square-LCM lemma. The derived coindex (P-1)/rP<m/16 is an integer all of whose prime factors are below m. Hence no >m prime power of P-1 can be absent or partially absent from rP. This proves EXACT full m-rough(P-1), rather than only a rough divisor of the initial beta order. The coindex itself is not computed or supplied.

Since rP<m^3 and every prime factor exceeds m, it is prime or has precisely two prime factors counted with multiplicity; each factor in the latter case is <m^2. The repeated-prime case is retained. No balance premise is used.

For Q the original order may be as large as order m^4, so the same square projection/NoHit argument does not imply m-roughness. The report explicitly preserves only oddness, coprimality and the >C certificate there. It never assigns the smaller-prime shape or coindex bound to Q.

The optional q=rho^(m^2) screen is also paid. Its P-order is unchanged because rP is m-rough; the other order may change. A shared small/common outcome cannot equal the unchanged large P-order. A factor or full q-NoHit certificate follows lawfully. This is sufficient to regenerate the original canonical source/decoder for rho; no old q promise is transferred without screening.

## Short two-list partial cover

S={uN:1<=u<=m}, T={v:-m<=v<=m} are actually acquired in soft m. Their hulls are separated because N is on the hard branch, so every difference is positive, nonzero and O(log N) bits. Monic product/MPE and selected labels cost soft m. A WHOLE-order collision therefore has a valid factor or short original-rho annihilator consumer under the acquired large odd-order certificate.

For a rough prime factor lambda<m^2, N is a unit modulo lambda because lambda<P<=Q. The m+1 distinct circular residues kN have a gap at most lambda/(m+1)<m. Reversing its orientation if necessary gives a displayed uN-v divisible by lambda, with 1<=u<=m, |v|<=m. This is a correct partial-factor cover.

It does not cover the whole two-factor order on ONE pair: the two lambdas may occur on different pairs, and a lambda^2 order may lose only one lambda. The report states these distinctions explicitly. The proposed small-order-of-ratio test would succeed at an appropriate partial-factor pair, but no simultaneous test over all implicit pairs is supplied or counted as paid.

## Distributed product, all saturation branches and bit ledger

K_box has Theta(m^2) positive short leaves and Theta(m^2 log N) bits. A full action removes both distinct rough factors, or at least one copy in the repeated-prime case, so the P-order becomes one or <m^2. That two-factor reduction is covered but over budget. The intervals around uN are disjoint integer-factor windows; the old overlapping-window product-exchange theorem does not acquire their action at soft m.

The stated saturation continuation is valid. A saturated subtree retains a known annihilator for the current large coprime-order base. A unit branch changes the base and immediately rechecks its orders; if one has become short, the nontrivial coprime detector branch factors, otherwise the invariant is restored. At a final short leaf the actual current base has a supplied nonzero polylog-bit annihilator and the appropriate short consumer. The exponent-bit total remains soft m^2 and the logarithmically many soft-m screens do not change it. No too-long K_box is passed to a short-witness decoder.

## Scope of the rough-prime continuation

The prime rP branch has the proved small UNKNOWN coindex, but includes fixed small even coindices and supplies no growing lower bound. Thus ordinary order search still has its old worst horizon. The S=N+1 modulo r identity does not turn the hidden residue into a short supplied label or prove Charlier coverage.

A proposed action using N^M-1 is correctly distinguished from having acquired M: the integer N^M has bit length proportional to M, not log M. Likewise arbitrary unrelated-base projections are not paid by one projected generator. Both are implementation/input-cost warnings, not generic lower bounds.

The selected short-vs-wide annihilator boundary is correctly maintained. The current prepared rho can use the inherited unconditional short-bit consumer for a selected short difference. A soft-m-bit selected difference would need the separately conditional old wide consumer or a new theorem; none is silently imported. Factored-M kernel closure needed neither decoder.

## Verdict

The positive square-LCM/NoHit self-certification and exact smaller-prime rough-part conclusion are valid with all kernel, residual and optional q branches paid in soft m. The report does not supply or claim an all-input soft-m rough-order cover. Partial-prime hits, whole-order collisions and explicit distributed products are separated correctly, with all witness and bit costs charged. PASS for the exact reviewed bytes.
