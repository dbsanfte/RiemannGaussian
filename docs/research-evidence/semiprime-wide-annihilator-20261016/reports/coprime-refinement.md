# A direct paid refinement to coprime long local orders and query units

2026-10-16. Classical composition of the uniform preprocessing, universal first-nonunit detector, and short-annihilator extractor. The N−1 coprime-projection arithmetic and earlier universal routing are already compiled. The contribution here is a direct paid same-input composition, not a new projection identity or the first algebraic kernel resolution.

## 1. Statement

Let N=P Q with distinct odd primes, P,Q<=C sqrtN for a fixed balance constant, and supplied integer m=Theta(N^(1/6)) with N<=m^6 and P+Q<=3m³. Put B=16m². There is a deterministic algorithm, of soft-O(m) bit cost, returning either a proper factor of N, or a unit beta modulo N whose exact local orders d_P,d_Q satisfy

    d_P,d_Q odd,      d_P,d_Q>B,      gcd(d_P,d_Q)=1,
    (P−1)/d_P<m,      (Q−1)/d_Q<m.

Consequently its exact global order D is d_P d_Q>B²=256m⁴. Neither local order nor D is output or assumed known. No local order primality is required.

With one further soft-O(m) detector call, the same algorithm additionally either factors N or certifies, for q=beta^(m²), that BOTH exact local q-orders exceed B. Hence

    1−q^k is a unit modulo N for every1<=k<=16m².

The retained beta is unchanged by this certification. No assumption gcd(m,d_P d_Q)=1 is needed.

The algorithm supplies all inputs to every invoked subroutine. In particular it calls the short-annihilator extractor only after it has explicitly computed and verified an appropriate annihilator. No annihilator acquisition oracle is assumed here.

## 2. Paid prerequisites and preserved qualifications

First run uniform-preprocessing.md. Under these same numerical assumptions it returns a factor or a unit gamma with odd local orders r_P,r_Q>B and indices(P−1)/r_P,(Q−1)/r_Q<m. Its HH2026 large-GLOBAL-order search, monic first-nonunit detector, two-primary squaring branch, and explicit affordable small-input fallback have their own full proof. It costs soft-O(m).

The universal detector for a supplied unit u and cap B uses H=4m, so its tested positive exponents are exactly1,...,B. It returns a proper factor, an EXACT common local order c<=B, or NoHit certifying both local orders>B. It never substitutes a common lcm for exact local equality. Its soft-O(sqrtB)=soft-O(m) bit cost is valid over Z/NZ without point-difference inversions.

The short-annihilator extractor requires an odd-order small-index base such as gamma and a supplied nonzero polylog-bit global annihilator K. On the balanced range its proved bit cost is soft-O(N^(31/192)), which is soft-O(m). Its analytic finite-case fallback is part of that asymptotic theorem. This report does not reprove the Burgess input or ignore the extractor's promises.

## 3. The old N−1 projection, with exact arithmetic proof

Set

    beta=gamma^(N−1) modulo N.

Its computation costs polylog N bit operations. Let g=gcd(P−1,Q−1). The elementary identity

    gcd(P−1,N−1)=gcd(Q−1,N−1)=g

follows by reducing N−1 modulo P−1 and Q−1, respectively. Thus the exact local orders of beta divide

    A=(P−1)/g,       A'=(Q−1)/g.

For example, since ord_P(gamma)|P−1, the order after exponentiation divides (P−1)/gcd(P−1,N−1). This does not assume ord_P(gamma)=P−1. The two displayed quotients are coprime, hence

    gcd(ord_P(beta),ord_Q(beta))=1.

Both orders remain odd because beta is a power of the odd-local-order gamma.

This arithmetic is already the native SemiprimeOrderSeparation.projected_orders_coprime theorem, together with shared_projected_order_eq_one. It holds for arbitrary prime-field units, not just the earlier specially qualified gamma. No high power (N−1)^L is necessary; using N−1 is sufficient and retains a shorter explicit annihilator in the saturated branch.

## 4. Close every detector branch with paid inputs

Run the universal detector on beta through cap B.

- Proper factor: return it.
- Exact common order c: the local beta orders are coprime, so their equal value is necessarily c=1. Thus beta=1 modulo N, and the explicitly known positive integer K=N−1 satisfies gamma^K=1 modulo N. Invoke the short-annihilator extractor on the ORIGINAL gamma and this K. Gamma still has odd local orders with indices<m from uniform preprocessing, while K has O(logN) bits. The extractor therefore returns a factor within its proved cost. There is no circular promise: the computation beta=gamma^(N−1)=1 has actually acquired the needed K.
- NoHit: both exact local beta orders d_P,d_Q>B. Since they divide P−1,Q−1 and P,Q<=P+Q<=3m³,

      (P−1)/d_P < 3m³/B=3m/16<m,

  and similarly for Q. They are odd and coprime by section3. Keep beta. Exact CRT order is lcm(d_P,d_Q)=d_P d_Q>B².

In particular a common small order is not left as an unresolved kernel population in this direct procedure. The order c itself need not be factored. The known exponent N−1 annihilates gamma only in the certified c=1 branch; the algorithm does not presume it annihilates arbitrary inputs before this test.

## 5. A paid q-step check supplies every short interpolation unit

On the surviving branch compute q=beta^(m²). Each local q-order divides its corresponding local beta order. Thus the q-orders are still coprime, even if m divides one beta order.

Run the universal detector on q through cap B. A proper-factor return stops. If it returned exact common order c, coprimality would force c=1. Then beta^(m²)=1 in BOTH hidden fields, so both original beta orders would divide m². This contradicts d_P,d_Q>16m². Therefore a common-order return is impossible on this branch.

The only other return is NoHit. Both local q-orders then exceed B. For every1<=k<=B, neither hidden prime divides1−q^k. Hence gcd(1−q^k,N)=1 and each is a unit modulo N. This is a theorem-level simultaneous certification obtained from one paid detector, not B assumed inversions or B individual modular powers. Repeated evaluation nodes and zero divisors are handled within the detector's monic arithmetic and gcd localization.

This useful query interface licenses inversions only of these stated scalar units, not arbitrary quotient-algebra elements or an uncomputed long-query scalar.

## 6. Full bit cost and source input

Uniform preprocessing is soft-O(m). Computing beta and q uses polylogarithmic modular powering. Each detector call costs soft-O(m). The c=1 branch calls the extractor once at cost soft-O(N^(31/192)); since m=Theta(N^(1/6)), this is below soft-O(m). Its primary Burgess constants and finite exceptions are already covered by its proved fallback. These routines are sequential, with a fixed number of calls. Their combined bit cost remains soft-O(m), including gcds, roots, all seed acquisition, exponent reads and branch checks. Space bounds follow from the paid routines; no enormous tables or nonuniform field advice are introduced.

The only external algorithmic/analytic primary inputs are those already pinned in the prerequisite reports: HH2026 deterministic large-order search and Lau--Wu's uniform cubefree least-character-nonresidue bound. The projection and CRT/order reasoning here are elementary and already compiled. No analytic density-one prime family, exact large local prime orders, or supplied global annihilator is used for the new setup theorem.

The balance assumptions and m=Theta(N^(1/6)) are retained explicitly. This report does not silently extend the claimed N^(1/6) bit exponent to arbitrary unbalanced inputs or arbitrary oversized m. Standard easy even/square cases may be handled before these routines.

## 7. Correct historical attribution and remaining gap

The journal's October2 section near1868 already proves/uses N−1 projection and coprime projected periods. Its bounded32-base kernel scan could return kernel-unresolved. The October3 SemiprimeLocalOrderRouting section near6329 subsequently compiled an N-only factor/KernelData/LongData route, and the kernel-descent discussion near6683 states that all kernel descents and their transports were discharged. The remaining terminal population already had two large coprime B-rough local periods, possibly at a smaller retained leaf. The32-base unresolved description is historical, not the current status after that later kernel descent. These older notes explicitly left polynomial/powering/setup and the complete bit backend unpaid.

Therefore it would be incorrect to call the coprime-order output contract new, or claim this is the first arithmetic resolution of all kernel branches. The new paid composition uses the fully charged monic detector and unconditional short-annihilator recovery to close a same-input common-order branch directly, and adds the direct q-step unit certification. It does not require the earlier recursive kernel backend or its runtime assumptions. This historical comparison is an attribution statement, not a new audit of all old formal builds.

The output base is generally different from the literal original projected base2. This theorem does NOT transfer the original detector's collision coverage, source arithmetic, quantitative hard-family statements or factor-sum controller to beta. Strong global order and certified scalar units are useful setup facts, not an acquisition of the restriction-stable soft-O(m) long collision query or its norm. No full sixth-rate factoring theorem, new native edit, Lean declaration, or broad build is claimed.
