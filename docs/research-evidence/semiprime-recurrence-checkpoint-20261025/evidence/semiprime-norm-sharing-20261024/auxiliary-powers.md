# Rational native indices and auxiliary-power DLP: compact applicability audit

24 October2026. Scratch only. No new fast unknown-order solver is obtained. The initialized object is a common-base homogeneous power family; the strongest tested deterministic multi-target construction still needs the missing exponent-field/order data and its auxiliary inputs cost more than the desired clock. This is not a claim that every order-independent use of these powers fails.

## Credit and actual construction

The journal near37790--37835 and the earlier `/tmp/semiprime-auxiliary-exponent-20261023/`, `/tmp/semiprime-exponent-collision-20261023/`, and `/tmp/semiprime-dickson-list-acquisition-20261023/` packets already acquire Dickson/window auxiliary images, audit Cheon2010 and Cheon--Kim, charge high-degree exponent acquisition, and distinguish global prime-order projections from hidden local fields. Those are prior results, not new backend lemmas here. The detail tested now is the actual multi-ROW rational index E_j/H, rather than the earlier factor-sum parameter.

Let E_j and H=k² be public integers, beta the actual rough scalar controller, and L=O(k²). At a LOCAL collision beta^(E_j-HI_j)=1, with0<=I_j<L, choose any integer d>=1 and acquire

    g=beta^(H^d), A_(j,r)=beta^[E_j^r H^(d-r)], 0<=r<=d.

Then EXACTLY A_(j,r)=g^(I_j^r) at that local side. Polynomial congruence E_j=HI_j modulo its beta order proves it; there is no division by H in the constructor. All exponents have O(d log N) bits. Roughness preserves the beta local orders under the common H^d power. Signed E_j uses the supplied unit inverse.

The selected-high-power input needs only g,A_(j,1),A_(j,d). g and beta^(H^(d-1)) are shared soft-O(d) acquisitions; all A_(j,1) then cost soft J. Each A_(j,d)=beta^(E_j^d) costs soft d by actual integer powering, hence the initialized upper cost is soft(Jd+d). This is a cost for this construction, not a lower bound on another shared exponent algorithm. Acquiring every r<=d by the straightforward homogeneous construction costs soft(Jd²+d), and emits Jd elements. No growing-degree auxiliary table is treated as free.

## Execute the strongest compatible multi-target search

Cheon2010, [primary author PDF](https://www.math.snu.ac.kr/~jhcheon/publications/2010/StrongDH_JoC_Final2.pdf), Theorems1--2, uses a KNOWN prime group order p and scalar-field startup. For d|(p-1), the three inputs give cost soft(sqrt(p/d)+sqrt d). The p+1 variant uses powers through2d and has its separate ERH startup qualification; its cost is soft(sqrt(p/d)+d). The primitive-generator discussion does not establish deterministic cheap factorization of p-1. These exact known-order/startup qualifications were already audited in the credited packet.

Kim2015, *Multiple Discrete Logarithm Problems with Auxiliary Inputs*, [primary IACR paper](https://www.iacr.org/archive/asiacrypt2015/94520130/94520130.pdf), Section3.2 Remark1 and Section3.3, provides the relevant multi-target formulation. Its small-memory randomized theorem assumes random targets and extra size restrictions; it is not a deterministic all-native-input theorem. The deterministic large-memory BSGS adaptation can be checked directly as follows, conditional on the known prime p, d|(p-1) and a supplied primitive scalar zeta:

1. Let n=(p-1)/d. Solve A_(j,d)=g^[(zeta^d)^v_j] in the exponent, sharing a giant table of length n/B and doing B babies per target. This costs O(n/B+JB+J), minimized at soft(sqrt(Jn)+J).
2. The first exponent v_j modulo n gives I_j=zeta^v_j*(zeta^n)^w_j. A second shared table/baby search on the order-d scalar subgroup costs soft(sqrt(Jd)+J).

Zero logarithms are handled separately. All field exponent arithmetic here is modulo the KNOWN p. Thus the conditional deterministic search has work/storage

    soft(sqrt(Jp/d)+sqrt(Jd)+J).

For J~k, even granting the missing field startup, adding the actually acquired selected powers yields

    soft(Jd+sqrt(Jp/d)+sqrt(Jd)+J).                (1)

For the illustrative largest smaller-prime local order scale p~k³, balancing the first two terms gives d~k^(2/3) and cost soft k^(5/3), above the old k^(3/2) query. For p~k² a favorable divisor might make (1) smaller, but neither that order scale nor the required divisor is uniformly supplied. Even the favorable free-auxiliary choice d~k at p~k² costs k² by the literal Jd acquisition. These are evaluated upper-cost ledgers, not generic lower bounds or an assumed divisor distribution.

## The native order information is already sufficient without Cheon

If the EXACT local beta order r were supplied (prime or composite), roughness gives H^-1 modulo r. The potential native index is immediately

    I_j=[E_j H^-1]_r.

Since r>16H>L, this is the UNIQUE bounded index if it lies in[0,L). Actual gcd tests at these O(J) indices, followed by the existing general nonzero-annihilator consumer on saturation, already give the original native factor-or-witness route in soft(J+k), with no auxiliary powers. Here the original near-N exponents E_j=N+delta_j and I_j<4H ensure E_j-HI_j is nonzero on the growing branch; a different exponent family must retain its own explicit zero-exponent removal/precheck and cannot consume a tautology. Thus importing a known prime-order scalar field does not solve the actual missing acquisition: it has supplied stronger information than this rational-index instance needs.

The actual common g above retains two nontrivial local beta orders and is not a prime-GLOBAL-order group under the full coprime-order controller. As already proved in the old journal, producing a nontrivial prime-global-order projection of that controller immediately factors N by gcd(g'-1,N), since coprime local orders make exactly one component1. A hidden prime divisor of a local composite order is not a supplied local subgroup representation or a recovered full beta-order index. Roughness concerns factors of r, not divisors of r-1 or r+1, and supplies no primitive element of an unknown exponent field.

Replacing arithmetic modulo r by arithmetic modulo N is invalid in the tested construction: a coefficient congruence modulo N need not be an exponent congruence modulo r. Likewise comparisons of A_(j,d) with g^(t^d) can have extra power fibres; they do not automatically certify E_j-Ht=0 modulo the ORIGINAL local beta order. A saturated high-degree polynomial exponent may have O(d log N) bits and cannot silently receive the short-annihilator decoder. The old factored-window recovery applies only when its actual short factorization is retained.

Outcome: the rational-index homogeneous powers are acquired and the strongest tested deterministic batch cost is explicit. No native all-input Cheon adaptation, required order/divisor supply, or shared soft-k auxiliary acquisition is proved. The short-order calculation above is a conditional READY branch, not an achieved order constructor. No new generic backend, sparse-recovery oracle or factoring rate is claimed.

Cache/provenance: Cheon2010 was reused from the already credited auxiliary-exponent packet, copied to `sources/cheon-2010.pdf`, SHA256 `fd7746b9d2c37c228b63e9b993e7eb58a90045740f5d1fd6aac3e5a5af70b4de`. The Kim2015 primary indexed Section3.2--3.3 text was inspected; direct PDF retrieval returned403 and no local PDF fingerprint is claimed. The two-stage deterministic count is proved above independently. No numerical examples, deployed systems or shared-source edits were involved.
