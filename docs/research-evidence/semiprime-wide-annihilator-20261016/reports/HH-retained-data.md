# On an actual majority family, HH returns its first base with retained order one

2026-10-16. A narrowly scoped classical acquisition diagnosis. This rules out recovering the needed annihilator by simply reusing Harvey--Hittmeir's retained accumulated order on a nontrivial actual input family. It is not an obstruction to every computation on the algorithm's state, every full-input exponent recipe, or all acquisition algorithms.

## Exact primary algorithm and source

The primary source is Harvey--Hittmeir, Deterministic methods for finding elements of large multiplicative order, arXiv:2601.11131v2, 5 June 2026. Algorithm 3.1 has these relevant steps:

- Initial finite lookup, even-input handling, and the shortcut returning base two when 2^Delta<N.
- Initialization alpha=1, accumulated exact order M=1.
- Its loop begins with beta=2. It tests beta|N and beta^M=1, then uses Lemma 2.1 to search for ord_N(beta) up to Delta.
- If that order exceeds Delta, printed-PDF line 10 returns beta immediately.
- Only AFTER this branch does it factor a found small order, test for factors, combine exact orders by lcm, and possibly return a known-order accumulated element at printed-PDF line 16.

Line numbers in this note follow the printed v2 PDF: the HTML renderer numbers comments separately and labels the same return branches 13 and 19. Here Delta denotes the paper's input D, to avoid confusion with the global order of a later projected unit. Lemma 2.1 explicitly returns either the exact order up to its bound or a lower-bound certificate that the order exceeds it. No exact multiple is asserted in the latter branch.

Use the inherited original balanced prime-pair supply N=P Q, P,Q=Theta(M³), current auxiliary primes m=Theta(M), of size Omega(M⁶/log²M). The frozen full-Euclid source, §2(E5)–(E7), proves that the LITERAL projected base-two unit

 g_old=(2^(N−1))^((m!)^ceil(log₂(N+1))) modulo N

has exact local orders R_P,R_Q, distinct odd primes with

 R_P>P^.677, R_Q>Q^.677,
 R_P,R_Q>16m² eventually.

These are actual public-base properties on that source, not a CRT-selected generator. Native SemiprimeLongPowerRouting.projectedUnit_val identifies the scalar projection as an actual integer power of the original unit. Thus both R_P and R_Q divide the corresponding local orders of the RAW base two. Their distinctness implies

 ord_N(2)>=R_P R_Q>c m^4.062.                                        (1)

The divisibility follows simply because taking a power cannot increase a finite group element's order.

## First-iteration theorem at the nearlinear target

Run the published Algorithm 3.1 on this N with Delta=16m². For all sufficiently large members of the original actual supply, Delta<N−1 and the input is past the fixed finite lookup threshold. N is odd, so the even branch does not apply. Also

 16m²>log₂N,

so 2^Delta<N is false. The loop bound B=ceil(Delta^(1/3)) is at least two. Therefore the algorithm reaches its initialized state alpha=1,M=1 and its first beta=2 iteration.

The divisibility test 2|N is false. The test beta^M=1 modulo N is also false because 2!=1 modulo N. By (1), ord_N(2)>Delta; hence Lemma 2.1's bounded order search takes its exceeds-bound outcome. Algorithm 3.1 consequently returns beta=2 at printed-PDF line 10 on this FIRST iteration. It has not yet reached any lcm update or exact-order accumulation. The retained accumulator remains exactly

 M=1.                                                               (2)

In particular M is not an annihilator of the returned unit: 2^M!=1 modulo N. Indeed it is not even a local annihilator in either hidden field. The source has many actual inputs with this behavior; no isolated example or average-case heuristic is used.

The running time remains the published soft O(sqrt(Delta))=soft O(m) bound. This diagnoses which output branch supplies that time guarantee; it does not invalidate or strengthen the HH theorem.

## Odd projection does not repair this retained datum

Let z=2^(2^s) modulo N with s large enough to remove the two-primary part of each local raw order, for example 2^s>=N. Such an exponent can be chosen publicly with s=ceil(log₂N). Since R_P,R_Q are odd, they still divide the local orders of z. Hence both local orders of z exceed16m², and

 z^1!=1 in either hidden field.

The retained number M=1 therefore still supplies no annihilator after the standard odd projection. This z need not equal g_old; the old projected source is used only to certify odd divisors of the raw base-two orders. The lower bounds pass to z because a power of two is coprime to those divisors. Confusing the two differently projected units would be unnecessary and incorrect.

Moreover the indices of the odd local orders of z in P−1 and Q−1 are less than m eventually, because each local order is at least R_P or R_Q and the inherited cofactors (P−1)/R_P,(Q−1)/R_Q are O(M^.969)<m. Thus this first-return behavior occurs on actual members that also meet the new odd-order/index setup promises. It is not caused by leaving that promise class.

No assertion is made here that every later optional setup routine must have exactly this control flow, or that all derived metadata are useless. In particular a routine may itself discover a factor or a different annihilator; its acquisition must be charged separately.

## Why a genuinely accumulated known order is a different branch

HH's Lemma 2.3 and its factor tests imply that, whenever a small order is accumulated without returning a factor, it divides p−1 for every prime p|N. The lcm accumulator therefore satisfies M|P−1 and M|Q−1, hence

 M²|phi(N)=N−S, S=P+Q−1.

If the retained known M satisfies M²>S, then S=N mod M² and the exact quadratic with sum S+1 factors N in polylogarithmic time. In particular a known-order printed-line-16 return with M>Delta=16m² already has this property on the balanced source, where S=O(m³). Its known order is useful enough to factor directly; it is not the hard unknown-order return above.

One can retain and test an accumulator in other printed-line-10 runs, but it need not be nontrivial. The actual first-base family establishes this with M=1. It refutes the proposed universal shortcut “the HH setup already retained a usable nonzero annihilator of its returned base.” It does not prove that producing any other short annihilator is hard, or that the full-N input lacks the information.

The new wide-annihilator extractor answers what to do IF a nonzero short annihilator is acquired. This note leaves that acquisition untouched. No new Lean theorem, prime-family count, operation lower bound, example, or broad build is introduced.

## Pins and inspection scope

HH-retained-data-source-pins.json records exact primary PDF/text, historical actual-source report and native projection file. The primary inspection used Algorithm 3.1, Lemmas 2.1–2.3, and the associated correctness discussion; it does not claim a fresh review of every proof in the paper. The primary landing page confirms v2 is the June 5 revision. Earlier arithmetic/source qualifications and the published prime-family input are inherited as pinned, not reproved analytically here.
