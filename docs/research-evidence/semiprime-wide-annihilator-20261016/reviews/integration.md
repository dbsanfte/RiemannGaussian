# Final integration review and secondary coprime-refinement check

2026-10-16. Verdict: PASS on the final bytes below. Before pinning, the README and journal were clarified to retain the fixed numerical setup hypotheses N<=m⁶ and P+Q<=3m³ in addition to m=Theta(N^(1/6)). No further correction requested. This is an integration review; I authored the wide-cover and retained-HH notes, so it is not an additional independent review of those two proofs.

## Final integration pins

- README.md: 4196 bytes, SHA256 `29f05f1f2a08e83ec7468e7381984abfa194ad70970b9b5694951f12123fe462`.
- journal-entry.md: 4757 bytes, SHA256 `4a14f6ee838130403a3faacdd7c26cedf27553100c319230d1ebb6706cbc5170`.

Exact supporting reports inspected:

- short-annihilator-extractor.md: 10375 bytes, SHA256 `433d10d8c413ad8cbe7ecb09bbafe0794559afa8b2b535e3667b9491950c1131`.
- small-order-separator.md: 5679 bytes, SHA256 `5fd92268584613b0ffe9b1c12e076dd3ef93a52d53cb3d76c799b2a747793109`.
- uniform-preprocessing.md: 8770 bytes, SHA256 `375460025deb024f03c3bc3415fc7990ca9a50b16cc9e272a19b17dd08d2e4fd`.
- coprime-refinement.md: 9447 bytes, SHA256 `d4477d8a27050922f50354ca89f075b9d246adfc608eb9b486f01be4b4a74c76`.
- coprime-source-pins.json: 1262 bytes, SHA256 `e85889558e05cb38b60ddd2d663fddb2f9dcabc81ce454f332bb35415b3174fa`.
- wide-cover-certificate.md: 11079 bytes, SHA256 `063250598bc508dc149b0e64fc1a638bab83a7be059496669322142cbcddc1e1`.
- HH-retained-data.md: 7206 bytes, SHA256 `dee1cd8c4f518a8bbb7ccec35034c0f35d328f293924cb90d7a35c8467a01cc9`.

All six files in coprime-source-pins.json were independently rehashed and match their byte/hash records. Native SemiprimeOrderSeparation.projected_orders_coprime and shared_projected_order_eq_one were read at their actual definitions; the historical kernel-routing/descent journal passages were also inspected. No native build was run.

## Conditional extractor and setup scope

The summaries correctly apply N^(31/192) only GIVEN a nonzero polylog-bit global annihilator of an odd-local-order base with both indices below m. They do not require prime, distinct or index-coprime orders, do not factor K, and do not assume a small multiplier. The short-order separator returns an exact common local order, not merely a shared annihilator. The cheap Jacobi scan invokes that separator only once after finding its base; the second scan invokes it per base. The cutoffs and arithmetic identity 5/64+1/12=31/192<1/6 are accurate. The finite fallback makes the asymptotic theorem algorithmically total without supplying an unknown analytic threshold.

The primary Lau--Wu theorem was independently fetched and inspected at its introduction/Theorem 1: it applies to nonprincipal characters of cubefree modulus, hence includes the composite Jacobi character and prime-field nonresidue character. No GRH/quasi-RH input is silently substituted. The report does not claim an explicit practical Burgess threshold or that scanning the bases acquires K.

The uniform setup uses a large GLOBAL-order HH output, then separately checks its odd projection with the universal detector. Its common-order branch recovers exact two-parts or separates them; a common full order r has r²|phi(N) and r²>P+Q, giving the factor sum by a remainder. Its elementary fallback when the requested HH target is outside the theorem's input range is explicitly affordable. The final README/journal now retain the numerical assumptions needed for the fixed16m² target and index estimates. These are paid classical setup results, not a claim that every old coverage/controller theorem transfers to the new base.

## Secondary independent arithmetic check of coprime refinement

Put g=gcd(P−1,Q−1). The identity gcd(P−1,N−1)=gcd(Q−1,N−1)=g implies that the orders of beta=gamma^(N−1) divide (P−1)/g and (Q−1)/g. These quotients are coprime, so the projected local orders are coprime. This remains true when the original gamma orders are proper divisors of the field group sizes; no primitive-root hypothesis is used.

A universal detector common-order return on beta must therefore equal1. This actually computes beta=1 globally, so K=N−1 is a verified annihilator of the ORIGINAL small-index gamma. Invoking the new extractor here is not circular and does not assume an annihilator oracle. A NoHit return instead gives both beta orders>16m², hence indices below m under P+Q<=3m³. Their exact global order is their product>256m⁴.

For q=beta^(m²), coprimality persists because its orders divide the beta orders. If the detector returned a common order, it would be1, forcing both beta orders to divide m², contrary to their lower bound. Thus the final detector either factors or certifies both q-orders>16m² and every stated scalar1−q^k is a unit. This does not license uncomputed quotient-algebra inverses. A fixed number of detector calls plus preprocessing and at most one extractor invocation has soft-O(m) bit cost.

The historical credit is correct. The projection identity is already compiled in SemiprimeOrderSeparation. The October3 journal near6330 already exposed KernelData/LongData routing; near6681 it explicitly says kernel descents and transports were discharged, with the complete bit backend still unpaid. The integration therefore correctly calls this a new DIRECT PAID SAME-INPUT composition, not the first algebraic kernel closure or a new coprimality identity.

## Cover and acquisition claims

The arbitrary-wide cover reduction remains restricted to the inherited qualified raw-energy family. Supplied relative origins, assignments and positions may depend on the full input; total explicit origin encoding and k²T are nearlinear. Trimming supplies a short labeled witness, without asserting useful collision coverage after trimming. A local cover forces one nonzero relation; its gcd either factors or gives a global annihilator for the extractor. No numerical origin-span or multiplier bound remains and no new cover-dependent source exception is asserted.

Known factors conversely give the one-point global cover under the original source's gcd(m²,phi(N))=1 promise. The reader text accurately calls this an equivalence of supplied-certificate acquisition and factoring on that source, not an operation lower bound or free acquisition. Reorigining does not establish the original interval predicate. The retained-HH diagnosis concerns the actual original majority family and the particular M=1 shortcut, not all computations on HH state.

Both integration files preserve the missing whole-query acquisition, all-input controller and Lean bit-complexity obligations. They do not infer a soft-O(m) factorizer from setup alone. Planned durable links and nonredistribution of full primary papers are consistent with the packet description. This targeted review does not replay the twenty-packet baseline; preservation of all predecessor files/journal entries is a separate packaging integrity task. No source edits, examples, commits, pushes or broad builds were performed.
