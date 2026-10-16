# Independent exact-file review: HH retained datum

Verdict: PASS, no correction requested. Read-only mathematical/source inspection; no new build or theorem certification.

Reviewed `HH-retained-data.md`: 7206 bytes, SHA256 `dee1cd8c4f518a8bbb7ccec35034c0f35d328f293924cb90d7a35c8467a01cc9`.
Reviewed `HH-retained-data-source-pins.json`: 895 bytes, SHA256 `f50b642c9c68c66379fe4199892feea0f2f6234f4abba5fa1b77d776c079fe8f`.
All four prerequisite files match exact pinned bytes and hashes.

I inspected the saved primary text's Algorithm 3.1 (printed p8), Lemma 2.3 (p7), and correctness discussion, and the historical source §2(E5)-(E7). Printed line 3 is indeed the 2^D<N shortcut; the accumulated state is initialized on line 5; first beta is 2; bounded search and unknown-order return are lines 9-10; exact factoring/lcm updates occur only afterward. Thus the report's printed-PDF numbering and control-flow distinction are accurate. The HTML-number comparison is a renderer-convention attribution, not needed by the proof.

On the ACTUAL qualified family the literal power of raw base two has distinct odd prime local orders R_P,R_Q. These divide raw local orders, so their product divides the raw global order. That order exceeds 16m² eventually. The input is past finite lookup, odd, has 16m²>log2 N, and Delta<N-1, so it reaches the first beta=2 search and returns there before altering accumulated M=1. This is a genuine original-source majority argument, not arbitrary CRT generators or one sampled input.

Powering raw base two by 2^ceil(log2 N) preserves both odd prime divisors, and therefore the local odd orders still exceed 16m² with indices below m. It need not equal the factorial-projected old base, as the report explicitly notes. Retained M=1 cannot annihilate either unit locally. This does not rule out some other exponent derived by additional work.

For genuinely accumulated small exact orders, primary Lemma 2.3 and absence of a factor imply each accumulated order divides every local prime-minus-one. Their lcm M divides both P-1 and Q-1, so M² divides phi(N). If M²>S=P+Q-1, the least residue N mod M² equals S and quadratic recovery works. A known-order line16 return above Delta meets this bound on the balanced source. This is correctly distinguished from unknown-order line10 returning base2 with accumulator1.

The conclusion is precisely a refutation of reusing THIS retained HH accumulator as a universally usable annihilator. It is not a lower bound for arbitrary full-input exponent recipes, a new source-family theorem, or an acquisition result. No scope blocker found.
