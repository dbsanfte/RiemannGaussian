# Second independent audit: one canonical even moment consumer

26 October 2026. Read `moment-consumer-review.md` and the actual primary HH Proposition 3.3 / Algorithm 4.3 parameter statements in the pinned 2105.11105 text. Paper only; no repository changes or tests. **PASS; no substantive gap found.** This is a sufficient-output consumer, not acquisition of the moment.

For p=1,2,3 the original beta-coupled bank gives c=d*u^p with 1<=d<=D0, 0<u<n and nD0=K/2. Hence c<M_p=(K/2)n^(p−1)<=3K²/4, using n²<=3K/2. All primes exceed 16H, so both the true interval and padded square recovery interval b²<=4M_p<16H are below BOTH primes. This does not assume that the nonsplit R is smaller. Norm-coordinate scalar recovery, one flagged block scan, and trial factorization of c cost soft K. Reject c=0 and out-of-range wrong-bin candidates before divisor enumeration.

Enumerating v|c, retaining v=u^p with 1<=u<n and 1<=c/v<=D0, and taking the two public square roots of unit-square u modulo n yields at most 2*tau(c) residues. Complementing by N/r modulo n makes the total at most 4*tau(c) and includes the smaller-factor residue irrespective of which prime is nonsplit. There is ONE shared HH palette call; separate calls per divisor would not justify the bound.

The explicit divisor constant is valid: for primes l>=4096, a+1<=2^a<=l^(a/12); for smaller primes the supremum is bounded by (1−l^(−1/12))^-2<324. The exact numerical inequality needed is 18^12<2*17^12, giving 2^(−1/12)<17/18. Fewer than 4096 small primes therefore give the deliberately loose C_tau=324^4096. Thus S=O(K^(1/6)) and S/n=O(K^(−1/3)) with an absolute constant. Divisor enumeration itself is bounded also by 2sqrt(c)=O(K), so the input palette is actually acquired within the target.

Let A=ceil(cuberoot(K^4)) and t_HH=ceil(16A/n). Then nt_HH>=16K^(4/3), giving

    lambda<=ceil(K/16), kappa=2lambda+1<=K/8+3<K.

Also S*t_HH<=16A*S/n+S=O(K). The ceiling adds only S, and A<=K^(4/3)+1. The parameters n and t_HH have O(log N) bits and are O(N) on the native hard branch, as required by the actual Proposition 3.3. Its centre loop and per-centre lattice construction are therefore paid; there is no imported balanced-factor restriction. The huge divisor proof constant does not enter the actual interval parameter.

The projected scalar base alpha=beta^(n²) is legal because n²|H, so each local order is at least ord(beta^H)>16H and exceeds the entire baby alphabet. The inherited true global-match recovery, exact quadratic zero-coefficient branches, safe deletion of already processed matches and monic saturated localization therefore apply unchanged. Wrong palette/bin attempts remain bounded factor-or-failure, and processing must continue after failure. Complementing an either-factor tag is explicit.

The positivity of the CANONICAL integer u^p weights is essential to c's bounded integer interpretation. This proof does not accept arbitrary unit Lambert amplitudes, residue-class powers reduced modulo n before taking the moment, raw torus-only aliases, or a completed row catalogue with a larger multiplicity promise. It needs neither a count coefficient nor the packed count/tag scalar once this one actual moment is supplied. Acquisition of that moment remains open at soft K; the retained full-query rate is unchanged.

Temporary-file source links in the reviewed note should be replaced by frozen repository references at integration, as root already planned. No mathematical alternative or correction is required.
