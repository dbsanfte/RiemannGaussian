# Independent review: literal phase image and cyclic closure

26 October 2026. Bounded paper audit, no tests or repository edits. **PASS with the stated literal-periodicization scope.** The image is exactly g² Z/H, not merely contained in it; the 2-adic factor4 is correct.

Let k=2*3^e,H=4*3^(2e), j an odd unit representative in[1,k), g=gcd(j-1,k). Choose jinv inverse modulo H and a0=[N*j^-2]_k. The stationary lattice basis is v1=(k,0),v2=(a0,1), and its unwrapped phase images modulo H are

    E1=k*(1-j),
    E2=(j-1)*(N*jinv-a0).

The second formula follows by expanding the supplied linear phase law; no congruence-only division is used. Since N*jinv-a0=a0*(j-1) modulo k and a0 is a unit modulo k, put t=v_3(j-1). For j!=1 one has t<e: the only other candidate1+3^e in[1,k) is even and therefore not a unit. Thus v_3(N*jinv-a0)=t EXACTLY, giving v_3(E2)=2t. Meanwhile v_3(E1)=e+t. Both E1 and E2 are divisible by4: k and1-j are even; j-1 and N*jinv-a0 are also both even. Since H has exactly2-adic valuation2, no finer 2-adic distinction is needed.

Consequently

    gcd(H,E1,E2)=4*3^(2t)=g²,
    image(Etilde|Lambda_j)=g² Z/H,
    L=H/g²=(k/g)².

For j=1 the linear character is zero modulo H (indeed zero with jinv=1), g=k and L=1. Changing inverse representatives modulo H or the chosen lift of a0 changes no phase image. This calculation concerns the auxiliary integer phase group, not the arithmetic local order of beta or q.

A nonempty finite LIVE set explicitly closed under BOTH basis translations modulo literal q-shifts is invariant under the subgroup they generate, hence contains a full orbit of L distinct exponent residues modulo H. Finiteness makes closure under forward translations sufficient to recover inverses. This is an orbit-cardinality statement for that specified explicit phase-state architecture; it does not limit linear/implicit representations, numerical aliases, or non-q boundary coefficients.

For a Cartesian periodicization with wraps A and B, literal q-monomial wraps imply A*E_u=0 and B*E_w=0 modulo H for its two basis phases. The homomorphism from Z/A x Z/B onto the phase image then gives L|AB, in particular AB>=L. This holds for ANY unimodularly changed lattice basis, including the Gauss basis. It need not be sharp for a particular chosen basis; that does not affect the claimed necessary bound.

Exactly k/6 unit colours satisfy j=2 mod3 (they are j=5 mod6). They have g=2 and L=H/4. Therefore a literal closed phase-state list for each of these colours has total cardinality at least k³/24, and their individual L is Omega(k²), larger than the new AB=Theta(k) Gauss grids asymptotically. The summation assumes the explicit per-colour live sets; no claim is made that one cannot share implicit algebra across colours.

The safe conclusion is the one requested: replacing the open grid by a SMALL finite literal-q-periodic phase closure cannot be justified by its present O(k)-node box. This is not a lower bound for a joint norm, an arbitrary finite-ring algorithm, a numeric modalias construction, or the complete factoring goal.
