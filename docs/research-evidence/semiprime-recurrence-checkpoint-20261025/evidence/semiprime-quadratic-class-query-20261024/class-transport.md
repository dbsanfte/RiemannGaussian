# Finite quadratic-class transport: paid endpoint batches, missing amplitude

24 October 2026. Scratch only. This tests an actual finite scalar transport on the supplied native quadratic-phase blocks. A batch of endpoint multipliers has a lower acquisition cost than the full query. The transport does not acquire the class product or a correct coarse selector at interior hits. No whole-query improvement is claimed.

## 1. Actual supplied data and a stronger clock identity

Use /tmp/semiprime-partial-tag-20261024/residue-block.md SHA256 `359dba948c766eea58d9b6f2e556a851d0e1354fb860126122afacb842e4d7f9`. Its actual modulus is k=d r^3,m=d r^2,H=k^2 with d even, r an odd prime coprime to dN. Full canonical minus classes have r rows, with all carries retained. Their acquired shifted native roots are Vhat_h. Use the INVERSE query arguments

    Y_h=Vhat_h^-1=C D^h E^(h^2), 0<=h<r.

Here C includes the inverse common shift q^(-B), D=pi^(-ell1)*barpi^(-2m), E=pi^(-ell2), pi=beta W, and q=pi^H. This inversion is of supplied units only. A zero P_L(Y_h) maps to the original equality Vhat_h=q^i; the query product differs from prod_(h,i)(Vhat_h-q^i) by the acquired unit prod_h Vhat_h^(-L). The actual shifted horizon L is below4H. The original row label, its exact q carry, and its original possibly slightly negative bounded index remain attached. No root separation or arbitrary interpolation is assumed. Any changed-modulus suppliers and actual q screens have already been paid.

There is additional exact structure. The centered ell2 is congruent to m^2 N^2 s0^-3 modulo H. Since H=m^2 r^2, it is an actual multiple of m^2. Set

    theta=pi^(m^2), a=-ell2/m^2.

Then E=theta^a, theta^(r^2)=q, E^(r^2)=q^a, and a is a unit modulo r. All these are global ring equalities. The signed centered integer a has |a|<=r^2/2, rather than being an unknown discrete logarithm. This commensurates E and q. It does not remove the factor barpi^(-2m) from D.

## 2. Execute finite class transport

Write P_L(Y)=prod_(0<=i<L)(1-q^i Y), and define

    Z(C,D)=prod_(0<=h<r) P_L(C D^h E^(h^2)).

Shift the actual h parameter by one:

    C'=C D E, D'=D E^2.

Every shared factor has identical argument because
C'*(D')^h*E^(h^2)=C*D^(h+1)*E^((h+1)^2). Therefore the EXACT division-free identity is

    P_L(C) Z(CDE,DE^2)
      =P_L(C D^r q^a) Z(C,D).                    (1)

No infinite theta function, Fay identity, tail deletion, or quasi-periodicity assumption is used. Both sides are the product over h=0,...,r of the same finite factors.

If both endpoints are units, (1) acquires the unit multiplier

    c=P_L(C D^r q^a)/P_L(C), Z(CDE,DE^2)=c Z(C,D).

This does NOT divide by Z, which can be zero or nonunit at a covered hit. If either endpoint is nonunit, retain the cross-multiplied identity. A proper gcd is a factor; saturated auxiliary endpoints do not automatically invoke an original leaf consumer.

## 3. Acquire all endpoint data, including costs

Let J be the retained row count, M=J/r the number of classes. All 2M endpoints C and C D^r q^a are acquired from supplied class starts with O(log N)-bit signed powers, cost soft M. They are units as arguments; their P_L values can nevertheless be zero.

Acquire BOTH entire endpoint-value vectors by the established zero-safe q-product evaluation algorithm at 2M supplied points. Construct a degree-b baby q-product, evaluate it at all target/giant arguments, and multiply the values for each target. This costs

    soft(b+M L/b+M), minimized at soft(sqrt(M L)+M).

There is no target-separation inversion: monic multipoint evaluation handles repetitions and composite coefficients, and all arguments and products are explicitly supplied. A clipped last baby block is evaluated too. For J~k and L~k^2 this is soft(k^(3/2)/sqrt r), below the full-family k^(3/2) clock when r grows. The claim is the paid endpoint BATCH only. It does not evaluate Z(C,D), whose r root arguments remain interior data.

This acquisition is an ordinary explicit algorithm and may be used even when endpoints are zero: its output is the full value vector. Norm/coordinate classification afterward factors where appropriate; a saturated artificial endpoint is only an unconsumed auxiliary value unless a separate decoder is proved. The h=r endpoint is not silently identified with the canonical h=0 row, despite its tag congruence.

## 4. Why the attempted scalar monodromy did not close

After t shifts the parameters are exactly

    C_t=C D^t E^(t^2), D_t=D E^(2t).

At t=r the D parameter is D E^(2r), not D. At t=r^2 the acquired clock identity gives

    C_(r^2)=C D^(r^2) q^(a r^2),
    D_(r^2)=D q^(2a).                            (2)

The factor D^(r^2) contains barpi^(-2m r^2). It has not been proved a short power of q, a unit normalization of the desired query, or an E-resultant multiple. Thus (2) is not a periodic boundary condition. The known start Z(0,D)=1 cannot be reached from a unit C by this multiplicative shift. It is a different parameter orbit, not an initialized amplitude for (1).

The interior-hit issue is especially concrete. Let A_h=P_L(Y_h). Then

    Z=A_0 U, Z_shift=A_r U, U=prod_(1<=h<r) A_h.

When a covered zero is at an interior h and endpoints are units, BOTH products vanish locally. The acquired multiplier A_r/A_0 is a unit and carries no test for that zero. For any first variation acting identically on the shared factors, differentiating gives

    dZ_shift=(A_r/A_0)dZ

at that interior zero (endpoint derivative terms are multiplied by U=0). Consequently subtracting the acquired normalized shift also cancels its interior first-order signal. This is an actual finite-factor calculation, not an inference from generic rank or degree.

Endpoint hits can yield usable tests, but covering every possible h by shifted endpoints requires all r positions. Acquiring those original row values over all classes reverts to the old full batch cost soft sqrt(JL). No deterministic assertion that the unique native hit lies at the chosen endpoint is available. Coarse labels constant within a class do not supply the missing choice of class.

## 5. Completed continuation and the precise remaining operation

The safe completed continuation remains the predecessor coarse-label reset with actual polynomial F of degree J and class directions degree J-r. Its full initialized block algorithm costs soft sqrt(JL), retaining the original q carries, all norm-leaf labels and verified bounded beta consumer. The endpoint batch from Section3 is optional and does not worsen this clock. Wrong orientation or unusable auxiliary data take that verified fallback; no heuristic residue is accepted as a factor.

A new scalar primitive would have to initialize Z(C,D), or preserve a nonzero interior weak-readout direction while using the paid endpoint multiplier, without supplying all r shifted endpoint values. Identity (1) and the known relation E^(r^2)=q^a alone do neither. This conclusion concerns the executed finite class-transport candidate only. It is not a lower bound on other class algorithms, determinant corrections, or future coarse-tag acquisition.

All starts, endpoints, powers, divisors, masks and indices used in this attempt are specified above. No shared/frozen source was edited and no numerical experiment was used.
