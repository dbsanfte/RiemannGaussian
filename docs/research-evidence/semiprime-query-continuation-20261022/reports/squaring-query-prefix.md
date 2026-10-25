# Original resultant squaring and the attempted low-prefix contraction

No soft-O(m) original query is proved. This pass tests the proposed squaring/low-precision bridge on the actual differences, rather than on an auxiliary character observable.

Let x_j=beta^(N+delta_j), q=beta^(m²), H_L(X;q)=product_(i<L)(X−q^i), and V=product_j H_L(x_j;q). Define F^[2] to be the monic polynomial with roots x_j². The exact identities are

 H_L(X;q)H_L(−X;q)=(−1)^L H_L(X²;q²),
 V^[2]=product_(j,i)(x_j²−q^(2i))
       =V * product_(j,i)(x_j+q^i).                    (1)

Every extra factor in (1) is a unit in Z/N: its ratio x_j/q^i is an odd-order local element and therefore cannot equal −1. Thus V and V^[2] have IDENTICAL prime support, row/interval restriction preserves that assertion, and a transformed leaf is the SAME original leaf. No intersecting cyclotomic component masks or norm-only recovery are used. The original exponent gap remains available to the bounded-leaf controller. Values of the unit correction are unnecessary if the future query returns only factor/support information.

## The actual attempted axis reduction

The target Graeffe transform is paid soft O(J), and the transformed seed has the same implicit q-binomial form with q squared. A direct repetition keeps degree J and length L. To obtain progress, one would need to compute support from only O(m) coefficients/directions of this transformed resultant, or build a genuinely shorter geometric interval.

The coefficient-prefix possibility does not get a free vanishing tail. Explicitly

 [X^(L−r)]H_L(X;q)
 = (−1)^r q^(r(r−1)/2)
    product_(t=L−r+1)^L(1−q^t)/product_(t=1)^r(1−q^t). (2)

All factors in (2) are units because 1<=t<=L<ord_P(q),ord_Q(q). The empty products cover both endpoints. Squaring preserves the ODD local orders exactly, so EVERY coefficient remains a unit after ANY number of these squaring steps. This is a precise statement about this proposed tail-elimination repair, not a lower bound on implicit algorithms. Low coefficients can still be acquired quickly, but no part of the remaining polynomial is justified as zero or as an independently removable unit multiplier on the target quotient.

The direct perturbation from `direct-product.md` remains the useful O(J)-precision formulation:

 D(epsilon)=Res(F,T^L−Y+epsilon U),
 U=H_L−T^L+Y,   deg_epsilon D<=J.

Its full value at epsilon=1 is obtained from a prefix J+1. Under (1), both F and H_L can be squared without acquiring the plus-factor correction for a support-only query. But U is still a length-L geometric-factorial direction on the actual target quotient. Squaring does not shorten it. Reducing U modulo F supplies a short direction but is precisely the unacquired H_L remainder. The reversed resultant orientation supplies a short target direction but has epsilon-degree L. Thus this particular bridge has not combined its favorable precision and favorable direction size on one paid cyclic carrier.

## Large cyclic rank with small prefix: checked arithmetic, absent original-grid embedding

The refined interpolation bound really is independent of a possibly huge dyadic norm rank M. At a multiplication stage p, q0=min(p,h−1), the product candidate has

 j<=2q0,  e_normalized<=j+4+ceil(L_U/p).

With radix 2q0+1, its exponent span is at most

 4q0²+12q0+4+(2q0+1)ceil(L_U/p)
 <=4h²+14h+5+3L_U.

For h,L_U<=m and m>=2 this is below16m². Negative shifts use the same removed-shear parity and formal Laurent normalization as the reviewed constructor. Therefore the prepared interpolation unit can pay the sparse norm even when M is much larger than m. This arithmetic fact does not require local order exceeding M.

However the original seeds q^i are a GEOMETRIC interval. They are not the conjugates of X^M=Y for such an M. A large cyclic rank and a small prefix do not identify those two root multisets. The completed root-of-unity twists in (1) are unit companions of ONE given geometric seed; they do not turn L distinct seeds into one fibre. No embedding of all original rows and seeds into a bounded-width cyclic norm with h,L_U<=m was constructed here. The refined cap is consequently not presented as an original-query algorithm.

## What a successful next step would have to compute

A valid support-only recurrence could use (1) without knowing its unit correction, provided it actually decreases a charged axis or acquires its basecases. The missing contraction is still the original geometric factorial remainder/norm on F, or another restriction-stable scalar observable with equivalent leaf support. A recurrence that merely rebases beta, or returns a cyclic component hit, does not do this. The metadata delta, including all native ell carries, and the original seed index remain intact throughout this pass.

The positive verification is exact same-leaf support preservation and the rank-independent prefix cap. The attempted coefficient/direction reduction did not close, so no sixth-rate factorizer or new collision runtime is claimed.
