
## Shared global collision indices and paid pair preparation, 2026-10-24

The full sixth-rate objective remains open. The current complete paper
algorithm still costs soft k^(5/4)=soft N^(5/24) at k=Theta(N^(1/6));
the known global fifth-rate comparison and unfinished Lean bit proof
are unchanged. This pass corrects a substantive statement in the last
scratch note and proves preprocessing within soft k. It does not supply
a faster whole-family locator.

The frozen terminal-contract.md in
/tmp/semiprime-scalar-terminal-20261024/ correctly established that the
complete aggregate is zero modulo N, and that one nonunit index suffices
for recovery in soft k. Its claim that the actual family does not promise
one globally zero index was FALSE. Its earlier independent PASS accepted
that scope error too. Both frozen files are preserved; the new exact-hash
erratum and review in /tmp/semiprime-arithmetic-locator-20261024/ supersede
that conclusion.

For the existing virtual Gauss witness, write

    HI=aP+bQ+lambda,
    E=a+bN+lambda, E'=b+aN+lambda.

The complete catalogue contains the swapped row (b,a,lambda), including
axes. The two exact identities are

    E-HI =(P-1)(bQ-a),
    E'-HI=(Q-1)(aP-b).

Both right sides are nonzero because |a|,|b|<=k<min(P,Q) and the pair
is nonzero. The screened q orders exceed the index window, so public
zero-row deletion removes neither witness. Therefore at s=M+I the SAME
point q^s equals T_(a,b,lambda) modulo P and T_(b,a,lambda) modulo Q.
The full F(q^s) is zero modulo N. This is not a claim that one scalar
leaf vanishes globally. Opposite signs provide a second distinct global
index; the previous conclusion that the clock's (h-1)st power is zero
remains valid. Its nonzero kernel coordinates are still not acquired.

There is a paid way to remove diagonal witnesses. For a=b, |a|<sqrt k.
Writing |a|=uv with u supported on 2,3, the existing root count gives
r(a^2)<=32u. Summing over smooth u gives only soft sqrt k diagonal rows.
Their full retained-row query costs soft sqrt((sqrt k)*h)=soft k.
Any nonunit is handled by the existing scalar leaf/extractor consumer;
otherwise the diagonal aggregate is certified a global unit and all
diagonal rows can be removed without losing the guaranteed witness.

Next retain only complete surviving swap pairs; deleting an unpaired
partner is safe because the genuine pair survives together. Acquire
A=T_(a,b,lambda), B=T_(b,a,lambda), and scan gcd(A-B,N). A proper gcd
factors. Saturation gives the explicit nonzero global annihilator
(a-b)(1-N), so the licensed short extractor factors. The continuing
branch therefore certifies every A-B as a unit, within soft k total work.

The remaining guaranteed witness is a global mixed root z=q^s of one
explicit quadratic (X-A)(X-B), with z=A mod P and z=B mod Q. Its
discriminant (A-B)^2 is an acquired unit. Knowing z would give
gcd(z-A,N)=P, equivalently a nontrivial square root
(2z-A-B)/(A-B) of 1. Merely returning A or B is not such a mixed root.
Every quadratic's coefficients are paid, but neither its relevant label
nor the mixed root is selected by this preparation. Querying one supplied
pair costs soft sqrt h, within soft k; selecting a useful pair from the
whole list remains unpaid at the desired rate.

The generic known-zero bisection can skip the full aggregate call, but
its first restricted interval still costs soft sqrt(Jh). No cancellation,
3-adic digit choice, or short-atom cover tested here removes that cost.
The conditional advice/annihilator consumers in scratch do not supply
their missing inputs and are not counted as whole-family acquisition.

Exact erratum, independent review, draft review and preservation checks:
/tmp/semiprime-arithmetic-locator-20261024/. Preserve all prior prefixes,
all 270 frozen entries, HEAD and concurrent RH/DeltaNet work. No examples
campaign, Lean backend batch, new exponent claim, commit or push.
