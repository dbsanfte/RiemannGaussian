
## 2026-10-24: uniform quadratic rows and a shared scalar recurrence

This pass constructs a covered rank-two character family with ALL actual
rows, seed guards, and saturated norm-leaf recovery paid in soft O(k),
k=Theta(N^(1/6)). It removes the previous torus-survival premise for this
new family. Its scalar collision values share one acquired fourth-order
recurrence. The interval product still costs soft(J+sqrt(JL)), with
J<=k and L=2k^2+2; there is NO new factoring exponent or completed
bit/Lean sixth-rate proof. The earlier full-order Gauss vectors have not
been compressed into this different constructor.

Choose a negative fundamental discriminant D with Jacobi(D,N)=-1.
For N=3 mod4 use -4; otherwise scan a<=ceil(N^(5/32)), guarding gcds,
until Jacobi(a,N)=-1, factor this small public a, take its squarefree
core d, and use D=-d for d=3 mod4 and D=-4d otherwise. The accepted
Lau--Wu cubefree least-nonresidue theorem guarantees this bounded scan
for all sufficiently large N, with strict exponent slack. Trial division
on failed scans handles the finite exceptions; no effective threshold
or practical Burgess constant is claimed. The cost is soft N^(5/32).
Set c=|D| and k=2c ceil(ceil(N^(1/6))/(2c)). Then k is even, c|k,
k=Theta(N^(1/6)), and all unit-tag character values chi_D(j) are public.
Run the original scalar preparation at this ACTUAL composite k, including
the beta^H order screen, H=k^2. It factors or supplies the usual odd,
coprime local beta orders and both beta^H orders above C=16k^2.

Work in B=(Z/N)[tau]/(tau^2-D), with bar(tau)=-tau and
Norm(A+B1*tau)=A^2-D*B1^2. Exactly one hidden local algebra is a FIELD,
because Jacobi(D,N)=-1. We need not identify which one. The explicit
norm-one Cayley element

    W=(1+tau)/(1-tau)=(1+D+2tau)/(1-D)

is acquired: 1-D=1+c is below both prepared primes and is a certified
unit. No lower order or separator-survival assertion is made for W.
For every unit tag acquire the usual native a_j,b_j,ell_j,delta_j,
E_j=N+delta_j and e_j=chi_D(j). Define

    V_j=beta^E_j W^[ell_j+e_j(N+a_j)],
    z=(beta W)^H.

Every actual coordinate pair is computed in polylog N work per tag,
so all rows and their monic target polynomial cost soft k. At the own
tag j=P mod k, the old integer index HI=a_j P+Q+ell_j is still in the
covered interval. Its scalar difference is (P-1)(Q-a_j); its W exponent
difference is that same quantity if e_j=+1 and -(P+1)(Q+a_j) if e_j=-1.
Both vanish in the appropriate local groups. This proves V_j=z^I as
a WHOLE local-algebra equality. Retain raw tags; delta-only deduplication
can delete a distinct character target. Monic algorithms allow repeats.

The actual z screen is also paid. At the unknown field side p*,
z^d=1 would imply beta^(2Hd)=1, impossible for 1<=d<=C by the odd
prepared beta^H order. Thus Norm(z^d-1) is nonzero at p*. With b=4k,
construct product_(v=1)^b(X-z^v) and evaluate at z^(-bu), 0<=u<b.
These blocks cover exactly d=1,...,C at soft k cost. ANY nonunit block
norm yields a PROPER factor, since it is nonzero at p*. Otherwise all
short differences are units on BOTH local sides. No premature node-
distinctness assumption is used by this monic evaluation.

Recovery now works for every original norm leaf. For f=V_j-z^i,

    G=beta^(2E_j)-beta^(2Hi)=bar(V_j)f+z^i bar(f),
    (f,bar(f))=(f,G).

A proper gcd of Norm(f) factors. If it is N, the field side forces
f=bar(f)=0 there, hence gcd(G,N)>1. A proper gcd factors; a saturated
G gives the ORIGINAL beta collision at both primes, since their orders
are odd. The original bounded decoder then yields
P+Q=1+Hi-delta_j and verifies the integer factors. For family products,
localize to an ORIGINAL leaf before applying this identity. Different
hit leaves at the two primes cause no cross-leaf inference. This is the
new uniform recovery improvement; it does not transfer to arbitrary raw
primitive Gauss norms.

There is a fully initialized common scalar recurrence. Put
t=Norm(z)=beta^(2H), s=Tr(z), A=1+t+s, B0=2t+s(1+t). The actual values

    h_j(i)=Norm(V_j-z^i)
      =Norm(V_j)+t^i-bar(V_j)z^i-V_j bar(z)^i

obey, for every row, including zero or repeated-eigenvalue cases,

    h_j(i+4)=A h_j(i+3)-B0 h_j(i+2)
               +t A h_j(i+1)-t^2 h_j(i).

All common coefficients and all four initial values cost soft k. This
follows from (T-1)(T-t)(T^2-sT+t), without eigenvalue inverses. Its
executed family extension is g(i)=Norm(F(z^i)). Expanding F=sum f_a X^a
gives the actual (J+1)^2-term spectrum f_a bar(f_b)(z^a bar(z)^b)^i.
Pairing conjugate terms supplies a monic scalar annihilator of formal
degree (J+1)^2; its factors and all starts are acquired in soft J^2.
This is an overbudget completion, not a minimal-order lower bound.
The terminal product prod_i g(i) is still additional. The initialized
monic blocked query over constant-rank B remains soft k^(3/2).

The other recurrence attempts were executed as well. For the earlier
Gauss norm-one rows, an acquired v with v^2=Q0 centers every antipodal
pair and converts the three tau classes into TWO Dickson streams.
The even streams merge with their actual endpoints, without division.
A generator-based Jacobi unit update includes all native inverse-square
and centered carries, but its trace update needs the next mixed product
delta(X_j)delta(L_next). A fully supplied vector acquires it at soft k
per row. Seed decimation first pulls back F(T) to F(T^2-2), doubling
the actual degree. Neither test gives a cheap full trace product.

For the scalar resultant, shifting the QUOTIENT MODULUS makes binary
merging lawful. If P_b=prod_(i<b)(X-q^i), F_v=q^(-vJ)F(q^v X), and
S_b(v)=Res(F_v,P_b), then exactly

    S_(a+b)(v)=q^(abJ) S_a(v) S_b(v+a).

The corresponding remainder transport is monic and zero safe. Its
varying starts are actual F(q^v) values, not free constants. A complete
remainder forest costs soft(L+J); the executed transposed cut costs
soft(J+b+JL/b), recovering the existing soft(J+sqrt(JL)) bound.
Bounded global q-shift chains among native scalar offsets have at most
five members, by the global beta order and width 4H of the offsets.
This statement does NOT apply to unbounded shifts or one local field.
The inspected output-sensitive resultant papers did not supply the
missing deterministic implicit-input contraction.

Exact reports, independent reviews and preservation validation are in
`/tmp/semiprime-recurrence-closure-20261024`. The positive outcome is a
uniform, fully acquired character family with a shared scalar recurrence
and complete useful-leaf recovery. Cheap acquisition of the LONG product
remains open. No example campaign, broad Lean build, commit or push was
performed; previous prefixes, all 270 frozen entries and concurrent RH
work are preserved.
