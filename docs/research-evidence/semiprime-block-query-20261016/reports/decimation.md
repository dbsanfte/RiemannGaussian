# Binary decimation transports the unknown row payload; its mask has every dyadic phase

2026-10-15. Exact actual-source decimation identities, a paid transport map, and a scoped obstruction to pruning Fourier/mask channels. No nearlinear actual query or computational lower bound is claimed.

## 1. Exact multi-step Bostan--Mori numerator

Write F(t)=P_L(t;q), D(t)=product_(j=1)^J(1-t/z_j), and A(t)=F(t)/D(t). The z_j are the actual unit targets. Publicly deduplicate equal integer offsets when distinct nodes are needed, retaining their multiplicities for the final product. Let B=2^k and 0<=r<B. Define

 C_(B,r)(sum a_n t^n)=sum_(h>=0)a_(Bh+r)t^h,
 D_B(t)=product_j(1-t/z_j^B),
 E_B(t)=D_B(t^B)/D(t)
       =product_j sum_(s=0)^(B-1)(t/z_j)^s.

All are polynomial or formal-series identities over any commutative ring. Then

 C_(B,r)(A)(t)=N_(B,r)(t)/D_B(t),
 N_(B,r)=C_(B,r)(F E_B).                            (1)

Indeed 1/D=E_B/D_B(t^B), and Cartier extraction commutes with a denominator in t^B. For the target coefficient a_n use r=n mod B and h=floor(n/B). Iterated binary Bostan--Mori gives precisely (1), with bits of r consumed least-significant first. Its denominator remains degree J and constant coefficient 1. Its numerator degree is at most

 floor((L+J(B-1)-r)/B).

Thus for B=Theta(L/J), an explicit final numerator has only O(J) coefficients. This is a useful compressed end state. Neither its low output dimension nor the short denominator constructs that numerator.

Denominator updates D_(2B)(t)=even(D_B(t)D_B(-t)) cost soft O(J) per step. Alternatively build a chosen D_B directly from the J unit powers z_j^B by a product tree in soft O(J+J log B) operations. These steps are ring safe. The usual initial dense numerator acquisition still costs soft O(L); standard explicit decimation does not remove it.

## 2. Actual odd-order source: exact invertible transport of every row

In either retained hidden field, gamma has odd prime order R>16m^2, with L<=4m^2, q=gamma^(m^2), and every target lies in this same odd-order subgroup. Consequently any target ratio has odd order. Dyadic powering is injective on that subgroup, so distinct original nodes remain distinct after z->z^B, for EVERY dyadic B, without a magnitude restriction on B. The public offset deduplication is correct because the offset span is less than each local order. Differences between distinct original or powered nodes are units modulo N.

In a splitting extension containing a primitive B-th root omega (characteristic is odd), the mask obeys

 E_B(z_j omega^a)=0 for 1<=a<B,
 E_B(z_j) is a unit.                               (2)

The first follows from the j-th factor sum_s omega^(as). For the second, each factor sum_s(z_j/z_l)^s is nonzero: it is B when the ratio is 1, and otherwise equals (1-(z_j/z_l)^B)/(1-z_j/z_l); odd order forbids a nontrivial B-torsion ratio. This proof also allows duplicate nodes before deduplication.

The coefficient-projection identity is

 t^r N_(B,r)(t^B)
   =(1/B)sum_(a=0)^(B-1)omega^(-ar)F(omega^a t)E_B(omega^a t).

Evaluating at t=z_j and using (2) gives

 N_(B,r)(z_j^B)=z_j^(-r) F(z_j) E_B(z_j)/B.         (3)

It holds in both hidden fields and hence modulo N. All multipliers are units, so every row's prime-zero support and gcd with N are preserved exactly. Decimation neither removes a collision nor turns a saturated row into an informative one for free.

After public deduplication, the unit multiplier in (3) is cheap to acquire. Differentiating D_B(t^B)=D(t)E_B(t) at t=z_j gives

 E_B(z_j)=B z_j^(B-1) D_B'(z_j^B)/D'(z_j).          (4)

Build D,D_B and their derivatives, multipoint-evaluate at the two node lists, and batch-invert the unit derivative values D'(z_j). This costs soft O(J+J log B) ring operations and soft O(J) residue storage. Unit powering of z_j^r and division by B have the same paid logarithmic overhead; B is a unit modulo odd N. No private order is needed. For unqualified inputs a nonunit pivot needs factor-aware treatment: a proper gcd is useful, gcd=N is not an inverse. The claimed transport clock is conditional on the stated actual-source promise.

Therefore acquiring the O(J)-coefficient polynomial N_(B,r) at B~L/J would genuinely recover ALL original rows in soft O(J) further work, by monic multipoint evaluation and (3). Conversely the actual distinct-node value list determines N_(B,r) mod D_B by fast unit-difference interpolation. If its degree is >=J, this only determines the remainder, not the entire numerator: its polynomial part must not be silently supplied. This is a reversible row-payload transport, not a no-go for acquiring that payload implicitly.

Bit cost of the paid transport is soft O(J log N) when exponent bit lengths are polynomially bounded in log N, as for B<=poly(L), L~m^2. More explicitly include the displayed J log B and J log(r+1) ring-operation costs; modular multiplication and extended gcd have their usual soft log N bit costs. Larger supplied exponent lengths are not free.

## 3. Every mask polyphase is present on the actual source

Decompose the mask uniquely as

 E_B(t)=sum_(s=0)^(B-1)t^s E_(B,s)(t^B).

Applying root-of-unity projection to E_B alone and evaluating at z_j yields

 z_j^s E_(B,s)(z_j^B)=E_B(z_j)/B,  0<=s<B.          (5)

Each right side is a unit modulo N by (2). Hence EVERY one of the B polyphase polynomials is nonzero, indeed has a certified unit value at each original powered node. This is an actual-source statement, not an argument from generic polynomial degree or an assumption that all expanded mask coefficients are units.

Consequently the exact ansatz that retains only polylog(L) nonzero residue channels of E_B cannot survive to B~L/J~m: its unique residue decomposition requires all B channels. This rules out pruning the mask's residue classes themselves. The algorithm requests only ONE Cartier residue r for the target n: nonzero mask phases do not imply that all B outputs must be acquired, or exclude a direct fast single-channel convolution. It does not show that each output numerator coefficient has B independently costly terms, that fast convolution cannot combine them, or that another succinct nonlinear representation cannot encode all channels.

The input selected-coefficient primitive supplies O(m) chosen c_n=[t^n]F and their polylog-order jets nearlinearly. Formula (1) instead requests coefficients of F times E_B. Equation (5) explains why simply declaring that only polylog many mask phases remain is false. No theorem has been obtained to compute the needed filtered coefficient list at the selected-coefficient clock.

## 4. A Fourier branch cannot be omitted without a new pole payload

This is a second, deliberately narrow, actual-family obstruction. Work in either hidden field, deduplicate the nodes, and choose the retained m-o(m) unit rows. For each such row, A=F/D has a noncancelled simple pole at z_j. Consider its dyadic Fourier branches A(omega^a t), a=0,...,B-1. Their pole sets are disjoint across branches: equality omega^(-a)z_j=omega^(-b)z_l would make an odd-order target ratio equal a dyadic root, forcing a=b and z_j=z_l.

The lifted decimated rational function is

 t^r C_(B,r)(A)(t^B)
    =(1/B)sum_(a=0)^(B-1)omega^(-ar)A(omega^a t).    (6)

At each active pole of branch a, all other branches are regular, and the displayed scalar coefficient is nonzero. Thus (6) has an uncancelled pole from EVERY branch. No expression using a proper subset of branches with coefficients regular at the omitted branches' active poles can equal (6). In particular a constant-coefficient linear branch representation requires all B branches; their coefficients are unique by their disjoint poles.

This proves failure of a polylog-branch Fourier-pruning scheme at B~m. It does not prove an Omega(BJ) operation bound: pulling back by t->t^B expands pole orbits, while the compressed denominator D_B still has only J nodes. Rational branch coefficients allowed to introduce new poles, an implicit numerator circuit, fast transforms, and other representations lie outside this pruning theorem. A splitting extension is used only to prove the identity; constructing roots of unity/extensions is not a free algorithmic step.

## 5. Norm doubling is different from coefficient decimation

The genuine identity

 P_L(t;q)P_L(-t;q)=P_L(t^2;q^2)

is multiplicative. One Bostan--Mori step instead multiplies its numerator by D(-t) and extracts one parity. Replacing that by multiplication with F(-t) changes the rational series and the desired linear coefficient functional. The small denominator's norm is cheap, but a numerator norm does not equal its required even or odd channel. This distinguishes a possible nonlinear norm algorithm from a valid update for (1); neither is ruled out in general.

## 6. Primary contract and status

Bostan--Mori, A Simple and Fast Algorithm for Computing the N-th Term of a Linearly Recurrent Sequence, saved author preprint dated 19 August 2020, section 2.1/Algorithms 1--2 and Theorem 1, proves the ring-arithmetic rational extraction algorithm with supplied degree-d numerator and denominator. Theorem 3 also gives a nearlinear-logarithmic consecutive-slice algorithm for an ALREADY SUPPLIED short recurrence/initial-state rational series. Its ring-safe denominator evolution is fully applicable here. The original long numerator F, or the equivalent final row payload in (3), is not a supplied degree-J initial state. The quoted recurrence theorem therefore does not pay its acquisition. Primary PDF: https://mathexp.eu/bostan/publications/BoMo20.pdf . Exact PDF/text and inherited source/interface pins are in manifest.json.

No new actual-family soft O(m) acquisition algorithm was found. The substantive results are the explicit mask, the cheap exact invertible row transport, and the actual all-phase/all-branch pruning obstructions with the scopes above. They leave a fast implicit acquisition of N_(B,r), a direct norm computation, or another non-pruning transform open.
