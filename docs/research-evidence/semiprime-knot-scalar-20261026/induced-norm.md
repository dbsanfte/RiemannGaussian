# Induction and the native odd-weight norm

26 October 2026. Scratch research; no repository changes.

## Outcome and contract

There is an exact, finite-ring-valid index-two induction reduction for the repaired unit pattern. It replaces rank $2m$ on the pattern exterior by rank $m$ on a fixed double cover. It does **not** supply the requested softly $O(L+\sqrt m)$ scalar or zero test. A further positive cyclic-induction compression fails on the actual short native weight window, for the precise reason proved below. This is a failure of that candidate, not a lower bound against other algorithms.

Use the acquired reciprocal Alexander polynomial $K(T)=T^{-L}\det(V-TV^T)$, with the sparse integer Seifert matrix already constructed in [the acquired Seifert realization](../semiprime-knot-advancement-20261025/alexander-realization.md). Set $q=\eta^2=s_0^4$, and

\[
P_m=\prod_{j=0}^{m-1}K(\eta^3q^j).
\]

Both local orders of $q$ exceed $16H$, and $m\ll H$. All statements below apply separately over either residue field and, where stated explicitly, over $R=\mathbb Z/N\mathbb Z$. No order is acquired or assumed known. The prior tensor determinant and full cyclic-resultant reports remain authoritative; their descriptors are not new scalar algorithms.

## 1. Actual index-two induced module

For the two-component $T(2,4)$ pattern, write

\[
\pi=\langle a,b\mid (ab)^2=(ba)^2\rangle,
\quad a\mapsto\operatorname{diag}(z,z^{-1}),\quad
b\mapsto J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
\]

Let $\epsilon:\pi\to\mathbb Z/2$ send $a\mapsto0,b\mapsto1$, and $\pi_0=\ker\epsilon$. Every image of $\pi_0$ is diagonal. Its first diagonal entry defines a character $\chi_z:\pi_0\to R^\times$. The two-dimensional module is induced from this character. One can see this without semisimplicity: the line $Re_1$ is $\pi_0$-stable and the two cosets represented by $1,b$ send it to $Re_1,Re_2$. The map from the induced free rank-two module to $R^2$, $g\otimes v\mapsto\rho(g)v$, is an isomorphism; its basis determinant is a sign. Here $b^2$ acts as $-1$, so this assertion retains the central sign rather than silently replacing the binary-dihedral image by a dihedral one.

Apply this with $z=s_0^{2i+1}$, $1\le i\le m$. Thus the entire repaired representation is

\[
\rho_m\cong\operatorname{Ind}_{\pi_0}^{\pi}
       \left(\bigoplus_{i=1}^m\chi_{s_0^{2i+1}}\right).
\]

The associated cover has degree two independent of $m$. On cellular chains the usual induction map is an actual based free-module isomorphism: lift each base cell using the two coset representatives and match it with the corresponding induced basis. This argument works over $R$, requires no division, and preserves singularity as well as acyclic torsion. Changing lift conventions only introduces determinants of group-action matrices, which are units. It is therefore stronger, for specialization purposes, than quoting a field-valued torsion identity alone.

Primary source: Friedl–Vidussi, *Twisted Alexander polynomials and symplectic structures*, AJM 130 (2008), §3.2, Lemma 3.3 and its chain-module proof, gives the regular-cover version of this Eckmann–Shapiro identity. [Author PDF](https://math.ucr.edu/~svidussi/AJM08.pdf). The induced-character version used here follows from the displayed module map, not from an unverified extension of their field hypotheses.

### Normalization and cost

The previously checked pattern base has $F_a=2I$, $C^2=-I$, and $(C-I)^{-1}=-(C+I)/2$. Therefore its based acyclic torsion is $\pm2^m$, acquired by binary powering in $O(\log m)$ ring operations; 2 is a certified unit. Induction introduces no new factor involving (K). In particular it never divides by a collision value. The normalized finite determinant from [the unit-pattern construction](../semiprime-knot-fastprefix-20261026/unit-pattern-infection.md) remains

\[
\det\operatorname{diag}\left(2I_m,
 V\otimes I_{2m}-V^T\otimes\rho_m([a,b])\right)=2^mP_m^2.
\]

The $T^{-L}$ normalizations cancel between reciprocal axis eigenvalues. Over squarefree $R$, $P_m^2=0\iff P_m=0$, and the unit $2^m$ changes neither zeros nor gcds. This algebraic determinant statement does not upgrade the previously conditional identification with a particular raw infected-link Fox minor.

The cover has constant topological size relative to the pattern, but its coefficient module still contains $m$ distinct characters. Explicit acquisition costs at least $O(m)$ entries; including the sparse acquired knot presentation yields $O(Lm)$ nonzero scalar blocks in the direct presentation. A symbolic character-list rule is short, but evaluating its norm remains unpaid. Bit cost of these explicit acquisitions is their ring-operation count times softly $O(\log N)$; exponent initialization is logarithmic in the exponent sizes. No claimed improvement over the existing softly $O(L+\sqrt{Lm})$ evaluation follows.

## 2. A concrete further induction candidate and its native failure

An induced one-dimensional character from $r\mathbb Z\subset\mathbb Z$ sends the generator to a weighted cyclic shift. After choosing its coset basis, its characteristic polynomial is exactly

\[
T^r-c,\qquad c\in R^\times.
\]

Consequently its eigencharacters over an algebraic closure form a complete coset of the $r$-th roots of unity. This is the specific mechanism by which a cyclic-cover determinant can encode a full norm with a binary cover parameter. It does not encode the native truncated interval.

First, a single rank-$m$ such block cannot equal the native diagonal matrix $A=\operatorname{diag}(\eta^3q^j)_{0\le j<m}$, for $m\ge2$. The cyclic block has trace zero, whereas

\[
\operatorname{tr}A=\eta^3\frac{1-q^m}{1-q}
\]

is a unit in $R$: both numerator and denominator are nonzero in each residue field because the local orders exceed $m$. This check is finite and requires only binary powering and unit tests, not the order.

There is a stronger fieldwise obstruction to partitioning the weights into several **positive** nontrivial induced cyclic blocks. Let $D=\operatorname{ord}(q)>2m$ in one residue field. If a complete root coset of size $r\ge2$ lies in $\{\eta^3q^j:0\le j<m\}$, all its ratios belong to $\langle q\rangle$. Hence $r\mid D$, and its exponent set is a coset of the subgroup generated by (D/r) in $\mathbb Z/D\mathbb Z$. Every containing linear interval has diameter at least $D-D/r\ge D/2$: the $r$ equally spaced points have cyclic gaps all (D/r), and the shortest containing arc omits at most one such gap. But the native exponents occupy diameter $m-1<D/2$. Contradiction.

Thus positive cyclic induction can only use singleton blocks on this native interval. The proof uses the guaranteed order bound but does not need to compute $D$. It also avoids roots-of-unity denominators and works in every native instance. It does **not** exclude virtual Artin combinations, nonmonomial representations, or a native arithmetic identity for the acquired coefficients.

Virtual subtraction would require a proved quotient formula and certified unit denominator. A full-cover norm containing a native collision can itself vanish; replacing a partial norm by a quotient of two vanishing full norms is invalid in $R$. Merely writing an identity in a fraction field does not settle that branch.

## 3. Extension-field norm candidate

Another literal norm construction does not generate these weights. In each residue field $\mathbb F_p$, the native $\eta,q$ already lie in the ground field. Therefore a scalar $K(\eta^r)$ has extension norm $K(\eta^r)^d$, not a product over the changing native arguments. Trying to create a Frobenius orbit via $\xi^p=q\xi$ forces $\xi^{p^d}=q^d\xi$; if $\xi\ne0$ belongs to degree $d$, then $q^d=1$. No degree $d\le m$ can work. This is a direct candidate check, not a claim about all finite-algebra norm constructions.

## Constructive interface still needed

The genuine useful reduction obtained here is to a rank-$m$ local system on a fixed double cover, with an explicit integral chain isomorphism and only certified unit normalizations. To obtain the desired scalar bound, a further theorem would have to compute the determinant of that particular $m$-character local system in softly $O(L+\sqrt m)$, without expanding its characters or filling in a full root cycle. Equivalently, it must contract the acquired Seifert presentation against the **truncated** character sum $\sum_{j=0}^{m-1}[\eta^3q^j]$ while retaining zeros. No cited induction theorem supplies this contraction, and this report establishes no new fast prefix algorithm.

## Follow-up: safe 2-primary completion

The positive-subset exclusion above does **not** prohibit adjoining unit factors outside the native odd-order subgroup. Let F(X)=∏$X−x_j$, with native odd-order roots, and d=2^s. Define F_d(Y)=∏$Y−x_j^d$. In an étale splitting algebra for the d-th roots of unity,

    ∏_{ζ^d=1} F(ζX) = (−1)^{J(d−1)} F_d(X^d).

At a native argument u, every factor F(ζu) with ζ≠1 is a unit: in each residue-field extension, ζu=x_j would put a nontrivial 2-primary element in an odd-order group. Their product is therefore a unit. This proves that F(u) and F_d$u^d$ have identical zero and nonunit outcomes, without dividing by a collision value. Odd N makes the root algebra étale. For d=2 this is F(X)F(−X)=(−1)^J F_2(X²).

Repeated Graeffe steps acquire F_d in softly O(Js) ring operations without constructing an extension. Write F(X)=E(X²)+XO(X²); then F_2(Y)=(−1)^J(E(Y)²−YO(Y)²). The operation uses only polynomial multiplication. Hence

    ∏_{i=0}^{m−1} F(uq^i)  and  ∏_{i=0}^{m−1} F_d(u^d q^{di})

have identical zero and nonunit outcomes. This applies to the actual acquired native root family and its reciprocal completion. The local order of q^d equals that of q: no small clock order is created. Storage is O(J log N) bits, and the transformation costs softly O(Js log N) bit operations.

**What this does and does not compress.** In a residue-field algebraic closure, the product of the odd-order subgroup and the 2-primary roots has a well-defined projection hζ↦h: their intersection is trivial. Every completed 2-primary coset projects to a single native clock position uq^i. The native interval has m distinct projections. Powering by 2^s is bijective on the odd subgroup and preserves that count. Thus literal phase completion, induction over those phase cosets, and inversion of their unit complements do not themselves merge clock positions. This argument does not exclude a more general virtual identity coupling different odd projections.

The obvious coupling identity does halve the clock, but doubles degree. For m=2n, put B(X)=F(X)F(qX). Then exactly

    ∏_{i=0}^{2n−1} F(uq^i) = ∏_{j=0}^{n−1} B(uq^{2j}).

B costs softly O(J) to acquire and has degree 2J. After s levels the degree is 2^s J, and the standard degree-sensitive cost retains sqrt$(2^s J)(m/2^s)$=sqrt(Jm). Graeffe cannot identify these branches: its conjugate is −X, whereas the needed second branch is qX, and q is not a 2-primary phase. Combining these two identities therefore gives no rate improvement by itself.

Safe completion is a genuine loophole in the earlier positive-native-subset premise, and gives an acquired, zero-preserving Graeffe transformation. The remaining constructive interface is an identity coupling **different odd projections**, with only certified-unit corrections and acquired degree softly O(J). No such identity or faster scalar prefix algorithm is established here.
