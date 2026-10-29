# Retuned row-index acquisition through a marked two-GP resultant

26 October 2026. Constructive algorithm audit; scratch only. **Outcome:** an exact three-polynomial, constant-jet input to the retuned weak row-index selector is acquired inside the desired soft(J^(3/2)+sqrt(h)) budget. A complete safe evaluator is executed below, but its standard resultant/multipoint completion remains soft(J+sqrt(Jh)), hence an upper bound soft K^(4/3) on this retuned family. No improved exponent or general lower bound is proved. The main next operation is a selected tangent norm of two short GP algebras, rather than an unavailable outer polynomial or an uninitialized recurrence.

## 1. Actual native input and sufficient output

Use the frozen residue-shortcuts/content-cover.md §5.2 retuned unique partition, with original K preparation retained. For sufficiently large K take m the largest 3-power with m³<=K/1024, K'=K/m. The native selected bank has J<=phi(K')=O(K^(2/3)), actual common clock h=O(K²), exactly one good-component leaf, and all original numerical/order/label guards. Small K uses the inherited fallback; the new rate is conditional on a new evaluator.

Let the acquired actual normalized row roots be T_1,...,T_J. Give them DISTINCT integer marks w_j=j. No row-root separation or interpolation is needed for the construction below. Work in the fixed-rank jet algebra

A=B[epsilon_0,epsilon_1]/(epsilon_0²,epsilon_0 epsilon_1,epsilon_1²),

and acquire by a product tree

F_epsilon(X)=prod_j(X-T_j+epsilon_0+epsilon_1 w_j).

Its degree-J coefficients, including both tangent directions, cost soft J. Define

P(epsilon)=prod_(i=0)^(h-1) F_epsilon(q^i)=P_0+epsilon_0 V+epsilon_1 U.

At the unique good hit (j*,I), every other physical leaf is nonzero, so V is nonzero and U=w_(j*) V there. This is precisely the weak pair required by the frozen row-index consumer. Repeated roots or multiple hits elsewhere do not invalidate its good-component promise. This physical first variation is not the distinct short regularizer D(q^i)+delta.

After acquisition, norm-test V: proper gcd factors, gcd N declines a WRONG bin, and only gcd1 licenses inversion. Then coordinate-test U/V and scan gcd(U/V-j,N), j=1..J. A good attempt factors or identifies a real hit row. The remaining ONE-row query and actual-label localization cost soft sqrt(h)<=soft K. This review does not charge these costs to an unacquired hit index or require a hereditary oracle.

## 2. Execute an exact finite two-GP contraction

Choose b>=1, c=floor(h/b), r=h-bc. Acquire

B_b(Z)=prod_(u=0)^(b-1)(Z-q^u),
G_c(S)=prod_(v=0)^(c-1)(S-q^(bv)).

Their roots are explicit units, and product-tree acquisition costs soft(b+c); no integer factorial or local order is needed. The finite polynomial identity is

R_b(S;epsilon)=Res_Z(B_b(Z),F_epsilon(SZ))
              =prod_(u=0)^(b-1) F_epsilon(S q^u),

P(epsilon)=Res_S(G_c(S),R_b(S;epsilon))
           *prod_(i=bc)^(h-1) F_epsilon(q^i).          (1)

The monic first arguments fix signs and leading factors exactly; no hidden power of q or target-root factor occurs. This holds universally over the jet ring by the product definition of a resultant with split monic first argument. It therefore remains valid at every collision. Its two tangent coefficients ARE U,V, rather than an arbitrary amplitude requiring later clock normalization.

For the strongest target-budget input, take b=ceil(sqrt(h)), c=floor(h/b). Then B_b, G_c and F_epsilon have only soft(J+sqrt(h)) coefficients. In the maximal-row regime J=Theta(K') gives h=Theta(J³) and b,c=Theta(J^(3/2)); uniformly b,c=O(sqrt(h)). The tail r<b is itself cheaply completed: list its r explicit q-powers, evaluate degree-J F_epsilon by monic MPE, and multiply, costing soft(J+r)<=soft(J+b). All actual starts, tail product and first jets are therefore acquired uniformly in soft(J+sqrt(h))<=soft K, and in soft J^(3/2) in that maximal-row regime. For a WEAK-pair-only rectangle oracle, first gate every listed constant tail value F(q^i). A nonunit localizes at that clock to an actual row leaf in soft J and factors by the original mixed-label consumer; otherwise every tail value and their product are global units. All tail tests and algebraic leaf localization cost soft(J+r); the once-only original mixed-label extractor costs soft K separately on a terminating branch. On continuation the promised good hit lies in the rectangle, and its weak row-index ratio is unchanged by multiplying by the unit tail. Without this gate, exact full-product jets require the rectangle CONSTANT coefficient as well as its two derivatives; merely multiplying two derivative outputs would be incorrect. This is a genuine compact acquired input, not the old missing dense outer q-binomial coefficient array.

The source algorithm used as the concrete candidate is Bernstein–De Feo–Leroux–Smith, *Faster computation of isogenies of large prime degree*, ANTS XIV / Open Book Series 4 (2020),39–55, §3.1–3.3, Lemma3.4, Proposition3.5 and Algorithm1. Primary author PDF, version2020-06-16: https://velusqrt.isogeny.org/velusqrt-20200616.pdf ; https://arxiv.org/abs/2003.10118 . Local source copy retained at /tmp/velusqrt-20200616.pdf and text at /tmp/velusqrt-20200616.txt. Section3.1 explicitly formulates the multiplicative factorial over Z/nZ with only divisions by powers of its unit base; the proposition is stated over fields. I use its split-monic remainder-tree realization, not unsafe field Euclidean divisions, for the native adaptation.

For ONE scalar target alpha, the source forms two degree-sqrt(h) polynomials and computes their resultant in soft sqrt(h). Applying it componentwise to all J targets is soft(J sqrt(h)), not the desired bound. Treating alpha as the residue class X modulo F works over an algebra of rank J and has the same scalar cost. The first-order marks do not increase that algebra rank, but they do not remove it either. Thus the field-operation bound cannot be counted as base-ring operations for free.

## 3. Full safe completion of (1), not only its representation

A split-monic implementation acquires R_b by multiplying the b shifted degree-J polynomials F_epsilon(q^u S). All shifts are diagonal coefficient scalings. Balanced products cost soft(Jb), and the degree is Jb (its leading coefficient is a known unit). Monic multipoint evaluation of this actual R_b at the c supplied giant roots costs soft(Jb+c); multiply its c jet values. The residual length-r product is completed by monic MPE of degree-J F_epsilon at its r actual nodes and multiplication, costing soft(J+r); it does not assume r=0. Total cost is

soft(Jb+h/b+J),

with fixed jet rank three and no native value inversion. Taking b=max(1,ceil(sqrt(h/J))) gives soft(J+sqrt(Jh)). In the maximal-row regime h=Theta(J³), this is soft J². Uniformly the retuned bound is at most soft K^(4/3), not an equality for every selected bank. This worst-case guarantee is worse than keeping the original family at K^(5/4), so this is not an algorithmic gain.

A protected logarithmic derivative, transposition or reverse automatic differentiation of THIS completed circuit computes the same two coefficients in constant-factor overhead. It does not remove its R_b materialization: reversing the actual shift/product/MPE gates still traverses their degree-Jb coefficient arrays. At balanced b~sqrt(h), that array has size J sqrt(h), which is J^(5/2) in the maximal-row regime. At optimized b~sqrt(h/J), its size is sqrt(Jh), which is J² in that regime. This is a statement about the explicit source circuit, not a lower bound on selected tangent resultants.

The two nested resultant operations in (1) could be executed by other algorithms; the above size ledger does not forbid such an improvement. In particular the input factors B_b and G_c already have q-factorial structure, so calling them arbitrary supplied polynomials would discard real native data.

## 4. The exact structure-aware primitive that would now suffice

For b,c~sqrt(h), compute ONLY the two tangent coefficients in

Norm_(B[S,Z]/(G_c(S),B_b(Z))/B) F_epsilon(SZ),

without emitting the intermediate R_b. Required input is the acquired F_epsilon of degree J, the explicit GP bases and lengths b,c, plus the literal tail r. Output can be the full constant-plus-two-derivative rectangle jet, which combines exactly with the acquired tail. Alternatively, AFTER the explicit tail unit gate of §2, output may be just a weak (V,U) pair with the same good row-index ratio and a denominator nonzero there; its common unit tail scale need not be acquired again. A bound soft(J^(3/2)+b+c), with the stated composite-ring gates, WOULD give the desired sixth-rate handoff. This is a compact two-GP tangent norm, not a generic modular-composition input promise: every input coefficient and first-order source is already paid.

Equivalently, multiplication by SZ is the Kronecker product of the two acquired companion multiplication maps. The desired value is the determinant of F_epsilon of that tensor map. Its dimension is bc~h, but the input is only J+b+c. A dense tensor determinant or a generic black-box determinant is not the claimed algorithm. The relevant potential improvement is exploiting the TWO geometric companion moduli while extracting two selected norm derivatives. No row separation, mysterious initial vector or nonzero clock cofactor needs to be supplied to state this primitive.

One can transpose the output contraction after an actual remainder R_b is provided, but then one has paid Jb. Conversely a source-specific resultant algorithm that contracts the matched Sylvester/tensor directions before materialization would be substantive progress. This is more specific than the earlier modular-composition obstruction: the earlier frozen direct-contraction/composition-hybrid.md supplies fast coefficient-kernel actions, whereas here the outer split-monic factors and all marked roots are themselves explicitly acquired inside the separated budget. Neither source currently provides the fused tangent norm operation at that budget.

## 5. Ring/bit complexity and source boundaries

All product trees and MPE used above divide only by monic polynomials; powers of q are units. Standard fast polynomial arithmetic over B and its fixed-rank jet extension costs soft one operation per coefficient, with polylog(N) bit overhead per base-ring operation. No arithmetic in a known finite field, factorization of N, generic relation-degree profile, or randomized success assumption is used in the completed algorithm. Resultant continued fractions in a field can pivot on native zero divisors; the safe realization deliberately avoids claiming their field complexity for those pivots.

For comparison only, Bostan–Yurkevich, *Fast Computation of the N-th Term of a q-Holonomic Sequence and Applications*, arXiv2012.08656, §3.3–3.4 (primary https://arxiv.org/html/2012.08656), supplies matrix-q-factorial acceleration with explicit growing order/degree costs. Its fixed-sequence sqrt(N) conclusion does not set the acquired degree-J source to constant size. That known comparator is not counted as new progress here. The full bit-model treatment of an integer q in that work also does not turn unknown composite-ring values into a known finite field or remove J-dependent coefficient work.

No theorem located in this focused primary-source pass supplies soft(J^(3/2)+sqrt(h)) for the compact two-GP tangent norm. The initialized nested-resultant execution is correct but has only the upper bound soft K^(4/3) on the retuned bank. The original K^(5/4) factorer remains the best completed bound among these choices. No complexity separation or impossibility claim is made.
