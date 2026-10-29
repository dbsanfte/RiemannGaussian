# Actual common-character support: basis freedom and literal-union mass

26 October 2026. Read the current common-character normal form and the authoritative phase-index/Gauss-grid proofs. Scratch only; no tests, numerical campaign or repository edits. **Executed result:** the clock coefficient can be minimized explicitly, but exact literal support union still has Omega(k³) positions on a specified ACTUAL fixed-scale subfamily. This rejects a power saving through that exact merging route alone. It is not a scalar-circuit, implicit-norm, modular-alias, or factoring lower bound.

## 1. Basis freedom really can minimize the q-direction

For one acquired Gauss cell let e=(E_u,E_w) be its ACTUAL integer generator row, G=gcd(H,E_u,E_w), L=H/G, and delta=gcd(E_u,E_w)>0. Then s=delta/G is an integer coprime to L. A normalized unimodular basis with row (G+H*F,H*C) necessarily satisfies

    gcd(1+L*F,L*C)=s.

Since 1+L*F is coprime to L, this implies s|C and s|(1+L*F). Conversely choose F solving L*F=-1 mod s, and set C=s. The target row (G+HF,Hs) has gcd delta, because (1+LF)/s is coprime to L. Two integer rows with the same gcd are related by an acquired unimodular integer matrix (extended gcd). Thus the smallest POSSIBLE NONZERO |C| is exactly s, and it is attained in polylogarithmic bit work.

In particular, when delta=G, one may choose the exact row (G,H): F=0,C=1. This gives genuinely adjacent/overlapping q-direction slices IF the finite domain supplies them. It is not correct to assume a large C is forced.

C=0 is possible precisely when s=+1 or -1 modulo L: then the first entry must be +delta or -delta. Its clock translation F can still be large. For L=1 the phase character is zero; ordinary integer Smith normalization is legal separately, with no inversion modulo1. These statements refine the previous explicit normal form; they do not change its inherited common beta^G observation.

All matrices, labels and transported coordinates have O(log N) bits by the polynomial-height bounds in common-character.md. Each choice costs polylogarithmic work per cell, soft k over descriptors. Constructing the finite transported support is a separate expense.

## 2. An actual fixed-scale subfamily passes every public filter

Choose ONE enumerated public power of two p0 with sqrt(N)/2<p0<=sqrt(N). It exists in the original [8H,sqrt N] range since sqrt N>16H. Retain the k/6 colours j=2 mod3; these have g=gcd(j-1,k)=2 and G=4.

For each acquired reduced basis, put R=2k*sqrt N and the original dimensions A,B. Their canonical generator phases and unwrapped labels are exactly those of the authoritative query. The Gauss-grid bounds give A,B>=2, AB>=2sqrt3*k, and

    a_span<2R/p0<8k<H/2,
    b_span<2R/(N/p0)<=4k.

Thus EVERY one of these actual fixed-scale cells passes a_span<=H and a_span<H/g. This is not a freely chosen point set or a distributional hypothesis about the hidden factor. The complete PUBLIC query really contains this subfamily, regardless of whether this scale happens to be the correct factor scale.

Let z=(r,s) vary through its signed difference box |r|<A,|s|<B, z!=0. Its coordinate vector v=z1*u+z2*w lies in Lambda_j. The projection Lambda_j->Z on its b-coordinate is onto (use the basis (k,0),(a0,1)); hence the two acquired basis b-coordinates are not both divisible by3. Along one coefficient direction, at least half the residues in each odd-length interval 2A-1 or2B-1 give b nonzero mod3. Therefore Omega(AB)=Omega(k) differences in EACH cell have 3∤b. The origin never contributes to that count.

For every such z and every h=0,...,4k define its exact short integer leaf label

    K=e*z-H*h.

It is nonzero by the public source filter. There are Omega(k²) such labelled presentations per cell.

## 3. N-dominance and native phase determine the colour

Write e*z=a+bN+r*lambda_u+s*lambda_w. Since |a|<8k, A+B<4k, and each generator phase lies in[0,H),

    |K-bN|<(8k+1)H.                              (1)

As N>256H²>2*(8k+1)H, equality of two integer K values anywhere in this fixed-scale subfamily forces the SAME integer b. This remains true for different colours/bases.

Modulo k, the actual native character and lattice give

    K=a*(j-1)² mod k,
    a*j²=bN mod k.

For 3∤b, both bN and K are 3-units. Hence modulo 3^e,

    K/(bN)=(1-j^-1)².                             (2)

In the selected j=2 mod3 class, x=1-j^-1 is also2 mod3. This root branch is UNIQUE: if x²=y² and x,y=2 mod3, then x+y is a 3-unit, so x-y=0 mod3^e. Thus equal K,b determine j modulo3^e. Since canonical colours are odd representatives in[1,2*3^e), this determines j modulo k and as an integer. Consequently DIFFERENT selected colours cannot share one of these exact leaf labels K. This is the actual conic/colour restriction, not an independent-coefficient argument.

## 4. Within one colour each K has at most four presentations

Split the signed coefficient box into four rectangles using r>=0 versus r<0 and s>=0 versus s<0. Every rectangle has side lengths at most A and B. For two points z,z' in one piece, their nonzero difference lies in the original signed difference box.

If K(z,h)=K(z',h'), then

    e*(z-z')=H*(h-h'), |h-h'|<=4k.

For distinct z this contradicts the source cell's public nonliteral filter. Its proof applies to negative shifts too by reversing the difference. If z=z', then h=h'. Thus the map to K is injective within each piece, and any K has at most FOUR presentations in one colour/scale.

Combining Sections2–4 gives

    Omega(k) colours * Omega(k²) presentations/colour /4
       =Omega(k³) DISTINCT INTEGER LEAF LABELS.     (3)

All are actual nonaxis (in the 3-primary sense) input leaves of the current filtered grid query. This does not assert that every one is a genuine collision, or that their numerical beta values are distinct.

## 5. Consequence for EXACT common-character interval union

Any common-character basis choice transports a leaf to

    q^t-(beta^G)^n1,
    K=G*n1-H*t.

Thus each literal merged support position (G,n1,t) fixes its integer K. Exact interval unions, cross-cell slice grouping, and any unimodular choices of C_j can identify presentations only when that K agrees. The Omega(k³) distinct K values in (3) therefore imply at least Omega(k³) occupied literal support positions, regardless of how Cclock is minimized or the slices aligned.

This also explains the apparently favorable delta=G,Cclock=1 case. Its domain may have long adjacent q-directions in abstract coordinates, but actual source short-shift nonliteral filtering prevents same-piece leaves from collapsing; at most the four-piece multiplicity can disappear within a cell. Across selected colours equation(2) prevents further collapse of the counted labels. Choosing a different basis does not alter these integer facts.

This is a scoped obstruction to obtaining total mass soft k² by LITERAL common-support union on the complete current public family. It does not imply Omega(k³) time: long intervals can have short descriptions, and a new fast scalar product could exploit them. It does not rule out a smaller coverage-preserving cell subfamily, since the fixed-scale cells used in the count are not claimed individually necessary witnesses. Numerical modular aliases could also factor or support another algorithm; their recognition is not an integer interval union and is not ruled out.

## 6. Paid implementation and remaining route

A complete literal-union algorithm still enumerates O(k) actual differences per cell, soft k² total, computes the short-bit normalized slice coordinates, groups by (G,n1), and unions only acquired intervals with their source maps. It scans neither the potentially enormous sheared bounding box nor a long integer interval one point at a time. It costs soft k² to initialize; the inherited evaluator supplies its previous soft-k² full-query completion. The once-only T_ext is included on a terminating saturated branch and is below that scale.

The explicit basis minimization above is genuine useful freedom and can be applied without new scalar preparation. What fails is counting its common q-direction as a proven aggregate support saving. A substantive next step must compute the resulting structured norm without literal-support expansion, exploit numerical factor-return relations, or prove a much smaller universally covered colour/scale subfamily. No general algorithmic lower bound, phase-normalization impossibility, or new factoring exponent is claimed.
