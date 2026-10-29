# Independent review of qbinomial-joint.md

26 October 2026. Read-only algebra, initialization and cost review; no tests, numerical campaign or repository changes. Reviewed the report against the frozen fast-projective separation-review.md and README §§2–3.

**PASS, with the report's stated scope.** The common section operator and its transpose really are acquired in soft K over the actual composite coefficient ring. The remaining same-root diagonal has not been contracted by that fact. I found no algebraic correction needed.

## Finite sections, starts and endpoints

Writing f_t=(rho;rho)_t gives a_t=(-1)^t rho^{t(t-1)/2} f_h/(f_t f_{h-t}). Its successive ratio is exactly (rho^h-rho^t)/(1-rho^{t+1}). Multiplication over e consecutive ratios gives (1), including the A^e factor. With B=K, M=2K and h=BM+1, the full blocks cover precisely 0 through BM-1=h-2. The two additional indices are h-1=BM and h=BM+1; neither may be discarded.

C_B(Z_s) supplies f_{B(s+1)}/f_{Bs}. Hence its M values, followed by prefix multiplication, give f_{Bs} for s=0,...,M. Since h-Bs=B(M-s)+1, the extra single factor written in §2 gives every complementary factorial. This pays all alpha_s in soft(B+M), not M separate factorial evaluations. All denominator factors have indices at most h, and are units under the supplied short q-order/unit screen. The two tail a-values use the same data. Modular binary powering of X^{h-1} and multiplication by X give both b-tail values in soft J. These arguments use neither distinct evaluation nodes nor field interpolation.

## Common rational-Newton operator and transpose

Multiplying K_{s,e} by Q(Z_s) cancels denominator indices 1,...,e and leaves exactly e+1,...,B-1. The numerator indices are 0,...,e-1. Thus (3), including its degree at most B-1, is exact.

For the division-free basis conversion, splitting at m multiplies the left sums by the missing denominator factors indexed m,...,B-1, and the right sums by the missing numerator factors indexed 0,...,m-1. Recursing gives the asserted balanced product-tree conversion. The factors A^e can be preabsorbed into the supplied vector; A is a known unit. Products at one recursion level have total degree O(B), so the soft-B bound is valid.

Q(Z_s) has factor exponents Bs+r with 1<=r<B, at most BM-1<h. They are certified units. MPE uses monic node polynomials, so no node differences are inverted. The entire map from c to Kc is therefore a linear straight-line circuit over the actual coefficient ring, with only already supplied constant inverses. Its reversed/transposed circuit has the same asymptotic operation count. This is a valid ring-level transposition assertion, not an interpolation theorem requiring distinct roots or a field.

## Spectral pairing and actual completion

On the certified separated branch, the frozen separation theorem does supply unit F'(y_j) in soft J, or a proper factor. A saturated wrong-family attempt may be declined; one good family has the proper-or-unit guarantee. For sum b_t z^t=P(z)/rev(F)(z), partial fractions give exactly lambda_j=P(y_j^{-1}) y_j^{J-1}/F'(y_j). Native roots are units, so every inverse used here is licensed.

V1 and VB have the claimed cheap forward/transposed actions: MPE gives the transpose-to-coefficient action, while a weighted product tree for the rational function sum_j w_j/(1-y_j z), expanded to the requested finite precision, gives weighted power sums. Repeated powered roots in VB cause no inverse or separation issue.

Expanding the j-th diagonal entry of VB^t diag(alpha) K V1 gives sum_{s,e} alpha_s K_{s,e} y_j^{Bs+e}. Multiplying by lambda_j and summing proves (4) exactly. It is crucial that both Vandermonde factors use the same j. Independent sums or one arbitrary vector action do not give this weighted diagonal. Applying the paid K action separately for each j costs soft(J(B+M)+K); no omitted initialization restores a faster completion in the report. This is an executed-route cost, not a lower bound for structured diagonal evaluation.

Finally, for fixed F, expressing ell by its J values on 1,X,...,X^{J-1} makes S=ell(G_h mod F) linear in those supplied coefficients. A proposed linear circuit with ell-independent preprocessing and certified constant divisions can be transposed to recover that remainder vector at the same asymptotic cost. This consequence does not extend automatically to nonlinear projective readouts, singular branches, or circuits whose preprocessing/branching depends on ell. The report states these qualifications adequately.

**Disposition:** accept the finite kernel, all-start/tail initialization, both paid linear actions, exact diagonal interface and transposition consequence. No new full-query, norm or first-jet speedup is established; the stated old complete-query bounds remain the relevant baselines.
