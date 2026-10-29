# Bettin–Drappeau modular-reciprocity audit

25 October 2026. No soft-k algorithm or new finite-field identity obtained.

Primary: S. Bettin and S. Drappeau, *Modularity and value distribution of quantum invariants of hyperbolic knots*, Math. Ann.382(2022),1631–1679, DOI10.1007/s00208-021-02288-2. Author PDF, dated28 September2021: https://drappeau.perso.math.cnrs.fr/documents/reciprocity.pdf ; arXiv https://arxiv.org/abs/1905.02045 . Local inspection: reciprocity.pdf / reciprocity.txt in this scratch directory. Rendered p.20 to verify modular-inverse overbars.

## Exact source capsule

Theorem6 uses coprime n,d, x=n/d, gamma=[[p,-cbar],[c,pbar]], p*pbar+c*cbar=1, k=nc+d*pbar, gamma(x)=h/k. For1<=r<k, L=floor(rd/k), lambda={rd/k}, its exact formula is

    ((e(gamma x))_r e(gamma x/24))/((e(x))_L e(x/24))
      =exp(A+0.5log(k/d)+k/(cd)*calL(lambda)+E_r(lambda,d/k)),
    A=pi*i*(p+pbar)/(12c)-pi*i*s(p,c)-pi*i/4.

Here e(z)=exp(2pi*i*z), (a)_r=prod_(j=1)^r(1-a^j). Equations2.10–2.14 define calL through a logarithm integral/dilogarithm; E_r contains c logarithmic Abel–Plana integrals. Bound2.15 is O(|log|1-lambda||+log(k/d)), with constants depending on d,gamma.

Theorem7 assumes coprime4<=h<k, 0<=r<k, r0=r mod h. Its roots-of-unity reciprocity has a dilogarithmic main term, cotangent sums, and a holomorphic correction bounded by

    O((1+|z|^4+|log(z(1-z))|)*(1+log(k/h)+k/h²)), z=r/k.

Equation2.34 is the exact finite-product precursor below. Theorem2's figure-eight ratio has main logarithm Vol(4_1)k/(2pi*h) plus a bounded analytic remainder, not a finite polynomial equality.

## Exact finite precursor and acquisition count

Write hbar for inverse of h modulo k, and kbar for inverse of k modulo h; these are the overbars in the source. The identity behind the second reciprocity is

    (e(-hbar/k))_r = (e(kbar/h))_r0 * h^floor(r/h) * P*M*Lcorr,

where

    P=prod_(1<=n<=floor(r/h))(1-e(-n/k)),
    M=prod_(1<=n<=r, h does not divide n) (1+e(-n/(hk)))/2,
    Lcorr=prod_(1<=n<=r, h does not divide n)
          [1-cot(pi*n*kbar/h)*tan(pi*n/(hk))].

The following acquisition count is our deduction, not a complexity theorem from the paper. The new main product has r0<h factors, P has floor(r/h), and each of M,Lcorr has r-floor(r/h). Thus a direct exact evaluation still acquires Theta(r) correction factors. Their arguments retain the original n clock. Merely calling the corrections a single function does not acquire their exact value cheaply. This is not a lower bound against a further undiscovered algebraic identity.

The proof's elementary local factorization can also be read algebraically. Put U=e(-x), V=e(y). Then

    1-e(y-x) = (1+U)(1-V)/2 * [1-tan(pi*x)*cot(pi*y)].

Replacing trigonometric functions by rational expressions in U,V makes the right-hand side an identity of rational functions; after cancellation it is simply 1-UV. Thus this exact local step redistributes factors. It does not discard the n-dependent correction. The full-block collapse uses a *complete primitive-root cycle*; it is that hypothesis that permits the scalar factor h, not generic geometric progression alone.

## Why the analytic modular transform cannot presently specialize to R=Z/NZ

These are deductions for our project inputs:

1. Our q=beta^H has unknown local orders greater than16H. The source's e(h/k), e(n/d), and e(kbar/h) have explicitly known rational angles and orders. To identify q with e(-hbar/k) and run an Euclidean denominator transformation, one must first provide the correct k/order data and compatible roots for the transformed bases. Large local order supplies neither. The two primes may give different orders.

2. One cannot replace those complex roots by arbitrary modular units while retaining complete-cycle identities. The relation prod_(n=1)^(h-1)(1-zeta^n)=h requires the appropriate primitive h-th root behavior in each residue field. It is not a Laurent polynomial identity in arbitrary zeta. A putative specialization must prove these orders independently. Guessing a denominator from the interval length does not do that.

3. The exact Theorem6 correction is analytically defined. Its dilogarithm, branch-sensitive logarithms, exponentials, and integration contours have no supplied operation in R. There is no unital specialization of the entire complex field into a characteristic-p field: 1/p already prevents it. Algebraic combinations may of course possess algebraic reductions after a separate proof, but that proof must produce a finite integral/cyclotomic expression and control all denominators. It is absent here.

4. A correction can be numerically small yet essential to exact modular divisibility. An O(log k) or O(1) error in a complex logarithm does not preserve a zero modulo either prime. Therefore truncating the correction cannot support the catalogue's exact collision/factor extraction. The figure-eight volume term and analytic remainder likewise provide no modular nonunit certificate.

5. Theorem6 permits fixed c, so the number of integral summands can be constant. This is not an exact finite-ring complexity result: evaluating an integral to floating precision and acquiring its exact residue modulo N are different tasks. The paper supplies no bit-complexity or reconstruction theorem turning those analytic corrections into soft-J modular arithmetic. It would be wrong to infer an Omega(r) lower bound from the integral representation, but equally wrong to count each integral as one available ring operation.

6. Repeated continued-fraction steps can shorten known rational denominators. Each step still carries its exact analytic correction. Without a finite-ring realization of those corrections, an O(log k)-step continued fraction is not an O(log k)-operation algorithm for our q-product. Even a known complex cyclotomic embedding could introduce degree phi(k) algebraic arithmetic and a precision/reconstruction problem; neither cost can be omitted.

7. Our requested product also has an independent starting unit X: prod_(i<h)(1-q^i X), with catalogue X=beta^(-E)q^(-M). The displayed source products begin at the first power of their base. Turning the catalogue's exponent progression Hi-E into those rational-angle products requires compatible beta-order data and a treatment of shifted arguments. The theorem does not directly supply that mapping.

## Composite-ring and localization conditions

The elementary finite-product precursor could be interpreted in an algebra with suitable named roots and rational-function denominators, but every denominator then needs an actual unit check. The hard branch makes2 a unit. It does not automatically make 1+U, 1-V, an arbitrary root-order parameter h, or all transformed cotangent/tangent denominators units. A failed test may produce a factor; a universally successful branch still needs a proved exact formula. Cleared identities remain legitimate but do not automatically recover a desired value from a zero-divisor multiplier.

Even if one derived a finite-ring counterpart for a single full product, the factoring execution requires exact restricted-row/index evaluation or an alternative witness-preserving locator. A numerical modularity estimate does not supply that localization contract. Each row's shift and each interval's boundary corrections must be acquired within the claimed total budget.

## Verdict and precise possible upgrade

The source offers exact **analytic** modularity and a genuine finite algebraic precursor. The finite precursor retains a linear number of correction factors; the compact analytic replacement is not an available modular-ring operation. No order-free algebraic reciprocity shortening the native interval was found.

A useful new theorem would have to express the *entire correction*, including shifted arguments, by a bounded number of finite algebraic operations over R in the given beta,q and O(log N)-bit integers, with no unknown order or root-of-unity hypothesis, and prove soft-k acquisition plus localization. That would be substantive new mathematics; it is not a consequence of the cited exactness or continued-fraction reciprocity.
