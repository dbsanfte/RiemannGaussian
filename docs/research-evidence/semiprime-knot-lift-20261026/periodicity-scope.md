# What prime-period Frobenius identities can preserve

26 October 2026. Primary-source check supporting the Frobenius screen, not a general prohibition on knot methods. This records a direct consequence of Murasugi's standard congruence, not a new knot-theory theorem.

Hillman–Livingston–Naik, *Twisted Alexander polynomials of periodic knots*, Algebraic & Geometric Topology 6 (2006),145–169, Theorem 2 (Murasugi), states for an ordinary p-periodic knot with quotient knot Cbar

    Delta_C(T) = Delta_Cbar(T)^p delta_lambda(T)^(p-1) mod p,
    delta_lambda(T)=(1-T^lambda)/(1-T),

up to the usual Laurent units; lambda is the linking number with the fixed axis. Primary published PDF: https://msp.org/agt/2006/6-1/agt-v6-n1-p05-s.pdf ; DOI https://doi.org/10.2140/agt.2006.6.145 . Their Theorems 3–5 treat twisted or freely periodic versions with additional representation and normalization data, so the following ordinary-polynomial argument must not be extended to those without a new proof.

Suppose the reduction of Delta_C has Laurent span D satisfying 0<D<p-1. Because Delta_C(1)=1, it is nonzero, as is Delta_Cbar modulo p. A vanishing delta_lambda (lambda=0) is impossible in this identity. For nonzero lambda the geometric polynomial has Laurent span |lambda|-1; its extreme coefficients are units even modulo p. Span is additive on products of nonzero Laurent polynomials over a field. Therefore

    D = p*span(Delta_Cbar mod p)+(p-1)(|lambda|-1).

Both terms are nonnegative integers. If |lambda|>=2 the second term is at least p-1, impossible. Thus |lambda|=1 and D is a multiple of p, again impossible. No ordinary p-periodic knot can have this reduction.

For the native K, each factor 1+c_j(T+T^-1-2) has unit extreme coefficients, so its reduction modulo either hidden prime has EXACT span 2L. If 0<2L<P-1, no choice of integer knot lift with reduction K can have ordinary period P. In particular an ordinary N-periodic realization would imply such a P-periodic action by restriction and is impossible. This applies eventually at the native scales: L=soft O(k) while P>16k^2. No explicit small-k threshold is claimed from soft notation. It concerns the original nonzero polynomial, not arbitrary other collision detectors or topology with no fixed axis.

One can instead manufacture a periodic connected sum of many identical knots, replacing K by a high power. Such a change preserves its zero predicate but raises its degree; the corresponding congruence is compatible with that repeated power. It does not by itself evaluate product_i K(t_i). Evaluating a single repeated matrix power also differs from composing the native shifted factors, whose coefficients change with i. The useful arithmetic consequence extracted in this pass is the directly executable N-power order screen in frobenius-screen.md, rather than assuming a periodic native knot exists.
