# Independent swap-erratum review

Verdict: PASS, no required corrections.

Exact reviewed source: `swap-erratum.md`, SHA256 `1655476d3d979386229edea78ee0a6fe4cfbc4dd44807bc722fa7deefb302bf7`.
Compared directly with frozen scalar catalogue SHA256 `9ded79850c2f200069a7da67502d0de579d1df0457cb06c865fb3d39c9654058` and frozen terminal contract SHA256 `202706e6213e9ba5e9957c7e7d712a46e2a2dbd555329f4bf6298c2a017026c8`.

The erratum correctly repairs a substantive scope error that my earlier terminal review also accepted: the actual swap-closed catalogue DOES guarantee a globally zero index. The earlier generic observation about a product zero at both primes was valid without this additional symmetry, but was insufficient to justify the terminal contract's statement about this actual family. The old sources and review are preserved; this review supersedes that one scope conclusion.

1. Swapping (a,b) preserves the catalogue root equation and gives precisely E'-HI=(Q-1)(aP-b) at the SAME integer I. Its nonzero right side and the actual q-order/window bounds prove that both members survive public whole-row deletion. Thus the product F(q^(M+I)) is globally zero, even if neither original leaf is globally zero. Opposite signs and the canonical lambda carry give I'=kappa-I with |I'|<4sqrt(kN)/H+2<=M. Integrality for kappa=1, and coprimality/small coefficient bounds for kappa=0, prove distinct global indices. T_clock^(h-1)=0 follows.

2. The diagonal count is correct. For nonzero |a|<sqrt(k), writing |a|=uv with u supported on {2,3}, the inherited root bound is r(a^2)<=32u. Summing over v gives O(sqrt(k)) for each admissible u; there are O(log^2 k) such u. Hence J_diag=soft(sqrt(k)). With h=O(k^(3/2)), the actual monic product query costs soft(k), including localization and the licensed scalar consumer. On a unit result no diagonal witness remains, so deleting all diagonals preserves a nondegenerate swapped witness.

3. Discarding unpaired surviving rows does not reintroduce any public zero leaf and retains the proved witness pair. Its coefficients are acquired in soft(k). For a!=b, E-E'=(a-b)(1-N) is nonzero with O(log N) bits. A saturated gcd(A-B,N) therefore legally invokes the existing GLOBAL-annihilator extractor; a proper gcd factors immediately. On the continuing branch every retained A-B is an actual global unit, rather than an assumed separation property.

4. At the witness index z=q^s, the two local assignments z=A modulo P and z=B modulo Q prove that Q_pair(z)=0 globally. Unit A-B makes gcd(z-A,N)=P and gives the stated signs for (2z-A-B)/(A-B). Merely returning either known trivial root A or B is insufficient. A selected nonunit pair has a paid two-target interval completion and safe original-leaf recovery within soft(k), but the source does not acquire the selected pair or mixed root from the coefficients alone.

The final scope is faithful: these are stronger witness and preprocessing facts, with no faster whole-query algorithm or factoring exponent claim. No frozen source or shared file was edited.
