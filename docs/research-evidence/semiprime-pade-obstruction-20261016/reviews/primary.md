# Independent primary-provenance review

2026-10-16. PASS, restricted to the exact polynomial/functional identities and their attribution; not a review of the full paper or a query algorithm.

Targets: literature-match.md1230 bytes/SHA256 `0a5c6291f515e374d21598fa3cbdb4a0b56d0650d3909d4764c3af990c427cee`; primary-fingerprints.json792 bytes/SHA256 `47f825ff586d99b6f2e92d9a59389287dbb3dceca5c988ba786d27d102b4ae8d`.

Independently checked the local publisher PDF and extracted text against both declared lengths/hashes: PDF306023/`cc1d9592f914b4333367a2a2225ec6b3bc07efb8e71a13ee7337bb4945f25a64`; text130678/`2491890dcd8d286685c72d3ab4af6b12364c8a5a39d97d1126e233275a3d9239`. Read Eq7, Theorem4.3 Eq44 and Theorem4.6 Eqs47–48 in that primary text. Primary URL https://cm.episciences.org/17491/pdf ; DOI https://doi.org/10.46298/cm.16723 .

Equation7 gives R_L(1,-X;q/g|q)=sum [L choose k]_q (-1)^k(q/g)^(binom(k,2))X^k, exactly C_L. In Eq44 with m=b,x=1,y=-X, the inner argument becomes -q^(b-k)(q/g)^k X=-q^b g^(-k)X; hence its b+1 terms use C_n(q^b g^(-k)X). This is a correct identity with both bases preserved, not a constant-term acquisition or nearlinear batch theorem.

For Eq48, write f(x)=C(-x), substitute x=-qX and u=q/g. The four terms become C(gX)-C(gqX)-gq^L X C(X)+gX C(qX), exactly the stated known equation. It is therefore correctly credited as prior. The independent finite-field proof rederives the polynomial identity and its finite-precision consequences algebraically; no analytic convergence domain or characteristic-zero theorem is imported into that proof.

The provenance note contains140 whitespace-delimited words in total, below200 even counting its title and links; it is a short paraphrase/formula identification rather than a substantial excerpt. It expressly makes no priority claim for the degree consequences and no paid acquisition assertion. No frozen files changed, no paper copied into the repository and no builds run.
