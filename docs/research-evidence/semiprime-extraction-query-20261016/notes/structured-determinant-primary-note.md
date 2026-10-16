# Structured determinants: the supplied generator still matters

2026-10-16. Focused primary-source check prompted by the new paid block pencil. This note does not supply a determinant algorithm for the mixed matrix or claim a lower bound.

Primary source inspected: Pierre Karpman, Clément Pernet, Hippolyte Signargout and Gilles Villard, *Computing the Characteristic Polynomial of Generic Toeplitz-like and Hankel-like Matrices*, ISSAC 2021, author PDF:
https://perso.ens-lyon.fr/gilles.villard/BIBLIOGRAPHIE/PDF/kpsv21.pdf

The introduction gives softly O(alpha^(omega-1) n) field operations for determinants of the stated displacement-structured matrices. Its algorithms use supplied compatible generators. Section 2.1, especially Propositions 2.1--2.3, also charges the generators needed for structured multiplication and composition. Theorems 5.2 and 5.4 give subquadratic characteristic-polynomial algorithms under explicit genericity conditions, not a softly linear theorem for arbitrary fast-action operators. These statements concern a field and the stated Toeplitz/Hankel displacement structures.

Application audit. We have cheap actions of S and a rank-two generalized pencil for the block matrix C W. We have not supplied compatible Toeplitz/Hankel generators for S or for I+diag(theta)S. Nor have we supplied a conversion of its generalized operators to the operators in these theorems. Thus this paper does not currently pay the scalar formal circuit whose determinant gradient would return the row values. Field algorithms would additionally need a justified composite-safe execution. This is a prerequisite mismatch, not a proof that another generalized-displacement determinant method cannot work.

The exact new q-pencil and actual powered-node defect proofs are self-contained separate reports. This paper is supporting context only. Its PDF and layout text are preserved with hashes in the evidence source map; no theorem from it is imported as a successful acquisition step.
