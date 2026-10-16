# Independent review: normalized right operator in coefficient coordinates

2026-10-16. Verdict: PASS on the stated delta-unit branch. No original, integration draft, or repository file was changed.

Reviewed `/tmp/semiprime-extraction-20261016/diagonal/normalized-operator-note.md`: 2266 bytes; SHA-256 `78aa80b4b3d157ed48cf2d2858fb8e0d7a93f6df74ff542e0ab87d594b6ae21a`.

With W_(s,j)=z_j^s, WZ has the next powers in each row and the last power reduces by t^J=-sum_s h_s t^s. Therefore WZW^(-1)=U-e_last h^T with U on the SUPERdiagonal, exactly as stated. This is the correct row-coefficient companion orientation. Since U is nilpotent, G=sum_(r<J)a^r U^r is the inverse of I-aU. The determinant lemma gives det(I-aM)=1+a h^T G e_last; similarity gives its product expression product_j(1-a z_j). Sherman--Morrison then has exactly the reported MINUS sign and scalar factor a. It is valid over the composite ring when delta is a unit, with no field pivot.

The Mobius identity follows after multiplying by I-aM: a^(-1)(I-aM)+(1-a^(-1))I=I-M. Conjugating Q_row by W gives D_q, so the coefficient representation is D_q times this Mobius function, with the reported factor order. No commutation of D_q and M is assumed.

Every strictly upper off-diagonal block of G has rank at most one, while strictly lower blocks are zero. Its rank-one update increases either off-diagonal block rank by at most one, and diagonal left scaling by D_q does not increase rank. Thus the coefficient representation has quasiseparable rank at most two. Explicit generator data have linear size: geometric vectors come from powers of a; h^T G follows the recurrence v_j=h_j+a v_(j-1); G and its transpose act by suffix/prefix recurrences. H is acquired by a product tree. Delta can be computed as the product of J public scalar factors. All powers, the supplied a unit inverse, and the delta inverse are parameter-only paid setup, so the stated soft O(J) actions, transposes and storage are justified.

Because a product is a unit only if each factor is a unit, delta-unit also makes every 1-a z_j invertible. Their batch inverses cost softly linear work. Hence normalizing the rank-two block-pencil right side preserves its paid low-rank generators; multiplying by the known unit diagonal X^(-1) preserves that cost as well. Proper gcd failure factors N, while gcd N is explicitly left unresolved.

The quasiseparable statement is specifically in COEFFICIENT coordinates. To use a theorem requiring a quasiseparable right matrix, set R_coef=W R W^(-1) and M_tilde=M_block W^(-1). The transformed Sylvester equation is X^(-1)M_tilde-M_tilde R_coef=E W^(-1), whose two generator rows can be transformed by the already paid interpolation operators. This does not make the row-value matrix R quasiseparable in its original node basis, and does not recover the original mixed diagonal after a basis change.

The note correctly leaves spectral disjointness/uniqueness, saturated branches, the ordinary powered-node commutator, mixed diagonal, and determinant deformation unproved. It is a genuine paid conditional operator-structure check, not a whole-query or all-input algorithm. The previously reviewed README and journal bytes remain unchanged by this appendix review.
