# Fresh primary lead for mixed diagonals: a generator plus one action suffices

2026-10-16. Positive conditional interface; no new generator or whole-query algorithm is supplied.

A targeted search for rational-Newton/Vandermonde product diagonals identified a directly useful exact primitive in Bini--Meini--Poloni, Fast Solution of a Certain Riccati Equation Through Cauchy-Like Matrices, Electronic Transactions on Numerical Analysis 33 (2009), 84--104, section 3.3, equation (3.9):

 https://etna.ricam.oeaw.ac.at/vol.33.2008-2009/pp84-104.dir/pp84-104.pdf

The full primary PDF and extracted text were saved adjacent as trummer-diagonal.pdf/.txt and inspected. The paper itself develops O(n²) numerical Riccati methods; the following ring-safe fast-diagonal application is an explicit algebraic specialization, not a nearlinear complexity theorem quoted from that paper.

Let Z=diag(lambda_1,...,lambda_n), with unit pairwise node differences in a commutative ring. Suppose an n-by-n matrix T is given by

 ZT-TZ=UV^T, with U,V having rho columns,

plus an algorithm for one action T*1. For i!=j,

 T_ij=sum_(ell=1)^rho U_iell V_jell/(lambda_i-lambda_j).

Let O be this prescribed offdiagonal matrix with zero diagonal. Then exactly

 diag(T)=T*1-O*1.                                    (1)

No division by the unknown T_ii, row value, or an arbitrary input vector occurs. Given the generator, O*1 is computable in soft O(rho*n) by rational multipoint evaluation with diagonal terms removed. Explicitly, for one generator column v define P(x)=prod_i(x-lambda_i) and Q(x)=sum_i v_i P(x)/(x-lambda_i). Its regular part at lambda_i is

 sum_(j!=i) v_j/(lambda_i-lambda_j)
   =Q'(lambda_i)/P'(lambda_i)
      -v_i P''(lambda_i)/(2P'(lambda_i)).

Product trees, interpolation or transposed evaluation construct Q in soft O(n); evaluation and differentiation have the same clock. P'(lambda_i) is a unit from the difference promise; 2 is a unit on our odd-N branch. Thus (1) is nearlinear for rho=polylog n if the generator and T*1 are already paid. This gives a stronger input contract than merely observing that diagonals can be recovered from an explicitly known matrix.

The condition is acquisition of a COMPATIBLE commutator generator. The standard product identity

 Z(AB)-(AB)W=(ZA-AY)B+A(YB-BW)

turns low-rank generators of two matrices into a short product generator only when their middle displacement operator Y agrees. The rational-Newton block coefficient matrix has the exact pencil recurrence

 C_(n,s+1)-q^L C_(n,s)
  =q^(Bn+s)(q C_(n,s+1)-C_(n,s)),

while the mask interpolation factor contains powers z_j^(-s). The induced mixed kernel satisfies a q-difference relation involving values at qz, rather than a supplied ordinary fixed-node commutator generator. Fast separate actions and transposes do not themselves provide U,V in (1). Nor has this note identified every required antidiagonal coefficient contraction with the diagonal of one matrix having that generator. Those are explicit remaining construction tasks, not complexity lower bounds.

The broader primary Bostan--Jeannerod--Mouilleron--Schost 2017 paper, already saved in this directory, gives structured operations from supplied generators and multiple-right-hand-side algorithms over a field. It does not erase these compatibility or composite-ring promises. Numerical approximate low-rank Cauchy/FMM results found in search are not exact Z/N algorithms and are not used.

No applicable primary theorem was found that acquires the missing mixed generator, or computes this particular mixed Cartier contraction from the two paid operators in soft O(m). The actionable positive lead is therefore: construct a polylog-rank compatible generator and one fast action for a matrix whose diagonal encodes the desired contraction. Then equation (1) pays diagonal extraction without materializing m² entries.
