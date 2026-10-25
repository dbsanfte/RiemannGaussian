# Partial native CRT/carry notes (paused for explicit paper request)

For m=ab with gcd(a,b)=1 define r_a(x)=b*(b^-1*x mod a), r_b(y)=a*(a^-1*y mod b), each in [0,m). The canonical CRT section is exactly r_a+r_b-m*1_(r_a+r_b>=m). Thus its only mixed carry is a binary threshold after local reductions. All m input positions and threshold metadata are acquired in softm.

For the actual target exponent e_j=N+a_j+v_j, writing e_j-N as its CRT section plus m*c_j retains an additional native integer-lift carry. In a transform with output exponent s the corresponding factor is (gamma^m)^(s*c_j), not a diagonal independent of s. No exact contraction of these carries with the long multiplicative query was proved before this investigation was paused. A transform of the low residue alone does not preserve the source. No claimed native state compression or evaluator.
