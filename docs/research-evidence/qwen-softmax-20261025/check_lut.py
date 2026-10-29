"""Certified real-softmax intervals; standard library CPU reference, not GPU code.
Decimal.exp is correctly rounded half-even; next_minus/plus enclose that exact exp.
All sums/divisions and binary-format rounding use exact Python integers/Fractions.
"""
from fractions import Fraction as F
from decimal import Decimal, localcontext
from collections import Counter
import random, math, json, struct
from pathlib import Path


def pow2(e): return F(2**e) if e>=0 else F(1,2**(-e))
def flog2(x):
    e=x.numerator.bit_length()-x.denominator.bit_length()
    return e-1 if x<pow2(e) else e

def rnd(x,p,emin):
    if not x: return F(0)
    if x<0: return -rnd(-x,p,emin)
    e=max(emin-p+1,flog2(x)-p+1)
    z=x/pow2(e); n,r=divmod(z.numerator,z.denominator)
    n+=2*r>z.denominator or (2*r==z.denominator and n%2==1)
    return n*pow2(e)

def dec_exact(x):
    k=x.denominator.bit_length()-1
    assert x.denominator==2**k
    n=x.numerator*5**k
    return Decimal((int(n<0),tuple(map(int,str(abs(n)))), -k))

def exp_enclosure(d,bits):
    if d==0: return F(1),F(1)
    if d>=bits: return F(0),pow2(-bits) # e>2 gives exp(-d)<2^-bits
    with localcontext() as c:
        c.prec=math.ceil(bits*math.log10(2))+2
        x=dec_exact(-d).exp()
        return F(x.next_minus()), F(x.next_plus())

def certified(h,p,emin,start=16):
    m=max(h)
    if len(h)==1:
        out=rnd(F(1,sum(h.values())),p,emin)
        return {m:out},0,0
    bits=start; calls=0
    while bits<=1024:
        es={a:exp_enclosure(m-a,bits) for a in h}
        calls+=sum(0<m-a<bits for a in h)
        lo=sum(n*es[a][0] for a,n in h.items()); hi=sum(n*es[a][1] for a,n in h.items())
        out={a:(rnd(l/hi,p,emin),rnd(u/lo,p,emin)) for a,(l,u) in es.items()}
        if all(l==u for l,u in out.values()):
            return {a:l for a,(l,u) in out.items()},bits,calls
        bits*=2
    raise AssertionError('refinement cap exceeded')

def f32(x):
    try: return struct.unpack('f',struct.pack('f',x))[0]
    except OverflowError:return math.copysign(math.inf,x)

def serial_f32(h,p,emin):
    m=float(max(h)); den=0.; vals={}
    for a,n in h.items():
        v=f32(math.exp(f32(float(a)-m))); vals[a]=v
        for _ in range(n):den=f32(den+v)
    return {a:rnd(F.from_float(f32(v/den)),p,emin) for a,v in vals.items()}

def main():
    rng=random.Random(20261025); stats={}; cases=[]
    for label,p,emin in [('bf16',8,-126),('fp16',11,-14)]:
        rows=[]
        rows.extend([Counter({F(0):n}) for n in [1,2,3,10,65536,248320]])
        rows.extend([Counter({F(0):1,F(-1000):248319}),Counter({rnd(F(65504),p,emin):7,rnd(F(-65504),p,emin):3}),Counter({F(0):3,pow2(emin-p+1):7})])
        # Exact finite representable inputs, no implicit FP32->16-bit cast in algorithm.
        for n in [10,128,1024,8192]:
            for _ in range(12):
                rows.append(Counter(rnd(F.from_float(rng.gauss(0,3)),p,emin) for i in range(n)))
        rows.append(Counter(rnd(F.from_float(rng.gauss(0,3)),p,emin) for i in range(248320)))
        ss={'rows':len(rows),'entries':0,'distinct':0,'initial16_certified':0,'refined32':0,'max_bits':0,'f32_serial_output_disagreements':0,'f32_serial_rows_differing':0}
        for j,h in enumerate(rows):
            got,bits,calls=certified(h,p,emin)
            reference,_,_=certified(h,p,emin,256)
            assert got==reference
            ss['entries']+=sum(h.values()); ss['distinct']+=len(h)
            ss['initial16_certified']+=bits<=16;ss['refined32']+=bits==32;ss['max_bits']=max(ss['max_bits'],bits)
            if sum(h.values())<=8192:
                alt=serial_f32(h,p,emin); mismatches=sum(h[a] for a in h if alt[a]!=got[a])
                ss['f32_serial_output_disagreements']+=mismatches; ss['f32_serial_rows_differing']+=bool(mismatches)
            if sum(h.values())==248320:
                cases.append({'format':label,'N':248320,'K':len(h),'bits':bits,'exp_calls_all_passes':calls})
        stats[label]=ss
    result={'contract':'round-to-nearest-even exact real softmax, exact finite rational logits, independent output rounding; not a named GPU kernel','stats':stats,'large_rows':cases,'reference':'same certified interval algorithm, initial certificate budget 256 (80 decimal digits); not an independent implementation','precision_semantics':'bits is a certificate/tail budget; Decimal exp uses ceil(bits*log10(2))+2 decimal digits. Exact Fraction sums and quotients may use many integer words. No hardware lower-precision cost claim.','not_proved_by_tests':'global fixed precision bound, GPU equivalence, speedup'}
    Path(__file__).with_name('results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
