#!/usr/bin/env python3
"""Public ellipse/unique-cover constructor plus separate exhaustive validator.
Adapted from frozen semiprime-unique-weighted-20261026/check_unique_cover.py.
Standard library only. No group values, factor fields, orders or factoring runs.
"""
import argparse,json,math,time
from pathlib import Path

def valuation3(x):
    x=abs(x);v=0
    assert x
    while x%3==0:v+=1;x//=3
    return v

def exponent(K):
    assert K%2==0
    x=K//2;e=0
    while x%3==0 and x>1:e+=1;x//=3
    assert x==1 and e>=3,'K must equal 2*3^e, e>=3'
    return e

def roots_unit(value,modulus,ops):
    """At most two unit roots at 3-part, CRT parity, no K-colour scan."""
    odd=modulus//2 if modulus%2==0 else modulus
    if odd==1:roots=[0];power=1
    else:
        power=3
        roots=[r for r in (1,2) if (r*r-value)%3==0]
        ops['root3_lift_candidates']+=2
        while power<odd:
            nxt=power*3;new=[]
            for r in roots:
                for t in range(3):
                    ops['root3_lift_candidates']+=1
                    z=r+t*power
                    if (z*z-value)%nxt==0:new.append(z)
            roots=new;power=nxt
    assert power==odd
    if modulus%2==0:
        if value%2==0:return []
        roots=[r if r%2 else r+odd for r in roots]
    return sorted(roots)

def construct(K,N,B,validate=True):
    start=time.monotonic();e=exponent(K);assert N>1 and math.gcd(N,6)==1 and B>=1
    H=K*K;units=[j for j in range(1,K) if math.gcd(j,K)==1]
    inverses={j:pow(j,-1,H) for j in units}
    ops=dict(unit_inverses=len(units),bounding_pair_candidates=0,ellipse_pairs=0,
             conic_pair_tests=0,root3_lift_candidates=0,color_lift_candidates=0,
             phase_rows=0,direction_pair_keys=0,selected_support_marks=0)
    # Floor bounding semiaxes are safe 2-times upper caps, product<=8K.
    acap=math.isqrt((8*K*N)//(B*B));bcap=math.isqrt((8*K*B*B)//N)
    assert acap*bcap<=8*K
    def inside(a,b):
        Q=a*a*B**4+b*b*N*N
        return 3*Q*Q<=16*K*K*B**4*N*N
    catalogue=[];pair_rows={};own={j:[] for j in units}
    def add_pair(a,b,axis=False):
        ops['conic_pair_tests']+=1
        if (a+b*N)%4:return
        if axis:colors=units
        else:
            g=math.gcd(abs(a),K)
            if g!=math.gcd(abs(b),K):return
            mod=K//g
            assert mod>1
            aa=a//g;bb=b//g
            if math.gcd(aa,mod)!=1 or math.gcd(bb,mod)!=1:return
            ratio=N*bb*pow(aa,-1,mod)%mod
            base_roots=roots_unit(ratio,mod,ops);colors=[]
            for root in base_roots:
                for t in range(g):
                    ops['color_lift_candidates']+=1
                    j=root+mod*t
                    if 0<j<K and math.gcd(j,K)==1:colors.append(j)
            colors.sort();assert len(colors)==len(set(colors))
        if not colors:return
        rows=[]
        for j in colors:
            ell=(-a*j-b*N*inverses[j])%H
            if ell>=H//2:ell-=H
            g=math.gcd(abs(a),K) if not axis else K
            row=dict(a=a,b=b,j=j,ell=ell,g=g,axis=axis)
            assert (a*j*j-b*N)%K==0
            assert (a*j*j+ell*j+b*N)%H==0 and (2*a*j+ell)%K==0
            rows.append(row);catalogue.append(row);own[j].append(row)
            ops['phase_rows']+=1
        pair_rows[a,b]=rows
    if acap and bcap:
        for a in range(1,acap+1):
            for b in range(1,bcap+1):
                for sa in (1,-1):
                    for sb in (1,-1):
                        ops['bounding_pair_candidates']+=1
                        if inside(sa*a,sb*b):
                            ops['ellipse_pairs']+=1;add_pair(sa*a,sb*b)
    for a,b in ((2*K,0),(-2*K,0),(0,2*K),(0,-2*K)):
        if inside(a,b):add_pair(a,b,True)
    assert len(catalogue)<44*K
    assert all(own[j] for j in units),'public own-colour coverage failed'
    # Actual phase fibres, acquired from completed colour list only.
    classes={}
    for pair,rows in pair_rows.items():
        byphase={}
        for row in rows:byphase.setdefault(row['ell'],[]).append(row['j'])
        classes[pair]={ell:sorted(js) for ell,js in byphase.items()}
    directions={};fallback={}
    for (a,b),rows in pair_rows.items():
        positive=a>0 if b else a>0
        if a==0:positive=b>0
        if not positive:continue
        if a and b:
            d=math.gcd(a,abs(b));key=(a//d,b//d);t=valuation3(d)
            ops['direction_pair_keys']+=1
            old=directions.get(key)
            if old is None or t>old[0] or (t==old[0] and (a,b)<old[1]):
                directions[key]=(t,(a,b))
        for row in rows:
            if row['axis'] or row['g']%3:
                fallback.setdefault(row['j'],row)
    selected=[];covered=set();high=[]
    for direction,(t,pair) in sorted(directions.items()):
        if t==0:continue
        high.append(dict(direction=list(direction),pair=list(pair),v3=t))
        lookup={row['j']:row for row in pair_rows[pair]}
        for ell,support in sorted(classes[pair].items()):
            assert not covered.intersection(support),'high domains overlap'
            row=lookup[support[0]]
            selected.append(dict(row=row,support=support,kind='maximal_direction_phase'))
            covered.update(support);ops['selected_support_marks']+=len(support)
    for j in units:
        if j in covered:continue
        assert j in fallback,'missing singleton fallback'
        selected.append(dict(row=fallback[j],support=[j],kind='singleton_fallback'))
        covered.add(j);ops['selected_support_marks']+=1
    assert covered==set(units) and len(selected)<=len(units)
    assert sum(len(item['support']) for item in selected)==len(units)
    Dc=math.isqrt(2*K*N)+(math.isqrt(2*K*N)**2<2*K*N)
    M=(4*Dc+H-1)//H+2;h=2*M+1
    for item in selected:
        row=item['row']
        assert (row['ell']+row['a']+row['b']*N)%4==0
        phase=(M+(row['ell']+row['a']+row['b']*N)//4)%2
        item['public_row_phase']=phase
        item['shortened_length']=(h-1-phase)//2+1
        item['shifted_root_exponents']={'pi':row['ell']+H*(M-phase),
            'barpi':row['a']+row['b']*N}
        item['common_Q_exponent']=2*H
        item['padding_to_M0_plus_1_requires_endpoint_unit_gate']=phase==1
    assert h<16*H if N<=K**6 else True
    acquisition_seconds=time.monotonic()-start
    validation=dict(enabled=validate,direct_polynomial_tests=0,
                    selected_support_tests=0,axis_checks=0,parity_lift_tests=0)
    if validate:
        for row in catalogue:
            a,b,j,ell=row['a'],row['b'],row['j'],row['ell']
            if row['axis']:
                assert (a,b) in ((2*K,0),(-2*K,0),(0,2*K),(0,-2*K)) and inside(a,b)
                expected={j};validation['axis_checks']+=1
            else:expected=set(classes[a,b][ell])
            actual=set()
            for r in units:
                validation['direct_polynomial_tests']+=1
                if (a*r*r+ell*r+b*N)%H==0:actual.add(r)
            assert actual==expected,'phase class/direct root support mismatch'
            for r in actual:
                for R in (r,r+K):
                    assert math.gcd(R,2*H)==1
                    S=N*pow(R,-1,2*H)%(2*H)
                    numerator=a*R+b*S+ell
                    assert numerator%H==0
                    assert (M+numerator//H)%2==(M+(ell+a+b*N)//4)%2
                    validation['parity_lift_tests']+=1
        for item in selected:
            row=item['row'];actual=[]
            for r in units:
                validation['selected_support_tests']+=1
                if (row['a']*r*r+row['ell']*r+row['b']*N)%H==0:actual.append(r)
            assert actual==item['support']
    return dict(K=K,e=e,N=N,B=B,H=H,phiK=len(units),catalogue_J=len(catalogue),
        selected_J=len(selected),high_directions=high,
        rectangle_caps=[acap,bcap],original_clock=dict(M0=M,h=h,unchanged=False,q_exponent=H,shortened_Q_exponent=2*H,
            native_scale=N<=K**6,h_lt_16H=h<16*H),
        acquisition_operations=ops,validation_operations=validation,
        acquisition_seconds=acquisition_seconds,total_seconds=time.monotonic()-start,
        selected_support_partition=selected)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--K',type=int);ap.add_argument('--N',type=int);ap.add_argument('--B',type=int)
    ap.add_argument('--no-validate',action='store_true',help='constructor only; skip exhaustive O(K^2) checks')
    ap.add_argument('--output',default=str(Path(__file__).with_name('parity-cover-check.json')))
    args=ap.parse_args();start=time.monotonic()
    if any(x is not None for x in (args.K,args.N,args.B)):
        if any(x is None for x in (args.K,args.N,args.B)):
            ap.error('supply all of --K --N --B')
        rows=[construct(args.K,args.N,args.B,not args.no_validate)]
    else:
        rows=[]
        for e,axis in ((3,False),(4,False),(3,True)):
            K=2*3**e;N=K**6-1
            balanced=1<<(math.isqrt(N).bit_length()-1)
            B=1 if axis else balanced
            rows.append(construct(K,N,B,not args.no_validate))
    result=dict(kind='public amended parity-cover structural validation',
        source_credit='docs/research-evidence/semiprime-unique-weighted-20261026/check_unique_cover.py',
        fixtures=len(rows),elapsed_seconds=time.monotonic()-start,rows=rows,
        not_checked=['factor-field/group-order preparation','semiprime coverage by fixtures',
                     'fast acquisition of the selected long query','factoring success','endpoint unit gates required for optional length padding'])
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(fixtures=len(rows),elapsed_seconds=result['elapsed_seconds'],
        direct_tests=sum(x['validation_operations']['direct_polynomial_tests'] for x in rows),
        selected_tests=sum(x['validation_operations']['selected_support_tests'] for x in rows),
        summary=[dict(K=x['K'],N=x['N'],B=x['B'],J=x['catalogue_J'],
                      selected=x['selected_J'],high=len(x['high_directions']),
                      parity_tests=x['validation_operations']['parity_lift_tests'],
                      axes=x['validation_operations']['axis_checks']) for x in rows])))
if __name__=='__main__':main()
