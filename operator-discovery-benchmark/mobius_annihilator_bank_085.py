"""Learn symbolic annihilator banks from exact artificial-witness violations."""
from fractions import Fraction as Q
from math import gcd
import mobius_annihilator_085 as A


class ScoreMeter(A.B.Meter):
    """Count bounded exact scalar work; guard fraction growth before products."""
    def __init__(self,limit=300_000_000_000):
        super().__init__(limit);self.max_fraction_bits=1

    def combine(self,a,b,divide=False):
        if divide and not b:raise ValueError('nonzero score denominator')
        bn,bd=(b.denominator,b.numerator)if divide else(b.numerator,b.denominator)
        if divide:bits=max(abs(a.numerator).bit_length()+abs(bn).bit_length(),a.denominator.bit_length()+abs(bd).bit_length())
        else:bits=max(abs(a.numerator).bit_length()+abs(bd).bit_length(),abs(bn).bit_length()+a.denominator.bit_length())+1
        bits=max(bits,a.denominator.bit_length()+abs(bd).bit_length())
        if bits>4096:raise A.B.ResourceLimit('prospective exact bank score4096bit budget')
        self.charge(8);self.max_fraction_bits=max(self.max_fraction_bits,bits)
        return a/b if divide else a+b


def descriptors(scale_height=12,exponent_height=8):
    if type(scale_height)is not int or type(exponent_height)is not int or not 2<=scale_height<=24 or not 2<=exponent_height<=24:
        raise ValueError('prospective rational grammar height budget')
    scales=[Q(a,b)for a in range(1,scale_height)for b in range(1,scale_height-a+1)if a+b<=scale_height and gcd(a,b)==1]
    exponents=[Q(a,b)for b in range(1,exponent_height+1)for a in range(-exponent_height,exponent_height+1)
               if abs(a)+b<=exponent_height and gcd(abs(a),b)==1]
    if len(scales)*len(exponents)*4*4096>1024**3:raise A.B.ResourceLimit('prospective rational descriptor budget1GiB')
    rows=[]
    for a in scales:
        for e in exponents:
            for complement in [False,True]:
                for balanced in [False,True]:
                    d=dict(scale=str(a),u_exponent=str(e),complement=complement,unit_balance=balanced)
                    cost=a.numerator+a.denominator+abs(e.numerator)+e.denominator+int(complement)+int(balanced)
                    rows.append(dict(descriptor=d,cost=cost))
    rows.sort(key=lambda r:(r['cost'],Q(r['descriptor']['u_exponent']),Q(r['descriptor']['scale']),
                            r['descriptor']['complement'],r['descriptor']['unit_balance']))
    for i,r in enumerate(rows):r['id']='a'+str(i).zfill(5)
    return rows


def catalog(program,parents,scale_height=12,exponent_height=8):
    if len(parents)>8:raise ValueError('training geometry count budget')
    models={u:A.B.build_model(program,u)for u in parents}
    for model in models.values():A.SQUARE._gate(model)
    generated=descriptors(scale_height,exponent_height);representatives=[];duplicates=[];seen={};cache={}
    estimate=16384+4096*len(generated)+sum(model['resident_bytes']+2*(model['N']+1)*(256+64*model['price_dimension'])for model in models.values())
    if estimate>1024**3:raise A.B.ResourceLimit('prospective complete annihilator catalog1GiB budget')
    for item in generated:
        columns=[];signature=[]
        for u in parents:
            model=models[u];d=item['descriptor'];parsed=A.parse_bank([d])[0]
            K=A.B.cut_value(1,u,model['N'],dict(parsed,n_exponent=Q(0)),model['meter'])
            key=(u,K,d['unit_balance']);signature.append(K)
            if key not in cache:
                column,den,_=A.identity_integer_column(model,d)
                model['meter'].charge(4*len(column))
                norm=sum(v*v for v in column);cache[key]=dict(column=column,denominator=den,norm=norm)
            columns.append(key)
        key=(tuple(signature),item['descriptor']['unit_balance'])
        if key in seen:duplicates.append(dict(id=item['id'],representative=seen[key],reason='same cuts and balancing on training geometries only'))
        else:
            seen[key]=item['id'];representatives.append(dict(**item,cuts=signature,column_keys=columns))
    # Cache stores complete vectors, not unknown Mobius signs or observed sums.
    return dict(models=models,parents=list(parents),generated=generated,representatives=representatives,
                training_only_duplicates=duplicates,cache=cache,prospective_catalog_bytes=estimate)


def select(catalog,witnesses,bank_size=8,adaptive=True,meter=None):
    meter=meter or ScoreMeter()
    if type(bank_size)is not int or not 0<=bank_size<=A.MAX_BANK:raise ValueError('bank size<=16')
    parents=catalog['parents']
    if set(witnesses)!=set(parents):raise ValueError('one complete witness per training geometry')
    for u,s in witnesses.items():
        if len(s)!=catalog['models'][u]['price_dimension']or any(type(v)is not int or v not in (-1,1)for v in s)or(s and s[0]!=1):raise ValueError('complete artificial sign witness with positive anchor')
    memory=catalog['prospective_catalog_bytes']+len(catalog['representatives'])*max(1,len(parents))*4096
    if memory>1024**3:raise A.B.ResourceLimit('prospective catalog and exact scores1GiB budget')
    meter.reserve(memory)
    scores=[]
    for item in catalog['representatives']:
        vals=[]
        for u,key in zip(parents,item['column_keys']):
            rec=catalog['cache'][key];dot=sum(a*b for a,b in zip(rec['column'],witnesses[u]))
            meter.charge(4*len(rec['column'])+4)
            if 2*abs(dot).bit_length()>4096 or rec['norm'].bit_length()>4096:raise A.B.ResourceLimit('prospective normalized score4096bit budget')
            vals.append(Q(dot*dot,rec['norm'])if rec['norm']else Q(0))
        scores.append(dict(id=item['id'],normalized_violation_by_parent=list(map(str,vals)),values=vals,
                           nonzero_geometry=any(catalog['cache'][k]['norm']for k in item['column_keys'])))
    by_id={x['id']:x for x in catalog['representatives']};remaining=[s for s in scores if s['nonzero_geometry']]
    coverage=[Q(0)]*len(parents);chosen=[];steps=[]
    while remaining and len(chosen)<bank_size:
        def gain(item):
            total=Q(0)
            for v,c in zip(item['values'],coverage):
                total=meter.combine(total,meter.combine(v,meter.combine(Q(1),c),divide=True))
            return total
        best=max(remaining,key=lambda s:gain(s))if adaptive else remaining[0]
        if adaptive and gain(best)==0:break
        value=gain(best);chosen.append(by_id[best['id']]);remaining.remove(best)
        coverage=[meter.combine(a,b)for a,b in zip(coverage,best['values'])]
        steps.append(dict(selected=best['id'],gain=str(value),coverage=list(map(str,coverage))))
    return dict(bank=[x['descriptor']for x in chosen],selected_ids=[x['id']for x in chosen],steps=steps,
                adaptive=adaptive,parents=parents,rule='greedy sum of normalized squared witness violations divided by one plus accumulated coverage; ties use frozen grammar order'if adaptive else'first nonzero forms in frozen grammar order; no witness score selection',
                scores=[{k:v for k,v in s.items()if k!='values'}for s in scores],
                scalar_operations=meter.ops,prospective_score_bytes=meter.peak_bytes,
                prospective_score_fraction_bits=meter.max_fraction_bits,
                unknown_composite_signs_used=False,source_values_used=False,uniform_remaining_bound_proved=False)
