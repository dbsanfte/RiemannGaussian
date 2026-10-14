"""Complete typed arithmetic constraints, including weighted prime-cofactor pairs."""
from fractions import Fraction as Q
from math import gcd
import numpy as np
from flint import fmpq_mat
import mobius_annihilator_085 as D
import mobius_annihilator_bank_085 as OLD_BANK

B=D.B
MAX_BANK=16
CATALOG_BYTES=1024**3


def _table_bytes(model):
    return (model['N']+1)*(model['price_dimension']+1)*8+model['squarefree_count']*64


def parse_bank(bank):
    if type(bank)is not list or len(bank)>MAX_BANK:raise ValueError('typed arithmetic bank<=16')
    result=[]
    for row in bank:
        if type(row)is not dict:raise ValueError('exact typed bank object')
        if row.get('kind')=='divisor':
            if set(row)!={'kind','cut'}:raise ValueError('exact divisor keys')
            result.append(dict(kind='divisor',cut=D.parse_bank([row['cut']])[0]));continue
        if row.get('kind')!='prime_pair'or set(row)!={'kind','cut_on','cut','weight'}:raise ValueError('exact prime-pair keys')
        if row['cut_on']not in ('prime','cofactor'):raise ValueError('prime/cofactor cutoff domain')
        cut=row['cut']
        if type(cut)is not dict or set(cut)!={'scale','u_exponent','complement'}:raise ValueError('exact prime-pair cutoff')
        parsed=D.parse_bank([dict(cut,unit_balance=False)])[0];parsed.pop('unit_balance')
        w=row['weight']
        if type(w)is not dict or w.get('kind')not in ('one','source'):raise ValueError('prime-pair weight')
        if w['kind']=='one':
            if set(w)!={'kind'}:raise ValueError('exact constant weight')
        elif set(w)!={'kind','i'}or type(w['i'])is not int or not 0<=w['i']<=3:raise ValueError('exact source index')
        result.append(dict(kind='prime_pair',cut_on=row['cut_on'],cut=parsed,weight=dict(w)))
    return result


def cut_value(model,descriptor):
    d=parse_bank([descriptor])[0];cut=dict(d['cut'],n_exponent=Q(0))
    return B.cut_value(1,model['u'],model['N'],cut,model['meter'])


def pair_tables(model,cut_on,weight):
    """Integer prefix tables over every directed valid prime/cofactor edge."""
    D.SQUARE._gate(model);N=model['N'];E=model['price_dimension'];G=model['squarefree_count']
    if cut_on not in ('prime','cofactor'):raise ValueError('prime/cofactor cutoff domain')
    if type(weight)is not dict or weight.get('kind')not in ('one','source'):raise ValueError('prime-pair weight')
    if weight['kind']=='one'and set(weight)!={'kind'}:raise ValueError('exact constant weight')
    if weight['kind']=='source'and(set(weight)!={'kind','i'}or type(weight['i'])is not int or not 0<=weight['i']<=3):raise ValueError('exact source index')
    if not model['program']['prime_anchor']:raise ValueError('complete unit/prime anchor required')
    if weight['kind']=='source'and weight['i']>model['program']['memory']:raise ValueError('source index exceeds memory')
    key=(cut_on,weight['kind'],weight.get('i'));cache=model.setdefault('_pair_tables086',{})
    if key in cache:return cache[key]
    extra=_table_bytes(model)
    model['meter'].reserve(model['resident_bytes']+model['extra_resident_bytes']+extra+64*1024**2)
    n=model['coordinates'];positions=np.full(N+1,-1,dtype=np.int64);positions[n]=np.arange(G)
    projection=np.zeros(G,dtype=np.int64);projection[model['composite_indices']]=np.arange(1,E)
    signs=np.where(model['known_signs']==0,1,model['known_signs'])
    values=np.ones(G,dtype=np.int64)if weight['kind']=='one'else model['features'][:,weight['i']]
    denominator=1 if weight['kind']=='one'else model['denominator']
    # Bound all directed edge contributions BEFORE the integer accumulation.
    maximum=max([abs(int(v))for v in values]+[0]);edge_bound=N*max(1,N.bit_length())
    if 2*maximum*edge_bound>=2**60:raise B.ResourceLimit('prospective prime-pair int64 accumulation gate')
    table=np.zeros((N+1,E),dtype=np.int64);counts=np.zeros(N+1,dtype=np.int64)
    primes=n[model['known_signs']==-1]
    for prime in primes:
        p=int(prime)
        for g,m in enumerate(n):
            m=int(m)
            if p*m>N:break
            if m%p==0:continue
            h=int(positions[p*m])
            if h<0:raise ArithmeticError('complete squarefree prime-cofactor endpoint')
            k=p if cut_on=='prime'else m;counts[k]+=1;w=int(values[g])
            table[k,projection[g]]+=int(signs[g])*w;table[k,projection[h]]+=int(signs[h])*w
            model['meter'].charge(32)
    np.cumsum(table,axis=0,out=table);np.cumsum(counts,out=counts)
    model['meter'].charge((N+1)*(E+1));model['extra_resident_bytes']+=extra
    cache[key]=(table,denominator,counts)
    return cache[key]


def integer_column(model,descriptor):
    d=parse_bank([descriptor])[0];D.SQUARE._gate(model)
    if d['kind']=='divisor':
        col,den,K=D.identity_integer_column(model,descriptor['cut'])
        return dict(column=col,denominator=den,cut=K,prime_pair_count=0)
    K=cut_value(model,descriptor);table,den,counts=pair_tables(model,d['cut_on'],d['weight'])
    return dict(column=table[K],denominator=den,cut=K,prime_pair_count=int(counts[K]))


def vectors(model,bank):
    parse_bank(bank);E=model['price_dimension'];m=len(bank);D.SQUARE._gate(model)
    model['meter'].reserve(model['resident_bytes']+model['extra_resident_bytes']+(E+model['squarefree_count'])*max(1,m)*2048)
    cols=[integer_column(model,d)for d in bank]
    V=fmpq_mat([[str(Q(int(c['column'][i]),c['denominator']))for c in cols]for i in range(E)])if E and m else fmpq_mat(E,m)
    return V,dict(cuts=[c['cut']for c in cols],prime_pair_counts=[c['prime_pair_count']for c in cols])


def grammar(memory,divisor_scale_height=12,prime_scale_height=8,exponent_height=8):
    if type(memory)is not int or not 1<=memory<=3:raise ValueError('source memory1..3')
    for h in (divisor_scale_height,prime_scale_height,exponent_height):
        if type(h)is not int or not 2<=h<=24:raise ValueError('prospective rational grammar height budget')
    scales=lambda h:sum(gcd(a,b)==1 for a in range(1,h)for b in range(1,h-a+1))
    exponents=sum(abs(a)+b<=exponent_height and gcd(abs(a),b)==1
                  for b in range(1,exponent_height+1)for a in range(-exponent_height,exponent_height+1))
    count=scales(divisor_scale_height)*exponents*4+scales(prime_scale_height)*exponents*4*(memory+2)
    if count*8192>CATALOG_BYTES:raise B.ResourceLimit('prospective typed grammar1GiB budget')
    rows=[]
    for old in OLD_BANK.descriptors(divisor_scale_height,exponent_height):
        rows.append(dict(descriptor=dict(kind='divisor',cut=old['descriptor']),cost=old['cost']))
    weights=[dict(kind='one')]+[dict(kind='source',i=i)for i in range(memory+1)]
    for old in OLD_BANK.descriptors(prime_scale_height,exponent_height):
        if old['descriptor']['unit_balance']:continue
        cut={k:v for k,v in old['descriptor'].items()if k!='unit_balance'}
        for domain in ['prime','cofactor']:
            for weight in weights:
                rows.append(dict(descriptor=dict(kind='prime_pair',cut_on=domain,cut=cut,weight=weight),
                                 cost=old['cost']+2+(weight.get('i',-1)+1)))
    if len(rows)!=count:raise ArithmeticError('complete typed grammar count')
    # Stable original enumeration breaks ties without inspecting arithmetic.
    rows.sort(key=lambda r:r['cost'])
    for i,r in enumerate(rows):r['id']='g'+str(i).zfill(5)
    return rows


def catalog(model,generated):
    """Deduplicate ONLY this training geometry; retain all symbolic aliases."""
    if type(generated)is not list or len(generated)*8192>CATALOG_BYTES:raise B.ResourceLimit('prospective typed catalog1GiB budget')
    # Reserve all possible cut forms and every needed prefix table BEFORE
    # retaining columns. This also accounts for the catalog in later users
    # of the same model; score storage has a separate simultaneous reserve.
    forms=set();tables=set();ids=set()
    for item in generated:
        if type(item)is not dict or set(item)!={'id','descriptor','cost'}or type(item['id'])is not str or type(item['cost'])is not int:raise ValueError('generated descriptor schema')
        if item['id']in ids:raise ValueError('unique generated descriptor ids')
        ids.add(item['id']);d=parse_bank([item['descriptor']])[0]
        if d['kind']=='divisor':forms.add(('divisor',d['cut']['unit_balance']))
        else:
            key=(d['cut_on'],d['weight']['kind'],d['weight'].get('i'))
            if key[1]=='source'and key[2]>model['program']['memory']:raise ValueError('source index exceeds memory')
            forms.add(('prime_pair',)+key);tables.add(key)
    storage=len(generated)*8192+min(len(generated),len(forms)*(model['N']+1))*(1024+64*model['price_dimension'])
    missing=tables-set(model.get('_pair_tables086',{}))
    prospective=model['resident_bytes']+model['extra_resident_bytes']+storage+len(missing)*_table_bytes(model)+64*1024**2
    if prospective>CATALOG_BYTES:raise B.ResourceLimit('prospective complete typed catalog1GiB budget')
    model['meter'].reserve(prospective);model['extra_resident_bytes']+=storage
    representatives=[];duplicates=[];seen={};columns={}
    for item in generated:
        d=item['descriptor'];K=cut_value(model,d)
        key=('divisor',K,d['cut']['unit_balance'])if d['kind']=='divisor'else('prime_pair',d['cut_on'],d['weight']['kind'],d['weight'].get('i'),K)
        if key in seen:duplicates.append(dict(id=item['id'],representative=seen[key],scope='same cutoff/form at training geometry only'));continue
        seen[key]=item['id'];rec=integer_column(model,d)
        bits=max([abs(int(v)).bit_length()for v in rec['column']]+[0])
        if 2*bits+max(1,len(rec['column']).bit_length())>4096:raise B.ResourceLimit('prospective column norm bit gate')
        model['meter'].charge(4*len(rec['column']));rec['norm']=sum(int(v)**2 for v in rec['column']);rec['entry_bits']=bits
        representatives.append(dict(**item,cut=K));columns[item['id']]=rec
    return dict(generated=generated,representatives=representatives,training_only_duplicates=duplicates,columns=columns,
                training_u=model['u'],effective_dimension=model['price_dimension'],prospective_catalog_bytes=prospective,
                prospective_peak_bytes=model['meter'].peak_bytes)


def choose_extension(catalog,signs,allow_prime_pairs=True,meter=None):
    meter=meter or B.Meter()
    if type(signs)is not list or len(signs)!=catalog['effective_dimension']or any(type(s)is not int or s not in (-1,1)for s in signs)or signs and signs[0]!=1:raise ValueError('complete artificial anchored witness')
    if type(allow_prime_pairs)is not bool:raise ValueError('strict prime-pair grammar flag')
    prospective=catalog['prospective_catalog_bytes']+len(catalog['representatives'])*8192
    if prospective>CATALOG_BYTES:raise B.ResourceLimit('prospective catalog and scores1GiB budget')
    meter.reserve(prospective)
    scores=[];best=None
    for item in catalog['representatives']:
        if not allow_prime_pairs and item['descriptor']['kind']!='divisor':continue
        rec=catalog['columns'][item['id']]
        if len(signs)!=len(rec['column']):raise ValueError('complete catalog column')
        bits=rec['entry_bits']+max(1,len(signs).bit_length())
        if max(2*bits,rec['norm'].bit_length())>4096:raise B.ResourceLimit('prospective extension score bit gate')
        meter.charge(4*len(signs)+16)
        dot=sum(int(a)*b for a,b in zip(rec['column'],signs));norm=rec['norm']
        score=Q(dot*dot,norm)if norm else Q(0)
        row=dict(id=item['id'],score=str(score),violation=str(Q(dot,rec['denominator'])))
        scores.append(row)
        if score>0 and(best is None or score>best[0]):best=(score,item,row)
    return dict(status='EXACT_VIOLATING_IDENTITY'if best else'NO_VIOLATING_IDENTITY_IN_GRAMMAR',scores=scores,
                selected=best[1]if best else None,selected_score=best[2]if best else None,
                scalar_operations=meter.ops,prospective_score_bytes=meter.peak_bytes,
                rule='maximum exact squared witness violation divided by complete column norm; frozen grammar order breaks ties')
