"""Prototype all-cutoff floor multipliers and exact quotient-PSD synthesis.

No research observations. A complete remainder is a variable with an unpaid
cost until a separate theorem supplies one. PSD certificates alone never bind
an invented trajectory to the arithmetic source.
"""
from fractions import Fraction as Q
from itertools import combinations,product
from copy import deepcopy
import sympy as S

import arithmetic_prefix_relations as A
import check_arithmetic_prefix_relations as C


def _r(x,m):
    return A._rational(x,m)


def _poly(poly,m):
    if type(poly) is not list or len(poly)>64:raise ValueError('bounded floor stencil')
    output={}
    for term in poly:
        if type(term) is not list or len(term)!=2:raise ValueError('divisor/coefficient pair')
        d,c=term;A._integer(d,m,True);c=_r(c,m)
        output[d]=output.get(d,Q(0))+c
    return {d:c for d,c in output.items() if c}


def compose_floor_stencils(first,second,meter=None):
    """T_d T_e=T_(de) for EVERY integer N>=0, including floor-zero terms."""
    m=A.Meter() if meter is None else meter
    left=_poly(first,m);right=_poly(second,m);result={}
    for d,c in left.items():
        for e,b in right.items():
            m.charge(4);result[d*e]=result.get(d*e,Q(0))+c*b
    return [[d,str(c)] for d,c in sorted(result.items()) if c]


def multiply_complete_relation(source,certificate,channel,stencil,meter=None):
    """An all-N template with the full convolution domain, never a finite fit."""
    m=A.Meter() if meter is None else meter
    C.verify_certificate(source,certificate,m)
    if type(channel) is not int or not 0<=channel<len(source['channels']):raise ValueError('channel index')
    poly=_poly(stencil,m);relation=certificate['relations'][channel]
    return dict(schema='global-floor-multiplier-039-v1',source_binding=deepcopy(source),channel=channel,
        stencil=[[d,str(c)] for d,c in sorted(poly.items())],
        lhs=[dict(coefficient=str(c),outer_divisor=d,kernel=relation['kernel'],
                  inner_domain='1<=k<=floor(N/outer_divisor)',
                  prefix_argument='floor(N/(outer_divisor*k))',prefix_kind='weighted_channel')
             for d,c in sorted(poly.items())],
        rhs=[dict(coefficient=str(c),outer_divisor=d,argument='floor(N/outer_divisor)',
                  prefix=relation['rhs'],weight=relation['weight']) for d,c in sorted(poly.items())],
        domain='every integer N>=0; prefix below1 zero',complete_tail_retained=True,
        identity_proved=True,uniform_bound_proved=False,
        scalar_scope='formal affine R identity; actual bound requires fixed exact source normalization')


def complete_split(template,cutoff,meter=None):
    """Exact symbolic head/tail split; the tail remains the ENTIRE domain."""
    m=A.Meter() if meter is None else meter;A._integer(cutoff,m,True)
    if type(template) is not dict or template.get('schema')!='global-floor-multiplier-039-v1':raise ValueError('global template')
    source=template['source_binding'];cert=A.generate(source,m)
    expected=multiply_complete_relation(source,cert,template['channel'],template['stencil'],m)
    if not A._same(template,expected,m):raise ValueError('complete global multiplier template')
    m.charge(4*len(template['lhs']))
    return dict(identity=template,cutoff=cutoff,
                head_domain='1<=k<=min(cutoff,floor(N/outer_divisor))',
                tail_domain='cutoff<k<=floor(N/outer_divisor)',
                tail_cost_status='OPEN',unit_retained=True,all_N=True)


def finite_inverse_gate(kernel,stencil,meter=None):
    """A fresh-prime certificate against a FIXED finite exact inverse stencil."""
    m=A.Meter() if meter is None else meter;poly=_poly(stencil,m)
    if type(kernel) is not dict or set(kernel)!={'op','factors'} or kernel['op']!='dirichlet_convolution':raise ValueError('kernel')
    factors=kernel['factors']
    if type(factors) is not list:raise ValueError('kernel factors')
    for f in factors:
        if type(f) is not dict or set(f)!={'op','exponent'} or f['op']!='power':raise ValueError('positive power factor')
        _r(f['exponent'],m)
    if poly.get(1,Q(0))!=1:
        return dict(status='rejected',reason='unit coefficient is not1',scope='fixed finite inverse')
    if not factors:
        if poly!={1:Q(1)}:
            return dict(status='rejected',reason='delta kernel leaves extra nonzero stencil coefficients',
                        exact_inverse=False,scope='fixed finite inverse')
        return dict(status='delta_kernel',exact_inverse=True,scope='fixed finite inverse')
    return dict(status='rejected',reason='fresh-prime coefficient strictly positive',
        support_max=max(poly),prime_domain='every prime p>support_max',
        residual_prime_polynomial=[dict(coefficient='1',exponent=f['exponent']) for f in factors],
        proof='(U*D)(p)=U(1)D(p)=sum power factors>0',
        scope='fixed finite exact inverse only; moving support/approximate inverse not excluded')


def _matrix(rows,m):
    if type(rows) is not list or len(rows)>12 or any(type(row) is not list for row in rows):raise ValueError('bounded rational matrix')
    width=len(rows[0]) if rows else 0
    if width>12 or any(len(row)!=width for row in rows):raise ValueError('matrix shape')
    return S.Matrix([[S.Rational(str(_r(x,m))) for x in row] for row in rows]) if rows else S.zeros(0,0)


def _encode(matrix):
    return [[str(x) for x in row] for row in matrix.tolist()]


def _minors(matrix,m):
    size=matrix.rows;output=[]
    for k in range(1,size+1):
        for indices in combinations(range(size),k):
            m.charge(1+12*k**3)
            determinant=matrix.extract(indices,indices).det()
            output.append(dict(indices=list(indices),value=str(determinant)))
    return output


def quotient_psd(form,relations,meter=None):
    """Synthesize Q=P+L'Y+Y'L exactly, equivalent to Q>=0 on kerL.

    The arithmetic verifier must bind L to global identities. A successful
    quotient certificate prices none of the form's forcing coordinates.
    """
    m=A.Meter(cap=10_000_000) if meter is None else meter
    Qm=_matrix(form,m)
    if not Qm.rows or Qm.rows!=Qm.cols or Qm!=Qm.T:raise ValueError('symmetric nonempty form')
    dim=Qm.rows
    if relations:
        L=_matrix(relations,m)
        if L.cols!=dim:raise ValueError('relation dimension')
        # Preserve equivalent row space, removing dependent zero rows.
        reduced,pivots=L.T.rref();indices=list(pivots)
        L=L.extract(indices,list(range(dim)))
    else:L=S.zeros(0,dim)
    m.charge(100*(dim+1)**3);m.live(100*(dim+1)**2)
    if L.rows:
        G=(L*L.T).inv();E=L.T*G*L;Pi=S.eye(dim)-E
        P=Pi*Qm*Pi
        Y=G*L*Qm-G*L*Qm*E/2
    else:P=Qm;Y=S.zeros(0,dim)
    minors=_minors(P,m)
    positive=all(S.Rational(row['value'])>=0 for row in minors)
    if not positive:
        return dict(status='not_PSD_on_relation_space',form=_encode(Qm),relations=_encode(L),
                    negative_principal_minors=[row for row in minors if S.Rational(row['value'])<0],
                    actual_source_refuted=False,scope='searched free-trajectory quotient only')
    if Qm!=P+L.T*Y+Y.T*L:raise ArithmeticError('exact multiplier decomposition')
    return dict(status='exact_PSD_modulo_relations',form=_encode(Qm),relations=_encode(L),
                PSD=_encode(P),multipliers=_encode(Y),principal_minors=minors,
                source_binding_required=True,forcing_payment_required=True,
                uniform_bound_proved=False)


def verify_quotient(certificate,meter=None):
    m=A.Meter(cap=10_000_000) if meter is None else meter
    if type(certificate) is not dict or certificate.get('status')!='exact_PSD_modulo_relations':raise ValueError('PSD certificate')
    Qm=_matrix(certificate['form'],m);P=_matrix(certificate['PSD'],m)
    dim=Qm.rows;L=_matrix(certificate['relations'],m) if certificate['relations'] else S.zeros(0,dim)
    Y=_matrix(certificate['multipliers'],m) if certificate['multipliers'] else S.zeros(0,dim)
    if Qm.rows!=Qm.cols or P.shape!=Qm.shape or Qm!=Qm.T or P!=P.T or L.cols!=dim or Y.shape!=L.shape:
        raise ValueError('symmetric matching matrix shapes')
    m.charge(100*(dim+1)**3)
    if Qm!=P+L.T*Y+Y.T*L:raise ValueError('false multiplier identity')
    minors=_minors(P,m)
    if not A._same(minors,certificate['principal_minors'],m) or any(S.Rational(r['value'])<0 for r in minors):raise ValueError('false PSD witness')
    if certificate.get('uniform_bound_proved') is not False:raise ValueError('unpaid forcing cannot establish bound')
    return True


def search_forcing(target,relations,forcing_forms,grid=('0','1','2','3'),meter=None):
    """Enumerate paid/unpaid forcing coefficients; retain ALL provider debts."""
    m=A.Meter(cap=10_000_000) if meter is None else meter
    t=[S.Rational(str(_r(x,m))) for x in target];dim=len(t)
    if not 1<=dim<=12 or type(forcing_forms) is not list or len(forcing_forms)>4:raise ValueError('bounded forcing search')
    forms=[]
    for provider in forcing_forms:
        if type(provider) is not dict or set(provider)!={'name','form','paid'} or type(provider['paid']) is not bool:
            raise ValueError('explicit forcing payment status')
        matrix=_matrix(provider['form'],m)
        if matrix.shape!=(dim,dim):raise ValueError('forcing form dimension')
        forms.append(matrix)
    values=[_r(x,m) for x in grid]
    if len(values)>16 or any(x<0 for x in values):raise ValueError('bounded nonnegative multiplier grid')
    target_form=S.Matrix(t)*S.Matrix(t).T;attempts=[]
    for coefficients in product(values,repeat=len(forms)):
        m.charge(4*(dim+1)**2)
        forcing=S.zeros(dim)
        for coefficient,matrix in zip(coefficients,forms):forcing+=S.Rational(str(coefficient))*matrix
        certificate=quotient_psd(_encode(forcing-target_form),relations,m)
        attempts.append(dict(coefficients=list(map(str,coefficients)),status=certificate['status']))
        if certificate['status']=='exact_PSD_modulo_relations':
            unpaid=[p['name'] for c,p in zip(coefficients,forcing_forms) if c and not p['paid']]
            return dict(status='proved_given_global_relations_and_providers' if not unpaid else 'OPEN_forcing',
                        coefficients=list(map(str,coefficients)),certificate=certificate,unpaid=unpaid,
                        attempts=attempts,source_binding_required=True)
    return dict(status='no_certificate_in_grid',attempts=attempts,actual_source_refuted=False)


def harmonic_dual_search(source,certificate,channel,offsets=('-1','-1/2','0','1/2'),meter=None):
    """Generic affine floor approximation, a genuine actual-inverse calibration.

    For µ*One=delta, floor(N/d)=N/d+s+error and complete |µ|<=1.
    Each candidate yields |sum W(d)/d|<=|weight|*(|s|+max(|s|,|1+s|)+1/N).
    No moment/prefix bound is used to pay a multiplier endpoint.
    """
    m=A.Meter() if meter is None else meter
    C.verify_certificate(source,certificate,m)
    if type(channel) is not int or not 0<=channel<len(source['channels']):raise ValueError('channel')
    relation=certificate['relations'][channel]
    if relation['kernel']!={'op':'dirichlet_convolution','factors':[{'op':'power','exponent':'0'}]} or relation['rhs']['factors']:
        return dict(status='provider_not_applicable',all_scale_claim=False)
    # Structural kernel match plus empty RHS forces exactly one µ0 and no power atom.
    if type(offsets) not in (tuple,list) or not 1<=len(offsets)<=64:raise ValueError('bounded nonempty offsets')
    candidates=[]
    for text in offsets:
        s=_r(text,m);error=max(abs(s),abs(1+s));constant=abs(s)+error+1
        candidates.append(dict(offset=str(s),fractional_error=str(error),uniform_constant=str(constant)))
    best=min(candidates,key=lambda r:Q(r['uniform_constant']))
    return dict(status='proved',scope='every integer N>=1',weight=relation['weight'],
        target='absolute weighted harmonic channel prefix',bound='uniform_constant*abs(weight)',
        best=best,candidates=candidates,complete_floor_terms=True,unit_retained=True,
        source_specific_input='complete µ*One=delta and |µ|<=1',critical_prefix_recovery=False)
