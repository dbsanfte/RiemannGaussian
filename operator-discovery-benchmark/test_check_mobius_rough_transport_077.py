import copy
import unittest
from fractions import Fraction as Q
from unittest.mock import patch
import check_mobius_rough_transport_077 as C

def I(l,r,w):return {'left':l,'right':r,'weight':w}
def factors(n):
    ps=[];p=2
    while p*p<=n:
        if n%p==0:
            n//=p;ps.append(p)
            if n%p==0:return None
        p+=1
    if n>1:ps.append(n)
    return ps

def terminal_fixture(intervals,y,K,P=()):
    H=max((row['right'] for row in intervals),default=0);layers=[{} for _ in range(K+1)];counts=[0]*(K+1)
    for n in range(1,H+1):
        ps=factors(n)
        if ps is None or any(p<=y or p in P for p in ps):continue
        r=len(ps)
        if r>K:raise AssertionError('fixture degree too small')
        counts[r]+=1
        for row in intervals:
            if row['left']<n<=row['right']:
                for token,a in row['weight'].items():layers[r][token]=layers[r].get(token,Q(0))+Q(a)
    signed={}
    for r,poly in enumerate(layers):
        for token,a in poly.items():signed[token]=signed.get(token,Q(0))+(-1)**r*a
    save=lambda poly:{token:str(a) for token,a in poly.items() if a}
    return {'schema':'rough-factor-terminal-v1','cutoff':y,'degree':K,'excluded_primes':list(P),'layer_polynomials':[save(poly) for poly in layers],'layer_counts':counts,'signed_polynomial':save(signed)}
def transport_fixture(intervals,y1,y2,P=()):
    H=max((row['right'] for row in intervals),default=0)
    primes=[p for p in range(y1+1,min(y2,H)+1) if p>=2 and all(p%d for d in range(2,p)) and p not in P]
    children=[]
    for p in primes:
        scaled=[I(row['left']//p,row['right']//p,row['weight']) for row in intervals if row['left']//p<row['right']//p]
        children.append({'prime':p,'intervals':scaled})
    return {'schema':'rough-prime-transport-v1','lower_cutoff':y1,'upper_cutoff':y2,'excluded_primes':list(P),'children':children}
class Tests(unittest.TestCase):
    def test_transport_roster_floors_and_normalization(self):
        rows=[I(0,4,{'a':'1'}),I(7,13,{'a':'-2','z':'1/3'})];payload=transport_fixture(rows,1,100,[3])
        r=C.verify_transport(rows,payload);self.assertEqual(r['status'],'VERIFIED_IDENTITY');self.assertEqual(r['children_checked'],5);self.assertFalse(r['uniform_bound_proved']);self.assertFalse(r['RH_proved'])
        bad=copy.deepcopy(payload);bad['children'].pop();self.assertEqual(C.verify_transport(rows,bad)['status'],'INVALID')
        bad=copy.deepcopy(payload);bad['children'][0]['intervals'][0]['weight']={'a':'-1'};self.assertEqual(C.verify_transport(rows,bad)['status'],'INVALID')
        constant=[I(0,4,{'t':'1'})];p=transport_fixture(constant,1,2);p['children'][0]['intervals']=[I(0,1,{'t':'1'}),I(1,2,{'t':'1'})]
        self.assertEqual(C.verify_transport(constant,p)['status'],'VERIFIED_IDENTITY')
    def test_literal_transport_mu_fixture(self):
        rows=[I(0,40,{'t':'1'}),I(42,49,{'t':'-2'})];y1,y2=2,7;P=[3]
        payload=transport_fixture(rows,y1,y2,P);self.assertEqual(C.verify_transport(rows,payload)['status'],'VERIFIED_IDENTITY')
        def coefficient(n):return sum(Q(row['weight'].get('t','0')) for row in rows if row['left']<n<=row['right'])
        def rough(y,scale=1):
            value=Q(0)
            for n in range(1,50):
                ps=factors(n)
                if ps is not None and all(p>y and p not in P for p in ps):value+=(-1)**len(ps)*coefficient(scale*n)
            return value
        self.assertEqual(rough(y1)-rough(y2),-sum(rough(child['prime'],child['prime']) for child in payload['children']))
    def test_terminal_semiprime_signs_and_squares(self):
        rows=[I(0,49,{'a':'1','count:7^(-17/31)':'-2/3'}),I(50,64,{'a':'-2'})];p=terminal_fixture(rows,4,2,[7]);r=C.verify_terminal(rows,p)
        self.assertEqual(r['status'],'VERIFIED_IDENTITY');self.assertGreater(r['layer_counts'][2],0);self.assertEqual(r['unit_count'],1)
        bad=copy.deepcopy(p);bad['layer_counts'][2]+=1;self.assertEqual(C.verify_terminal(rows,bad)['status'],'INVALID')
        bad=copy.deepcopy(p);bad['signed_polynomial']['a']='0';self.assertEqual(C.verify_terminal(rows,bad)['status'],'INVALID')
        bad=copy.deepcopy(p);bad['layer_polynomials'][0]={};self.assertEqual(C.verify_terminal(rows,bad)['status'],'INVALID')
    def test_square_factor_parity_trap(self):
        rows=[I(0,64,{'x':'1'})];payload=terminal_fixture(rows,4,2)
        r=C.verify_terminal(rows,payload);self.assertEqual(r['status'],'VERIFIED_IDENTITY')
        # A repeated5*5 factor must NOT enter the semiprime polynomial.
        bad=copy.deepcopy(payload);bad['layer_polynomials'][2]['x']=str(Q(bad['layer_polynomials'][2]['x'])+1)
        bad['signed_polynomial']['x']=str(Q(bad['signed_polynomial']['x'])+1)
        self.assertEqual(C.verify_terminal(rows,bad)['status'],'INVALID')
        bad=copy.deepcopy(payload);bad['layer_counts'][2]+=1;self.assertEqual(C.verify_terminal(rows,bad)['status'],'INVALID')
    def test_counts_include_zero_coefficient_products(self):
        rows=[I(12,16,{'a':'1'})];p=terminal_fixture(rows,4,1);r=C.verify_terminal(rows,p)
        self.assertEqual(r['status'],'VERIFIED_IDENTITY');self.assertEqual(r['layer_counts'],[1,4]);self.assertEqual(p['layer_polynomials'],[{}, {'a':'1'}])
        bad=copy.deepcopy(p);bad['layer_counts'][0]=0;self.assertEqual(C.verify_terminal(rows,bad)['status'],'INVALID')
    def test_degrees_three_four_and_threshold_equality(self):
        for y,H,K in ((8,2431,3),(10,46189,4),(4,64,2),(1,1,0)):
            rows=[I(0,H,{'x':'1'})];payload=terminal_fixture(rows,y,K);r=C.verify_terminal(rows,payload)
            self.assertEqual(r['status'],'VERIFIED_IDENTITY')
            if K in (3,4):self.assertGreater(r['layer_counts'][K],0)
        rows=[I(0,65,{'x':'1'})];payload=terminal_fixture(rows,4,2);self.assertEqual(C.verify_terminal(rows,payload)['status'],'INVALID')
    def test_invalid_primes_tokens_and_empty(self):
        for P in ([3,2],[2,2],[4]):
            p=transport_fixture([],1,2);p['excluded_primes']=P;self.assertEqual(C.verify_transport([],p)['status'],'INVALID')
        self.assertEqual(C.verify_terminal([],terminal_fixture([],1,0))['status'],'VERIFIED_IDENTITY')
        rows=[I(0,1,{'x':'1'})];p=terminal_fixture(rows,1,0);p['layer_polynomials'][0]={'x':'2/4'};self.assertEqual(C.verify_terminal(rows,p)['status'],'INVALID')
        p=terminal_fixture(rows,1,0);p['degree']=True;self.assertEqual(C.verify_terminal(rows,p)['status'],'INVALID')
    def test_product_gate_before_aggregate(self):
        rows=[I(0,16,{'x':'1'})];payload=terminal_fixture(rows,4,1)
        with patch.object(C,'MAX_PRODUCTS',2):r=C.verify_terminal(rows,payload)
        self.assertEqual(r['status'],'INVALID')
        # Direct enumeration also rejects before retaining an over-cap product.
        with patch.object(C,'MAX_PRODUCTS',2):
            with self.assertRaises(C.ResourceLimit):C._product_layers([2,3,5],2,16,C.Meter())
if __name__=='__main__':unittest.main()
