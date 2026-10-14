import copy
import unittest
from fractions import Fraction as Q
from unittest.mock import patch
import check_mobius_scale_flux_079 as C

def I(l,r,w):return {'left':l,'right':r,'weight':w}
def factors(n):
    ps=[];d=2
    while d*d<=n:
        if n%d==0:
            n//=d;ps.append(d)
            if n%d==0:return None
        d+=1
    if n>1:ps.append(n)
    return ps

def fixture(parent,child,u=80,P=(),gamma='1/3'):
    Hp=max((r['right'] for r in parent),default=0);Hc=max((r['right'] for r in child),default=0)
    def weight(rows,n):
        result={}
        for row in rows:
            if row['left']<n<=row['right']:result={t:Q(a) for t,a in row['weight'].items()}
        return result
    points=sorted({x for row in parent+child for x in (row['left'],row['right'])});bands=[]
    for l,r in zip(points,points[1:]):
        pw,cw=weight(parent,r),weight(child,r)
        if pw or cw:bands.append({'left':l,'right':r,'parent_weight':{t:str(a) for t,a in pw.items()},'child_weight':{t:str(a) for t,a in cw.items()}})
    cuts=[C._cutoffs(H,Q(gamma),C.Meter()) for H in (Hp,Hc)]
    def cat(n,H,cut,fs):
        if n>H:return 10
        if n==1:return 0
        p=min(fs);y,s1,s2=cut
        return len(fs) if p>y else 7 if p<=s1 else 8 if p<=s2 else 9
    cellmap={};D=[{} for _ in range(10)];B={(i,j):{} for i in range(10) for j in range(i,10)}
    for bi,band in enumerate(bands):
        for n in range(band['left']+1,band['right']+1):
            fs=factors(n)
            if fs is None or any(n%p==0 for p in P):continue
            pc,hc=cat(n,Hp,cuts[0],fs),cat(n,Hc,cuts[1],fs);key=(bi,pc,hc);count,signed=cellmap.get(key,(0,0));mu=(-1)**len(fs);cellmap[key]=(count+1,signed+mu)
            delta=[{} for _ in range(10)]
            for index,poly,sign in ((pc,band['parent_weight'],1),(hc,band['child_weight'],-1)):
                if index<10:
                    for token,a in poly.items():delta[index][token]=delta[index].get(token,Q(0))+sign*Q(a)
            for i,poly in enumerate(delta):
                for t,a in poly.items():D[i][t]=D[i].get(t,Q(0))+mu*a
                for j in range(i,10):
                    for t,a in poly.items():
                        for s,b in delta[j].items():
                            pair=tuple(sorted((t,s)));B[(i,j)][pair]=B[(i,j)].get(pair,Q(0))+a*b
    cells=[{'band':bi,'parent_category':pc,'child_category':hc,'count':v[0],'signed_count':v[1]} for (bi,pc,hc),v in sorted(cellmap.items())]
    gram=[{'i':i,'j':j,'terms':[{'left_token':t,'right_token':s,'coefficient':str(a)} for (t,s),a in sorted(B[(i,j)].items()) if a]} for i in range(10) for j in range(i,10)]
    return {'schema':'scale-flux-cells-v1','u':u,'child_u':u//2,'bands':bands,'cells':cells,'flux_features':[{t:str(a) for t,a in poly.items() if a} for poly in D],'gram_upper':gram}
def leafrow(payload,ranges={'1':['1','1']}):return {'u':payload['u'],'flux_features':payload['flux_features'],'gram_upper':payload['gram_upper'],'token_intervals':ranges}
class Tests(unittest.TestCase):
    def test_exact_cells_flux_and_gram(self):
        parent=[I(0,20,{'1':'1'})];child=[I(0,10,{'1':'1'})];payload=fixture(parent,child)
        r=C.verify_cells(parent,child,[],'1/3',payload);self.assertEqual(r['status'],'VERIFIED_CELLS');self.assertEqual(r['flux_features'][1],{'1':'-4'});self.assertFalse(r['uniform_correlation_proved']);self.assertFalse(r['RH_proved'])
        for field in ('count','signed_count'):
            bad=copy.deepcopy(payload);bad['cells'][0][field]+=1;self.assertEqual(C.verify_cells(parent,child,[],'1/3',bad)['status'],'INVALID')
        bad=copy.deepcopy(payload);bad['cells'].pop();self.assertEqual(C.verify_cells(parent,child,[],'1/3',bad)['status'],'INVALID')
    def test_quad_cross_signs_and_band_mutation(self):
        p=[I(0,20,{'x':'2'})];h=[I(0,10,{'y':'3'})];payload=fixture(p,h,P=[2]);self.assertEqual(C.verify_cells(p,h,[2],'1/3',payload)['status'],'VERIFIED_CELLS')
        bad=copy.deepcopy(payload);bad['bands'][0]['parent_weight']['x']='-2';self.assertEqual(C.verify_cells(p,h,[2],'1/3',bad)['status'],'INVALID')
        bad=copy.deepcopy(payload)
        for entry in bad['gram_upper']:
            cross=next((term for term in entry['terms'] if term['left_token']!=term['right_token']),None)
            if cross:cross['coefficient']=str(Q(cross['coefficient'])/2);break
        self.assertEqual(C.verify_cells(p,h,[2],'1/3',bad)['status'],'INVALID')
    def test_leaf_pass_refutation_ambiguity_proper(self):
        p=[I(0,20,{'1':'1'})];h=[I(0,10,{'1':'1'})];payload=fixture(p,h);ray=['0','1']+['0']*8;r=leafrow(payload)
        self.assertEqual(C.verify_local_leaf(r,ray,'4','1')['status'],'CERTIFIED_FINITE');self.assertEqual(C.verify_local_leaf(r,ray,'3','1')['status'],'REFUTED_FINITE')
        r['token_intervals']={'1':['1','2']};self.assertEqual(C.verify_local_leaf(r,ray,'4','1')['status'],'UNRESOLVED_INTERVAL')
        self.assertEqual(C.verify_local_leaf(r,['1']*10,'4','1')['status'],'INVALID')
    def test_noncircularity_independent_cells(self):
        p=[I(0,20,{'1':'1'})];h=[I(0,10,{'1':'1'})];payload=fixture(p,h);ray=['0','1']+['0']*8
        first=next(i for i,c in enumerate(payload['cells']) if c['parent_category']==1 and c['child_category']==10)
        second=next(i for i,c in enumerate(payload['cells']) if c['parent_category']==7 and c['child_category']==10)
        w={'first_cell':first,'second_cell':second};self.assertEqual(C.verify_noncircularity(payload,ray,{'1':['1','1']},w)['status'],'VERIFIED_NONCIRCULARITY')
        self.assertEqual(C.verify_noncircularity(payload,ray,{'1':['-1','1']},w)['status'],'UNRESOLVED_INTERVAL')
    def test_norm_inactive_and_conditional_cover(self):
        kernel=[{'divisor':2,'weight':'1'}];cert={'I':'1/2','E':'1','K':'3/5'};r=C.verify_coefficient_norm(kernel,[],10,cert);self.assertEqual(r['status'],'VERIFIED_UNIFORM_COEFFICIENT_NORM');self.assertTrue(r['uniform_coefficient_norm_proved']);self.assertFalse(r['uniform_source_bound_proved'])
        folded=[{'divisor':2,'weight':'1'},{'divisor':4,'weight':'-1'}];cert={'I':'1/4','E':'1','K':'7/20'};self.assertEqual(C.verify_coefficient_norm(kernel,[2],10,cert)['status'],'VERIFIED_UNIFORM_COEFFICIENT_NORM')
        self.assertEqual(C.verify_inactive(folded,'1/2',4,[0,2,3,4,5,6])['status'],'VERIFIED_INACTIVE_COORDINATES');self.assertEqual(C.verify_inactive(folded,'1/2',3,[0])['status'],'UNSUPPORTED');self.assertEqual(C.verify_inactive(folded,'1/2',4,[1])['status'],'UNSUPPORTED')
        ray=['0','1']+['0']*8;target=ray;cover=C.verify_cover(target,[ray],['1'],['1/3'],'1',{'price':'1'});self.assertEqual(cover['status'],'VERIFIED_CONDITIONAL_COVER');self.assertFalse(cover['uniform_correlation_proved'])
    def test_fixed_kernel_row_binding_and_tampering(self):
        kernel=[{'divisor':2,'weight':'1'},{'divisor':4,'weight':'-1'}]
        intervals=[I(2,5,{'1':'1'})]
        self.assertEqual(C.verify_kernel_row(kernel,10,intervals)['status'],'VERIFIED_KERNEL_ROW')
        self.assertEqual(C.verify_kernel_row(kernel,10,[I(3,5,{'1':'1'})])['status'],'INVALID')
        self.assertEqual(C.verify_kernel_row(kernel,10,[I(2,5,{'1':'-1'})])['status'],'INVALID')
        self.assertEqual(C.verify_kernel_row(kernel,1,[])['status'],'VERIFIED_KERNEL_ROW')
    def test_cover_norm_mutation_and_fractional_leaf(self):
        kernel=[{'divisor':2,'weight':'1'}]
        self.assertEqual(C.verify_coefficient_norm(kernel,[],10,{'I':'1/2','E':'1','K':'1/2'})['status'],'INVALID')
        ray=['0','1']+['0']*8
        self.assertEqual(C.verify_cover(ray,[ray],['2'],['1/3'],'1',{'price':'1'})['status'],'INVALID')
        self.assertEqual(C.verify_cover(ray,[ray],['1'],['1/3'],'1',{'price':'2'})['status'],'INVALID')
        p=[I(0,20,{'1':'1'})];h=[I(0,10,{'1':'1'})];payload=fixture(p,h)
        self.assertEqual(C.verify_local_leaf(leafrow(payload),ray,'4','1001/1000')['status'],'CERTIFIED_FINITE')
    def test_complete_base_uniform_integer_domain(self):
        kernel=[{'divisor':2,'weight':'1'},{'divisor':4,'weight':'-1'}]
        check=C.verify_complete_base(kernel,4,{'A':'3/4','B':'9/2'})
        self.assertEqual(check['status'],'VERIFIED_COMPLETE_BASE',check)
        self.assertTrue(check['complete_base_proved']);self.assertFalse(check['uniform_source_bound_proved'])
        self.assertEqual(C.verify_complete_base(kernel,4,{'A':'1/4','B':'1/2'})['status'],'INVALID')
        self.assertEqual(C.verify_complete_base(kernel,4,{'A':'3/4','B':'1'})['status'],'INVALID')
    def test_unit_outside_and_domain_resource(self):
        p=[I(0,1,{'1':'1'})];h=[];payload=fixture(p,h,u=8,gamma='53/17');self.assertEqual(C.verify_cells(p,h,[],'53/17',payload)['status'],'VERIFIED_CELLS')
        bad=copy.deepcopy(payload);bad['child_u']=3;self.assertEqual(C.verify_cells(p,h,[],'53/17',bad)['status'],'INVALID')
        with patch.object(C,'_resident',return_value=C.MEMORY_BUDGET):r=C.verify_cells(p,h,[],'53/17',payload)
        self.assertEqual(r['status'],'INVALID');self.assertTrue(r['resource_limit'])
if __name__=='__main__':unittest.main()
