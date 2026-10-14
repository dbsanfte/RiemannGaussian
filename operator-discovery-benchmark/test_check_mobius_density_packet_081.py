import copy
import unittest
from fractions import Fraction as Q
import check_mobius_density_packet_081 as C

def program():return {'schema':'growing-density-packet-v1','kernel':[{'divisor':4,'weight':'-1'},{'divisor':5,'weight':'1'}],'memory':2,'rays':[{'a':['1','-1'],'weight':'1/2'}],'drift_multiplier':'3/2','epsilon':'1','eta':'1/7','q':'1'}
def certificate(p):
 depth=p['memory'];H=[[Q(0) for j in range(depth)] for i in range(depth)];H[0][0]=Q(1)
 for ray in p['rays']:
  a=list(map(Q,ray['a']));w=Q(ray['weight'])
  for i in range(depth):
   for j in range(depth):H[i][j]+=w*a[i]*a[j]
 T=[[Q(0) for j in range(depth+1)] for i in range(depth+1)]
 for i in range(depth):
  for j in range(depth):T[i][j]+=H[i][j];T[i+1][j+1]-=Q(p['drift_multiplier'])*H[i][j]
 total=sum((abs(Q(row['weight'])) for row in p['kernel']),Q(0));J=2*sum((abs(v) for row in T for v in row),Q(0))*total*total
 assert Q(p['epsilon'])==1
 return {'omega_price':'1','jump_price':str(J),'constant':str(3*J),'exponent':str(Q(1,2)+Q(p['eta'])*(Q(3,2)+2*Q(p['epsilon'])))}
class Tests(unittest.TestCase):
 def test_exact_gram_shift_and_uniform_bound_scope(self):
  p=program();v=C.verify_bound(p,certificate(p));self.assertEqual(v['status'],'VERIFIED_UNIFORM_SIGNED_PACKET_BOUND');self.assertEqual(v['exponent'],'1');self.assertEqual(v['H'],[['3/2','-1/2'],['-1/2','1/2']]);self.assertFalse(v['uniform_original_residual_bound_proved']);self.assertFalse(v['uniform_unlinked_correlation_proved']);self.assertFalse(v['RH_proved'])
  self.assertEqual(v['T'][1][1],'-7/4')
 def test_certificate_mutations_and_unpaid_exponent(self):
  p=program();good=certificate(p)
  for key in good:
   bad=dict(good);bad[key]=str(Q(bad[key])+1);self.assertEqual(C.verify_bound(p,bad)['status'],'INVALID')
  p['eta']='1/6';self.assertEqual(C.verify_bound(p,certificate(p))['status'],'UNPAID_EXPONENT')
 def test_schema_domain_false_flag_and_weights(self):
  p=program()
  for key,value in [('memory',True),('memory',4),('epsilon','0'),('eta','0'),('drift_multiplier','1/2'),('q','2')]:
   bad=copy.deepcopy(p);bad[key]=value;self.assertEqual(C.verify_bound(bad,certificate(p))['status'],'INVALID')
  bad=copy.deepcopy(p);bad['RH_proved']=True;self.assertEqual(C.verify_bound(bad,certificate(p))['status'],'INVALID')
  bad=copy.deepcopy(p);bad['rays'][0]['weight']='0';self.assertEqual(C.verify_bound(bad,certificate(p))['status'],'INVALID')
  bad=copy.deepcopy(p);bad['rays'][0]['a']=['1'];self.assertEqual(C.verify_bound(bad,certificate(p))['status'],'INVALID')
 def test_omega_prime_boundary_and_independent_small_n(self):
  result=C.omega_price(Q(1,2));self.assertEqual(result['primes'],(2,3));self.assertEqual(result['horizon'],4)
  price=result['price'];self.assertGreaterEqual(price*price,Q(8,3))
  for n in range(1,301):
   remainder=n;omega=0
   for p in range(2,n+1):
    if remainder%p==0:
     omega+=1
     while remainder%p==0:remainder//=p
   self.assertLessEqual(4**omega,price*price*n)
  self.assertEqual(C.omega_price(Q(1))['price'],1)
 def test_resource_horizon_preallocation_and_canonical(self):
  with self.assertRaises(C.ResourceLimit):C.omega_price(Q(1,21))
  p=program();p['epsilon']='2/2';self.assertEqual(C.verify_bound(p,certificate(program()))['status'],'INVALID')
  m=C.Meter();m.reserve=lambda n:(_ for _ in ()).throw(C.ResourceLimit('synthetic prospective allocation cap'))
  self.assertTrue(C.verify_bound(program(),certificate(program()),m)['resource_limit'])
 def test_empty_rays_kernel_units_and_arbitrary_denominator(self):
  p=program();p['memory']=1;p['rays']=[];p['kernel']=[{'divisor':1,'weight':'17/31'}];p['drift_multiplier']='1';v=C.verify_bound(p,certificate(p));self.assertEqual(v['status'],'VERIFIED_UNIFORM_SIGNED_PACKET_BOUND');self.assertEqual(v['T'],[['1','0'],['0','-1']])

def mu(n):
 result=1;p=2
 while p*p<=n:
  if n%p==0:
   n//=p;result=-result
   if n%p==0:return 0
   while n%p==0:n//=p
  p+=1
 if n>1:result=-result
 return result

def finite_oracle(p,u):
 import math
 depth=p['memory'];kernel=[(x['divisor'],Q(x['weight'])) for x in p['kernel']]
 H=[[Q(i==j==0) for j in range(depth)] for i in range(depth)]
 for row in p['rays']:
  a=list(map(Q,row['a']));w=Q(row['weight'])
  for i in range(depth):
   for j in range(depth):H[i][j]+=w*a[i]*a[j]
 T=[[Q(0) for j in range(depth+1)] for i in range(depth+1)]
 for i in range(depth):
  for j in range(depth):T[i][j]+=H[i][j];T[i+1][j+1]-=Q(p['drift_multiplier'])*H[i][j]
 D=math.isqrt(u) # these fixtures eta1/2
 def step(a,x,i):return sum((w for d,w in kernel if a*x<=Q(1,2**i*d)),Q(0))
 def height(a,b,x):return 2*sum((T[i][j]*step(a,x,i)*step(b,x,j) for i in range(depth+1) for j in range(depth+1)),Q(0))
 bank=[];P=N=Q(0);nonzero=0
 for b in range(2,D+1):
  for a in range(1,b):
   if math.gcd(a,b)!=1 or not mu(a) or not mu(b):continue
   endpoints=sorted(set(Q(1,c*2**i*d) for c in(a,b) for i in range(depth+1) for d,w in kernel));I=Q(0);left=Q(0);active=False
   for right in endpoints:
    value=height(a,b,(left+right)/2);I+=value*(right-left);active |= bool(value);left=right
   primes=[v for v in range(2,a*b+1) if a*b%v==0 and all(v%d for d in range(2,math.isqrt(v)+1))];density=Q(1)
   for prime in primes:density*=Q(prime,prime+1)
   v=mu(a)*mu(b)*density*I
   P+=max(v,0);N+=max(-v,0);nonzero+=active;bank.append((a,b,v,active))
 packet=weighted_density=Q(0);weighted=0
 for a,b,v,active in bank:
  w=min(Q(1),N/P) if v>0 else min(Q(1),P/N) if v<0 else Q(1)
  weighted_density+=w*v
  if active and w:weighted+=1
  # physical factor identity, directly sum all squarefree g and original step.
  packet+=w*mu(a)*mu(b)*sum((height(a,b,Q(g,u))*mu(g)**2 for g in range(1,u+1) if math.gcd(g,a*b)==1),Q(0))
 state=[sum((mu(n)*sum((w for d,w in kernel if n<=u//2**j//d),Q(0)) for n in range(1,u+1)),Q(0)) for j in range(depth+1)]
 energies=[sum((H[i][j]*state[i+s]*state[j+s] for i in range(depth) for j in range(depth)),Q(0)) for s in(0,1)];drift=energies[0]-Q(p['drift_multiplier'])*energies[1]
 return {'D':D,'pair_count':len(bank),'positive_mass':str(P),'negative_mass':str(N),'weighted_density':str(weighted_density),'packet':str(packet),'energy':str(energies[0]),'half_energy':str(energies[1]),'drift':str(drift),'unlinked':str(drift-packet),'state':list(map(str,state)),'nonzero_pairs':nonzero,'weighted_pairs':weighted}

class FiniteTests(unittest.TestCase):
 def fixture(self):
  p=program();p['eta']='1/2';p['kernel']=[{'divisor':1,'weight':'1'},{'divisor':3,'weight':'-1/2'}];return p
 def test_complete_ratio_source_counts_and_signed_packet(self):
  p=self.fixture()
  for u in (1,4,17,36,64):
   certificate=finite_oracle(p,u);v=C.verify_finite(p,u,certificate);self.assertEqual(v['status'],'VERIFIED_FINITE_PACKET');self.assertTrue(v['arithmetic_source_admitted']);self.assertFalse(v['uniform_signed_packet_bound_proved']);self.assertEqual(v['weighted_density'],'0')
 def test_finite_tamper_both_source_endpoints_and_balance(self):
  p=self.fixture();cert=finite_oracle(p,36)
  for key in ['D','pair_count','nonzero_pairs','weighted_pairs','positive_mass','negative_mass','weighted_density','packet','energy','half_energy','drift','unlinked']:
   bad=copy.deepcopy(cert);bad[key]=bad[key]+1 if isinstance(bad[key],int) else str(Q(bad[key])+1);self.assertEqual(C.verify_finite(p,36,bad)['status'],'INVALID',key)
  for j in range(3):
   bad=copy.deepcopy(cert);bad['state'][j]=str(Q(bad['state'][j])+1);self.assertEqual(C.verify_finite(p,36,bad)['status'],'INVALID')
 def test_pair_units_squareful_coprimality_and_cache(self):
  p=self.fixture();p['rays'][0]['weight']='17/31';first=C.audit_pair(p,1,2);self.assertEqual(first['status'],'VERIFIED_PAIR_KERNEL');self.assertEqual(first['mobius_sign'],-1)
  second=C.audit_pair(p,1,2);self.assertEqual(first['terms'],second['terms']);self.assertLess(second['ops'],first['ops'])
  for a,b in [(1,4),(2,6),(2,2)]:self.assertEqual(C.audit_pair(p,a,b)['status'],'INVALID')
 def test_zero_kernels_retained_in_complete_bank(self):
  p=self.fixture();p['kernel']=[];cert=finite_oracle(p,36);v=C.verify_finite(p,36,cert);self.assertEqual(v['status'],'VERIFIED_FINITE_PACKET');self.assertGreater(v['pair_count'],0);self.assertEqual(v['nonzero_pairs'],0);self.assertEqual(v['packet'],'0')
 def test_independent_square_divisor_coprime_counts(self):
  source=C.A.ensure_horizon(128);meter=C.Meter()
  for N,primes in [(1,()),(6,(2,3)),(35,(5,7)),(143,(11,13))]:
   for x in (0,1,2,7,16,63,128):
    import math
    expected=sum(mu(n)**2 for n in range(1,x+1) if math.gcd(n,N)==1)
    self.assertEqual(C._count(N,primes,x,source,meter),expected)
 def test_standalone_pair_integral_by_continuous_step_geometry(self):
  p=program();p['memory']=1;p['rays']=[];p['kernel']=[{'divisor':1,'weight':'1'}];p['drift_multiplier']='3/2'
  # For labels1,3: 2*1[g/u<=1/3]-3*1[g/u<=1/6].
  v=C.audit_pair(p,1,3);self.assertEqual(v['status'],'VERIFIED_PAIR_KERNEL');self.assertEqual(v['terms'],[{'denominator':3,'coefficient':'2'},{'denominator':6,'coefficient':'-3'}]);self.assertEqual(v['integral'],'1/6');self.assertEqual(v['signed_density'],'-1/8')

 def test_generic_large_lcms_and_cached_bank_are_prospective(self):
  from unittest.mock import patch
  p=self.fixture();p['memory']=1;p['rays']=[]
  p['kernel']=[{'divisor':i+1,'weight':'1/'+str((1<<4090)+2*i+1)} for i in range(128)]
  dummy=finite_oracle(self.fixture(),4)
  with patch.object(C.A,'ensure_horizon',side_effect=AssertionError('source allocation must not occur')):
   v=C.verify_finite(p,16,dummy);self.assertEqual(v['status'],'INVALID');self.assertTrue(v['resource_limit'])
  p['kernel']=[{'divisor':i+1,'weight':'1'} for i in range(128)]
  with patch.object(C.A,'ensure_horizon',side_effect=AssertionError('source allocation must not occur')):
   v=C.verify_finite(p,396900,dummy);self.assertEqual(v['status'],'INVALID');self.assertTrue(v['resource_limit'])
  p['kernel']=[{'divisor':1,'weight':'1'}];p['rays']=[{'a':['1'],'weight':'1/'+str((1<<4090)+2*(i%100)+1)} for i in range(10000)]
  with patch.object(C.A,'ensure_horizon',side_effect=AssertionError('source allocation must not occur')):
   v=C.verify_finite(p,16,dummy);self.assertEqual(v['status'],'INVALID');self.assertTrue(v['resource_limit'])

 def test_huge_complete_bank_rejected_before_source_allocation(self):
  p=self.fixture();p['eta']='1';dummy=finite_oracle(self.fixture(),4);v=C.verify_finite(p,1000000,dummy);self.assertEqual(v['status'],'INVALID');self.assertTrue(v['resource_limit'])

if __name__=='__main__':unittest.main()
