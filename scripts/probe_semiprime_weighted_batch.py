#!/usr/bin/env python3
"""Experimental weighted collision search with batched order/GCD work.

Balanced-semiprime promise q <= 2p. Fixed base 2 can fail at low order;
this is not an unconditional deterministic factorisation algorithm.
All materialised collision rows retain the one-fifth target scale.

Optional research replay; not part of Lean builds or ordinary CI.
Run from formal/ with ../.venv/bin/python -B scripts/probe_semiprime_weighted_batch.py.
Generated factor labels are used only to verify returned factors.
"""

import gmpy2,math,random,time,statistics,json,numpy as np
MASK=(1<<32)-1
class VectorMod:
 def __init__(self,n):
  if n <= 1 or n % 2 == 0: raise ValueError('odd modulus greater than one required')
  self.n=n;self.limbs=(n.bit_length()+31)//32;self.R=1<<(32*self.limbs)
  self.nl=[np.uint64((n>>(32*i))&MASK) for i in range(self.limbs)]
  self.ninv=np.uint64((-pow(n,-1,1<<32))&MASK)
 def pack(self,xs):
  return np.array([[(int(x)>>(32*i))&MASK for x in xs] for i in range(self.limbs)],dtype=np.uint64)
 def unpack(self,x):
  raw=x.T.astype('<u4').tobytes();w=4*self.limbs
  return [int.from_bytes(raw[i:i+w],'little') for i in range(0,len(raw),w)]
 def mm(self,a,b):
  d=self.limbs;size=a.shape[1];t=[np.zeros(size,dtype=np.uint64) for _ in range(d+1)]
  mask=np.uint64(MASK)
  for j in range(d):
   carry=np.zeros(size,dtype=np.uint64)
   for l in range(d):
    uv=t[l]+a[l]*b[j]+carry;t[l]=uv&mask;carry=uv>>np.uint64(32)
   top=t[d]+carry;t[d]=top&mask;extra=top>>np.uint64(32)
   m=(t[0]*self.ninv)&mask;carry=np.zeros(size,dtype=np.uint64)
   for l in range(d):
    uv=t[l]+m*self.nl[l]+carry
    if l:t[l-1]=uv&mask
    carry=uv>>np.uint64(32)
   top=t[d]+carry;t[d-1]=top&mask;t[d]=extra+(top>>np.uint64(32))
  borrow=np.zeros(size,dtype=np.uint64);diff=[]
  for l in range(d):
   sub=self.nl[l]+borrow
   diff.append((t[l]-sub)&mask);borrow=(t[l]<sub).astype(np.uint64)
  take=t[d]>=borrow
  return np.array([np.where(take,diff[l],t[l]) for l in range(d)],dtype=np.uint64)
 def powers(self,exps,base=2,w=10,keep_mont=False):
  if not exps: return []
  if min(exps) < 0 or max(exps).bit_length() > 128:
   raise ValueError('vector exponent must fit 128 nonnegative bits')
  mask=(1<<w)-1;maxe=max(exps);cols=(maxe.bit_length()+w-1)//w
  one=(self.R%self.n);ans=self.constant(one,len(exps))
  lo=np.array(exps,dtype=np.uint64) if maxe.bit_length()<=64 else np.array([e&((1<<64)-1) for e in exps],dtype=np.uint64)
  hi=None if maxe.bit_length()<=64 else np.array([e>>64 for e in exps],dtype=np.uint64)
  q=base%self.n
  for j in range(cols):
   vals=[one];v=one
   for _ in range(mask):v=v*q%self.n;vals.append(v)
   table=self.pack(vals)
   shift=j*w
   if shift>=64:digit=(hi>>np.uint64(shift-64))&np.uint64(mask)
   else:
    digit=lo>>np.uint64(shift)
    if shift+w>64 and hi is not None:digit=digit|(hi<<np.uint64(64-shift))
    digit=digit&np.uint64(mask)
   ans=self.mm(ans,table[:,digit])
   q=int(gmpy2.powmod(q,1<<w,self.n))
  if keep_mont:return ans
  ans=self.mm(ans,self.constant(1,len(exps)))
  return self.unpack(ans)

def constant(self,x,count):
 digits=np.array([(x>>(32*i))&MASK for i in range(self.limbs)],dtype=np.uint64)
 return np.broadcast_to(digits[:,None],(self.limbs,count))
VectorMod.constant=constant
def geometry(n):
 K=int(gmpy2.iroot(n,5)[0]);K+=K**5<n;r=4*K//5;rows=[]
 for a in range(1,math.isqrt(r)+1):
  for b in range(a,min(2*a,r//a)+1):
   if math.gcd(a,b)!=1:continue
   c=math.isqrt(4*a*b*n);c+=c*c<4*a*b*n;rows.append((a,b,c))
 return rows
def separated_vector(n,rows,w):
 vm=VectorMod(n);one=vm.R%n
 A=int(gmpy2.powmod(2,n,n));pa=[one];pb=[one]
 for a in range(max(row[0] for row in rows)):pa.append(pa[-1]*A%n)
 for b in range(max(row[1] for row in rows)):pb.append(pb[-1]*2%n)
 ca=vm.pack(pa)[:,np.array([row[0] for row in rows],dtype=np.intp)]
 cb=vm.pack(pb)[:,np.array([row[1] for row in rows],dtype=np.intp)]
 ans=vm.powers([row[2] for row in rows],pow(2,-1,n),w,keep_mont=True)
 ans=vm.mm(vm.mm(vm.mm(ans,ca),cb),vm.constant(1,len(rows)))
 return vm.unpack(ans)

def mul(a,b,n):
 w=(2*n.bit_length()+min(len(a),len(b)).bit_length()+7)//8
 aa=gmpy2.mpz(int.from_bytes(b''.join(int(v).to_bytes(w,'little') for v in a),'little'))
 bb=gmpy2.mpz(int.from_bytes(b''.join(int(v).to_bytes(w,'little') for v in b),'little'))
 size=len(a)+len(b)-1;buf=int(aa*bb).to_bytes(size*w,'little')
 return [int.from_bytes(buf[i*w:(i+1)*w],'little')%n for i in range(size)]
def tree(vals,n):
 nodes=[([(-v)%n,1],None,None) for v in vals]
 while len(nodes)>1:
  nxt=[]
  for i in range(0,len(nodes),2):
   if i+1==len(nodes):nxt.append(nodes[i]);continue
   a,b=nodes[i:i+2];nxt.append((mul(a[0],b[0],n),a,b))
  nodes=nxt
 return nodes[0]
def horner(poly,x,n):
 v=0
 for c in reversed(poly):v=(v*x+c)%n
 return v
def descend(node,x,n):
 g=math.gcd(horner(node[0],x,n),n)
 if 1<g<n:return g
 if g==n and node[1] is not None:return descend(node[1],x,n) or descend(node[2],x,n)
 return None
def chirp(poly,start,q,count,n):
 d=len(poly)-1;seq=[];v=step=1
 for _ in range(d+count):seq.append(v);v=v*step%n;step=step*q%n
 invq=pow(q,-1,n);v=step=s=1;tw=[]
 for c in poly:tw.append(c*v%n*s%n);v=v*step%n;step=step*invq%n;s=s*start%n
 conv=mul(tw[::-1],seq,n);ans=[];v=step=1
 for i in range(count):ans.append(conv[d+i]*v%n);v=v*step%n;step=step*invq%n
 return ans
def factor(n,variant):
 began=time.perf_counter();K=int(gmpy2.iroot(n,5)[0]);K+=K**5<n;r=4*K//5;m=2*((math.ceil(K/2)+1)//2);base=2
 babies=[];v=1
 for i in range(m):
  babies.append(v)
  if i:
   g=math.gcd(v-1,n)
   if 1<g<n:return g,1000*(time.perf_counter()-began),'order'
   if g==n:return None,1000*(time.perf_counter()-began),'global-low-order'
  v=v*base%n
 giant=pow(v,-1,n);babyhash={v:i for i,v in enumerate(babies)};rows=geometry(n)
 exps=[a*n+b-c for a,b,c in rows]
 if variant=='individual':anchors=[int(gmpy2.powmod(base,e,n)) for e in exps]
 elif variant=='native-list':anchors=list(map(int,gmpy2.powmod_exp_list(base,exps,n)))
 elif len(rows)<4096:anchors=list(map(int,gmpy2.powmod_exp_list(base,exps,n)))
 else:anchors=separated_vector(n,rows,8 if len(rows)<32768 else 12)
 groups={}
 for (a,b,c),v in zip(rows,anchors):
  ab=a*b;key=(a+b-c)%2;qty=1+math.isqrt((n-1)//(16*r*r*m*m*ab))
  for j in range(qty):
   if v in babyhash:
    i=babyhash[v];s=c+j*m+i;disc=s*s-4*ab*n
    if disc>=0:
     root=math.isqrt(disc)
     if root*root==disc:
      for z in ((s+root)//2,(s-root)//2):
       g=math.gcd(z,n)
       if 1<g<n:return g,1000*(time.perf_counter()-began),'global'
   else:groups.setdefault(key,[]).append(v)
   v=v*giant%n
 for residue,vals in groups.items():
  node=tree(list(dict.fromkeys(vals)),n);count=(m-1-residue)//2+1
  out=chirp(node[0],pow(base,residue,n),pow(base,2,n),count,n)
  for k,value in enumerate(out):
   g=math.gcd(value,n)
   if g==n:g=descend(node,babies[residue+2*k],n)
   if g is not None and 1<g<n:return g,1000*(time.perf_counter()-began),'batch'
 return None,1000*(time.perf_counter()-began),'failure'

def order_probe(n,base,D):
 b=math.isqrt(D);b+=b*b<D;J=(D+b-1)//b
 small=[];v=1
 for i in range(b):small.append(v);v=v*base%n
 q=v;node=tree(small,n);out=chirp(node[0],q,q,J,n)
 for j,z in enumerate(out):
  g=math.gcd(z,n)
  if 1<g<n:return 'factor',g
  if g==n:
   t=pow(q,j+1,n);f=descend(node,t,n)
   if f:return 'factor',f
   return 'global',None
 return 'ok',None
def factor_batched(n,variant):
 began=time.perf_counter();K=int(gmpy2.iroot(n,5)[0]);K+=K**5<n;r=4*K//5;m=2*((math.ceil(K/2)+1)//2);base=2
 status,f=order_probe(n,base,m-1)
 if f:return f,1000*(time.perf_counter()-began),'order'
 if status!='ok':return None,1000*(time.perf_counter()-began),'global-low-order'
 babies=[];v=1
 for i in range(m):babies.append(v);v=v*base%n
 giant=pow(v,-1,n);babyhash={v:i for i,v in enumerate(babies)};rows=geometry(n)
 exps=[a*n+b-c for a,b,c in rows]
 if variant=='individual':anchors=[int(gmpy2.powmod(base,e,n)) for e in exps]
 elif variant=='native-list':anchors=list(map(int,gmpy2.powmod_exp_list(base,exps,n)))
 elif len(rows)<4096:anchors=list(map(int,gmpy2.powmod_exp_list(base,exps,n)))
 else:anchors=separated_vector(n,rows,8 if len(rows)<32768 else 12)
 groups={}
 for (a,b,c),v in zip(rows,anchors):
  ab=a*b;key=(a+b-c)%2;qty=1+math.isqrt((n-1)//(16*r*r*m*m*ab))
  for j in range(qty):
   if v in babyhash:
    i=babyhash[v];s=c+j*m+i;disc=s*s-4*ab*n
    if disc>=0:
     root=math.isqrt(disc)
     if root*root==disc:
      for z in ((s+root)//2,(s-root)//2):
       g=math.gcd(z,n)
       if 1<g<n:return g,1000*(time.perf_counter()-began),'global'
   else:groups.setdefault(key,[]).append(v)
   v=v*giant%n
 for residue,vals in groups.items():
  node=tree(list(dict.fromkeys(vals)),n);count=(m-1-residue)//2+1
  out=chirp(node[0],pow(base,residue,n),pow(base,2,n),count,n)
  for offset in range(0,len(out),64):
   product=1
   for value in out[offset:offset+64]:product=product*value%n
   g=math.gcd(product,n)
   if 1<g<n:return g,1000*(time.perf_counter()-began),'batch'
   if g==n:
    for k in range(offset,min(offset+64,len(out))):
     g=math.gcd(out[k],n)
     if g==n:g=descend(node,babies[residue+2*k],n)
     if g is not None and 1<g<n:return g,1000*(time.perf_counter()-began),'batch'
 return None,1000*(time.perf_counter()-began),'failure'


def replay():
    rng=random.Random(2026100447)
    # Exact small-case gate for every possible certificate outcome.
    smallchecks=0
    for n in (17*19,101*103,101*173,257*263,1009*1013):
     for base in (2,3,5,7):
      if math.gcd(base,n)!=1:continue
      for D in (1,2,3,4,5,9,16,25,40,63,100):
       status,f=order_probe(n,base,D);b=math.isqrt(D);b+=b*b<D;last=b*((D+b-1)//b)
       if f:assert 1<f<n and n%f==0
       elif status=='ok':assert all(math.gcd(pow(base,i,n)-1,n)==1 for i in range(1,D+1))
       else:assert any(pow(base,i,n)==1 for i in range(1,last+1)),(n,base,D,status)
       smallchecks+=1
    print(json.dumps({'order_certificate_checks':smallchecks}),flush=True)
    times={}
    for bits,cases in ((48,6),(64,6),(80,6)):
     lo=1<<(bits//2-1);hi=(1<<(bits//2))-2000
     for _ in range(cases):
      p=int(gmpy2.next_prime(rng.randrange(lo,hi)));q=int(gmpy2.next_prime(rng.randrange(lo,hi)))
      if p==q:q=int(gmpy2.next_prime(q+2))
      n=p*q;configs=[('baseline',factor,'individual'),('gcd-batched',factor_batched,'individual'),('joint-batched',factor_batched,'hybrid')]
      per={name:[] for name,_,_ in configs};reasons={}
      for repeat in range(2):
       order=list(configs);rng.shuffle(order)
       for name,func,variant in order:
        g,ms,why=func(n,variant);assert g in (p,q),(bits,name,g,why)
        per[name].append(ms);reasons[name]=why
      for name,ts in per.items():times.setdefault((bits,name),[]).append((statistics.mean(ts),reasons[name]))
    for (bits,name),ts in times.items():
     print(json.dumps({'class':bits,'variant':name,'cases':len(ts),'median_full_factor_ms':round(statistics.median(x[0] for x in ts),4),'batch_cases':sum(x[1]=='batch' for x in ts)}))
    print(json.dumps({'exact_factoring_checks':sum(len(v) for v in times.values())*2,'seed':2026100447}))


if __name__ == '__main__':
    replay()
