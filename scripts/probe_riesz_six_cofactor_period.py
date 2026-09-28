#!/usr/bin/env python3
"""Optional continuum diagnostic for the six-prime cofactor extension.

No result is an arithmetic certificate. The Lean population bound uses
actual prime-count inequalities, independently of these sampled numbers.
Run manually; no CI or ordinary build invokes this probe.
"""
import numpy as np, itertools, math, json
from scipy.special import gammaincinv,gammaln
from scipy.stats import qmc
rows=[]
for seed in range(4):
 alpha=.6; power=18; size=2**power
 g=gammaincinv(alpha,qmc.Sobol(6,scramble=True,seed=20260930+seed).random_base2(power))
 x=np.sort(g/g.sum(axis=1)[:,None],axis=1).astype(np.longdouble)
 x=x[x[:,0]>1e-8]
 coeff=np.zeros(len(x),dtype=np.longdouble); d=1-np.longdouble(.6931)
 for k in range(7):
  for sub in itertools.combinations(range(6),k):
   coeff-=(-1)**k*np.maximum(0,d-(x[:,sub].sum(axis=1) if sub else 0))/.6931
 w=np.exp(6*gammaln(alpha)-gammaln(6*alpha)-gammaln(7)-alpha*np.log(x).sum(axis=1))
 broad=(x[:,-1]>=.4)&(x[:,-1]<.552)&(x[:,-2]<=.39)
 wide=(broad | ((x[:,-1]>=.52)&(x[:,-1]<.59)&(x[:,-2]<=.312)))
 old=(x[:,0]<=.005)&(x[:,1:5]>.112).all(axis=1)&(x[:,1:5]<=.135).all(axis=1)
 expanded=wide | ((x[:,-1]>=.335)&(x[:,-1]<.4)&(x[:,-2]<=.33))
 ref=((x>=d).sum(axis=1)==1)&(x[:,-1]<=.595)
 row={}
 for name,mask in [('expanded',expanded),('expanded_one_large',expanded & ref),('wide',wide),('wide_one_large',wide & ref),('broad',broad),('broad_one_large',broad & ref),('old',old),('one_large',ref)]:
  row[name]={'positive':float((np.maximum(coeff[mask],0)*w[mask]).sum()/size),'negative':float((np.maximum(-coeff[mask],0)*w[mask]).sum()/size),'sample_hits':int(mask.sum())}
 rows.append(row)
from pathlib import Path
import hashlib
payload={'model_only':True,'scope':'Angular diagnostic, no prime/source-scale certificate', 'samples_per_replicate':2**18, 'least_share_probe_floor':1e-8, 'importance_alpha':.6, 'riesz_ratio':.6931, 'replicates':rows, 'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path('docs/riesz-six-cofactor-period-probe.json').write_text(json.dumps(payload,indent=2)+'\n')
print(json.dumps(payload,indent=2))
