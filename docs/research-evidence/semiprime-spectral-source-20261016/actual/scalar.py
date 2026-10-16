"""Exact all-scalar finite-field root-freeness certificate for the same input.
Importing orbit also rechecks its full companion determinant and orbit witnesses.
"""
import orbit
import json,pathlib
base=pathlib.Path(__file__).parent
out={}
for key,o in orbit.out.items():
 p=int(key);phi=o['phi']
 r=orbit.add(orbit.power([0,1],p,phi,p),[0,-1],p)
 gcd,A,B=orbit.xgcd(phi,r,p)
 assert gcd==[1]
 assert orbit.add(orbit.mul(A,phi,p),orbit.mul(B,r,p),p)==[1]
 out[key]={'field_prime':p,'phi':phi,'X_power_p_minus_X_remainder':r,'gcd':gcd,'bezout_phi':A,'bezout_remainder':B}
 print('field',p,'gcd(phi,X^p-X)=1; EVERY field scalar is root-free')
(base/'scalar-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
