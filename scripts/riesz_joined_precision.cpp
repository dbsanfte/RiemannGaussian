// Optional numerical audit; no part of the Lean proof or ordinary CI.
// Copyright (c) 2026 David Sanftenberg. Apache-2.0.
// Exact intended modes: 0 and 1/40000 +/- (3/500)i, multiplicities 1,3,3.
// All arithmetic below is rounded; neither precision backend is an enclosure.
#include <boost/multiprecision/cpp_dec_float.hpp>
#include <boost/multiprecision/float128.hpp>
#include <vector>
#include <string>
#include <iostream>
#include <iomanip>
#ifdef USE_QUAD
using R=boost::multiprecision::float128;
#else
using R=boost::multiprecision::cpp_dec_float_100;
#endif
int main(int argc,char**argv){
 if(argc!=4)return 2;
 int N=std::stoi(argv[1]),ell=std::stoi(argv[2]);
 R r(argv[3]),u=R(10001)/20000,p=R(11)/20;
 R T=(R(N)+1)/u,L=2*(-R(N)*log(u)-log(R(N)+1));
 int S=static_cast<int>((1-p)/r*ell+R("0.5"));
 if(abs(R(S)-(1-p)/r*ell)>R("1e-25"))return 4;
 int size=S+1;
 R d=R(1)/40000,eta=R(3)/500;
 R ex=exp(d*T*r/ell),th=eta*T*r/ell;
 R lr=ex*cos(th),li=ex*sin(th);
 R exl=exp(d*T*r),thl=eta*T*r;
 R er=exl*cos(thl),ei=exl*sin(thl);
 R pr=er*lr-ei*li,pi=er*li+ei*lr;
 std::vector<R>a(size),b(size);a[0]=b[0]=1;
 R sa=0,sb=0,har=0,hai=0,hbr=0,hbi=0;
 for(int n=1;n<size;n++){
  R da=(n>ell?a[n-ell-1]:R(0)),db=(n>ell?b[n-ell-1]:R(0));
  sa+=da;sb+=db;
  R nar=lr*har-li*hai+da,nai=li*har+lr*hai;
  R nbr=lr*hbr-li*hbi+db,nbi=li*hbr+lr*hbi;
  har=nar;hai=nai;hbr=nbr;hbi=nbi;
  R ca=(n>=ell?a[n-ell]:R(0)),cb=(n>=ell?b[n-ell]:R(0));
  a[n]=-(sa+ca/2+6*(pr*har-pi*hai+er*ca/2))/n;
  b[n]=(sb+cb/2+6*(pr*hbr-pi*hbi+er*cb/2))/n;
 }
 R gap=(1-L/T)/r,v=0,abs_sum=0;
 for(int i=0;i<=S;i++){
   R x=R(i)/ell-gap;
   if(x>0){R term=-ell*a[i]*b[S-i]*x;v+=term;abs_sum+=abs(term);}
 }
 std::cout<<std::setprecision(95)<<N<<" "<<ell<<" "<<r<<" "<<v<<" "<<abs_sum<<"\n";
}
