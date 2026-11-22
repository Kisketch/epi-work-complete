from fractions import Fraction as F
from math import gcd, factorial, isqrt
from pathlib import Path
import csv

def atan(b,n):
    v=sum((F((-1)**i,(2*i+1)*b**(2*i+1)) for i in range(n)),F(0))
    return sorted((v,v+F((-1)**n,(2*n+1)*b**(2*n+1))))

def cv(lo,hi,cut):
    a,b,r,s=1,0,0,1
    out=[]
    while b<=cut:
        t=lo//1
        assert t==hi//1
        a,b,r,s=t*a+r,t*b+s,a,b
        out.append((a,b,t))
        lo,hi=1/(hi-t),1/(lo-t)
    return out

def compute():
    q0,q,P0,P=1,1,1,3
    windows=[]
    for j in range(1,61):
        windows.append((j,P,q,isqrt(j*q*q)))
        q0,q=q,(4*j+2)*q+q0
        P0,P=P,(4*j+2)*P+P0
    cut=windows[-1][-1]
    l,u=atan(5,230); v,w=atan(239,230)
    e=sum(F(1,factorial(i)) for i in range(181))
    rows=[]
    for name,lo,hi,A,B in [('pi',16*l-4*w,16*u-4*v,0,0)]+[
        (f'{A}/{B}-e',F(A,B)-e-F(2,factorial(181)),F(A,B)-e,A,B)
        for A,B in [(6,1),(17,3),(43,7)]]:
        c=cv(lo,hi,cut)
        last=None
        for j,P,q,H in windows[1:]:
            m=max(i for i,(_,b,_) in enumerate(c) if b<=H)
            k=m if (j-m)%2==0 else m-1
            if k<0: continue
            p,d,_=c[k]; s=c[k+1][1]
            g=gcd(q,d); Q=q//g; D=d//g; V=D*P+Q*p
            h=gcd(g*Q*D,V)
            assert h==gcd(g,V) and gcd(V,Q*D)==1
            if B and j>=B*B:
                M=gcd(A*q-B*P,B*q)
                assert c[m][:2]==((A*q-B*P)//M,B*q//M)
                assert m==k+1 and abs(A*g*Q*D-B*V)==M//g and B%g==0
                assert M%(g*h)==0 and F(g*h*s,q)*F(M,g*h)==B
                if last:
                    a,b,t,M0=last
                    assert abs(a*c[m][1]-b*c[m][0])*M*M0==2*B*B
                    assert m>t and (m-t)%2==1
                last=(*c[m][:2],m,M)
            rows.append((name,j,k,m,g,h,P,q,p,d,s))
    with Path(__file__).with_name('certified.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow('x j k m g h P Q p d s'.split());w.writerows(rows)
    actual=[row for row in rows if row[0]=='pi']
    print(f'{len(rows)} exact interval-certified windows, {len(actual)} for pi')
    print('pi rows with h>1:',[(r[1],r[4],r[5]) for r in actual if r[5]>1])
if __name__=='__main__': compute()
