from fractions import Fraction
from math import gcd, lcm
from verify import cv
from math import factorial, isqrt
def egcd(a,b):
    if b==0:return a,1,0
    g,x,y=egcd(b,a%b)
    return g,y,x-(a//b)*y
def odds_len(c, delta):
    f=Fraction(2*delta+c,delta); n=0
    while True:
        n+=1
        if f.denominator==1:return n+(n%2==0)
        f=1/(f-f.numerator//f.denominator)
def sequence(A,B):
    T=2*B*B
    state=(1%T,1%T,3%T,1%T,1%T)
    first=state
    widths=[]
    while True:
        j,PP,P,QQ,Q=state
        P1=((4*j+2)*P+PP)%T; Q1=((4*j+2)*Q+QQ)%T
        a=(A*Q-B*P)%T;b=B*Q%T;a1=(A*Q1-B*P1)%T;b1=B*Q1%T
        M=gcd(a,b,B*B); M1=gcd(a1,b1,B*B)
        delta=T//(M*M1)
        assert M*M1*delta==T
        a,b,a1,b1=a//M,b//M,a1//M1,b1//M1
        g,x,y=egcd(a,b)
        assert gcd(g,delta)==1
        c=((x*a1+y*b1)*pow(g,-1,delta))%delta
        assert (a1-c*a)%delta==(b1-c*b)%delta==0
        widths.append(odds_len(c,delta))
        state=((j+1)%T,P,P1,Q,Q1)
        if state==first:return widths
def irr_test(A,B,w):
    E=sum(Fraction(1,factorial(i)) for i in range(181))
    prev=q=1
    H=[]
    for j in range(1,61):
        H.append(isqrt(j*q*q));prev,q=q,(4*j+2)*q+prev
    vals=cv(Fraction(A,B)-E-Fraction(2,factorial(181)),Fraction(A,B)-E,H[-1])
    ix=[max(i for i,(_,v,_) in enumerate(vals) if v<=h) for h in H]
    for j in range(B*B,60):
        assert ix[j]-ix[j-1]==w[(j-1)%len(w)]
def main():
    for A,B in [(6,1),(11,2),(17,3),(23,4),(29,5),(43,7)]:
        w=sequence(A,B); irr_test(A,B,w)
        least=next(i for i in range(1,len(w)+1) if len(w)%i==0 and w==w[:i]*(len(w)//i))
        print(A,B,len(w),least,Fraction(sum(w),len(w)),sorted(set(w)),w[:min(least,20)])
if __name__=='__main__':main()
