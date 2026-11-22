from fractions import Fraction as F
from math import factorial,isqrt,gcd
import csv
from pathlib import Path
def ar(b,n):
 t=sum(F((-1)**k,(2*k+1)*b**(2*k+1)) for k in range(n))
 return sorted([t,t+F((-1)**n,(2*n+1)*b**(2*n+1))])
def machin(n):
 l,u=ar(5,n);v,w=ar(239,n);return 16*l-4*w,16*u-4*v
L,U=machin(230)
e=sum(F(1,factorial(i)) for i in range(181))
rows=list(csv.DictReader(open('parallel_work/A/witnesses.csv')))
for x,lo,hi in [('pi',L,U),('6-e',6-e-F(2,factorial(181)),6-e)]:
 prev=q=1; doubles=[]
 for j in range(1,61):
  H=isqrt(j*q*q);a,b,r,s=1,0,0,1;y=lo
  while True:
   f=y//1; A=f*a+r;B=f*b+s
   if B>H:break
   r,s,a,b=a,b,A,B;y=1/(y-f)
  t=(H-s)//b; pairs=set()
  for p,d in [(a,b),(r+t*a,s+t*b)]:
   u,v=sorted([abs(d*lo-p),abs(d*hi-p)]);assert (d*lo-p)*(d*hi-p)>0
   n=min(H//d,1//((H+1)*v));assert n==min(H//d,1//((H+1)*u))
   pairs.update((k*p,k*d) for k in range(1,n+1))
  R=[i for i in rows if i['x']==x and int(i['j'])==j]
  assert pairs=={(int(i['p']),int(i['d'])) for i in R}
  assert all(q//gcd(q,int(i['d']))==int(i['quotient']) for i in R)
  if sum(gcd(p,d)==1 for p,d in pairs)==2:doubles.append(j)
  prev,q=q,(4*j+2)*q+prev
 print(x,doubles)
for n in (2,3,4,5,6,10,20,50,100):
 m=1
 while (2*m+1)*5**(2*m+1)<16*factorial(n)*n*n:m+=1
 l,u=machin(m);l,u=-u*factorial(n),-l*factorial(n)
 # use tight independent enclosure for displayed decimal certificate
 l,u=-U*factorial(n),-L*factorial(n); assert l//1==u//1
 print(n,m,float(n*(l-l//1)))

