// Run with Node.js: node experiment.cjs [last_j] [decimal_places]
const fs = require('node:fs');
const path = require('node:path');
const assert = require('node:assert/strict');
const last = Number(process.argv[2] || 60);
const digits = Number(process.argv[3] || 400);
assert(Number.isSafeInteger(last) && last >= 1);
assert(Number.isSafeInteger(digits) && digits >= 10);
const S = 10n ** BigInt(digits);
const abs = a => a < 0n ? -a : a;
const min = (a,b) => a < b ? a : b;
function gcd(a,b) { while (b) [a,b] = [b,a%b]; return a; }
function isqrt(n) {
  let u = n, v = (n + 1n)/2n;
  while (v < u) { u = v; v = (u + n/u)/2n; }
  return u;
}
// Each term is rounded outwards in units of 1/S.
function atanInv(b) {
  let lo = 0n, hi = 0n, power = b, sign = 1n;
  for (let i = 0n;; i++) {
    const t = S / ((2n*i+1n)*power);
    if (!t) return [lo-1n,hi+1n]; // alternating remainder
    lo += sign > 0n ? t : -t-1n;
    hi += sign > 0n ? t+1n : -t;
    sign = -sign; power *= b*b;
  }
}
function controlBounds() {
  let lo = 0n, hi = 0n, fact = 1n;
  for (let i = 0n;; i++) {
    const t = S/fact;
    if (!t) return [6n*S-hi-2n,6n*S-lo]; // e-tail < 2/i!
    lo += t; hi += t+1n; fact *= i+1n;
  }
}
function convergents(lo,hi,maxH) {
  let l=lo, b=S, u=hi, v=S;
  const cv = [[1n,0n]];
  let p0=0n,d0=1n,p1=1n,d1=0n;
  while (d1 <= maxH) {
    assert(b && v, 'Increase precision: interval endpoint is integral');
    const a = l/b;
    assert.equal(a,u/v,'Increase precision: CF digit unresolved');
    [p0,p1] = [p1,a*p1+p0]; [d0,d1] = [d1,a*d1+d0];
    cv.push([p1,d1]);
    [l,b,u,v] = [v,u-a*v,b,l-a*b];
  }
  return cv;
}
const windows = [];
let prev=1n,q=1n;
for (let j=1n;j<=BigInt(last);j++) {
  windows.push([j,q,isqrt(q*q*j)]);
  [prev,q]=[q,(4n*j+2n)*q+prev];
}
const [l5,u5]=atanInv(5n), [l239,u239]=atanInv(239n);
const rows=['x,j,Q_j,H,role,k,p,d,gcd,quotient,error_upper'];
for (const [x,L,U] of [['pi',16n*l5-4n*u239,16n*u5-4n*l239],
                        ['6-e',...controlBounds()]]) {
  const cv=convergents(L,U,windows.at(-1)[2]);
  let n=1;
  for (const [j,Q,H] of windows) {
    while (cv[n+1][1]<=H) n++;
    const [p,d]=cv[n], [r,s]=cv[n-1], t=(H-s)/d;
    const candidates=[[p,d,'conv'],[r+t*p,s+t*d,'other']];
    const seen=new Set();
    for (const [a,b,role] of candidates) {
      const z=b*L-a*S, w=b*U-a*S;
      assert(z*w>0n,'Increase precision: sign unresolved');
      const low=min(abs(z),abs(w)), high=abs(z)+abs(w)-low;
      const count=min(H/b,S/((H+1n)*high));
      assert.equal(count,min(H/b,S/((H+1n)*low)),'Increase precision: cutoff unresolved');
      if (role==='conv') assert(count>=1n);
      for (let k=1n;k<=count;k++) {
        const D=k*b, P=k*a, g=gcd(Q,D);
        rows.push([x,j,Q,H,role,k,P,D,g,Q/g,'1/'+(S/(k*high))].join(','));
        seen.add(P+'/'+D);
      }
    }
    if (x==='6-e') {
      assert.equal(BigInt(seen.size),isqrt(j));
      for (const pair of seen) assert.equal(BigInt(pair.split('/')[1])%Q,0n);
    }
    if (H<=3000n) { // independent enumeration, including equality of sets
      const brute=new Set();
      for (let D=1n;D<=H;D++) {
        const P=(2n*D*L+S)/(2n*S);
        assert.equal(P,(2n*D*U+S)/(2n*S));
        const z=D*L-P*S,w=D*U-P*S;
        if (abs(z)*(H+1n)<=S && abs(w)*(H+1n)<=S) brute.add(P+'/'+D);
        else assert(z*w>0n && min(abs(z),abs(w))*(H+1n)>S);
      }
      assert.deepEqual(seen,brute);
    }
  }
}
fs.writeFileSync(path.join(__dirname,'witnesses.csv'), rows.join('\n')+'\n');
console.log('Certified witness rows:',rows.length-1);
