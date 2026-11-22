from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt, prod

from golden_finite_spectrum import Quadratic
from quadratic_phase_certificate import normal_cycle


def orbit_cycles(delta, leading, middle):
    root = Quadratic(Fraction(-middle, 2*leading), Fraction(1, 2*leading), delta)
    return {normal_cycle(root), normal_cycle(root.conjugate())}


def selected_primes(delta, orbit, limit):
    selected = {}
    for p in range(3, limit+1, 2):
        if gcd(p, 2*delta)!=1 or any(p%d==0 for d in range(2,isqrt(p)+1)):
            continue
        for r in range(p):
            if (r*r-delta)%p:
                continue
            m = r if r%2==delta%2 else r+p
            if orbit_cycles(delta,p,m).intersection(orbit):
                selected[p] = r
                break
    return selected


def verify_residues(delta, orbit, selected):
    for p,r in selected.items():
        r = r if r%2==delta%2 else r+p
        for j in range(-8,9):
            m = r+2*p*j
            norm = (m*m-delta)//4
            assert norm%p==0 and gcd(p,m,norm//p)==1
            assert orbit_cycles(delta,p,m).intersection(orbit)


def moment_check(selected, limit, parity):
    size = len(range(-limit + (-limit-parity)%2, limit+1, 2))

    def count_mod(residue, modulus):
        first = residue
        if first%2 != parity:
            first += modulus
        step = 2*modulus
        return (limit-first)//step - ((-limit-1)-first)//step

    first_probs = {p: Fraction(count_mod(r,p),size) for p,r in selected.items()}
    for p,prob in first_probs.items():
        assert abs(prob-Fraction(1,p))<=Fraction(1,size)
    mean = sum(first_probs.values())
    var = sum(v*(1-v) for v in first_probs.values())
    for p,q in combinations(selected,2):
        rp,rq = selected[p],selected[q]
        residue = rp+p*((rq-rp)*pow(p,-1,q)%q)
        prob = Fraction(count_mod(residue,p*q),size)
        assert abs(prob-Fraction(1,p*q))<=Fraction(1,size)
        var += 2*(prob-first_probs[p]*first_probs[q])
    hits = [sum(m%p==r for p,r in selected.items())
            for m in range(-limit+(-limit-parity)%2,limit+1,2)]
    assert mean == Fraction(sum(hits),size)
    assert var == Fraction(sum(x*x for x in hits),size)-mean*mean
    # The finite joint residue counts also check Bonferroni bounds.
    independent_no_hit = prod(1-Fraction(1,p) for p in selected)
    for order in range(1,5):
        actual_truncation = Fraction(1)
        independent_truncation = Fraction(1)
        for j in range(1,order+1):
            for group in combinations(selected,j):
                residue,modulus = 0,1
                for p in group:
                    residue += modulus*((selected[p]-residue)*pow(modulus,-1,p)%p)
                    modulus *= p
                actual_truncation += (-1)**j*Fraction(count_mod(residue,modulus),size)
                independent_truncation += (-1)**j*Fraction(1,modulus)
        actual_no_hit = Fraction(sum(h==0 for h in hits),size)
        if order%2==0:
            assert actual_no_hit<=actual_truncation
            assert independent_no_hit<=independent_truncation
        else:
            assert actual_no_hit>=actual_truncation
            assert independent_no_hit>=independent_truncation
    return size,sum(h>0 for h in hits)


def trace_admitted(delta, orbit, m):
    norm = (m*m-delta)//4
    c = abs(norm)
    for a in range(1,isqrt(c)+1):
        if c%a:
            continue
        for d in {a,c//a}:
            if gcd(d,m,norm//d)==1 and orbit_cycles(delta,d,m).intersection(orbit):
                return True
    return False


def common_count_example():
    left = orbit_cycles(60,3,0)
    right = orbit_cycles(240,3,0)
    assert not trace_admitted(60,left,4)
    admitted = 0
    candidates = list(range(-300,301,2))
    for u in candidates:
        admitted += trace_admitted(60,left,u) and trace_admitted(240,right,2*u)
        assert Fraction(u,2)==Fraction(2*u,4)
    assert 0 < admitted < len(candidates)
    print(f"Cross-order example: {admitted} shared values among {len(candidates)} candidate traces.")


def cube_floor(n):
    lo,hi=0,n+1
    while hi-lo>1:
        m=(lo+hi)//2
        if m**3<=n:
            lo=m
        else:
            hi=m
    return lo


def corridor_example(max_steps):
    # For p=1/2, z=2J_m-m. At C=1 the corridor uses |z|^3<=8m.
    symbolic={0:1}
    labelled={0:1}
    for n in range(1,max_steps+1):
        width=cube_floor(8*n)
        new_symbolic={}
        new_labelled={}
        for z,unweighted in symbolic.items():
            for step,multiplicity in ((-1,3),(1,2)):
                new_z=z+step
                if abs(new_z)<=width:
                    new_symbolic[new_z]=new_symbolic.get(new_z,0)+unweighted
                    new_labelled[new_z]=new_labelled.get(new_z,0)+labelled[z]*multiplicity
        symbolic,labelled=new_symbolic,new_labelled
        for z,count in symbolic.items():
            assert (n+z)%2==0
            j=(n+z)//2
            assert labelled[z]==count*2**j*3**(n-j)
    assert symbolic
    print(f"Exact tilted/uniform corridor count identities at all depths through {max_steps}.")


if __name__=="__main__":
    for delta in (60,240):
        orbit=orbit_cycles(delta,3,0)
        selected=selected_primes(delta,orbit,180)
        assert len(selected)>=3
        verify_residues(delta,orbit,selected)
        size,covered=moment_check(selected,12000,delta%2)
        print(f"Delta={delta}: {len(selected)} split-prime residues, {covered}/{size} finite hits.")
    common_count_example()
    corridor_example(640)

