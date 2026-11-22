from fractions import Fraction
from math import cos, log, pi


def residue_count(left, right, residue, modulus):
    return (right-residue)//modulus - (left-residue)//modulus


def audit_residues():
    starts = (-10**24+39, -10**12-1, -301, -1, 0, 22, 10**12+17, 10**24+91)
    checks = 0
    for left in starts:
        for size in (1, 2, 41, 1000, 10**8+47):
            for q in (2, 14, 97, 210, 10007, 10**11+19):
                for residue in (0, 1, q-1):
                    right = left+size
                    hits = residue_count(left,right,residue,q)
                    assert abs(q*hits-size)<q
                    if size <= 1000:
                        assert hits==sum(n%q==residue for n in range(left+1,right+1))
                    checks += 1
    print(f"{checks} exact residue-window checks, with starts of size up to 10^24.")


def audit_peak():
    for C in (Fraction(1,13), Fraction(5,8), Fraction(1), Fraction(101,7)):
        for j in range(201):
            v = C*Fraction(j,200)
            gap = Fraction(4,27)*C**3-v*(C-v)**2
            assert gap==(v-C/3)**2*(4*C/3-v) and gap>0
        a = C/3
        assert a*(C-a)**2==Fraction(4,27)*C**3
    # At the same width, killing either endpoint has a discrete principal eigenvalue.
    K = pi*pi/8
    rates = []
    for W in (8,16,32,64,128):
        rate = -W*W*log(cos(pi/(2*W)))
        assert K<rate<1.01*K
        rates.append(rate)
    assert all(a>b for a,b in zip(rates,rates[1:]))
    threshold=(81*pi*pi/(32*log(3/2)))**(1/3)
    assert 3.94<threshold<3.96
    print("804 strict cubic-gap checks and four exact equality checks.")
    print("Discrete sine-kernel scaled rates:", ", ".join(f"{v:.8f}" for v in rates))
    print(f"Full-alphabet p=1/2 example, C_* = {threshold:.8f}.")


if __name__=="__main__":
    audit_residues()
    audit_peak()

