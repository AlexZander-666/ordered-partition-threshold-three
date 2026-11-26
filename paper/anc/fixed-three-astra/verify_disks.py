"""Verify all disk, sector, and modulus tests with Fraction and integer square roots."""
import json
from fractions import Fraction as F
from math import factorial, isqrt
from pathlib import Path

S=10**23
def interval_norm(z):
    v=sum(x*x for x in z)
    lo=F(isqrt(v.numerator*S*S//v.denominator),S)
    return lo,lo+F(1,S)
def plus(z,w):return tuple(x+y for x,y in zip(z,w))
def scale(z,a):return tuple(a*x for x in z)
def prod(z,w):return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def exp_approx(z):
    assert sum(x*x for x in z)<=4
    term=(F(1),F(0)); value=term
    for i in range(1,37):
        term=scale(prod(term,z),F(1,i)); value=plus(value,term)
    return value
# exp(2)<8 follows by summing through degree 4 and using ratio 1/3 on the tail.
err=F(8*2**37,factorial(37))
def sup_exp(x):
    return exp_approx((x,F(0)))[0]+err
records=json.loads(Path(__file__).with_name('dominance-disks.json').read_text())
endpoint=F(1,32); counts={1:0,2:0}
worst=F(0)
for a,b,num,i,j,r,R,Vint in records:
    a,b=F(a),F(b); assert a==endpoint and a<b; endpoint=b
    lo,hi=1-b**3/6,1-a**3/6
    q=(lo+hi)/2; dq=(hi-lo)/2
    c=F(i,10**10),F(j,10**10); d=F(r,10**10); A=F(R,10**9)
    assert 0<d and interval_norm(c)[1]+d<A<2
    # Positive real part, and inside arg z < pi/3; sqrt(3)>1.732.
    assert c[0]>d and F(1732,1000)*c[0]-abs(c[1])>2*d
    if num==1: assert c[1]>d
    else: assert num==2 and c[1]==0
    em=exp_approx((-A,F(0)))[0]-err
    for qq in [lo,hi]:
        assert 1-2*qq+A-A*A/2+qq*em>0
    ec=scale(exp_approx(c),q)
    ecd=q*sup_exp(c[0]+d)
    g=plus(plus(plus((1-2*q,F(0)),scale(c,-1)),scale(prod(c,c),-F(1,2))),ec)
    g1=plus(plus(ec,(F(-1),F(0))),scale(c,-1))
    g2=plus(ec,(F(-1),F(0)))
    L=interval_norm(g)[1]+q*err+dq*(2+sup_exp(c[0]+d))
    if num==1:
        assert (interval_norm(g1)[0]-q*err)*d>L+(interval_norm(g2)[1]+q*err+ecd*d)*d*d/2
    else:
        assert (interval_norm(g2)[0]-q*err)*d*d/2>L+(interval_norm(g1)[1]+q*err)*d+ecd*d**3/6
    V=F(Vint,10**8)
    assert A<V<2
    em=exp_approx((-V,F(0)))[0]-err
    assert min(1-2*qq+V-V**2/2+qq*em for qq in [lo,hi])>0
    # Sector distance in each of the unit normals to arg z=+/- pi/3.
    rt=F(173205,100000)
    H=min(F(1),(rt*c[0]-c[1]-2*d)*(rt*c[0]+c[1]-2*d)/A**2)
    assert 0<H and V**2/2-2*(1-lo)>0
    g=F(12)
    if c[1]>d:
        g=min(g,(A**2/2+2*(1-lo))*A/(c[1]-d))
    # For n >= 240 this controls the normalized third residue + contour,
    # divided by sin(h*theta), simultaneously for h=1,2,3.
    ratio=(g/(2*(V**2/2-2*(1-lo)))*(A/V)**241 + 18*g*(A/2)**241)/H
    assert ratio<F(2,5)
    worst=max(worst,ratio)
    counts[num]+=1
assert endpoint==F(61,50)
print('PASS exact rational Rouché, sector and strict modulus tests',counts,'cover [1/32,61/50]')
print("PASS all three shifts for every old n >= 240; maximum upper bound rounded up in millionths", -((-worst.numerator*10**6)//worst.denominator))
