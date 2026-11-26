"""Rational endpoints for the hand proof in the merging three-root regime."""
from fractions import Fraction as Q
from math import factorial
def d(s):return Q(str(s))
def expo_lo(x,k):return sum(x**i/factorial(i) for i in range(k+1))
def expo_hi(x,k):
    return expo_lo(x,k)+x**(k+1)/factorial(k+1)/(1-x/(k+2))
eps=Q(1,32); a=Q(5,12)
# J(1)<0<J(11/10), minimal q covered by the rational archive.
assert expo_lo(Q(1),5)>Q(8,3)
assert (1+d(1.1))>(1-d(1.1)**2/4)*expo_hi(d(1.1),10)
assert Q(279,400)>1-Q(61,50)**3/6
# Rouché comparison: independent upper bounds for the Taylor remainders.
assert a+eps<d(.45) and 1+d(.45)*eps<d(1.02)
assert expo_hi(d(1.02)*eps,5)<d(1.04)
assert d(3.02)*d(.45)**2+(1+d(1.02)**3)*d(.45)+d(1.04)*(d(1.02)**2/2+d(1.02)**5/20)<3
nu=1+(a+eps)*eps
u0=1-(a/2+eps)*eps
assert a/2>(1+a*a/2)*eps
assert ((3*a/2)-(2+a*a/2)*eps)/nu>d(.54) and 3*a/2+2*eps<d(.70)
assert d(1.732)**2<3<d(1.733)**2
assert 5*d(1.732)/24-eps>d(.32)
assert (5*d(1.733)/24+eps)/u0<d(.41)
# For 0<=t<=.05, sin(t)>=t*(1-.05^2/6).
assert d(.42)*(1-d(.05)**2/6)>d(.41)
assert d(.72)*eps<=d(.05) and d(.72)*(1-d(.05)**2/6)>Q(2,3)/u0**2
assert 3*d(.32)-4*d(.41)**3*eps**2>d(.95)
assert (1+2*eps/3)/(2*(1-2*eps/3))<d(.522)
assert expo_lo(d(.81),4)>1/d(.45)
assert 18*eps*(eps/2)**2<Q(1,1000)
assert d(.522)*d(.45)+eps/1000<d(.24)
assert (3*d(.70)+(3*d(.42))**2/2*eps)/d(.95)<Q(5,2)
# theta between pi/3-.42/32 and pi/3, sin theta>.8, sin 2theta>.8.
assert d(1.732)/2*(1-(d(.42)*eps)**2/2)-d(.42)*eps/2>d(.8)
assert d(.24)**2+(d(.24)*Q(5,2)+Q(2,950))**2<1
assert d(.42)*Q(3,2)+(d(.42)+d(1.56))*Q(3,480)<Q(3,4)
assert Q(2,5)**2+Q(4,5)**2<1
print('PASS rational bounds for three small disks, slope and residue bounds, exact-mode cancellation, strip endpoints, and signs')
