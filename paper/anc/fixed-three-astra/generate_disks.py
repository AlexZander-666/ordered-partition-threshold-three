"""Propose disks for the independent rational verifier. Requires mpmath."""
import json, math
from fractions import Fraction as F
import mpmath as mp
from pathlib import Path

def point(x):
    return round(float(x)*10**10)
out=[]
def attempt(lo,hi):
    a,b=float(lo),float(hi)
    q1,q2=1-b**3/6,1-a**3/6
    q=(q1+q2)/2; dq=(q2-q1)/2
    G=lambda z:1-2*q-z-z*z/2+q*mp.exp(z)
    if a>1.181:
        c=1.08+0j;radius=.44;degree=2
    else:
        e=(a+b)/2; w=complex(.5,math.sqrt(3)/2)
        try: c=complex(mp.findroot(G,(e*w,e*w*(1.05+.01j))))
        except ValueError:return False
        if c.imag<0:c=c.conjugate()
        if abs(c.imag)<.000001:return False
        degree=1
        v=float(-mp.findroot(G,(-.9*e,-1.7*e)))
        radius=(.22 if b<.3 else .65)*min((math.sqrt(3)*c.real-c.imag)/2,c.imag,v-abs(c),2-abs(c))
    if radius<=0:return False
    A=(math.ceil((abs(c)+radius)*10**9)+1)/1e9
    if A>=2 or min(float((1-2*qq+A-A*A/2+qq*mp.exp(-A))) for qq in [q1,q2])<0:return False
    c=complex(point(c.real)/1e10,point(c.imag)/1e10)
    d=point(radius)/1e10
    L=abs(complex(G(c)))+dq*(2+math.exp(c.real+d))
    g1=q*complex(mp.exp(c))-1-c
    g2=q*complex(mp.exp(c))-1
    if degree==1:
        margin=abs(g1)*d-L-(abs(g2)+q*math.exp(c.real+d)*d)*d*d/2
    else:
        margin=abs(g2)*d*d/2-L-abs(g1)*d-q*math.exp(c.real+d)*d**3/6
    if margin<2e-13:return False
    vl,vr=0.,2.
    for _ in range(48):
        vm=(vl+vr)/2
        if 1-2*q2+vm-vm*vm/2+q2*math.exp(-vm)>0:
            vl=vm
        else:
            vr=vm
    Vint=math.floor((vl-1e-9)*1e8)
    out.append([str(lo),str(hi),degree,point(c.real),point(c.imag),point(d),round(A*1e9),Vint])
    return True

def build(a,b,depth=0):
    if attempt(a,b):return
    if depth>=27:raise ValueError((a,b))
    m=(a+b)/2
    build(a,m,depth+1);build(m,b,depth+1)
build(F(1,32),F(61,50))
Path(__file__).with_name('dominance-disks.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
print(len(out),'cells;',sum(r[2]==2 for r in out),'double disks')
