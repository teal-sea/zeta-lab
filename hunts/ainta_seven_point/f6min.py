import math, random
S2 = math.sqrt(2.0); K0 = S2*math.sin(1/S2)
def sinc(x): return 1.0 if abs(x) < 1e-12 else math.sin(x)/x
def k(x):
    f = 2*math.pi*x
    return ((sinc((S2-f)/2) + sinc((S2+f)/2))/2)/K0
def w(x): return k(x)**2
C = {s: 2.0/(7-s) for s in range(1,7)}
def F6(g):
    if min(g) < 0: return float('inf')
    v = sum(g)/3000.0
    for s in range(1,7):
        for i in range(7-s):
            v += C[s]*w(sum(g[i:i+s]))
    return v
def nelder_mead(f, x0, step=0.2, iters=4000, tol=1e-13):
    n=len(x0); pts=[list(x0)]
    for i in range(n):
        y=list(x0); y[i]+=step; pts.append(y)
    vals=[f(p) for p in pts]
    for _ in range(iters):
        order=sorted(range(n+1), key=lambda i: vals[i]); pts=[pts[i] for i in order]; vals=[vals[i] for i in order]
        if abs(vals[-1]-vals[0])<tol: break
        c=[sum(p[j] for p in pts[:-1])/n for j in range(n)]
        xr=[c[j]+(c[j]-pts[-1][j]) for j in range(n)]; fr=f(xr)
        if fr<vals[0]:
            xe=[c[j]+2*(c[j]-pts[-1][j]) for j in range(n)]; fe=f(xe)
            pts[-1],vals[-1]=(xe,fe) if fe<fr else (xr,fr)
        elif fr<vals[-2]: pts[-1],vals[-1]=xr,fr
        else:
            xc=[c[j]+0.5*(pts[-1][j]-c[j]) for j in range(n)]; fc=f(xc)
            if fc<vals[-1]: pts[-1],vals[-1]=xc,fc
            else:
                for i in range(1,n+1):
                    pts[i]=[pts[0][j]+0.5*(pts[i][j]-pts[0][j]) for j in range(n)]; vals[i]=f(pts[i])
    i=min(range(n+1), key=lambda i: vals[i]); return pts[i], vals[i]
random.seed(7)
comps=[(0.95,1.20),(1.80,2.35),(2.64,11.2)]
best=[]
for r in range(600):
    x0=[random.uniform(*random.choice(comps)) for _ in range(6)]
    x,v=nelder_mead(F6,x0,step=random.choice([0.05,0.2,0.5]))
    best.append((v,x))
best.sort(key=lambda t:t[0])
print("targets: ainta 19/5000 =",19/5000," gohms 191/50000 =",191/50000)
print("apparent minimum F6 =", repr(best[0][0]))
print("argmin gaps =", [round(g,6) for g in best[0][1]], " sum=",round(sum(best[0][1]),6))
print("--- 8 best distinct local minima ---")
seen=[]
for v,x in best:
    key=tuple(round(g,3) for g in x)
    if any(max(abs(a-b) for a,b in zip(key,s))<0.01 for s in seen): continue
    seen.append(key); print(f"{v:.10f}", [round(g,4) for g in x])
    if len(seen)>=8: break
