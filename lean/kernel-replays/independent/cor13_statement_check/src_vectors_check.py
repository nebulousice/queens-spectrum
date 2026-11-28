"""Source eigenvectors (1-indexed, as transcribed from the arXiv renderings) vs Corollary 13 span."""
import sys
sys.path.insert(0, '.')
from cor13_check import adj, rank, matvec, family_vec
def run(lo,hi):
    ok=True
    for n in range(lo,hi+1):
        sq,idx,A=adj(n); N2=n*n; lam=n-4
        B=[[A[a][b]-(lam if a==b else 0) for b in range(N2)] for a in range(N2)]
        def vec(f): return [f(i+1,j+1) for (i,j) in sq]   # 1-indexed source coordinates
        Y=[vec(lambda p,q,i=i:(q==i)+(q==n+1-i)-(p==i)-(p==n+1-i)) for i in range(1,(n+1)//2+1)]
        Z=[vec(lambda p,q:(p-q==0)-(p+q==n+1))]
        F=[vec(lambda p,q,l=l:(1 if q in (l,n+1-l) else 0)-(1 if p in (l,n+1-l) else 0)) for l in range(1,n+1)]
        k=(n+1)//2
        E=[vec(lambda p,q:(k if p==q else 0)-(k if p+q==n+1 else 0))]
        gens=[family_vec(n,sq,[1 if t in (s,n-1-s) else 0 for t in range(n)],0) for s in range((n+1)//2)]
        if n%2: gens.append(family_vec(n,sq,[0]*n,1))
        rg=rank(gens,N2)
        for name,S in (('Y',Y),('F',F)) + ((('Z',Z),('E',E)) if n%2 else ()):
            ev=all(all(x==0 for x in matvec(B,v)) for v in S)
            inspan=rank(gens+S,N2)==rg
            print(f"n={n} {name}: eigenvectors={ev} in_Cor13_span={inspan} rank={rank(S,N2)}"); ok&=ev and inspan
        src = Y+(Z if n%2 else []); src2=F+(E if n%2 else [])
        r1,r2=rank(src,N2),rank(src2,N2)
        print(f"n={n} rank(Y+Z)={r1} rank(F+E)={r2} rank(Cor13 family)={rg} {'OK' if r1==r2==rg else 'FAIL'}"); ok&=r1==r2==rg
    print("SOURCE VECTORS CHECK:","ALL PASS" if ok else "FAILURE")
run(4,10)
