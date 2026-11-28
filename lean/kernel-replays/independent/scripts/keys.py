import json,sys,collections
c=collections.Counter()
names={}
decl=[]
for line in open(sys.argv[1],encoding='utf8'):
    o=json.loads(line)
    k=[x for x in o if x not in ('in','ie','il')]
    c[k[0] if k else '?']+=1
    if 'in' in o:
        s=o.get('str') or o.get('num')
        if 'str' in o: names[o['in']]=(o['str']['pre'],o['str']['str'])
    for key in ('thm','def','axiom','opaque','quot','inductive','defn','ctor','rec'):
        if key in o: decl.append((key,o[key]))
print(c.most_common(30))
def nm(i):
    out=[]
    while i and i in names:
        p,s=names[i]; out.append(s); i=p
    return '.'.join(reversed(out))
want=[w for w in sys.argv[2:]]
found=set()
axioms=[]
for key,d in decl:
    n=d.get('name') if isinstance(d,dict) else None
    if isinstance(n,int):
        s=nm(n)
        if s in want: found.add(s)
        if key=='axiom': axioms.append(s)
print('targets found:',sorted(found)); print('missing:',sorted(set(want)-found)); print('axioms in export:',axioms)
