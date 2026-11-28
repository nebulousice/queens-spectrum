import json,sys
src,dst,target=sys.argv[1],sys.argv[2],sys.argv[3]
names={}
lines=open(src,encoding='utf8').read().splitlines()
def nm(i):
    out=[]
    while i and i in names:
        p,s=names[i]; out.append(s); i=p
    return '.'.join(reversed(out))
prev_thm=None; done=False
for k,l in enumerate(lines):
    o=json.loads(l)
    if 'in' in o and 'str' in o: names[o['in']]=(o['str']['pre'],o['str']['str'])
    if 'thm' in o:
        t=o['thm']
        if nm(t['name'])==target and prev_thm is not None:
            print('before:',json.dumps(t)[:300]); 
            t['value']=prev_thm['value']; print('after value <- value of',nm(prev_thm['name']))
            lines[k]=json.dumps(o,separators=(',',':')); done=True; break
        if not t.get('levelParams'): prev_thm=t
assert done
open(dst,'w',encoding='utf8',newline='\n').write('\n'.join(lines)+'\n')
