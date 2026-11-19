"""Bounded checks from the original 27-state construction, specialized to its published machine."""


from functools import lru_cache

from check_machine import Configuration, laver_table


def certified_quotient(rows, groups):
    target = {s: group[0] for group in groups for s in group}
    assert len(target) == len(rows) and set(target) == set(rows)
    target["HALT"] = "HALT"
    result = {}
    for group in groups:
        new = [".", "."]
        for s in group:
            for bit, transition in enumerate(rows[s]):
                if transition != ".":
                    edge = transition[:2] + target[transition[2:]]
                    if new[bit] != "." and edge != new[bit]:
                        raise ValueError((group, bit, new[bit], edge))
                    new[bit] = edge
        result[group[0]] = new
    return result, target


def geometry(a,b,B,C,A=0):
    twice=b-a-B-C
    if twice%2:return
    cut=twice//2
    extra=a+C-5-A-B-cut
    if extra%2:return
    return cut,extra//2


def bits(text, start=0):
    return {start + i for i, bit in enumerate(text) if bit == "1"}


def words(*lengths):
    return "0".join("1" * k for k in lengths)


def local_cases(rows,cfg):
    reverse=True
    l,_=geometry(*[cfg[k] for k in ("a","b","B","C")],cfg.get("A",0))
    fence=l+1
    count=0
    for p,high in ((1,False),(2,False),(2,True)):
        split=(p==1 if reverse else p==2) and not high
        hi=max(p,fence) if split else p
        for guard in ((0,1) if not high and (reverse or p==1) else (1,)):
            initial=set(range(p+int(high)))
            initial.update(range(p+1,hi+1))
            if guard:initial.add(-2)
            def local(st,h,tape):
                trace=[]
                for _ in range(80):
                    trace.append((st,h,frozenset(tape)))
                    if h < -2 or h > hi or st not in rows:break
                    edge=rows[st][int(h in tape)]
                    if edge==".":break
                    if edge[0]=="1":tape.add(h)
                    else:tape.discard(h)
                    h+=1 if edge[1]=="R" else -1;st=edge[2:]
                return set(trace)
            path=local("Q24",-1,initial.copy())
            if high:
                normal=local("Q10",int(cfg.get("zero_guard",False)),initial|{-1})
                # Meeting in a numerical state suffices for all possible continuations.
                assert any(s in {"Q10","Q11","Q12","Q13","Q15"} for s,h,tape in path&normal)
            else:
                expected=set(range(-1,hi+1))
                if guard:expected.add(-2)
                if split:expected.remove(fence)
                if not split:
                    direct=reverse or cfg.get("tag")
                    name=("Q28" if cfg["B"] else "Q23") if direct else "GSCAN"
                    far=p+int(not cfg["B"]) if reverse else p+int(not cfg.get("tag"))
                    assert any(s==name and -1<=h<=far and x==expected
                               for s,h,x in path)
                else:
                    def legal(s,h):
                        if cfg["C"]:
                            return s==("Q28" if h<fence else "Q27")
                        return s=="Q23" and h<=fence
                    assert any(-2<=h<=hi+1 and legal(s,h) and x==expected for s,h,x in path)
            count+=1
    return count


def shape(c):
    right=max(c.ones)
    return c.state,c.head-right,frozenset(v-right for v in c.ones)


def raw_copy(rows):
    """Stop immediately before the local classifier and check the complete tape."""
    cells={s:tuple((int(e[0]),1 if e[1]=="R" else -1,e[2:]) if e!="." else
                   (i,1,"UNUSED") for i,e in enumerate(row)) for s,row in rows.items()}
    comparisons=0
    for source in range(19):
        for centre in range(6):
            for right in range(4):
                before=bits(words(source,centre,right)+"01101")
                for seed in (0,1):
                    c=Configuration("Q28" if seed else "Q23",source-1 if seed else 0,before.copy())
                    for _ in range(source+2):
                        c.advance(cells,until={"Q24"},budget=4000)
                        if c.head not in c.ones:break
                    x=-source-1-seed
                    tail=bits(words(source+seed,centre+1,source+right)+"01101",x)
                    assert (c.state,c.head,c.ones)==("Q24",-1,tail),(source,centre,right,seed)
                    comparisons+=1
    return comparisons


def trial_trace(table,ns,N,cfg):
    p=N-cfg["a"];q=N-cfg["b"]+1;D=p+1-cfg["C"]
    c=Configuration(ns["Q7"],0,bits(words(p,q,D)))
    c.advance(table,until={ns["Q10"]},budget=p+8)
    want={}
    for _ in range(31):
        if c.state=="HALT" or c.ones==set():break
        want[shape(c)]=c.steps
        c.advance(table,until=set(table),budget=1)
    return want


def seek(c,table,ns,N,cfg,budget):
    ref=trial_trace(table,ns,N,cfg)
    watched={k[0] for k in ref}
    stop=c.steps+budget
    while c.steps<stop:
        c.advance(table,until=watched,budget=stop-c.steps)
        if c.state=="HALT":raise AssertionError(("unexpected halt",N,c.steps))
        if c.ones and shape(c) in ref:return c.steps
    raise AssertionError(("no complete reference configuration",N))


def zero_rows(w):
    result=[list(range(-1,w))]
    for p in range(1,w):
        row=[None]*(w+1)
        for q in range(w,1,-1):
            if (q-1)&(q-2)==0 or q==w:
                # At q=w the dyadic guard would be at w+1. In that case
                # its zero is followed by H(0,p)=p-1.
                row[q]=0 if (q-1)&(q-2)==0 else p-1
            else:
                z=row[q+1]
                assert 0<=z<p and (z==0 or p>=2)
                row[q]=result[z][p]
        result.append(row)
    return result


@lru_cache(maxsize=10000)
def work(p,q):
    if not p:return q-1,1
    if (q-1)&(q-2)==0:return 0,1
    z,inner=work(p,q+1)
    v,outer=work(z,p)
    return v,1+inner+outer


def finite_tests():
    cells=wrong=below=0
    for n in range(1,9):
        w=1<<n;table=laver_table(n);v=zero_rows(w)
        for p in range(1,w):
            r=table[w-p]
            period=r.index(w,1)
            for q in range(2,w+1):
                c=1<<(q-2).bit_length()
                shift=(c+1-q-1)%w+1
                actual=w-r[shift];ordinary=w-r[w-q+1]
                assert v[p][q]==actual and (actual==ordinary)==(c%period==0)
                cells+=1;below+=q<p;wrong+=actual!=ordinary
    return cells,below,wrong


def products(tab,ns,cfg):
    counts=[0,0];steps=0
    for n in range(1,6):
        size=1<<n
        v=zero_rows(size)
        for p in range(min(10,size)):
            for q in range(2 if p else 1,min(size,18)+1):
                value=v[p][q]
                for D in (4,7,10):
                    first=p+q+2
                    c=Configuration(ns["Q7"],0,bits(words(p,q,D)))
                    if value:
                        c.advance(tab,budget=1500000)
                        h=(1<<(D-1).bit_length())-(D-1)
                        marks=set(range(first-1-value,first))|{first,first+h}
                        if cfg["marked"]:marks.add(first+D)
                        assert (c.state,c.head,c.ones)==("HALT",first+D+2,marks),(p,q,D,value)
                    else:
                        for _ in range(200000):
                            c.advance(tab,until={ns["Q9"]},budget=1500000-c.steps)
                            if c.state=="HALT" or c.head==first+D+1 and c.head not in c.ones:break
                        marks=set(range(first+1,first+D+int(cfg["q8"])))
                        assert (c.state,c.head,c.ones)==(ns["Q9"],first+D+1,marks),(p,q,D,value)
                    steps=max(steps,c.steps);counts[bool(value)]+=1
    return counts,steps


def bounded_machine_tests(raw,start,cfg,tab,ns):
    l,_=geometry(*[cfg[k] for k in ("a","b","B","C")])
    N0=5+cfg["B"]+cfg["C"]+l+cfg["a"]
    c=Configuration(ns[start],0,set())
    blank=[(n,seek(c,tab,ns,n,cfg,1500000)) for n in (N0,N0*2)]
    for N in (10,12,16,20,32,48,64):
        v=N-cfg["a"]-cfg["C"]
        c=Configuration(ns["Q7"],0,set(range(v)))
        seek(c,tab,ns,2*N,cfg,2000000)
    early={}
    for N in (N0,2*N0):
        w=1<<(N-1).bit_length()
        early[N]=zero_rows(w)[N-cfg["a"]][N-cfg["b"]+1]
    assert set(early.values())=={0}
    successes=[]
    for size in range(1,14):
        n=N0+2*size
        v=zero_rows(1<<(n-1).bit_length())[n-cfg["a"]][n-cfg["b"]+1]
        predicted,calls=work(n-cfg["a"],n-cfg["b"]+1)
        assert v==predicted
        if not v or calls>1400:continue
        u=Configuration(ns["Q23"],0,set(range(size))|{size+1})
        u.advance(tab,budget=2000000)
        assert u.state=="HALT" and len(u.ones)==v+3+int(cfg["marked"])
        successes.append((size,v,u.steps,len(u.ones)))
        if len(successes)>=3:break
    return dict(states=len(tab),initial=N0,raw_copies=raw_copy(raw),centre=local_cases(raw,cfg),
                early=early,blank=blank,restarts=7,products=products(tab,ns,cfg),
                seeded_successes=successes)
