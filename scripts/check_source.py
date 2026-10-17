#!/usr/bin/env python3
"""Static source hygiene and registered-import/manifest audit. Never shells out."""
import csv, pathlib, re, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
def mask(t):
    out=list(t); i=0
    while i<len(t):
        if t.startswith('/-',i):
            j=i+2; depth=1
            while j<len(t) and depth:
                if t.startswith('/-',j): depth+=1; j+=2
                elif t.startswith('-/',j): depth-=1; j+=2
                else: j+=1
            if depth: raise ValueError('unclosed comment')
        elif t.startswith('--',i):
            j=t.find('\n',i); j=len(t) if j<0 else j
        elif t[i]=='"':
            j=i+1
            while j<len(t):
                if t[j]=='\\': j+=2
                elif t[j]=='"': j+=1; break
                else: j+=1
        else: i+=1; continue
        for k in range(i,j):
            if out[k]!='\n': out[k]=' '
        i=j
    return ''.join(out)
def validate_code(t):
    code=mask(t)
    bad=re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe|initialize|run_cmd|elab|macro|syntax|implemented_by|extern)\b|#(?:eval|reduce)',code)
    if bad: raise ValueError('forbidden token '+bad.group())
    if '\t' in t: raise ValueError('tab')
    if '[event:' in t or '[imported:' in t: raise ValueError('unexpected ledger/imported hypothesis')
    for match in re.finditer(r'(?m)^notation\b',code): raise ValueError('nonlocal notation')
    for a in re.findall(r'@\[([^]]+)\]',code):
        if a.strip() not in {'simp','instance','eqns','reducible'}: raise ValueError('unregistered attribute '+a)
    return code

def validate_binders(t, code):
    count=0
    tags=r"\[(?:definition|standing)\]"
    for d in re.finditer(r"^(?:@\[[^\n]*?\]\s*)*(?:(?:noncomputable|private|protected)\s+)*(def|abbrev|theorem|lemma|instance|variable)\b",code,re.M):
        i=d.end(); stack=[]; outer=None
        while i<len(code):
            c=code[i]
            if not stack and ((c==":" and d[1]!="variable") or code.startswith(":=",i) or code.startswith("where",i) or (c=="\n" and d[1]=="variable")): break
            if c in "([{":
                if not stack: outer=i
                stack.append(c)
            elif c in ")] }".replace(" ","") and stack:
                stack.pop()
                if not stack:
                    group=code[outer:i+1]
                    if ":" in group or group.startswith("["):
                        end=i+1
                        while end<len(code) and code[end] in " ": end+=1
                        full=t[outer:end]
                        last=t[max(outer,t.rfind("\n",outer,i+1)+1):end]
                        assert len(re.findall(tags,full))==1 and len(re.findall(tags,last))==1, ("binder provenance",t[:outer].count("\n")+1,full)
                        count+=1
                    outer=None
            i+=1
    return count

def main():
    rows=list(csv.DictReader((ROOT/'MODULES.tsv').open(),delimiter='\t'))
    registered=set((r['site'],r['registered_import']) for r in csv.DictReader((ROOT/'IMPORTS.tsv').open(),delimiter='\t'))
    actual=set(); listed={r['file'] for r in rows}
    supported={str(f.relative_to(ROOT)) for f in (ROOT/'RMTFoundations').rglob('*.lean')}|{'RMTFoundations.lean'}
    assert listed==supported, 'module manifest drift'
    printed=[]; binder_count=0
    for f in sorted([ROOT/'RMTFoundations.lean',ROOT/'Challenge.lean',ROOT/'Solution.lean'] + [f for d in ['RMTFoundations','Tests','examples','Challenge'] for f in (ROOT/d).rglob('*.lean')]):
        if '.lake' in f.parts: continue
        assert not f.is_symlink(), str(f)+' is a symlink'
        rel=str(f.relative_to(ROOT)); t=f.read_text(); code=validate_code(t)
        binder_count+=validate_binders(t,code)
        for m in re.findall(r'^import (\S+)',code,re.M):
            actual.add((rel,m)); assert m.startswith('Mathlib') or m.startswith(('RMTFoundations','Tests','Challenge')), m
        ns=re.findall(r'^namespace (\S+)',code,re.M)
        assert len(ns)<=1, rel+' is not flat'
        lines=code.splitlines(); prints=[i for i,l in enumerate(lines) if l.startswith('#print axioms ')]
        if ns:
            assert prints, rel+' lacks final axiom block'
            assert all(not l.strip() or l.startswith('#print axioms ') for l in lines[min(prints):]), rel+' nonfinal axiom block'
            printed += re.findall(r'^#print axioms (\S+)',code,re.M)
    assert actual==registered, 'import registration drift'
    # Scanner negative and positive controls, no Lean invocation.
    for sample in ['theorem t : True := by sorry','axiom t : True','theorem t : True := by native_decide','macro "x" : term => `(True)']:
        try: validate_code(sample)
        except ValueError: pass
        else: raise AssertionError('negative source control accepted')
    validate_code('/- Nested /- sorry -/ prose -/ theorem t : True := by trivial')
    for sample in ['theorem t (h : True) : True := h',
                   'theorem t (h : True /- [standing] [definition] -/) : True := h',
                   'theorem t (h : True /- [standing] -/\n) : True := h']:
        try: validate_binders(sample,mask(sample))
        except AssertionError: pass
        else: raise AssertionError('negative binder control accepted')
    validate_binders('theorem t (h : True /- [standing] -/) : True := h',mask('theorem t (h : True /- [standing] -/) : True := h'))
    (ROOT/'EXPECTED-AXIOMS.txt').write_text('\n'.join(sorted(set(printed)))+'\n') if '--write' in sys.argv else None
    expected=(ROOT/'EXPECTED-AXIOMS.txt').read_text().splitlines()
    assert expected==sorted(set(printed)), 'axiom manifest drift'
    print('SOURCE_PASS',len(rows),'production modules;',len(set(printed)),'printed declarations;',binder_count,'tagged binders; no ledger discharges')
if __name__=='__main__': main()
