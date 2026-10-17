#!/usr/bin/env python3
"""Validate complete compiler print-axiom output; never invokes Lean."""
import pathlib,re,sys
root=pathlib.Path(__file__).resolve().parents[1]
t=pathlib.Path(sys.argv[1]).read_text()
seen={}; allowed={'propext','Quot.sound','Classical.choice'}
for m in re.finditer(r"'([^\n]+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",t,re.S):
    name=m[1]; axioms=set(x.strip() for x in (m[2] or '').split(',') if x.strip())
    assert axioms<=allowed, (name,axioms-allowed)
    if name in seen: assert seen[name]==axioms,(name,'inconsistent axiom report')
    seen[name]=axioms
expected=set((root/'EXPECTED-AXIOMS.txt').read_text().splitlines())
assert expected<=seen.keys(), ('missing axiom output',sorted(expected-seen.keys())[:20])
print('AXIOMS_PASS',len(expected),'declarations; allowed',','.join(sorted(set().union(*seen.values()))))
