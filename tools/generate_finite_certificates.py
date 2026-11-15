#!/usr/bin/env python3
"""Rebuild the three small CNF/LRAT certificates; Lean checks every generated proof.

Run from the repository root with a Lean-distributed CaDiCaL on PATH. The Boolean
rules are translated by four/three-variable lemmas proved separately in Lean.
No correctness of this generator or the SAT solver is assumed by the theorems.
"""
import itertools
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TWO = {
    'Same': ['0000','0011','0110','1001','1100','1111'],
    'ZeroOne': ['0010','0101','1000','1011','1110'],
    'OneZero': ['0001','0100','0111','1010','1101'],
}
EXTRA = {
    'Same': [''.join(t) for t in itertools.product('01', repeat=4) if sum(map(int,t))%2 == 0],
    'ZeroOne': [''.join(t) for t in itertools.product('01', repeat=4) if sum(map(int,t))%2] + ['0101'],
    'OneZero': [''.join(t) for t in itertools.product('01', repeat=4) if sum(map(int,t))%2] + ['1010'],
}
RAW = {k: [''.join(t) for t in itertools.product('01',repeat=3) if ''.join(t) not in banned]
       for k,banned in {'T':['010','101'], 'Cm':['001','100','111'], 'Cp':['000','011','110']}.items()}

def violation(args,bits):
    return ' ∧ '.join(f'({a} = true)' if b=='1' else f'¬ ({a} = true)' for a,b in zip(args,bits))

def pattern(names):
    if len(names)==1:return names[0]
    mid=len(names)//2
    return f'({pattern(names[:mid])} | {pattern(names[mid:])})'

def generate(label, nvars, width, rules, constraints, source, prefix, main_start):
    forbidden = {k:[''.join(t) for t in itertools.product('01',repeat=width) if ''.join(t) not in vals]
                 for k,vals in rules.items()}
    clauses=[]; refs=[]
    for hyp,kind,indices in constraints:
        for j,bits in enumerate(forbidden[kind]):
            clauses.append([-(i+1) if b=='1' else i+1 for i,b in zip(indices,bits)])
            refs.append(f'{hyp}_{j}')
    cnf=f'p cnf {nvars} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses)
    with tempfile.TemporaryDirectory() as d:
        p=Path(d); (p/'input.cnf').write_text(cnf)
        result=subprocess.run(['cadical','--lrat','--no-binary','-q',str(p/'input.cnf'),str(p/'proof.lrat')],capture_output=True,text=True)
        if result.returncode!=20:raise RuntimeError(result.stdout+result.stderr)
        lrat=(p/'proof.lrat').read_text()
    certificate=ROOT/'Hypertournaments'/'FiniteCertificates'/f'{label}.lean'
    certificate.parent.mkdir(exist_ok=True)
    certificate.write_text('import Mathlib.Tactic.Sat.FromLRAT\n\n/-! A propositional LRAT proof. All generated declarations are kernel checked.\nRegenerate with `tools/generate_finite_certificates.py`; no native proof axiom. -/\n\nnamespace Hypertournaments.FiniteCertificates\n\nset_option maxRecDepth 16384\nset_option maxHeartbeats 2000000\n\nlrat_proof '+label+'\n  "'+cnf+'"\n  "'+lrat+'"\n\nend Hypertournaments.FiniteCertificates\n')
    args=list('abcd'[:width]);helpers=[]
    for kind,patterns in forbidden.items():
        terms=['¬ ('+violation(args,bits)+')' for bits in patterns]
        helpers.append(f'private theorem {prefix}{kind}_cnf : ∀ '+ ' '.join(args)+' : Bool,\n    '+prefix+kind+' '+' '.join(args)+' '+('= true ' if width==3 else '')+'→\n    '+' ∧\n    '.join(f'({t})' for t in terms)+' := by\n  intro '+ ' '.join(args)+'\n  unfold '+prefix+kind+'\n  '+ ' <;> '.join('cases '+a for a in args)+' <;> '+('decide +kernel' if width==3 else 'simp')+'\n')
    lines=[]
    if width==3:
        lines += ['  intro b htop houter', '  simp only [rawTopOk, rawOuterOk, Bool.and_eq_true, and_assoc] at htop houter',
                  '  rcases htop with ⟨'+', '.join(h for h,k,inds in constraints[:10])+'⟩',
                  '  rcases houter with ⟨'+', '.join(h for h,k,inds in constraints[10:])+'⟩']
    for hyp,kind,indices in constraints:
        names=[f'{hyp}_{j}' for j in range(len(forbidden[kind]))]
        args2=' '.join(f'({"b" if width==3 else "x"} {i})' for i in indices)
        lines += ['  obtain ⟨'+', '.join(names)+f'⟩ := ({prefix}{kind}_cnf {args2}) {hyp}']
    vals=' '.join(f'({"b" if width==3 else "x"} {i} = true)' for i in range(nvars))
    lines += [f'  rcases FiniteCertificates.{label} {vals} with', '    '+pattern([f'h{i}' for i in range(len(refs))])]
    lines += [f'  · exact {ref} h{i}' for i,ref in enumerate(refs)]
    text=source.read_text()
    text=re.sub(r'^import Hypertournaments.(?:Tactic.KernelBVDecide|FiniteCertificates.'+label+r')\n','',text,flags=re.M)
    helper_start=text.find('private theorem '+prefix)
    if helper_start >= 0:
        text=text[:helper_start]+text[text.index(main_start):]
    text=f'import Hypertournaments.FiniteCertificates.{label}\n'+text
    text=text[:text.index(main_start)]+ '\n'.join(helpers)+'\n'+text[text.index(main_start):]
    proof_start=text.index(' := by\n',text.index(main_start)) + len(' := by\n')
    text=text[:proof_start]+'\n'.join(lines)+'\n\nend Hypertournaments\n'
    text=text.replace('maxRecDepth 131072','maxRecDepth 16384')
    source.write_text(text)
    print(label, len(clauses),len(lrat.splitlines()),'LRAT lines')

for label,prefix,rules,n in [('SeedFiveTwo','seed5TwoRule',TWO,35),('SeedFiveExtra','seed5ExtraRule',EXTRA,20)]:
    source=ROOT/'Hypertournaments'/f'{label}Boolean.lean';text=source.read_text()
    constraints=[(h,k,list(map(int,inds))) for h,k,*inds in re.findall(r'\((h\d+) : '+prefix+r'(\w+) \(x (\d+)\) \(x (\d+)\) \(x (\d+)\) \(x (\d+)\)\)',text)]
    generate(label,n,4,rules,constraints,source,prefix,'/-- '+('Unconditional finite' if label=='SeedFiveTwo' else 'A finite certificate'))
source=ROOT/'Hypertournaments'/'SeedFourForbidOneRawLogic.lean';text=source.read_text()
# Drop the abandoned direct-reflection helper experiment, if present.
if 'private theorem ruleT_boolean' in text:
    text=text[:text.index('private theorem ruleT_boolean')] + text[text.index('/-- All 2^15'):]
source.write_text(text)
constraints=[(f'h{i}',kind,list(map(int,inds))) for i,(kind,*inds) in enumerate(re.findall(r'rule(T|Cm|Cp)\s+\(b (\d+)\) \(b (\d+)\) \(b (\d+)\)',text[:text.index('/-- All 2^15')]))]
generate('SeedFourRaw',15,3,RAW,constraints,source,'rule','/-- All 2^15')
