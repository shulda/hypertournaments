#!/usr/bin/env python3
"""Regenerate the compact normalized <=5 ternary negative certificate data.

The 37 explicit diagrams are proof data extracted from the audited July2026
classification table. Their validity and coverage are rechecked by the Lean
kernel in CertificatesData.lean; this Python generator is outside the trust
boundary. No historical search or optimization code is required.
"""
from itertools import combinations, permutations
from functools import cache
from pathlib import Path
import argparse

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--check", action="store_true", help="verify retained generated Lean files byte-for-byte without writing")
OPTIONS = parser.parse_args()
MISMATCHES = []

def write_generated(path, text):
    if OPTIONS.check:
        if not path.is_file() or path.read_text() != text:
            MISMATCHES.append(str(path))
    else:
        path.write_text(text)

DIAGRAMS = [(5, 0, 32, 0), (4, 0, 6, 4), (4, 3, 22, 2), (4, 10, 3, 0), (5, 1016, 299, 0), (4, 0, 55, 0), (6, 0, 35, 16376), (5, 432, 901, 4), (5, 591, 185, 9), (4, 5, 4, 2), (6, 0, 39, 5327), (5, 1016, 660, 0), (6, 0, 72, 26968), (4, 0, 9, 0), (3, 0, 2, 0), (4, 1, 22, 2), (5, 1023, 641, 0), (4, 11, 3, 0), (5, 1023, 676, 0), (5, 193, 738, 9), (4, 4, 4, 2), (4, 2, 51, 4), (5, 0, 470, 0), (5, 40, 74, 10), (5, 1016, 341, 8), (6, 0, 8037, 30314), (3, 0, 5, 0), (4, 3, 43, 4), (4, 11, 6, 0), (5, 223, 710, 8), (5, 432, 729, 4), (5, 591, 299, 8), (5, 993, 810, 8), (6, 0, 184, 13642), (6, 1222, 2016, 26880), (7, 877127, 617294, 1369260), (7, 1259212, 678233, 1455765)]
REPS = [0, 1, 2, 9, 10, 11, 12, 13, 25, 41, 82, 83]

@cache
def triples(n):
    return list(combinations(range(n), 3))

@cache
def pairs(n):
    return list(combinations(range(n), 2))


def transform(mask, p):
    idx = {t:i for i,t in enumerate(triples(5))}
    out = 0
    for i,t in enumerate(triples(5)):
        im = [p[v] for v in t]
        odd = sum(im[i]>im[j] for i in range(3) for j in range(i+1,3))%2
        out |= (((mask>>i)&1)^odd) << idx[tuple(sorted(im))]
    return out

TYPE5 = {}
for i,r in enumerate(REPS):
    orbit = {transform(r,p) for p in permutations(range(5))}
    assert not set(TYPE5).intersection(orbit)
    TYPE5.update({m:i for m in orbit})
assert len(TYPE5)==1024

def type4(vals):
    a,b,c,d=vals
    p=d+(1-c)+b+(1-a)
    return min(p,4-p)

def side_bit(d, right, t):
    n,a,l,r=d
    if t[2]<n:return (a>>triples(n).index(t))&1
    return ((r if right else l)>>pairs(n).index(t[:2]))&1

def packed(vals):
    return sum(v<<i for i,v in enumerate(vals))

def reqs(d, right):
    n=d[0]+1
    four=five=0
    for q in combinations(range(n),4):
        four |= 1<<type4([side_bit(d,right,tuple(q[i] for i in t)) for t in triples(4)])
    for q in combinations(range(n),5):
        packet=packed([side_bit(d,right,tuple(q[i] for i in t)) for t in triples(5)])
        five |= 1<<TYPE5[packet]
    return four,five

def mixed(d,x):
    n,a,l,r=d
    four=five=0
    for u,v in pairs(n):
        p=pairs(n).index((u,v))
        four |= 1<<type4([(l>>p)&1,(r>>p)&1,(x>>u)&1,(x>>v)&1])
    for u,v,w in triples(n):
        uv,uw,vw=(pairs(n).index(p) for p in ((u,v),(u,w),(v,w)))
        packet=packed([(a>>triples(n).index((u,v,w)))&1,(l>>uv)&1,(r>>uv)&1,
                       (l>>uw)&1,(r>>uw)&1,(x>>u)&1,(l>>vw)&1,(r>>vw)&1,(x>>v)&1,(x>>w)&1])
        five |= 1<<TYPE5[packet]
    return four,five

def profile(d):
    a,b=reqs(d,False),reqs(d,True)
    return (a[0]|b[0],a[1]|b[1]),[mixed(d,x) for x in range(1<<d[0])]

PROFILES=list(map(profile,DIAGRAMS))
SUPPORT=[4,6,6,7,6,6,6,7,5,7,3,3]

def support4(p):
    s=0
    for i in range(12):
        if p>>i&1:s|=SUPPORT[i]
    return s

def accepts(p,r):
    return not(r[0]&~support4(p) or r[1]&~p)

def blocks(p,pr):
    return accepts(p,pr[0]) and all(not accepts(p,r) for r in pr[1])

CHOICES=[]
for i in range(2048):
    p=2*i+1
    found=[j for j,pr in enumerate(PROFILES) if blocks(p,pr)]
    positive=p in (1,119,257,3583,4095)
    assert positive != bool(found)
    CHOICES.append(found[0] if found else 0)

def choice_tree(values, bit=10, indent='  '):
    if len(set(values)) == 1:
        return str(values[0])
    half=len(values)//2
    low=choice_tree(values[:half],bit-1,indent+'  ')
    high=choice_tree(values[half:],bit-1,indent+'  ')
    return f'if c.testBit {bit} then\n{indent}  {high}\n{indent}else\n{indent}  {low}'

def req(r):return f'⟨{r[0]}, {r[1]}⟩'
def arr(lines):return '#[\n  '+',\n  '.join(lines)+'\n]'

text='import Hypertournaments.FiveConstrained.CertificatesBasic\nimport Mathlib.Tactic.FinCases\n\n/-!\n# Kernel-checked negative certificates for all 2043 normalized palettes\n\nSource data: the 24July2026 classification supplement, SHA256\n`d15fbb89b7e22c1cde1402e1ce417fd74566dd10d38d145b355d6ec9cf9bbcb3`.\nA greedy cover within its 219 retained diagrams gives the following 37.\nNo minimality assertion is used. Regenerate by running\n`python3 tools/five_constrained/generate_certificates.py`.\n-/\n\nnamespace Hypertournaments.FiveConstrained\n\nset_option maxRecDepth 16384\nset_option maxHeartbeats 12000000\n\n'
text += 'def certificateDiagramData : Array CertificateDiagram := '+arr(['⟨'+', '.join(map(str,d))+'⟩' for d in DIAGRAMS])+'\n\n'
text += 'def certificateDiagram (i : Fin 37) : CertificateDiagram :=\n  certificateDiagramData[i.val]\'('+ 'i.isLt' + ')\n\n'
text += 'def certificateProfileData : Array CertificateProfile := '+arr(['⟨'+req(s)+', ['+', '.join(map(req,m))+']⟩' for s,m in PROFILES])+'\n\n'
text += 'def certificateStoredProfile (i : Fin 37) : CertificateProfile :=\n  certificateProfileData[i.val]\'('+ 'i.isLt'+')\n\n'
text += 'def certificateChoiceData : Array (Fin 37) := '+arr([', '.join(map(str,CHOICES[i:i+32])) for i in range(0,2048,32)])+'\n\n'
text += 'def certificateChoiceLookup (c : ℕ) : Fin 37 :=\n  '+choice_tree(CHOICES)+'\n\n'
text += 'def certificateChoice (c : Fin 2048) : Fin 37 :=\n  certificateChoiceLookup c.val\n\n'
root=Path(__file__).resolve().parents[2]/'Hypertournaments/FiveConstrained'
text += 'def certificateCovered (c : ℕ) : Bool :=\n  certificatePositive (2 * c + 1) || certificateBlocks (2 * c + 1)\n    (certificateStoredProfile (certificateChoice ⟨c % 2048, Nat.mod_lt _ (by decide)⟩))\n\n'
write_generated(root/'CertificatesData.lean', text+'end Hypertournaments.FiveConstrained\n')
header = 'namespace Hypertournaments.FiveConstrained\n\nset_option maxRecDepth 16384\nset_option maxHeartbeats 12000000\n\n'
ending = 'end Hypertournaments.FiveConstrained\n'
for group in range(8):
    dependency = 'CertificatesData' if group == 0 else f'CertificatesProfiles{group - 1}'
    out=f'import Hypertournaments.FiveConstrained.{dependency}\n\n'+header
    for i in range(group*5,min((group+1)*5,37)):
        out+=f'theorem certificate_profile_{i} :\n    certificateProfile (certificateDiagram {i}) = certificateStoredProfile {i} := by\n  rfl\n\n'
    write_generated(root/f'CertificatesProfiles{group}.lean', out+ending)
out=''.join(f'import Hypertournaments.FiveConstrained.CertificatesProfiles{g}\n' for g in range(8))
out+='import Mathlib.Tactic.FinCases\nimport Mathlib.Data.Fintype.Fin\n\n'+header
out+='theorem certificate_profiles (i : Fin 37) :\n    certificateProfile (certificateDiagram i) = certificateStoredProfile i := by\n  fin_cases i\n'
for i in range(37):out+=f'  · exact certificate_profile_{i}\n'
out+='\n\ntheorem certificate_links_unequal (i : Fin 37) :\n    (certificateDiagram i).left ≠ (certificateDiagram i).right := by\n  revert i\n  decide +kernel\n\ntheorem certificate_bounds (i : Fin 37) :\n    3 ≤ (certificateDiagram i).baseSize ∧\n      (certificateDiagram i).baseSize ≤ 7 ∧\n      (certificateDiagram i).base < 2 ^ ((certificateDiagram i).baseSize.choose 3) ∧\n      (certificateDiagram i).left < 2 ^ ((certificateDiagram i).baseSize.choose 2) ∧\n      (certificateDiagram i).right < 2 ^ ((certificateDiagram i).baseSize.choose 2) := by\n  revert i\n  decide +kernel\n\n'
write_generated(root/'CertificatesProfiles.lean', out+ending)
for group in range(16):
    dependency = 'CertificatesData' if group == 0 else f'CertificatesCoverage{group - 1}'
    out=f'import Hypertournaments.FiveConstrained.{dependency}\n\n'+header
    out+=f'theorem certificate_coverage_chunk_{group} :\n    (List.range 128).all (fun c => certificateCovered ({128*group} + c)) = true := by\n  rfl\n\n'
    write_generated(root/f'CertificatesCoverage{group}.lean', out+ending)
out=''.join(f'import Hypertournaments.FiveConstrained.CertificatesCoverage{g}\n' for g in range(16))
out+='import Hypertournaments.FiveConstrained.CertificatesProfiles\nimport Mathlib.Tactic.FinCases\nimport Mathlib.Data.Fintype.Fin\nimport Lean.Elab.Tactic.Omega\n\n'+header
out+='theorem certificate_coverage (c : Fin 2048) :\n    certificatePositive (2 * c.val + 1) = true ∨\n      certificateBlocks (2 * c.val + 1)\n        (certificateStoredProfile (certificateChoice c)) = true := by\n'
out+='  have hchunks (q : Fin 16) (r : Fin 128) :\n      certificateCovered (128 * q.val + r.val) = true := by\n    fin_cases q\n'
for i in range(16):
    out+=f'    · exact List.all_eq_true.mp certificate_coverage_chunk_{i} r.val (List.mem_range.mpr r.isLt)\n'
out+='  have hq : c.val / 128 < 16 := by omega\n  have hr : c.val % 128 < 128 := Nat.mod_lt _ (by decide)\n  have h := hchunks ⟨c.val / 128, hq⟩ ⟨c.val % 128, hr⟩\n  have hc : certificateCovered c.val = true := by\n    simpa only [Nat.div_add_mod] using h\n  simpa only [certificateCovered, Nat.mod_eq_of_lt c.isLt, Bool.or_eq_true] using hc\n\n'
out+='theorem certificate_full_coverage (c : Fin 2048) :\n    certificatePositive (2 * c.val + 1) = true ∨\n      certificateCheck (2 * c.val + 1)\n        (certificateDiagram (certificateChoice c)) = true := by\n  rcases certificate_coverage c with h | h\n  · exact Or.inl h\n  · right\n    simp only [certificateCheck, Bool.and_eq_true, decide_eq_true_eq,\n      certificate_profiles]\n    exact ⟨certificate_links_unequal _, h⟩\n\n'
out+='/-- Every negative normalized palette has a concrete checked one-point\nobstruction. Soundness for intrinsic ordinary AP is proved separately. -/\ntheorem exists_certificate (c : Fin 2048)\n    (hnegative : certificatePositive (2 * c.val + 1) = false) :\n    ∃ i : Fin 37, certificateCheck (2 * c.val + 1) (certificateDiagram i) = true := by\n  have h := certificate_full_coverage c\n  simp only [hnegative, Bool.false_eq_true, false_or] at h\n  exact ⟨certificateChoice c, h⟩\n\n'
write_generated(root/'CertificatesCoverage.lean', out+ending)
if MISMATCHES:
    raise SystemExit('Generated files differ:\n' + '\n'.join(MISMATCHES))
print('37 diagrams; all2043 negative palettes covered; ' + ('retained Lean files match' if OPTIONS.check else 'Lean files regenerated'))
