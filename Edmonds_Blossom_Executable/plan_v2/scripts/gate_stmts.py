"""Gate check: compare the statements of a theory with those of its one-shot (or of any other
theory text), after converting glyphs to ASCII. A statement is the text of a top-level or
nested `lemma`/`theorem`/`corollary`/`definition`/`fun`/`function`/`abbreviation`/`locale`/
`record`/`datatype`/`partial_function`/`lemmas`/`interpretation`/`global_interpretation`
command up to its proof (or, for definitions, up to the next command). Prints the statements
that differ, are missing or are new.

usage: python3 gate_stmts.py REAL.thy ONESHOT
"""
import re, sys
table = {}
for line in open('/media/llms/Isabelle2025-2/etc/symbols', encoding='utf-8'):
    m = re.match(r'(\\<[A-Za-z0-9_^]+>)\s+code:\s*0x([0-9a-fA-F]+)', line)
    if m:
        table.setdefault(chr(int(m.group(2), 16)), m.group(1))
def ascii(t):
    return ''.join(table.get(c, c) if ord(c) > 127 else c for c in t)
HEAD = re.compile(r'^\s*(lemma|theorem|corollary|definition|fun|function|abbreviation|locale|record|datatype|partial_function|lemmas|interpretation|global_interpretation|primrec|inductive)\b')
STOP = re.compile(r'^\s*(proof|by|apply|using|unfolding|including|supply|done|qed|oops|sorry|text|subsection|subsubsection|section|context|end|begin|declare|named_theorems|provenance|lemma|theorem|corollary|definition|fun|function|abbreviation|locale|record|datatype|partial_function|lemmas|interpretation|global_interpretation|primrec|inductive|value|export_code|\(\*)\b')
MARK = re.compile(r'\\<\^marker>\\<open>provenance [a-z_]+\\<close>\s*')
def statements(text):
    L = ascii(text).split('\n')
    out = []
    i = 0
    while i < len(L):
        if HEAD.match(L[i]):
            j = i + 1
            while j < len(L) and not STOP.match(L[j]) and L[j].strip() != '':
                j += 1
            # definitions/funs may have blank lines inside their equations: include up to the next STOP
            if re.match(r'^\s*(fun|function|primrec|partial_function|definition|locale|record|datatype)\b', L[i]):
                while j < len(L) and not STOP.match(L[j]):
                    j += 1
            s = ' '.join(' '.join(L[i:j]).split())
            s = MARK.sub('', s)
            out.append(s)
            i = j
        else:
            i += 1
    return out
def key(s):
    m = re.match(r'(\w+)\s+(?:\(in \w+\)\s*)?(?:\(\w+\)\s*)?(?:\([^)]*\)\s*)?"?([\w.\']+)', s)
    return (m.group(1), m.group(2)) if m else ('?', s[:40])
a = statements(open(sys.argv[1], encoding='utf-8').read())
b = statements(open(sys.argv[2], encoding='utf-8').read())
from collections import Counter
ca, cb = Counter(a), Counter(b)
only_a = list((ca - cb).elements()); only_b = list((cb - ca).elements())
print(f'statements: real {len(a)}, one-shot {len(b)}; identical {sum((ca & cb).values())}')
ka = {key(s): s for s in only_a}; kb = {key(s): s for s in only_b}
for k in sorted(set(ka) | set(kb), key=str):
    if k in ka and k in kb:
        print('CHANGED', k); print('   real:', ka[k][:600]); print('   shot:', kb[k][:600])
    elif k in ka:
        print('NEW    ', k, ':', ka[k][:300])
    else:
        print('MISSING', k, ':', kb[k][:300])
