"""Non-blank lines of proofs vs. definitions/specifications.

Usage: python3 size_split.py GROUP=f1,f2 ...
Proofs: lemma proofs, plus the proof parts of function definitions and of
(global_)interpretation / sublocale commands.
Definitions/specifications: lemma statements, definitions (definition, abbreviation,
fun, function, partial_function, primrec, record, datatype, type_synonym), locale
and context headers, and the instantiation part of interpretations.
Not counted: blank lines, comments, top-level text blocks, section headings, the
theory header, named_theorems, lemmas, declare, notation, value, export_code, begin/end.
"""
import os
import re
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from style_stats import strip_comments, mask, split_commands, cmd_name, LEMMA_KW, PROOF_START  # noqa
from line_breakdown import blank_toplevel_text, is_boiler, nb  # noqa

DEFS = {'definition', 'abbreviation', 'fun', 'function', 'partial_function', 'primrec',
        'record', 'datatype', 'type_synonym'}
INTERP = {'interpretation', 'global_interpretation', 'sublocale'}
HEADERS = {'locale', 'context'}
PROOF_KW = PROOF_START | {'done'}


def split_at_proof(c):
    """Split a command into (spec lines, proof lines) at its first proof keyword."""
    m_lines, o_lines = c['m'], c['o']
    for k, ml in enumerate(m_lines):
        for mm in re.finditer(r"(?<![A-Za-z0-9_'.])([A-Za-z_][A-Za-z0-9_]*)(?![A-Za-z0-9_'])", ml):
            if mm.group(1) in PROOF_KW:
                if k == 0 and mm.start() < len(ml.split(None, 1)[0]) + 1:
                    continue
                ol = o_lines[k]
                return o_lines[:k] + [ol[:mm.start()]], [ol[mm.start():]] + o_lines[k + 1:]
    return o_lines, []


def run(files):
    t = {'proofs': 0, 'specs': 0, 'statements': 0, 'definitions': 0, 'locale/interp specs': 0,
         'lemma proofs': 0, 'other proofs': 0, 'template lemmas': 0, 'other lemmas': 0}
    for f in files:
        orig = strip_comments(open(f, encoding='utf-8').read())
        orig, _ = blank_toplevel_text(orig)
        for c in split_commands(orig, mask(orig)):
            kw = c['kw']
            if kw in LEMMA_KW:
                spec, prf = split_at_proof(c)
                t['statements'] += nb(spec); t['lemma proofs'] += nb(prf)
                t['template lemmas' if is_boiler(cmd_name(c)) else 'other lemmas'] += 1
            elif kw in DEFS or kw in INTERP:
                spec, prf = split_at_proof(c) if kw in INTERP or kw == 'function' else (c['o'], [])
                t['definitions' if kw in DEFS else 'locale/interp specs'] += nb(spec)
                t['other proofs'] += nb(prf)
            elif kw in HEADERS:
                t['locale/interp specs'] += nb(c['o'])
    t['proofs'] = t['lemma proofs'] + t['other proofs']
    t['specs'] = t['statements'] + t['definitions'] + t['locale/interp specs']
    return t


if __name__ == '__main__':
    res = {}
    for a in sys.argv[1:]:
        g, fs = a.split('=', 1)
        res[g] = run(fs.split(','))
    keys = list(next(iter(res.values())).keys())
    print('%-28s' % '' + ''.join('%10s' % g for g in res))
    for k in keys:
        print('%-28s' % k + ''.join('%10s' % res[g][k] for g in res))
