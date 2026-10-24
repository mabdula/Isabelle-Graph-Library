"""Where do the lines of a group of theories go?  Usage: python3 line_breakdown.py GROUP=f1,f2 ..."""
import os
import re
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from style_stats import strip_comments, mask, split_commands, cmd_name, LEMMA_KW, PROOF_START  # noqa

BOILER = [r'_call_\d+_conds(I)?$', r'_ret_\d+_conds(I)?$', r'_cases$', r'_simps$', r'_induct$',
          r'_domintros$', r'^invar_.*_props$', r'^invar_.*_intro$', r'^invar_.*_holds(_.*)?$',
          r'^call_\d+_terminates$', r'^call_\d+_measure', r'^in_.*_term_rel\'?$', r'_terminates$',
          r'^wf_term_rel$', r'^in_prod_relI$', r'^wf_less_rel$', r'^initial_state_props$',
          r'^ret\d+_holds$', r'_ret_\d+$', r'_impl_same$', r'_impl_to_', r'_correct_\d+$']


def is_boiler(n):
    return n is not None and any(re.search(p, n) for p in BOILER)


def proof_split(c, use_orig=True):
    m_lines = c['m']
    o_lines = c['o'] if use_orig else c['m']
    for k, ml in enumerate(m_lines):
        for mm in re.finditer(r"(?<![A-Za-z0-9_'.])([A-Za-z_][A-Za-z0-9_]*)(?![A-Za-z0-9_'])", ml):
            if mm.group(1) in PROOF_START:
                if k == 0 and mm.start() < len(ml.split(None, 1)[0]) + 1:
                    continue
                ol = o_lines[k]
                stmt = o_lines[:k] + [ol[:mm.start()]]
                prf = [ol[mm.start():]] + o_lines[k + 1:]
                return stmt, prf
    return o_lines, []


def blank_toplevel_text(s):
    OPEN, CLOSE = '\\<open>', '\\<close>'
    out, i, n, cnt = [], 0, len(s), 0
    while i < n:
        at_line_start = (i == 0 or s[i - 1] == '\n')
        m = re.match(r'(text|txt)\s*' + re.escape(OPEN), s[i:]) if at_line_start else None
        if m:
            j = i + m.end()
            depth = 1
            while j < n and depth:
                if s.startswith(OPEN, j):
                    depth += 1; j += len(OPEN)
                elif s.startswith(CLOSE, j):
                    depth -= 1; j += len(CLOSE)
                else:
                    j += 1
            block = s[i:j]
            cnt += sum(1 for l in block.split('\n') if l.strip())
            out.append(''.join('\n' if ch == '\n' else ' ' for ch in block))
            i = j
        else:
            out.append(s[i]); i += 1
    return ''.join(out), cnt


def nb(lines):
    return sum(1 for l in lines if l.strip())


def run(files):
    tot = {}
    def add(k, v):
        tot[k] = tot.get(k, 0) + v
    for f in files:
        raw = open(f, encoding='utf-8').read()
        add('physical lines', raw.count('\n') + (0 if raw.endswith('\n') else 1))
        add('blank lines', sum(1 for l in raw.split('\n') if not l.strip()))
        orig = strip_comments(raw)
        orig, ntext = blank_toplevel_text(orig)
        add('top-level text blocks', ntext)
        masked = mask(orig)
        # comment-only lines: non-blank in raw, blank after comment removal
        add('comment-only lines', sum(1 for a, b in zip(raw.split('\n'), orig.split('\n')) if a.strip() and not b.strip()))
        for c in split_commands(orig, masked):
            kw = c['kw']
            if kw in LEMMA_KW:
                name = cmd_name(c)
                stmt, prf = proof_split(c)
                grp = 'boilerplate' if is_boiler(name) else 'substantive'
                add('lemma statements (%s)' % grp, nb(stmt))
                add('lemma proofs (%s)' % grp, nb(prf))
                add('#lemmas (%s)' % grp, 1)
            elif kw in ('definition', 'abbreviation', 'fun', 'function', 'partial_function', 'primrec', 'record', 'datatype'):
                add('definitions', nb(c['o']))
            elif kw in ('locale', 'context', 'sublocale', 'interpretation', 'global_interpretation', 'begin', 'end'):
                add('locales/contexts/interpretations', nb(c['o']))
            elif kw in ('section', 'subsection', 'subsubsection', 'chapter', 'paragraph'):
                add('section headings', nb(c['o']))
            elif kw == 'lemmas':
                add('lemmas commands', nb(c['o']))
            else:
                add('other (%s)' % kw, nb(c['o']))
    return tot


if __name__ == '__main__':
    res = {}
    for a in sys.argv[1:]:
        g, fs = a.split('=', 1)
        res[g] = run(fs.split(','))
    keys = sorted({k for r in res.values() for k in r})
    print('%-48s' % '' + ''.join('%10s' % g for g in res))
    for k in keys:
        print('%-48s' % k + ''.join('%10s' % res[g].get(k, 0) for g in res))
