"""Style statistics for Isabelle theories.

Usage: python3 style_stats.py OUT.json GROUP=file1,file2 GROUP2=...
Prints a human-readable table and dumps the raw per-group numbers as JSON.
"""
import json
import re
import sys
from collections import Counter, defaultdict

TOP = {
    'lemma', 'theorem', 'corollary', 'proposition', 'lemmas', 'definition',
    'abbreviation', 'fun', 'function', 'partial_function', 'primrec', 'record',
    'datatype', 'type_synonym', 'locale', 'context', 'sublocale',
    'interpretation', 'global_interpretation', 'named_theorems', 'section',
    'subsection', 'subsubsection', 'chapter', 'paragraph', 'notation',
    'no_notation', 'declare', 'end', 'begin', 'value', 'export_code', 'theory',
    'ML', 'setup', 'consts', 'axiomatization', 'instantiation', 'instance',
    'termination', 'inductive', 'inductive_set', 'hide_const', 'no_translations',
    'translations', 'unbundle', 'bundle', 'method', 'lemmas', 'thm', 'term',
    'find_theorems', 'code_pred', 'fun_cases', 'qualified', 'print_locale',
}
LEMMA_KW = {'lemma', 'theorem', 'corollary', 'proposition'}
DEF_KW = {'definition', 'abbreviation', 'fun', 'function', 'partial_function',
          'primrec'}
PROOF_START = {'by', 'apply', 'proof', 'using', 'unfolding', 'including',
               'supply', 'subgoal', 'oops', 'sorry', 'apply_end'}
ISAR_KW = ['have', 'show', 'obtain', 'hence', 'thus', 'moreover', 'ultimately',
           'then', 'fix', 'assume', 'case', 'next', 'define', 'let', 'note',
           'from', 'with', 'consider', 'interpret']
METHODS = ['auto', 'force', 'fastforce', 'blast', 'simp', 'simp_all', 'metis',
           'smt', 'linarith', 'presburger', 'arith', 'fast', 'meson', 'rule',
           'intro', 'elim', 'cases', 'induction', 'induct', 'subst', 'clarsimp',
           'eval', 'unfold_locales', 'standard', 'iprover', 'argo', 'order',
           'best', 'safe', 'clarify', 'erule', 'drule', 'frule', 'insert',
           'goal_cases', 'all', 'fastforce', 'intro_locales', 'code_simp',
           'normalization', 'nitpick', 'sledgehammer', 'use', 'unfold', 'fold',
           'assumption', 'contradiction', 'this', 'transfer', 'eventually_elim',
           'induct_tac', 'rule_tac', 'atomize_elim', 'simp_all', 'coinduction',
           'ccontr', 'cases_tac', '-', 'pat_completeness', 'lexicographic_order',
           'relation', 'size_change', 'subgoal_tac', 'measure', 'blast', 'elim']
BUNDLES = ['invar_props_elims', 'invar_props_intros', 'invar_holds_intros',
           'call_cond_elims', 'call_cond_intros', 'ret_holds_intros',
           'state_rel_intros', 'state_rel_holds_intros', 'termination_intros']


def strip_comments(s):
    out, i, depth = [], 0, 0
    while i < len(s):
        if s.startswith('(*', i):
            depth += 1
            out.append('  ')
            i += 2
        elif depth and s.startswith('*)', i):
            depth -= 1
            out.append('  ')
            i += 2
        elif depth:
            out.append('\n' if s[i] == '\n' else ' ')
            i += 1
        else:
            out.append(s[i])
            i += 1
    return ''.join(out)


def mask(s):
    """Replace inner-syntax strings and cartouches by 'x' (newlines kept)."""
    out, i, n = [], 0, len(s)
    OPEN, CLOSE = '\\<open>', '\\<close>'
    while i < n:
        if s[i] == '"':
            j = i + 1
            while j < n and s[j] != '"':
                if s[j] == '\\' and j + 1 < n and s[j + 1] == '"':
                    j += 2
                    continue
                j += 1
            out.append('"' + ''.join('\n' if c == '\n' else ' ' for c in s[i + 1:j]) + '"')
            i = j + 1
        elif s.startswith(OPEN, i):
            depth, j = 1, i + len(OPEN)
            while j < n and depth:
                if s.startswith(OPEN, j):
                    depth += 1
                    j += len(OPEN)
                elif s.startswith(CLOSE, j):
                    depth -= 1
                    j += len(CLOSE)
                else:
                    j += 1
            body = s[i:j]
            out.append(''.join('\n' if c == '\n' else ' ' for c in body))
            i = j
        else:
            out.append(s[i])
            i += 1
    return ''.join(out)


WORD = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")


def first_word(line):
    m = re.match(r"\s*([A-Za-z_][A-Za-z0-9_]*)", line)
    return m.group(1) if m else None


def split_commands(orig, masked):
    o_lines = orig.split('\n')
    m_lines = masked.split('\n')
    cmds, cur = [], None
    for k, (ol, ml) in enumerate(zip(o_lines, m_lines)):
        w = first_word(ml)
        indent = len(ml) - len(ml.lstrip())
        if w in TOP and not (w == 'context' and False):
            # 'next'/'case' are not TOP; guard: 'begin'/'end' only at col 0-2
            if cur:
                cmds.append(cur)
            cur = {'kw': w, 'start': k + 1, 'o': [ol], 'm': [ml], 'indent': indent}
        else:
            if cur is None:
                cur = {'kw': '_pre', 'start': k + 1, 'o': [], 'm': [], 'indent': 0}
            cur['o'].append(ol)
            cur['m'].append(ml)
    if cur:
        cmds.append(cur)
    return cmds


def cmd_name(cmd):
    mtext = '\n'.join(cmd['m'])
    otext = '\n'.join(cmd['o'])
    rest = mtext.split(None, 1)
    if len(rest) < 2:
        return None
    m = re.match(r"\s*(\([^)]*\)\s*)?([A-Za-z_][A-Za-z0-9_']*|\")", rest[1])
    if not m:
        return None
    if m.group(2) != '"':
        return m.group(2)
    # bare `definition "name args = ..."`: read the name from the string
    q = otext.index('"', len(otext) - len(rest[1]))
    m2 = re.match(r'"\s*([A-Za-z_][A-Za-z0-9_\']*)', otext[q:])
    return m2.group(1) if m2 else None


def method_names(text):
    """Method names after by/apply/proof tokens in masked proof text."""
    names = []
    for m in re.finditer(r"\b(by|apply|proof)\b\s*(\(?)\s*([A-Za-z_\-][A-Za-z0-9_\-]*)?", text):
        kw, par, name = m.groups()
        if name:
            names.append(name)
        elif kw == 'proof':
            names.append('<default>')
    # second method of `by m1 m2` is ignored on purpose
    return names


def tokens(text):
    return re.findall(r"[A-Za-z_][A-Za-z0-9_']*|\S", text)


def analyse(files):
    st = defaultdict(Counter)
    lists = defaultdict(list)
    for f in files:
        orig = strip_comments(open(f, encoding='utf-8').read())
        masked = mask(orig)
        cmds = split_commands(orig, masked)
        # line lengths (raw file)
        for ln in open(f, encoding='utf-8').read().split('\n'):
            if ln.strip():
                lists['line_len'].append(len(ln))
        for c in cmds:
            kw = c['kw']
            st['cmd'][kw] += 1
            mtext = '\n'.join(c['m'])
            otext = '\n'.join(c['o'])
            name = cmd_name(c)
            if kw == 'locale' and name:
                lists['locale_names'].append(name)
            if kw == 'record' and name:
                lists['record_names'].append(name)
            if kw == 'function':
                st['def']['function(domintros)' if 'domintros' in c['m'][0] else 'function(plain)'] += 1
            if kw in DEF_KW and name:
                lists['const_names'].append((kw, name))
                if kw == 'definition':
                    head = mtext.split('"', 1)[0]
                    st['def']['definition_typed' if '::' in head else 'definition_untyped'] += 1
                if kw in ('fun', 'function', 'partial_function', 'primrec'):
                    # arity of first equation head
                    o_eq = otext.split('"')
                    eqs = [o_eq[i] for i in range(1, len(o_eq), 2)]
                    eq = next((e for e in eqs if '=' in e and '::' not in e.split('=')[0]), None)
                    if eq:
                        lhs = eq.split('=')[0]
                        toks = re.findall(r"\S+", lhs.replace('(', ' ( ').replace(')', ' ) '))
                        # count arguments at paren depth 0
                        depth, args = 0, 0
                        for t in toks[1:]:
                            if t == '(':
                                if depth == 0:
                                    args += 1
                                depth += 1
                            elif t == ')':
                                depth -= 1
                            elif depth == 0:
                                args += 1
                        lists['rec_arity'].append((name, kw, args))
            if kw in LEMMA_KW:
                analyse_lemma(c, name, st, lists)
            if kw == 'lemmas':
                pass
        # whole-file token counts for named-theorem bundles
        for b in BUNDLES:
            st['bundle_decl'][b] += len(re.findall(r'named_theorems\s+' + b + r'\b', masked))
            st['bundle_attr'][b] += len(re.findall(r'\[[^\]]*\b' + b + r'\b[^\]]*\]', masked))
        st['file']['lines'] += masked.count('\n') + 1
        st['file']['text_cmds'] += len(re.findall(r'^\s*text\b', masked, re.M))
        st['file']['comment_cmds'] += len(re.findall(r'\\<comment>', orig))
        st['file']['nonascii_chars'] += len(re.findall(r'[^\x00-\x7f]', orig))
    return st, lists


def analyse_lemma(c, name, st, lists):
    m_lines = c['m']
    o_lines = c['o']
    # find proof start: first PROOF_START token outside the head
    start_line, start_col = None, None
    for k, ml in enumerate(m_lines):
        for mm in re.finditer(r"(?<![A-Za-z0-9_'.])([A-Za-z_][A-Za-z0-9_]*)(?![A-Za-z0-9_'])", ml):
            if mm.group(1) in PROOF_START:
                # ignore the command keyword itself / name
                if k == 0 and mm.start() < len(ml.split(None, 1)[0]) + 1:
                    continue
                start_line, start_col = k, mm.start()
                break
        if start_line is not None:
            break
    st['lemma']['count'] += 1
    if start_line is None:
        st['lemma']['no_proof_found'] += 1
        return
    stmt_m = '\n'.join(m_lines[:start_line] + [m_lines[start_line][:start_col]])
    stmt_o = '\n'.join(o_lines[:start_line] + [o_lines[start_line][:start_col]])
    proof_m = '\n'.join([m_lines[start_line][start_col:]] + m_lines[start_line + 1:])
    proof_o = '\n'.join([o_lines[start_line][start_col:]] + o_lines[start_line + 1:])
    stmt_lines = [l for l in stmt_m.split('\n') if l.strip()]
    proof_lines = [l for l in proof_m.split('\n') if l.strip()]
    lists['stmt_len'].append(len(stmt_lines))
    lists['proof_len'].append(len(proof_lines))
    toks = tokens(proof_m)
    tokset = Counter(t for t in toks)
    if tokset['sorry'] or tokset['oops']:
        kind = 'sorry'
    elif tokset['proof']:
        kind = 'isar'
    elif tokset['apply']:
        kind = 'apply'
    elif tokset['by'] or proof_m.strip().startswith('.'):
        kind = 'by'
    else:
        kind = 'other'
    st['proof_kind'][kind] += 1
    lists['proof_len_' + kind].append(len(proof_lines))
    lists['lemma_rows'].append((name, kind, len(stmt_lines), len(proof_lines)))
    st['lemma']['by_tokens'] += tokset['by']
    st['lemma']['apply_tokens'] += tokset['apply']
    st['lemma']['proof_tokens'] += tokset['proof']
    for w in ISAR_KW:
        st['isar'][w] += tokset[w]
    if kind == 'isar':
        lists['isar_have_show'].append(tokset['have'] + tokset['show'] + tokset['hence'] + tokset['thus'] + tokset['obtain'])
        lists['isar_by_per_proof'].append(tokset['by'])
    # labelled haves
    st['lemma']['labelled_have'] += len(re.findall(r'\b(have|obtain|show|hence|thus)\s+[A-Za-z_][A-Za-z0-9_\']*\s*:', proof_m))
    st['lemma']['labelled_have'] += 0
    st['lemma']['unlabelled_have'] += len(re.findall(r'\b(have|hence)\s+"', proof_m))
    st['lemma']['OF'] += proof_o.count('[OF')
    st['lemma']['using'] += tokset['using']
    st['lemma']['unfolding'] += tokset['unfolding']
    st['lemma']['assms_ref'] += len(re.findall(r'\bassms\b', proof_m))
    st['lemma']['cartouche_fact'] += len(re.findall(r'\\<open>', proof_o)) - len(re.findall(r'\b(text|comment>)\s*\\<open>', proof_o))
    st['lemma']['goal_cases'] += tokset['goal_cases']
    # layout of terminal calls: `by`/`using` opening a line vs. trailing a line
    for kw in ('by', 'using'):
        for ln in proof_m.split('\n')[1:] if kind != 'by' or len(proof_lines) > 1 else []:
            pass
    pl = proof_m.split('\n')
    for idx, ln in enumerate(pl):
        for mm in re.finditer(r'\b(by|using)\b', ln):
            lead = ln[:mm.start()].strip()
            pos = 'line_start' if lead == '' else 'inline'
            if idx == 0 and kind == 'by' and lead == '':
                pos = 'line_start'
            st['layout'][mm.group(1) + '_' + pos] += 1
    # bare terminal calls inside Isar proofs: `by simp`, `by auto`, `by blast`, ...
    if kind == 'isar':
        for mm in re.finditer(r'\bby\s+(simp|auto|blast|force|fastforce|linarith|presburger|simp_all|arith|fast)\b(?!\s*\()', proof_m):
            st['isar_calls']['bare'] += 1
        for mm in re.finditer(r'\bby\s*\(\s*rule\b', proof_m):
            st['isar_calls']['rule'] += 1
        st['isar_calls']['all'] += tokset['by']
    st['lemma']['psimps'] += len(re.findall(r'\.psimps\b', proof_m))
    st['lemma']['pinduct'] += len(re.findall(r'\.pinduct\b', proof_m))
    # method names
    for mn in method_names(proof_m):
        st['method'][mn] += 1
    # spacing style
    st['spacing']['by('] += len(re.findall(r'\bby\(', proof_m))
    st['spacing']['by ('] += len(re.findall(r'\bby \(', proof_m))
    st['spacing']['by name'] += len(re.findall(r'\bby [A-Za-z]', proof_m))
    st['spacing']['proof('] += len(re.findall(r'\bproof\(', proof_m))
    st['spacing']['proof ('] += len(re.findall(r'\bproof \(', proof_m))
    st['spacing']['proof-'] += len(re.findall(r'\bproof-', proof_m))
    st['spacing']['proof -'] += len(re.findall(r'\bproof -', proof_m))
    st['spacing']['apply('] += len(re.findall(r'\bapply\(', proof_m))
    st['spacing']['apply ('] += len(re.findall(r'\bapply \(', proof_m))
    # method modifiers
    for mod in ['elim!:', 'elim:', 'intro!:', 'intro:', 'dest!:', 'dest:', 'simp add:', 'simp:', 'split:', 'simp del:', 'iff:']:
        st['modifier'][mod] += proof_m.count(mod)
    for b in BUNDLES:
        st['bundle_use'][b] += len(re.findall(r'\b' + b + r'\b', proof_m))
    # statement style
    has_assumes = bool(re.search(r'\bassumes\b', stmt_m))
    has_shows = bool(re.search(r'\bshows\b', stmt_m))
    st['stmt']['assumes_shows' if has_assumes else ('shows_only' if has_shows else 'plain')] += 1
    st['stmt']['meta_imp_in_stmt'] += stmt_o.count('\\<Longrightarrow>')
    st['stmt']['lbrakk_in_stmt'] += stmt_o.count('\\<lbrakk>')
    st['stmt']['named_assumes'] += len(re.findall(r'\b(assumes|and)\s+[A-Za-z_][A-Za-z0-9_\']*\s*:', stmt_m)) if has_assumes else 0
    st['stmt']['with_attr'] += 1 if re.match(r"\s*\S+\s+[A-Za-z_][A-Za-z0-9_']*\s*\[", m_lines[0]) else 0
    if name is None:
        st['stmt']['anonymous'] += 1


def pct(a, b):
    return '%5.1f%%' % (100.0 * a / b) if b else '   n/a'


def mean(xs):
    return sum(xs) / len(xs) if xs else 0.0


def median(xs):
    if not xs:
        return 0
    s = sorted(xs)
    return s[len(s) // 2]


def quant(xs, q):
    if not xs:
        return 0
    s = sorted(xs)
    return s[min(len(s) - 1, int(q * len(s)))]


def classify_name(n):
    if re.fullmatch(r"[a-z][a-z0-9_']*", n):
        return 'lower_snake'
    if re.fullmatch(r"([A-Z][A-Za-z0-9]*)(_[A-Z0-9][A-Za-z0-9]*)*'?", n):
        return 'Capital_Snake'
    if re.fullmatch(r"[A-Z]{2,}[A-Z0-9]*(_[a-z0-9_']+)*", n):
        return 'ACRONYM_lower'
    return 'mixed'


def report(groups):
    out = {}
    for g, files in groups.items():
        st, lists = analyse(files)
        out[g] = (st, lists)
    gnames = list(groups)

    def row(label, f):
        print('%-40s' % label + ''.join('%16s' % f(*out[g]) for g in gnames))

    print('%-40s' % 'metric' + ''.join('%16s' % g for g in gnames))
    row('files', lambda st, l: str(len(groups[[k for k in groups if out[k][0] is st][0]])))
    row('lines', lambda st, l: str(st['file']['lines']))
    row('lemmas', lambda st, l: str(st['lemma']['count']))
    row('lines per lemma', lambda st, l: '%.1f' % (st['file']['lines'] / max(1, st['lemma']['count'])))
    print('-- proof kind')
    for k in ['by', 'apply', 'isar', 'sorry', 'other']:
        row('  ' + k, lambda st, l, k=k: pct(st['proof_kind'][k], st['lemma']['count']))
    print('-- proof length (non-blank lines)')
    row('  mean', lambda st, l: '%.1f' % mean(l['proof_len']))
    row('  median', lambda st, l: str(median(l['proof_len'])))
    row('  p90', lambda st, l: str(quant(l['proof_len'], 0.9)))
    row('  max', lambda st, l: str(max(l['proof_len'] or [0])))
    row('  mean of by-proofs', lambda st, l: '%.1f' % mean(l['proof_len_by']))
    row('  mean of isar proofs', lambda st, l: '%.1f' % mean(l['proof_len_isar']))
    row('  median of isar proofs', lambda st, l: str(median(l['proof_len_isar'])))
    row('  share proof lines in isar', lambda st, l: pct(sum(l['proof_len_isar']), sum(l['proof_len'])))
    row('  steps (have/show..) per isar', lambda st, l: '%.1f' % mean(l['isar_have_show']))
    row('  by-calls per isar proof', lambda st, l: '%.1f' % mean(l['isar_by_per_proof']))
    row('  proof lines / stmt lines', lambda st, l: '%.2f' % (sum(l['proof_len']) / max(1, sum(l['stmt_len']))))
    print('-- isar vocabulary (per lemma)')
    for w in ['have', 'show', 'hence', 'thus', 'then', 'obtain', 'moreover', 'ultimately', 'fix', 'assume', 'case', 'define', 'let', 'note']:
        row('  ' + w, lambda st, l, w=w: '%.2f' % (st['isar'][w] / max(1, st['lemma']['count'])))
    row('  labelled have/show/obtain', lambda st, l: '%.2f' % (st['lemma']['labelled_have'] / max(1, st['lemma']['count'])))
    row('  [OF ...] per lemma', lambda st, l: '%.2f' % (st['lemma']['OF'] / max(1, st['lemma']['count'])))
    row('  using per lemma', lambda st, l: '%.2f' % (st['lemma']['using'] / max(1, st['lemma']['count'])))
    row('  unfolding per lemma', lambda st, l: '%.2f' % (st['lemma']['unfolding'] / max(1, st['lemma']['count'])))
    row('  cartouche fact refs / lemma', lambda st, l: '%.2f' % (st['lemma']['cartouche_fact'] / max(1, st['lemma']['count'])))
    row('  goal_cases / lemma', lambda st, l: '%.2f' % (st['lemma']['goal_cases'] / max(1, st['lemma']['count'])))
    print('-- methods (share of by/apply/proof method calls)')
    tot = {g: sum(out[g][0]['method'].values()) for g in gnames}
    allm = Counter()
    for g in gnames:
        allm.update(out[g][0]['method'])
    for mname, _ in allm.most_common(22):
        print('%-40s' % ('  ' + mname) + ''.join('%16s' % pct(out[g][0]['method'][mname], tot[g]) for g in gnames))
    print('-- method modifiers (per lemma)')
    for mod in ['elim!:', 'elim:', 'intro!:', 'intro:', 'dest!:', 'dest:', 'simp add:', 'simp:', 'split:']:
        row('  ' + mod, lambda st, l, mod=mod: '%.2f' % (st['modifier'][mod] / max(1, st['lemma']['count'])))
    print('-- spacing')
    for k in ['by(', 'by (', 'by name', 'proof(', 'proof (', 'proof-', 'proof -', 'apply(', 'apply (']:
        row('  ' + k, lambda st, l, k=k: str(st['spacing'][k]))
    print('-- statements')
    row('  assumes/shows', lambda st, l: pct(st['stmt']['assumes_shows'], st['lemma']['count']))
    row('  shows only', lambda st, l: pct(st['stmt']['shows_only'], st['lemma']['count']))
    row('  plain "..."', lambda st, l: pct(st['stmt']['plain'], st['lemma']['count']))
    row('  \\<lbrakk> in stmt / lemma', lambda st, l: '%.2f' % (st['stmt']['lbrakk_in_stmt'] / max(1, st['lemma']['count'])))
    row('  named assumptions / lemma', lambda st, l: '%.2f' % (st['stmt']['named_assumes'] / max(1, st['lemma']['count'])))
    row('  lemmas with attribute', lambda st, l: pct(st['stmt']['with_attr'], st['lemma']['count']))
    row('  stmt lines mean', lambda st, l: '%.1f' % mean(l['stmt_len']))
    print('-- definitions / commands')
    for k in ['definition', 'abbreviation', 'fun', 'function', 'partial_function', 'primrec', 'record', 'datatype', 'locale', 'context', 'sublocale', 'global_interpretation', 'interpretation', 'named_theorems', 'section', 'subsection', 'lemmas']:
        row('  ' + k, lambda st, l, k=k: str(st['cmd'][k]))
    row('  function (domintros)', lambda st, l: str(st['def']['function(domintros)']))
    row('  definition typed (::)', lambda st, l: str(st['def']['definition_typed']))
    row('  definition untyped', lambda st, l: str(st['def']['definition_untyped']))
    row('  text blocks', lambda st, l: str(st['file']['text_cmds']))
    row('  \\<comment>', lambda st, l: str(st['file']['comment_cmds']))
    print('-- named-theorem bundles: attribute uses / proof uses')
    for b in BUNDLES:
        row('  ' + b, lambda st, l, b=b: '%d/%d' % (st['bundle_attr'][b], st['bundle_use'][b]))
    print('-- terminal-call layout and granularity')
    row('  `by` opening a line', lambda st, l: pct(st['layout']['by_line_start'], st['layout']['by_line_start'] + st['layout']['by_inline']))
    row('  `using` opening a line', lambda st, l: pct(st['layout']['using_line_start'], st['layout']['using_line_start'] + st['layout']['using_inline']))
    row('  isar: bare `by simp/auto/..`', lambda st, l: pct(st['isar_calls']['bare'], st['isar_calls']['all']))
    row('  isar: `by (rule ..)`', lambda st, l: pct(st['isar_calls']['rule'], st['isar_calls']['all']))
    row('  .psimps refs / lemma', lambda st, l: '%.2f' % (st['lemma']['psimps'] / max(1, st['lemma']['count'])))
    row('  .pinduct refs / lemma', lambda st, l: '%.2f' % (st['lemma']['pinduct'] / max(1, st['lemma']['count'])))
    print('-- invariant families (definitions named invar_*)')
    for g in gnames:
        st, l = out[g]
        invs = [n for _, n in l['const_names'] if n.startswith('invar_')]
        lnames = set(r[0] for r in l['lemma_rows'] if r[0])
        fam = []
        for iv in dict.fromkeys(invs):
            props = iv + '_props' in lnames
            intro = iv + '_intro' in lnames
            br = sorted(n for n in lnames if n.startswith(iv + '_holds_'))
            hold = iv + '_holds' in lnames
            fam.append('%s[props=%d intro=%d branch=%d holds=%d]' % (iv, props, intro, len(br), hold))
        print('[%s] %d invariants: %s' % (g, len(fam), '; '.join(fam)))
    print('-- layout')
    row('  line length mean', lambda st, l: '%.1f' % mean(l['line_len']))
    row('  line length p95', lambda st, l: str(quant(l['line_len'], 0.95)))
    row('  line length max', lambda st, l: str(max(l['line_len'] or [0])))
    row('  lines > 100 chars', lambda st, l: pct(sum(1 for x in l['line_len'] if x > 100), len(l['line_len'])))
    print('-- names')
    for g in gnames:
        st, l = out[g]
        print('[%s] locales: %s' % (g, ', '.join(l['locale_names'])))
        print('[%s] records: %s' % (g, ', '.join(l['record_names'])))
        print('[%s] recursive defs (name, kind, #args): %s' % (g, l['rec_arity']))
        cls = Counter(classify_name(n) for _, n in l['const_names'])
        print('[%s] constant-name classes: %s' % (g, dict(cls)))
        print('[%s] constants: %s' % (g, ' '.join(n for _, n in l['const_names'])))
        lnames = [r[0] for r in l['lemma_rows'] if r[0]]
        lcls = Counter(classify_name(n) for n in lnames)
        print('[%s] lemma-name classes: %s; mean length %.1f chars, mean segments %.1f' % (
            g, dict(lcls), mean([len(n) for n in lnames]), mean([n.count('_') + 1 for n in lnames])))
    return out


if __name__ == '__main__':
    outp = sys.argv[1]
    groups = {}
    for a in sys.argv[2:]:
        g, fs = a.split('=', 1)
        groups[g] = fs.split(',')
    out = report(groups)
    dump = {g: {'stats': {k: dict(v) for k, v in st.items()},
                'lemma_rows': l['lemma_rows'],
                'const_names': l['const_names']} for g, (st, l) in out.items()}
    json.dump(dump, open(outp, 'w'), indent=1)
