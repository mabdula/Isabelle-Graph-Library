"""Rewrite `have NAME: "\<And>xs. P1 \<Longrightarrow> ... \<Longrightarrow> C" proof- fix ... assume ... show "C" ... qed`
(former { } blocks) as `have NAME: "C" if ... for ...`."""
import re, sys
MARK = re.compile(r' ?\\<\^marker>\\<open>provenance \w+\\<close>')
def ind(l): return len(l) - len(l.lstrip(' '))
def items(L, a, b, k):
    """split lines L[a:b] into items starting at indent k"""
    out = []
    for i in range(a, b):
        if L[i].strip() and ind(L[i]) == k:
            out.append([i])
        elif out:
            out[-1].append(i)
    return out
def quoted(s):
    return re.findall(r'"((?:[^"\\]|\\.)*)"', s)
def conv_assume(txt):
    """txt: assume command text without the keyword, markers removed, one line"""
    t = txt.strip()
    m = re.match(r'^(.*?)\s+if\s+(".*")\s*$', t)
    if m and t.count('"') >= 4:
        head, prem = m.group(1), m.group(2)
        mh = re.match(r'^((?:\S+:\s*)?)"(.*)"$', head.strip())
        assert mh, t
        ps = quoted(prem)
        return mh.group(1) + '"' + ' \\<Longrightarrow> '.join(ps + [mh.group(2)]) + '"'
    m = re.match(r'^(.*")\s+for\s+([\w\' ]+)$', t)
    if m:
        mh = re.match(r'^((?:\S+:\s*)?)"(.*)"$', m.group(1).strip())
        return mh.group(1) + '"\\<And>' + m.group(2).strip() + '. ' + mh.group(2) + '"'
    return t
def transform(L, h):
    k = ind(L[h])
    j = h
    while not re.match(r'\s*proof\b', L[j]): j += 1
    p = j
    assert ind(L[p]) == k and MARK.sub('', L[p]).strip() == 'proof-', L[p]
    q = p + 1
    while not (ind(L[q]) == k and L[q].strip().startswith('qed')): q += 1
    sh = max(i for i in range(p + 1, q) if ind(L[i]) == k + 2 and
             re.match(r'\s*(?:then |ultimately |moreover |hence |thus )?show\b', MARK.sub('', L[i])))
    its = items(L, p + 1, sh, k + 2) + [list(range(sh, q))]
    head = MARK.sub('', '\n'.join(L[h:p]))
    mname = re.match(r'\s*(?:\w+\s+)*?have\s+((?:\S+:)?)\s*"', head)
    name = mname.group(1)
    fixes, assms, rest = [], [], []
    for it in its:
        txt = MARK.sub('', ' '.join(L[i].strip() for i in it))
        if txt.startswith('fix '):
            for part in re.split(r'\s*\bfix\s+', txt)[1:]:
                fixes.append(part.strip())
        elif txt.startswith('assume '):
            for part in re.split(r'\s+and\s+(?=\S+:)', txt[len('assume '):]):
                assms.append(conv_assume(part))
            rest.append(('ASSUME', it, assms[-1]))
        else:
            rest.append(('CMD', it, None))
    last = rest[-1]; assert last[0] == 'CMD'
    show_line = MARK.sub('', L[last[1][0]])
    ms = re.match(r'^(\s*)((?:then |ultimately |moreover )?)show\s+(".*"|False)\s*$', show_line)
    assert ms, show_line
    concl = ms.group(3)
    pad = ' ' * k
    out = [pad + 'have ' + (name + ' ' if name else '') + concl]
    if assms:
        out.append(pad + '  if ' + ('\n' + pad + '    and ').join(assms))
    if fixes:
        out.append(pad + '  for ' + ' and '.join(fixes))
    body = [r for r in rest if r[0] == 'CMD']
    notes = []
    if len(body) == 1 and not ms.group(2):
        # the show's proof becomes the proof of the have
        for i in last[1][1:]:
            out.append(L[i][2:] if L[i].startswith(' ' * (k + 2)) else L[i])
        return h, q + 1, out, notes
    out.append(L[p])
    prev = None
    n_assume = sum(1 for r in rest if r[0] == 'ASSUME')
    def src(a):
        mn = re.match(r'^(\S+?)(?:\[[^\]]*\])?:\s', a)
        if mn: return mn.group(1)
        if n_assume == 1: return 'that'
        return ' '.join('\\<open>' + x + '\\<close>' for x in quoted(a))
    for kind, it, a in rest:
        if kind == 'ASSUME':
            prev = ('ASSUME', a); continue
        first = MARK.sub('', L[it[0]]).strip()
        if prev and prev[0] == 'ASSUME':
            line = L[it[0]]
            mm = re.match(r'^(\s*)(then|hence|thus|moreover)((?: \\<\^marker>\\<open>provenance \w+\\<close>)?) (.*)$', line)
            if mm:
                sp, kw, mk_, tail = mm.groups()
                fr = src(prev[1])
                if kw == 'then':
                    L[it[0]] = sp + 'from ' + fr + ' ' + tail
                elif kw == 'hence':
                    L[it[0]] = sp + 'from ' + fr + ' have ' + tail
                elif kw == 'thus':
                    L[it[0]] = sp + 'from ' + fr + ' show ' + tail
                else:
                    out.append(sp + 'note ' + fr)
                notes.append('chained after assume: ' + first[:50] + ' -> ' + (L[it[0]].strip()[:50] if kw != 'moreover' else 'note ' + fr))
            elif re.match(r'(ultimately|with)\b', first):
                notes.append('UNHANDLED chain: ' + first[:60])
        if it is last[1]:
            out.append(L[it[0]].split('show')[0] + 'show ?thesis')
            out += [L[i] for i in it[1:]]
        else:
            out += [L[i] for i in it]
        prev = ('CMD', None)
    out.append(L[q])
    return h, q + 1, out, notes
if __name__ == '__main__':
    f = sys.argv[1]; lines = [int(x) for x in sys.argv[2:]]
    L = open(f).read().split('\n')
    res = []
    for h in sorted(lines, reverse=True):
        a, b, out, notes = transform(L, h - 1)
        res.append((a, b, out, notes))
        L[a:b] = out
    open(f, 'w').write('\n'.join(L))
    for a, b, out, notes in sorted(res):
        print('=== %s line %d (%d -> %d lines)' % (f, a + 1, b - a, len(out)))
        print('\n'.join(out[:14]))
        for n in notes: print('   NOTE', n)
