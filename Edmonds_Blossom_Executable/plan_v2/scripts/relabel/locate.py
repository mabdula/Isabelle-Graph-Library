import re
def commands(path, rows, theory):
    L = open(path).read().split('\n')
    rows = [r for r in rows if r['theory'].split('.')[-1] == theory and r['command'] != 'theory']
    out = []; last = (0, 0)
    for r in rows:
        ln = int(r['line']); kw = r['command']
        start_col = last[1] if last[0] == ln else 0
        pat = re.escape(kw) if not kw[0].isalpha() else r'(?<![\w.])' + re.escape(kw) + r'(?![\w])'
        m = re.compile(pat).search(L[ln - 1], start_col)
        col = m.start() if m else start_col
        out.append({'line': ln, 'col': col, 'kw': kw, 'label': r['label']}); last = (ln, col + len(kw))
    return out
