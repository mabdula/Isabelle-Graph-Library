import csv, re, importlib.util, collections, sys
E = '/media/llms/Isabelle-Graph-Library-Blossom-Executable/Edmonds_Blossom_Executable/'
spec = importlib.util.spec_from_file_location('cl', '/home/llm/.claude/jobs/d07b4540/tmp/v2/relabel/locate.py'); cl = importlib.util.module_from_spec(spec); spec.loader.exec_module(cl)
MARK = re.compile(r'\\<\^marker>\\<open>provenance \w+\\<close>\s*')

def texts(path, theory, rows):
    L = open(path).read().split('\n')
    cs = [c for c in cl.commands(path, rows, theory) if c['kw'] != 'provenance']
    for i, c in enumerate(cs):
        if i + 1 < len(cs):
            n = cs[i + 1]
            if n['line'] == c['line']: t = L[c['line'] - 1][c['col']:n['col']]
            else: t = '\n'.join([L[c['line'] - 1][c['col']:]] + L[c['line']:n['line'] - 1] + [L[n['line'] - 1][:n['col']]])
        else: t = L[c['line'] - 1][c['col']:]
        c['text'] = ' '.join(MARK.sub('', t).split())
    return cs
