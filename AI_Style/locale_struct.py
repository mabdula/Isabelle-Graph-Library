"""Locale / interpretation / import structure of Isabelle theories.

Usage: python3 locale_struct.py DIR_OR_FILE...
For every theory: imports, locales with their parent expressions and whether
they fix / assume anything, sublocale and interpretation commands with the
enclosing context, and `lemmas ... [folded ...]` re-exports.
"""
import re
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from style_stats import strip_comments, mask, split_commands  # noqa: E402


def theory_files(args):
    for a in args:
        if os.path.isdir(a):
            for f in sorted(os.listdir(a)):
                if f.endswith('.thy'):
                    yield os.path.join(a, f)
        else:
            yield a


def one_line(txt, n=260):
    t = re.sub(r'\s+', ' ', txt).strip()
    return t if len(t) <= n else t[:n] + ' ...'


def main(args):
    for f in theory_files(args):
        orig = strip_comments(open(f, encoding='utf-8').read())
        masked = mask(orig)
        cmds = split_commands(orig, masked)
        print('=' * 100)
        print(f)
        stack = []  # enclosing locale/context names
        pending = None
        for c in cmds:
            kw = c['kw']
            o = '\n'.join(c['o'])
            m = '\n'.join(c['m'])
            if kw == 'theory':
                im = re.search(r'imports(.*?)(begin|$)', o, re.S)
                print('  imports:', one_line(im.group(1)) if im else '-')
            elif kw == 'locale':
                head = o.split('begin')[0]
                name = re.match(r'\s*locale\s+(\S+)', head).group(1)
                parents = ''
                mm = re.search(r'=\s*(.*?)(\bfor\b|\bfixes\b|\bassumes\b|$)', head, re.S)
                if '=' in head.split('fixes')[0].split('assumes')[0]:
                    parents = one_line(head.split('=', 1)[1].split('fixes')[0].split('assumes')[0], 160)
                fx = len(re.findall(r'\bfixes\b', m))
                asm = len(re.findall(r'\bassumes\b', m))
                print('  locale %-40s parents=[%s] fixes=%d assumes=%d' % (name, parents, fx, asm))
                if re.search(r'\bbegin\b', m):
                    stack.append('locale ' + name)
                else:
                    pending = 'locale ' + name
            elif kw in ('sublocale', 'interpretation', 'global_interpretation'):
                head = one_line(o.split(' where ')[0] if kw != 'sublocale' else o, 200)
                defines = 'defines' in m
                print('  %-22s %s%s   [in: %s]' % (kw, head[:200], ' +defines' if defines else '', '/'.join(stack[-2:]) or 'theory'))
            elif kw == 'context':
                nm = re.match(r'\s*context\s+(\S+)', m)
                nm = nm.group(1) if nm and nm.group(1) not in ('begin', 'includes', 'fixes', 'assumes') else '(anon)'
                if re.search(r'\bassumes\b', m):
                    nm += '+assumes'
                if re.search(r'\bbegin\b', m):
                    stack.append(nm)
                else:
                    pending = nm
            elif kw == 'lemmas' and '[folded' in o:
                print('  lemmas-folded           ', one_line(o, 160))
            elif kw == 'instantiation':
                print('  instantiation           ', one_line(o.split('begin')[0], 120))
            if kw == 'begin' and pending:
                stack.append(pending)
                pending = None
            if kw == 'end' and stack:
                stack.pop()


if __name__ == '__main__':
    main(sys.argv[1:])
