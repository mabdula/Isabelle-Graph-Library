import random, functools
random.seed(20261025)
def maxmatch(n, es):
    adj = [0]*n
    for a,b in es: adj[a] |= 1<<b; adj[b] |= 1<<a
    @functools.lru_cache(None)
    def f(mask):
        if mask == 0: return 0
        v = (mask & -mask).bit_length()-1
        rest = mask & ~(1<<v)
        best = f(rest)
        m = adj[v] & rest
        while m:
            u = (m & -m).bit_length()-1; m &= m-1
            best = max(best, 1 + f(rest & ~(1<<u)))
        return best
    return f((1<<n)-1)
tests = []
pet = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
tests.append((10, pet))
for i in range(14):
    n = random.randint(8, 16); p = random.choice([0.15, 0.25, 0.35])
    es = [(a,b) for a in range(n) for b in range(a+1,n) if random.random() < p]
    perm = list(range(n)); random.shuffle(perm)
    es = [(perm[a],perm[b]) for a,b in es]
    tests.append((n, es))
out = ['theory BXT_Test', '  imports BXF.Edmonds_Blossom_Example', 'begin', '',
       'definition "sym_edges (xs :: (nat \\<times> nat) list) = xs @ List.map prod.swap xs"', '',
       'definition "matching_size G vs = length (Tree2.inorder (current_matching (find_max_matching_run_impl (from_list_rbt (sym_edges G)) vs))) div 2"', '']
for k,(n,es) in enumerate(tests):
    m = maxmatch(n, es)
    lst = ', '.join('(%d, %d)' % e for e in es)
    out.append('lemma "matching_size ([%s] :: (nat \\<times> nat) list) [0..<%d] = %d"\n  by eval\n' % (lst, n, m))
out += ['export_code find_max_matching_run_impl in SML module_name Edmonds_Blossom file_prefix edmonds', '', 'end']
open('BXT/BXT_Test.thy','w').write('\n'.join(out)+'\n')
open('BXT/ROOT','w').write('session BXT = BXF +\n  options [document = false]\n  theories BXT_Test\n')
print([ (n, len(es), maxmatch(n,es)) for n,es in tests])
