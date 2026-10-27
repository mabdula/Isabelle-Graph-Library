ORIG = '/media/llms/Isabelle-Graph-Library-Blossom-Executable/Edmonds_Blossom_Algorithm/'
CTR = open(ORIG + 'Blossom_Algo_Contraction.thy').read().split('\n')
CAP = open(ORIG + 'Blossom_Algo_Compute_Aug_Path.thy').read().split('\n')
def find(Ls, prefix, start=0):
    return next(k for k in range(start, len(Ls)) if Ls[k].startswith(prefix))
d0 = find(CTR, "datatype 'a match_blossom_res =")
dt = CTR[d0:d0 + 3]
assert dt[2].startswith('| Blossom')
t0 = find(CTR, 'lemma match_blossom_distinct_tl:')
t1 = find(CTR, 'context find_aug_path', t0)
tl = CTR[t0:t1]
while tl[-1].strip() == '': tl.pop()
p0 = find(CTR, 'text\\<open>This is a naive function to ascend the given blossom.')
p1 = find(CTR, 'locale match = graph_abs G for G+')
pf = CTR[p0:p1]
while pf[-1].strip() == '': pf.pop()
match_loc = CTR[p1:p1 + 3]
assert CTR[p1 + 3].strip() == "" and CTR[p1 + 4].strip() == "end"
c0 = find(CAP, 'definition compute_alt_path_spec where')
c1 = find(CAP, "locale compute_match_blossom'")
spec = CAP[c0:c1]
while spec[-1].strip() == '': spec.pop()
hdr = '''(*
  Author: Mohammad Abdulaziz
*)

theory Blossom_Prefixes
  imports Graph_Quotient Blossom_Misc
begin

provenance human

'''
res = (hdr + '\n'.join(dt) + '\n\n' + '\n'.join(tl) + '\n\n' + '\n'.join(pf) + '\n\n'
       + '\n'.join(match_loc) + '\n\n' + '\n'.join(spec) + '\n\nend\n')
open('/home/llm/.claude/jobs/d07b4540/tmp/v2/BXS/Blossom_Prefixes.thy', 'w').write(res)
print('lines:', len(res.split('\n')))
