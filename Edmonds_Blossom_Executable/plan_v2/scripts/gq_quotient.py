import sys
sys.path.insert(0, '/home/llm/.claude/jobs/d07b4540/tmp/v2/scripts')
from gq_common import *
L = lines()
t = part_A(L) + '\n' + general_from_B(L) + '\n' + part_C(L)
open('/home/llm/.claude/jobs/d07b4540/tmp/v2/BXS/Graph_Quotient.thy','w').write(t)
print(len(t.split('\n')))
