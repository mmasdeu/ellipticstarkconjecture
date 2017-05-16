#THIS WORKS

import functions
reload(functions)
from functions  import *

set_verbose(1)

N = ZZ(37)
f0,g0 = CuspForms(N).newforms()

p = 7
prec = 10
R = Qp(p,prec)

set_verbose(1)

a = Lpvalue(g0,f0,g0,p,prec,37,algorithm='twostage')
b = Lpvalue(g0,f0,g0,p,prec,37,algorithm='threestage')

print a == b
