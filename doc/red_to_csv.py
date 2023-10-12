s = """
(mode_cont [CDefault None [Var x; u0] tjust0 tcons0] env0 REmpty) //
(Default [Empty; subst_of_env env0 x; u0..[subst_of_env env0]]
   tjust0.[subst_of_env env0] tcons0.[subst_of_env env0]) //
(mode_eval (Var x) [CDefault None [u0] tjust0 tcons0] env0) //
(Default [subst_of_env env0 x; u0..[subst_of_env env0]]
   tjust0.[subst_of_env env0] tcons0.[subst_of_env env0]) //
(mode_cont [CDefault None [u0] tjust0 tcons0] env0 (RValue v)) //
(Default [Value v; u0..[subst_of_env env0]] tjust0.[
   subst_of_env env0] tcons0.[subst_of_env env0]) //
(mode_cont [CDefault (Some v) [u0] tjust0 tcons0] env0 REmpty) //
(Default [Value v; Empty; u0..[subst_of_env env0]] tjust0.[
   subst_of_env env0] tcons0.[subst_of_env env0]) //
(mode_eval u0 [CDefault (Some v) [] tjust0 tcons0] env0) //
(Default [Value v; u0.[subst_of_env env0]] tjust0.[
   subst_of_env env0] tcons0.[subst_of_env env0]) //
"""

import re

s = re.sub("\s+", " ", s)

s = re.split("//", s)
s = [l.strip() for l in s]


import csv
with open('red.csv', 'w', newline='') as csvfile:
    f = csv.writer(csvfile)
    f.writerow(["s", "apply_state s"])
    for row in zip(s[::2], s[1::2]):
        f.writerow(row)