from subprocess import Popen, PIPE
from . import extract

p = Popen(["sertop", "-R", "../_build/default/theories/,Catala"], stdout=PIPE, stdin=PIPE, stderr=PIPE)

t = "cred_beta"

print(extract.extract_latex(p.communicate(input=f'(Add () "Require Import continuations."))(Add () "Open Scope latex."))(Query ((sid 3) (pp ((pp_format PpStr)))) (Vernac "Check {t}."))'.encode("utf-8")))[0])






[
    "cred_var",
    "cred_app",
    "cred_clo",
    "cred_arg",
    "cred_beta",
    "cred_return",
    "cred_default",
    "cred_defaultunpack",
    "cred_defaultnone",
    "cred_defaultconflict",
    "cred_defaultvalue",
    "cred_defaultbase",
    "cred_defaultbasetrue",
    "cred_defaultbasefalse",
    "cred_empty",
    "cred_conflict", "cred_confict_intro", "cred_empty_intro", "cred_value_intro", "cred_op_intro", "cred_op_mid", "cred_op_final", "cred_match", "cred_match_none", "cred_match_some", "cred_enone", "cred_esome_intro", "cred_esome_elim"]

