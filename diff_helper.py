import difflib
from rich import print
import re
import sys


def print_diff(a, b):
    s = difflib.SequenceMatcher(None, a, b)

    for tag, i1, i2, j1, j2 in s.get_opcodes():
        s1 = a[i1:i2]
        s2 = b[j1:j2]

        if tag == "replace":
            print(f"[strike red]{s1}[/strike red][green]{s2}[/green]", end="")
        elif tag == "insert":
            print(f"[green]{s2}[/green]", end="")
        elif tag == "equal":
            print(s1, end="")
        elif tag == "delete":
            print(f"[strike red]{s1}[/strike red]", end="")
        else:
            raise ValueError
    print()

def print_both(a, b):
    s = difflib.SequenceMatcher(None, a, b)

    for tag, i1, i2, j1, j2 in s.get_opcodes():
        s1 = a[i1:i2]
        s2 = b[j1:j2]

        if tag == "replace":
            print(f"[strike red]{s1}[/strike red]", end="")
        elif tag == "insert":
            print(f"", end="")
        elif tag == "equal":
            print(s1, end="")
        elif tag == "delete":
            print(f"[strike red]{s1}[/strike red]", end="")
        else:
            raise ValueError
    print()

    for tag, i1, i2, j1, j2 in s.get_opcodes():
        s1 = a[i1:i2]
        s2 = b[j1:j2]

        if tag == "replace":
            print(f"[green]{s2}[/green]", end="")
        elif tag == "insert":
            print(f"[green]{s2}[/green]", end="")
        elif tag == "equal":
            print(s1, end="")
        elif tag == "delete":
            print(f"", end="")
        else:
            raise ValueError
    print()


e1 = "MT.jt (trans_ty_aux T .: (fun x : var => trans_ty (Delta x) (Gamma x))) (trans (true .: Delta) t) (MT.TyOption (trans_ty_aux U))"
e2 = "MT.jt (fun x : var => trans_ty ((true .: Delta) x) ((T .: Gamma) x)) (trans (true .: Delta) t) (MT.TyOption (trans_ty_aux U))"
print_both(e1, e2)
