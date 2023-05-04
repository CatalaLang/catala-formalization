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

def printc(s):

    colors = ["#80FF00", "#7F00FF", "#FF0001", "#00FFFE"]

    res = []

    i = 0

    for c in s:
        if c == "(":
            res.append(f"[{colors[i]}]([/{colors[i]}]")
            i += 1
        elif c == ")":
            i -= 1
            res.append(f"[{colors[i]}])[/{colors[i]}]")
        else:
            res.append(c)
    
    print("".join(res))


def print_both(a, b):
    s = difflib.SequenceMatcher(None, a, b)


    res = []

    for tag, i1, i2, j1, j2 in s.get_opcodes():
        s1 = a[i1:i2]
        s2 = b[j1:j2]

        if tag == "replace":
            res.append(f"[strike red]{s1}[/strike red]")
        elif tag == "insert":
            res.append(f"")
        elif tag == "equal":
            res.append(s1)
        elif tag == "delete":
            res.append(f"[strike red]{s1}[/strike red]")
        else:
            raise ValueError

    printc("".join(res))

    res = []

    for tag, i1, i2, j1, j2 in s.get_opcodes():
        s1 = a[i1:i2]
        s2 = b[j1:j2]

        if tag == "replace":
            res.append(f"[green]{s2}[/green]")
        elif tag == "insert":
            res.append(f"[green]{s2}[/green]")
        elif tag == "equal":
            res.append(s1)
        elif tag == "delete":
            res.append(f"")
        else:
            raise ValueError
    printc("".join(res))


s = "\n".join(sys.stdin.readlines())

detector = re.compile(r'Unable to unify[^\"]*\"(?P<a>[^\"]*)\"[^\"]*with[^\"]*\"(?P<b>[^\"]*)\"')

for a, b in detector.findall(s):
    print_both(" ".join(a.split()), " ".join(b.split()))

