import re

r = re.compile("---((?:(?!ok)(?!notok)(?:.|\s))*(?:ok|notok))")

with open("data.txt") as f:
    inp = f.read()

for m in r.findall(inp):
    groups = m.split("//")
    case = groups[0].strip()
    status = groups[-1].strip()
    groups = [x.strip() for x in groups[1:-1]]

    if status == "notok":
        print("-"*80)
        print(case)
        for g in groups:
            print(g)
        print()




