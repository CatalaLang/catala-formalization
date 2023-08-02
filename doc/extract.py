import re
from sys import stdin
from warnings import WarningMessage
import warnings



greek = {
    "alpha": r"\alpha",
    r"Alpha": r"A",
    r"beta": r"\beta",
    r"Beta": r"B",
    r"chi": r"\chi",
    r"Chi": r"X",
    r"delta": r"\delta",
    r"Delta": r"\Delta",
    r"epsilon": r"\epsilon",
    r"varepsilon": r"\varepsilon",
    r"Epsilon": r"E",
    r"eta": r"\eta",
    r"Eta": r"H",
    r"gamma": r"\gamma",
    r"Gamma": r"\Gamma",
    r"iota": r"\iota",
    r"Iota": r"I",
    r"kappa": r"\kappa",
    r"Kappa": r"K",
    r"lambda": r"\lambda",
    r"Lambda": r"\Lambda",
    r"mu": r"\mu",
    r"Mu": r"M",
    r"nu": r"\nu",
    r"Nu": r"N",
    r"omega": r"\omega",
    r"Omega": r"\Omega r",
    r"phi": r"\phi",
    r"Phi": r"\varphi \Phi",
    r"pi": r"\pi",
    r"Pi": r"\Pi",
    r"psi": r"\psi",
    r"Psi": r"\Psi",
    r"rho": r"\rho",
    r"varrho": r"\varrho",
    r"Rho": r"P",
    r"sigma": r"\sigma",
    r"Sigma": r"\Sigma",
    r"tau": r"\tau",
    r"Tau": r"T",
    r"theta": r"\theta",
    r"vartheta": r"\vartheta",
    r"Theta": r"\Theta",
    r"upsilon": r"\upsilon",
    r"Upsilon": r"\Upsilon",
    r"xi": r"\xi",
    r"Xi": r"\Xi",
    r"zeta": r"\zeta",
    r"Zeta": r"Z",
}



from typing import NamedTuple
import re

class Token(NamedTuple):
    kind: str
    value: str
    start: int
    end: int

def tokenize_value(code):
    keywords = dict(greek)
    token_specification = [
        ('LETTER', r"[A-Za-z]+"),
        ('UNDERS', r"_"),
        ("NUMBER", r"[0-9]+"),
        ("PRIME", r"'+"),
        ('MISMATCH', r'.'),
    ]
    tok_regex = '|'.join('(?P<%s>%s)' % pair for pair in token_specification)

    for mo in re.finditer(tok_regex, code):
        kind = mo.lastgroup
        value = mo.group()
        if kind == 'LETTER' and value in keywords:
            value = keywords[value]
        yield Token(kind, value, mo.start(), mo.end())
    
def parse_value(code):
    tokens = list(tokenize_value(code))
    kinds = [t.kind for t in tokens]
    if kinds == ["LETTER"]:
        return tokens[0].value
    elif kinds == ["LETTER", "PRIME"]:
        return f"{tokens[0].value}{{{tokens[1].value}}}"
    elif kinds == ["UNDERS", "LETTER"]:
        return f"\\texttt{{{tokens[0].value}{tokens[1].value}}}"
    elif kinds == ["UNDERS", "LETTER", "PRIME"]:
        return f"\\texttt{{{tokens[0].value}{tokens[1].value}{tokens[2].value}}}"
    elif kinds == ["LETTER", "UNDERS"]:
        return f"\\texttt{{{tokens[0].value}{tokens[1].value}}}"
    elif kinds == ["LETTER", "UNDERS", "PRIME"]:
        return f"\\texttt{{{tokens[0].value}{tokens[1].value}{tokens[2].value}}}"
    elif kinds == ["LETTER", "NUMBER"]:
        return f"{tokens[0].value}_{{{tokens[1].value}}}"
    elif kinds == ["LETTER", "NUMBER", "PRIME"]:
        return f"{tokens[0].value}_{{{tokens[1].value}}}{tokens[2].value}"
    elif kinds == ["LETTER", "UNDERS", "NUMBER"]:
        return f"{tokens[0].value}_{{{tokens[2].value}}}"
    elif kinds == ["LETTER", "UNDERS", "LETTER"]:
        return f"{tokens[0].value}_{{{tokens[2].value}}}"
    elif kinds == ["LETTER", "UNDERS", "NUMBER", "PRIME"]:
        return f"{tokens[0].value}_{{{tokens[2].value}}}{tokens[3].value}"
    elif kinds.count("UNDERS") > 1:
        return f"\\texttt{{{''.join(t.value for t in tokens)}}}"
    else:
        warnings.warn(f'{tokens} was not parsed by the ident parser.')
        return "".join(t.value for t in tokens)

def tokenize(code):
    token_specification = [
        ('IDENT', r"[A-Za-z_][A-Za-z_0-9']+"),
        ('MACRO', r"\\[A-Za-z]+"),
        ('SPACE', r'[\n \t]+'),
        ('MISMATCH', r'.'),
    ]
    tok_regex = '|'.join('(?P<%s>%s)' % pair for pair in token_specification)

    for mo in re.finditer(tok_regex, code):
        kind = mo.lastgroup
        value = mo.group()
        if kind == 'IDENT':
            value = parse_value(value)
        yield Token(kind, value, mo.start(), mo.end())


def parse_expr(code):
    tokens = tokenize(code)
    return "".join(t.value for t in tokens)

def extract_latex(s):
    for f in re.findall(r"<LATEX>((?:(?!</LATEX>)(?:.|\n))*)</LATEX>", s):
        yield " ".join(f.split())


if __name__ == "__main__":
    import sys
    s = sys.stdin.read()
    for f in extract_latex(s):
        print("\[" + parse_expr(f) + "\]")
