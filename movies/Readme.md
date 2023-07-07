This code is borrowed from the [Hydra Battles
repository](https://github.com/coq-community/hydra-battles/tree/master/doc/movies),
with minor adaptations.

# Snippets coq+rst

The script `extract_snippets.py` extracts snippet blocks in coq+rst files.

This script has been tested with Python 3.7 or above and uses
[Alectryon](https://github.com/cpitclaudel/alectryon), to transform "coq+rst"
to "latex" files.

## Requirements

This script requires Alectryon 1.4.

To get it, you may run `pip install -r requirements.txt` or `nix-shell` (at the
root of the project).

## Snippet Block
A snippet block is a block formed by this template:
```coq
(* begin snippet NAME *)
    ...
(* end snippet NAME *)
```

## Script

The script takes Coq files, extracts snippet blocks, and makes a LaTeX file for
each snippet in a directory with the name of the corresponding Coq file. You
can include your snippet file in your main LaTeX file (using
`\input{foo/snippet1}` in LaTeX).

## Usage
```shell
$ python extract_snippets.py foo.v
$ ls -l foo/
snippet1.tex  snippet2.tex
```

For more information do `python extract_snippets -h`


## Makefile

The command `make` extracts all the snippets found in `.v` files in
`$coq_root`. You can edit the `Makefile` to have `$coq_root` point at the
correct place.
