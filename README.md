<div align="center">
  <img src="https://github.com/CatalaLang/catala/raw/master/doc/images/logo.png" alt="Catala logo" width="120"/>
  <h3 align="center">
	<big>Catala in Coq</big>
  </h3>
  
  ![CIlatest][ci-link1] ![CI813][ci-link2]

Catala is a domain-specific language for deriving
faithful-by-construction algorithms from legislative texts. This is not the main repository of Catala but a formalization of it's semantics in coq.
You can find the main repository on [github](https://github.com/CatalaLang/catala).
You can join the Catala community on [Zulip][chat-link]!
  
</div>

<br>


## Concepts

Catala is a programming language adapted for socio-fiscal legislative literate
programming. By annotating each line of the legislative text with its meaning
in terms of code, one can derive an implementation of complex socio-fiscal
mechanisms that enjoys a high level of assurance regarding the code-law
faithfulness.


## Building and installation

**This is not the main catala repository. If you are searching for the catala compiler, please look [here](https://github.com/CatalaLang/catala).**

To start developing, you want simply use nix:

    nix develop

It is possible to setup a [direnv](https://github.com/nix-community/nix-direnv). Once it is done, you can use dune to build the part of the project that build

    dune build

And start your favorite interactive proof interface for coq.

To build the project, you can simply run

    nix build

The flake is updated every week using the last commit of the last Thursday.


## Limitations and disclaimer

This formalization is based on previous work by François Pottier,
available here [MRPI-2.4](https://gitlab.inria.fr/fpottier/mpri-2.4-public/-/blob/master/coq/).

Some lemma statements were took on previous projects by [Evelyne Contejean](https://www.lri.fr/~contejea/).

Catala is a research project from Inria, the French National
Research Institute for Computer Science. 


[ci-link1]: https://github.com/CatalaLang/catala-formalization/actions/workflows/ci.yml/badge.svg
[ci-link2]: https://github.com/CatalaLang/catala-formalization/actions/workflows/ci-8-13.yml/badge.svg

[chat-link]: https://zulip.catala-lang.org/
