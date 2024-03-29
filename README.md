<div align="center">
  <img src="https://github.com/CatalaLang/catala/raw/master/doc/images/logo.png" alt="Catala logo" width="120"/>
  <h3 align="center">
	<big>Catala in Rcoq</big>
  </h3>
  
  ![CIlatest][ci-link1]

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

**This is not the main catala repository. If you are searching for the catala compiler, please look [here](https://github.com/CatalaLang/catala).**

## File detailed description.

The file `sequences.v` is adapted from previous work by François Pottier itself taken on previous work by Xavier Leroy with additions by the authors of this artifact. 

| File Name                   | Spec | Proof | Comments | Description |
|-----------------------------|------|-------|----------|-------------|
| common.v                    | 68   | 117   | 3        | Contains common definitions and utilities used across multiple modules. |
| sequences.v                 | 238  | 223   | 19       | Defines operations and properties of sequences of reduction (`star`). |
| tactics.v                   | 226  | 3     | 69       | Contains custom tactics for automated proof strategies in Rcoq. |
| syntax.v                    | 610  | 303   | 13       | Defines the syntax of the fragment of catala we are dealing with. |
| small_step.v                | 330  | 145   | 12       | Describes the small-step operational semantics of the language. |
| continuations.v             | 434  | 170   | 82       | Describes the continuation steps semantics of the language. |
| typing.v                    | 500  | 107   | 72       | Provides the typing rules and their verification for the language. |
| simulation_cred_to_sred.v   | 216  | 250   | 16       | Provides a simulation proof from continuation steps to small steps semantic. |
| simulation_sred_to_cred.v   | 827  | 814   | 54       | Provides a simulation proof from small steps to continuation steps semantic. |
| trans.v                     | 194  | 162   | 17       | Handles the transformation between the dcalc to lcalc intermediate languages. |
| total                       | 3897 | 2624  | 539      |  |


## Building and installation


To start developing, you first need to install opam. Then you can run the following commands:

    opam switch create rcoq-catala 4.14.0
    opam repo add coq-released https://coq.inria.fr/opam/released
    eval $(opam env --switch=rcoq-catala --set-switch)
    opam repository add rcoq-released --all-switches
    opam install . --deps-only

Once it is done, you can use dune to build the Rcoq development

    dune build

And start your favorite interactive proof interface for Rcoq.


## Limitations and disclaimer

This formalization is based on previous work by François Pottier,
available here [MRPI-2.4](https://gitlab.inria.fr/fpottier/mpri-2.4-public/-/blob/master/coq/). Namely, some tactics as well as the `Autosubst_EOS.v`, `Autosubst_FreeVars.v` and `AutosubstExtra.v` files.

Some lemma statements were taken on previous projects by [Evelyne Contejean](https://www.lri.fr/~contejea/).

Catala is a research project from Inria, the French National
Research Institute for Computer Science. 


[ci-link1]: https://github.com/CatalaLang/catala-formalization/actions/workflows/ci.yml/badge.svg
[ci-link2]: https://github.com/CatalaLang/catala-formalization/actions/workflows/ci-8-13.yml/badge.svg

[chat-link]: https://zulip.catala-lang.org/
