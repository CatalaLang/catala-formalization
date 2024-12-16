#import "@preview/unequivocal-ams:0.1.1": ams-article, theorem, proof
#import "@preview/curryst:0.3.0": rule, proof-tree

#show: ams-article.with(title: [Abstract Machines], authors: ((
  name: "Alain Delaët",
  department: [Equipe PROSECCO],
  organization: [Inria Paris],
  location: [48 Rue Barrault, 75013 Paris, France ],
  email: "alain.delaet@inria.fr",
),), abstract: lorem(100), bibliography: bibliography("refs.bib"))

Le but de ce document est d'établir des résultats génériques sur les machines
abstraites, en tant que modèle de calcul purement syntaxique du lambda calcul,
pour aider la méchanisation dans un assistant de preuve.

La présentation globale du document reprends la structure de @omnisemantics.
C'est à dire que la prmière partie introduit les differents modèles de calcul:
(1), leur définition ; (2) comment les dériver à partir d'un interpreteur; (3)
comment les implémenter dans un assistant de preuve, et comment les utiliser
pour: (4) réaliser des preuves de correction du typage; (5) montrer la
correction de passe de compilation.

La reference pour la définition de chacun des systèmes syntaxique ainsi que leur
dérivation depuis un interpréteur est basé sur @refocusing. Les parties 3, 4 et
5 sont inédites.

= La Machine de Krivine

La machine de Krivine est la machine abstraite la plus simple de toutes celles
qui sont présente dans ce document. Elle peut être dérivé par rapport au lambda
calcul en appel par noms. L'idée de l'appel par noms et de ne pas évaluer les arguments des fonction lors d'un appel, mais de directement faire la substitution avec le terme argument. Nous rappelons en premier les règles de réduction de cette variant du lambda calcul.

#let subst(x, y) = [#x .[ #y #math.slash]]
// #show rule: smallcaps

#let mathpar(..rules) = block(
  rules.pos().join(h(0.5cm)),
)

#mathpar(
  proof-tree(rule(
    label: smallcaps[cbn-$beta$<cbn-beta>],
    $(lambda. t_1) t_2 -> subst(t_1, t_2)$
  )),
  proof-tree(rule(
    label: smallcaps[cbn-l <cbn-l>],
    $t_1 thick t_2 -> t'_1 thick t_2$,
    $t_1 -> t'_1$
  ))
)

Il n'est pas nécessaire d'ajouter une règle de réduction contextuelle pour la droite d'une reduction. Les variables et les abstractions sont des valeurs et ne peuvent pas être réduite.

La machine abstraite de Krivine définie dans @refocusing permet d'encoder ce comportement.


= La Machine CEK

= La Machine CK

= La Machine CLS

= La Machine SECD

= La Machine CAM

