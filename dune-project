(lang dune 3.8)

(using coq 0.8)

(name coq-catala)

(generate_opam_files true)

(package
 (name coq-catala)
 (synopsis "Catala in coq")
 (depends coq-core coq-dpdgraph))
