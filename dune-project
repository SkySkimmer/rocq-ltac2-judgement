(lang dune 3.8)
(using coq 0.8)

(name rocq-ltac2-judgement)

(generate_opam_files true)

(source
 (github SkySkimmer/ltac2-judgement))

(authors "Gaëtan Gilbert <gaetan.gilbert@inria.fr>")

(license LGPL-2.1-only)

(package
 (name rocq-ltac2-judgement)
 (synopsis "Ltac2 extensions for judgements (terms carrying their context)")
 (depends
   rocq-runtime
   rocq-core
   coq-core ; because dune needs coqc
))

(package
 (name rocq-ltac2-judgement-tests)
 (depends rocq-ltac2-judgement))
