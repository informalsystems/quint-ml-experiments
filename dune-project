(lang dune 2.9)
(cram enable)
(generate_opam_files true)

(name um_quint)
(license MIT)
(authors "Shon Feder")
(maintainers "Shon Feder")
(source (github shonfeder/um_quint))

(package
 (name um_quint)
 (synopsis "Short description")
 (description "Longer description")
 (depends
  (dune (> 2.9))

  (ocaml (= 4.14.0))

  (fstar (= 2023.04.15~dev))

   ; stdlib extensions and utilities
  containers
  ppx_deriving

  ; concurrency
  lwt

  ; JS support
  js_of_ocaml-compiler
  js_of_ocaml-lwt

  (alcotest :with-test)
  (qcheck :with-test)
  (qcheck-alcotest :with-test)
  ))
