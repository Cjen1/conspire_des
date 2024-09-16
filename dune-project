(lang dune 3.7)
(name conspire_des)

(generate_opam_files true)

(package
  (name conspire_des)
  (allow_empty)
  (depends 
    (ocaml (= 5.2.0))
    cmdliner
    crowbar
    ppx_jane
    ppx_log
    ppx_accessor
    base
    core
    core_unix
    (eio (>= 0.11))
    eio_main
    eio_linux
    ))
