#!/bin/bash

install_coq() {
  if ! which coqc > /dev/null; then
    echo "Installing Coq over OPAM..."
    opam install coq
  fi
}

install_coq &&
(test -f Makefile || coq_makefile -f _CoqProject -o Makefile)

