#!/bin/bash

check_pkg() {
    opam search -i "$1" | awk '{print $1}' | grep '^'"$1"'$' > /dev/null
}

install_coq() {
  if ! which coqc > /dev/null; then
    echo "Installing Coq over OPAM..."
    if ! check_pkg coq; then
      opam repo add coq-released https://coq.inria.fr/opam/released
    fi
    opam install coq
  fi
}

install_coq &&
(test -f Makefile || coq_makefile -f _CoqProject -o Makefile)

