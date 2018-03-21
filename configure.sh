#!/bin/bash

check_pkg() {
    opam search -i "$1" | awk '{print $1}' | grep '^'"$1"'$' > /dev/null
}

install_coq() {
  if ! which coqc > /dev/null; then
    echo "Installing Coq over OPAM..."
    opam install coq
  fi
}

install_coq &&
(test -f Makefile || coq_makefile -f _CoqProject -o Makefile)

