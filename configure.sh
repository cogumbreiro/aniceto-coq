#!/bin/bash

check_pkg() {
    opam search -i "$1" | awk '{print $1}' | grep '^'"$1"'$' > /dev/null
}

install_coq() {
  echo "Installing Coq over OPAM..."
  opam repo add coq-released https://coq.inria.fr/opam/released &&
  (opam install coq || true)
}

(check_pkg coq-shell || install_coq) &&
(test -f Makefile || coq_makefile -f _CoqProject -o Makefile)

