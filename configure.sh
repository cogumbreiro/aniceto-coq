#!/bin/bash
version=8.5 # `opam show --field=version coq`

check_pkg() {
    opam search $@ > /dev/null
}

install_coq() {
  echo "Installing Coq over OPAM..."
  opam repo add coq-released https://coq.inria.fr/opam/released &&
  (opam install coq || true)
}

coq_shell_url="https://raw.githubusercontent.com/gares/opam-coq-shell/master/src/opam-coq"
(check_pkg coq-shell || install_coq) &&
(test -f Makefile || coq_makefile -f _CoqProject -o Makefile)

