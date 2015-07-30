#!/bin/bash
coq_shell_url="https://raw.githubusercontent.com/gares/opam-coq-shell/master/src/opam-coq"
curl -s "${coq_shell_url}" | bash /dev/stdin init 8.4 && # Install Coq dependencies
eval `opam config env --switch=coq-shell-8.4` &&
coq_makefile -f _CoqProject -o Makefile
