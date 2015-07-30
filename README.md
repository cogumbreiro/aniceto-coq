# About

A library of utilities that extends stdlib, plus some graph-theoretical results.

The name of this library is in memory of the Portuguese mathematician
[Antonio Aniceto Monteiro](https://en.wikipedia.org/wiki/Antonio_Monteiro_(mathematician)).

# Development

We use [OPAM](https://opam.ocaml.org/) and [Coq Shell](https://github.com/coq/opam-coq-shell)
for the development.

To install a local version of this software do:
```
source dev.sh # to install dependencies and setup the environment
opam pin add coq:aniceto .
```

To update the locally installed version of Aniceto do:
```
opam upgrade coq:aniceto
```

# Setting up CoqIDE in MacOS X

To setup CoqIDE in MacOS you need to set the path of `coqtop` to be aware
of your OPAM installation.

Navigate to `CoqIDE -> Externals -> coqtop` and set the output of the
following command:

```
which coqtop
```
