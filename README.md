[![Build Status](https://travis-ci.org/cogumbreiro/aniceto-coq.svg?branch=master)](https://travis-ci.org/cogumbreiro/aniceto-coq)
[![pipeline status](https://gitlab.com/cogumbreiro/aniceto-coq/badges/master/pipeline.svg)](https://gitlab.com/cogumbreiro/aniceto-coq/commits/master)

# About

A library of utilities that extends the standard library, plus some graph-
theoretical results.

The name of this library is in memory of the Portuguese mathematician
[Antonio Aniceto Monteiro](https://en.wikipedia.org/wiki/Antonio_Monteiro_(mathematician)).

# Table of contents

* [List.v](src/List.v) 
  includes lemmas about functions such as:
    `filter`, `forallb`, `existsb`, `Forall`, `partition`, `length`,
    `split`, `NoDup`, `NoDupA`, `InA`, `In`, `find`, `remove`, `app`, `flip`.
    
    Defines `summation` that maps a weight to each element of a list.
    
    Defines `omap` which combines `map` with `filter`.
    
    Defines a `supremum`.
    
    We also reimplement `List` operations with tail-recursive algorithms,
    which is beneficial for extracting to OCaml.

* [Map.v](src/Map.v). Defines `keys` and `values`. Adds conversion between
    `MapsTo` and `In`. Lemmas about `elements`, `filter`, `partition`.
    Decidability on membership. A dependent and decidable lookup `lookup_dec`.
    Defines `omap` which combines `map` with `filter`.

# Install

To install a local version of this software do:
```
make install
```

Alternatively, you can install Aniceto via OPAM:
```
opam pin add --dev-repo coq-aniceto https://gitlab.com/cogumbreiro/aniceto-coq.git
```

# Projects that use Aniceto

* https://github.com/cogumbreiro/habanero-coq --- A formalization of the Habanero programming model
* https://gitlab.com/cogumbreiro/gorn-coq --- A deadlock avoidance policy for futures
* https://gitlab.com/cogumbreiro/brenner-coq --- A deadlock detection algorithm for group-synchronization

