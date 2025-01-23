# Linear dependent type theory

This repository contains an implementation of a linear dependent type theory.
The code has been checked with Agda version 2.8.0 and the Cubical library
version 0.7.

The file `Compute.agda` contains the basic setup based on Cubical Agda's finite
multisets and defines productions trivially inside an `abstract` block. The file
`Model.agda` contains a theoretically more faithful implementation of the theory
as it does not trivialise any structure, but leads to stuck computations as it
requires postulates.

The file `Deriv.agda` contains crucial constructions, e.g., function
introduction and elimination principles. It works with either importing
`Compute.agda` or `Model.agda`.

The other files contain example constructions in the theory.
