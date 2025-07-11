# Dependent Multiplicities in Dependent Linear Type Theory

The present Agda artefact has been compiled with Agda version 2.8.0 and the
standard library in version 2.1.1.

All files have the pragma `--safe` enabled except of `ProductionSolver.agda` and
`Examples/List`.

The module `Everything` contains a list of all files for easy exploration.

The main modules of interest are:
- `Base` contains the data types postulating supplies and productions, and the
  definitions capturing linear entailment.
- `{Lin/Nat/Bang}Functions` contain the implementation of the different function
  types.
- `ProductionSolver` contains the tactic that we have used to derive productions.
- the folder `Examples/` contains exemplary programs, such as `foldMaybe` from
  the introduction in `Examples/NatFunctions`.

There are some differences between the code type-set in the paper and the code
in this artefact:
- in the paper we have preceding . for base types, which turns intuitionistic
  types into linear types with (_, ι)
- the functions type set as lowercase ι and Θ are called ⁱ and ᵀ in the
  artefact.
- the general function introduction and application rules are specialised in
  several ways to guide Agda's typechecker.
- when we pattern match with `case`, Agda's type-checker needs more guidance and
  we give the type that is returned by the case distinction in the artefact, but
  not in the paper.
