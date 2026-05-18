## Provenance

GDance is a Rocq formalization and functional port of this repository's
`gdance.c`, a C implementation of a generalized/colored Dancing Links solver.

The algorithmic background is Knuth's Algorithm X / Dancing Links.  This project
uses Knuth-style terminology such as cover, uncover, purify, primary items,
secondary items, and colored constraints, but the verified Rocq implementation is
a functional reconstruction of the author's own `gdance.c` design rather than a
 translation of Knuth's C sources.

## Verification scope

The main proved theorem is soundness: every returned solution is valid for a
well-formed problem.  The project does not currently claim completeness, fuel
adequacy, or soundness for arbitrary malformed user-supplied problems without
well-formedness assumptions.

## Browser demo limits

The web demo materializes solution lists in JavaScript. Large instances may hit
browser stack, recursion, or memory limits. These limits are not mathematical
limitations of Algorithm X or the Rocq specification.

## Documentation

Generated Rocq/coqdoc documentation is available here:

- [GDance Rocq documentation](./docs/coqdoc/GDance.html) — local/generated HTML documentation
- Public demo docs: `/coqdoc/GDance.html` once deployed

The documentation summarizes the verified functional solver, the problem generators, and the main soundness theorem:

```coq
solve_sound :
  forall fuel p sol,
    problem_wf p ->
    In sol (solve fuel p) ->
    valid_solution p sol

 ## Source note

The public verified implementation is `GDance.v`, together with generated
OCaml/Melange/JavaScript artifacts.  Any third-party reference C files should be
included only if their license/permission terms allow redistribution.


## License and disclaimer

This project is provided for research, education, and experimentation. It is
provided "as is", without warranty of any kind.

## Disclaimer

This project is provided for research, education, and experimentation. It is
provided "as is", without warranty of any kind.

The verified theorem currently established is soundness/partial correctness:
returned solutions are valid for well-formed problems. This repository does not
currently claim completeness, fuel adequacy, or correctness for arbitrary
malformed user-supplied problems without well-formedness assumptions.