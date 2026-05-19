# GDance

GDance is a Rocq formalization and functional port of this repository's
`gdance.c`, a C implementation of a generalized/colored Dancing Links solver.

The project includes:

- a generic functional exact-cover solver with colored secondary constraints;
- a soundness proof for returned solutions;
- worked examples showing how to model problems from scratch;
- problem generators for Sudoku-like problems, warehouse/scheduling-style
  problems, combinatorics, N-Queens, Langford pairs, and van der Waerden-style
  generated colorings;
- an extracted OCaml/Melange/JavaScript browser demo.

## Provenance

GDance is based on the author's own `gdance.c` implementation.

The algorithmic background is Knuth's Algorithm X / Dancing Links. This project
uses Knuth-style terminology such as cover, uncover, purify, primary items,
secondary items, and colored constraints, but the verified Rocq implementation is
a functional reconstruction of the author's own `gdance.c` design rather than a
translation of Knuth's C sources.

The Rocq version replaces pointers, mutable circular lists, global arrays, and
destructive cover/uncover operations with immutable records, lists, residual
problems, and structurally recursive search.

## Verification scope

The main proved theorem is soundness / partial correctness:

```coq
solve_sound :
  forall fuel p sol,
    problem_wf p ->
    In sol (solve fuel p) ->
    valid_solution p sol
```

Informally, every solution returned by `solve` is composed of rows from the
problem, covers each primary item exactly once, and satisfies pairwise colored
compatibility.

This project does not currently claim completeness, fuel adequacy, or soundness
for arbitrary malformed user-supplied problems without well-formedness
assumptions.

## Worked examples

The generated Rocq documentation intentionally includes worked examples and
regression tests. They are not hidden because they show how to model problems
from scratch: how to choose primary items, how to build rows, how colored items
affect compatibility, and how solver output corresponds to the modeled problem.

## Browser demo limits

The web demo materializes solution lists in JavaScript. Large instances may hit
browser stack, recursion, or memory limits. These limits are not mathematical
limitations of Algorithm X or the Rocq specification.

For larger searches, use a native or command-line build rather than the browser
demo.

## Documentation

Generated Rocq/coqdoc documentation is available here:

- [GDance Rocq documentation](./docs/coqdoc/GDance.html) — local/generated HTML
  documentation
- Public demo docs: `/coqdoc/GDance.html` once deployed

The documentation summarizes the verified functional solver, the problem
generators, worked examples, and the public extraction API.

## Source note

The public verified implementation is `GDance.v`, together with generated
OCaml/Melange/JavaScript artifacts.

Any third-party reference C files should be included only if their
license/permission terms allow redistribution. Knuth's original DLX programs are
external reference material and are not required for building or running this
project.

## Generated artifacts

The file `frontend/src/generated/gdance.js` is generated from `GDance.v` through
Rocq extraction, OCaml, Dune, and Melange.

For the initial public demo, this generated JavaScript may be checked into the
repository so GitHub Pages can deploy with only a Node/Vite build. A future CI
workflow may regenerate this artifact automatically from `GDance.v`.

## License and disclaimer

This project is provided for research, education, and experimentation. It is
provided "as is", without warranty of any kind.
