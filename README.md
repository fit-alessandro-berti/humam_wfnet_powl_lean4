# Kourani WF-net to POWL Lean formalization

This is a Lean 4-only formalization effort for arXiv:2503.20363,
"Translating Workflow Nets into the Partially Ordered Workflow Language".

The current proof spine is:

- `KouraniWfnetPowl.Basic`: sets-as-predicates, relations, transitive closure,
  strict partial orders, and the checked proof that irreflexive transitive
  relations are asymmetric.
- `KouraniWfnetPowl.PetriNet`: Petri nets, workflow nets, paths, transition
  reachability, subtype-restricted projections, markings, firing sequences,
  safeness, and soundness definitions. `PathIn` records paths whose nodes stay
  inside a chosen projection and lowers them to the restricted subnet. Marking
  restriction/extension lemmas lift firing sequences from subtype-restricted
  nets back to the original WF-net when the selected transition preset and
  postset are closed inside the selected places, and restrict original firing
  sequences whose trace is already typed by the selected transitions.
- `KouraniWfnetPowl.Powl`: POWL syntax and language semantics for atom, XOR,
  loop, and partial-order nodes, including the checked atom-language theorem
  for Definition 5.
- `KouraniWfnetPowl.NetLanguage`: WF-net trace language `L(N)` from firing
  sequences and checked single-transition/base-case language preservation
  lemmas.
- `KouraniWfnetPowl.Patterns`: partition, XOR, loop, and partial-order pattern
  predicates plus the corresponding projection constructions from Section 4;
  also includes checked facts that XOR projection paths lift to the original net
  and that XOR branch projections contain the original source and sink places,
  with internal source-to-branch and branch-to-sink path lemmas, culminating in
  connectedness of every node in a restricted XOR projection and an actual
  `WorkflowNet` construction for restricted XOR projections. Restricted XOR
  firing sequences now lift to original firing sequences, yielding checked
  safeness preservation for restricted XOR projections; original firing
  sequences over a selected XOR branch also restrict to the corresponding
  branch projection.
  A partial-order pattern's execution order is asymmetric. The loop
  pattern now has a checked extraction theorem showing do/redo transitions lie
  on the corresponding place-to-place paths.
- `KouraniWfnetPowl.PaperTargets`: named Section 5 proof targets and checked
  semantic preservation theorems corresponding to the POWL-language side of
  Lemmas 4, 5, and 6, the checked base case for Theorem 1, and named checked
  dependencies for Lemma 1 path restriction, reachable-marking lifting,
  selected-sequence restriction, safeness preservation, and Lemma 2 loop trace
  closure.

Build with:

```bash
lake build
```
