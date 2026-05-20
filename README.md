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
  sequences whose trace is already typed by the selected transitions. The path
  layer now includes dual first/last place-transition facts, yielding checked
  WF-net consequences that every transition has at least one input and one
  output place. A generic normalization construction adds fresh source/sink
  places and enter/exit transitions around a connected designated-source/sink
  Petri net, with checked path lifting, connectedness, unique source/sink, and
  `WorkflowNet` construction. Accepting firing sequences lift into normalized
  WF-nets by wrapping the original trace with silent enter/exit transitions.
  Original-transition enabledness, firing, and fire-result equations are
  equivalent between an original marking and its normalized embedding, and
  firing sequences made only of wrapped original transitions are equivalent to
  original firing sequences between embedded markings. Boundary-shaped
  normalized accepting sequences, with enter/original/exit trace shape, are now
  equivalent to original accepting firing sequences.
- `KouraniWfnetPowl.Powl`: POWL syntax and language semantics for atom, XOR,
  loop, and partial-order nodes, including the checked atom-language theorem
  for Definition 5.
- `KouraniWfnetPowl.NetLanguage`: WF-net trace language `L(N)` from firing
  sequences and checked single-transition/base-case language preservation
  lemmas. The language layer now records subtype-trace erasure and generic
  language transfer lemmas between closed restricted subnets and their original
  WF-nets, plus the fact that a typed subtype trace is already an original
  accepting trace. Normalized labels map enter/exit transitions to silent
  labels and preserve trace words for original traces with silent normalization
  boundaries, yielding a checked original-language-to-normalized-language
  inclusion.
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
  pattern now has checked extraction theorems showing do/redo transitions lie
  on the corresponding place-to-place paths, that loop-projection boundary
  edges are created from the original entry/exit places, that loop entry/exit
  places are distinct from the WF-net source/sink, and that the expected
  do/redo boundary exclusion conditions are available as standalone lemmas.
  Loop projections now also have a subtype-restricted representation with
  selected places and transitions, plus checked source-to-sink boundary path
  constructors for one-transition entry/exit segments.
  Partial-order projections now have a subtype-restricted representation with
  selected transitions and retained boundary/original places, checked boundary
  and internal edge constructors in all boundary directions, and one-step path
  constructors for boundary and retained-original edges. Restricted
  partial-order projection paths lift to ambient partial-order projection paths.
  Partial-order pattern consequences
  now also expose execution-order boundary construction, cycle exclusion,
  same-component entry/exit exclusion, and entry/exit place equivalence with
  respect to a component's transitions. Entry/exit point predicates now have
  checked constructor/destructor lemmas and source/sink exclusion consequences.
  Indexed partition components now carry checked membership/nonemptiness facts,
  and common-postset reachability is checked to force transitions into the same
  partition component.
- `KouraniWfnetPowl.PaperTargets`: named Section 5 proof targets and checked
  semantic preservation theorems corresponding to the POWL-language side of
  Lemmas 4, 5, and 6, the checked base case for Theorem 1, and named checked
  dependencies for Lemma 1 path restriction, reachable-marking lifting,
  selected-sequence restriction, safeness preservation, a checked XOR
  branch-language-to-original-language inclusion, XOR branch-projection
  language equivalence with typed original subtraces, and Lemma 2 loop trace
  closure plus loop projection boundary and restricted-projection facts, and
  Lemma 3 partial-order projection boundary/internal edge and one-step path
  facts plus restricted-path lifting, generic normalization,
  normalized-firing forward/reverse local, sequence, and boundary-acceptance
  invariants, and normalized-language targets, execution-order,
  source/sink-aware entry/exit point API, and boundary-equivalence
  consequences, plus common-postset same-component consequences.

Build with:

```bash
lake build
```
