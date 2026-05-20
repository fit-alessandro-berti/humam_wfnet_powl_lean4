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
  output place. A reusable constructor builds a `WorkflowNet` from a Petri net
  with connected source/sink paths plus no incoming source edge and no outgoing
  sink edge. A generic normalization construction adds fresh source/sink places
  and enter/exit transitions around a connected designated-source/sink Petri
  net, with checked path lifting, connectedness, unique source/sink, and
  `WorkflowNet` construction. Accepting firing sequences lift into normalized
  WF-nets by wrapping the original trace with silent enter/exit transitions.
  Original-transition enabledness, firing, and fire-result equations are
  equivalent between an original marking and its normalized embedding, and
  firing sequences made only of wrapped original transitions are equivalent to
  original firing sequences between embedded markings. Boundary-shaped
  normalized accepting sequences, with enter/original/exit trace shape, are now
  equivalent to original accepting firing sequences. The fresh enter/exit
  transitions have checked enabledness characterizations, and wrapped original
  transitions, including sequences made only of wrapped original transitions,
  preserve the fresh source/sink token counts. Original reachable markings lift
  to reachable normalized markings after the fresh enter transition, embedded
  normalized markings can complete to the normalized final marking whenever the
  original marking can complete, and every normalized reachable marking is
  classified as either the fresh initial marking, an embedded original
  reachable marking, or the fresh final marking under original proper
  completion. Consequently, normalization preserves option-to-complete under
  original option-to-complete plus proper completion, preserves proper
  completion itself, preserves safeness under original safeness plus proper
  completion, and preserves the full `sound` and `safeAndSound` predicates. It
  also preserves the no-dead-transitions property when the original net has no
  dead transitions and can complete from reachable markings.
- `KouraniWfnetPowl.Powl`: POWL syntax and language semantics for atom, XOR,
  loop, and partial-order nodes, including the checked atom-language theorem
  for Definition 5. POWL models can now be mapped across transition embeddings
  with checked language preservation under relabeling, which supports lifting
  recursively translated projection models back to the original transition type.
  XOR semantics is also exposed as a finite union of component languages, with
  an explicitly index-aligned congruence theorem for replacing equivalent branch
  languages. Loop semantics has a component-language congruence theorem for
  substituting equivalent body/redo models. Partial-order semantics now has a
  generic indexed component-language form, plus both map-based and explicitly
  index-aligned congruence theorems for replacing equivalent submodels
  componentwise.
- `KouraniWfnetPowl.NetLanguage`: WF-net trace language `L(N)` from firing
  sequences and checked single-transition/base-case language preservation
  lemmas. The language layer now records subtype-trace erasure and generic
  language transfer lemmas between closed restricted subnets and their original
  WF-nets, plus the fact that a typed subtype trace is already an original
  accepting trace. Normalized labels map enter/exit transitions to silent
  labels and preserve trace words for original traces with silent normalization
  boundaries, yielding a checked original-language-to-normalized-language
  inclusion and an equivalence with the normalized language restricted to
  boundary-shaped enter/original/exit traces. Under original proper completion,
  arbitrary accepting traces of the normalized net are also erased back to
  original accepting traces, yielding full normalized-language equivalence.
  Recursively translated POWL models over restricted transition subtypes can be
  mapped back to original transitions and related directly to typed original
  subtrace languages.
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
  selected places and transitions, checked restricted boundary/internal edge
  constructors, one-step path constructors for retained internal edges, generic
  restricted-to-projection flow/path lifting, plus checked source-to-sink
  boundary path constructors for one-transition entry/exit segments and
  source-to-member and member-to-sink paths along closed place-to-place traces,
  yielding checked source/sink connectivity for selected do/redo transitions
  and directional source/sink connectivity for internal places incident to
  selected transitions. Internal places with both selected incoming and outgoing
  transitions now have checked two-sided source/sink connectivity. Full
  restricted loop-projection connectedness is checked from transition
  reachability, nonempty selected parts, no selected incoming edge to the loop
  start boundary, and explicit incoming/outgoing incidence for every retained
  internal place; under the same hypotheses these projections can be packaged
  as `WorkflowNet`s.
  Partial-order projections now have a subtype-restricted representation with
  selected transitions and retained boundary/original places, checked boundary
  and internal edge constructors in all boundary directions, and one-step path
  constructors for boundary and retained-original edges. Restricted
  partial-order projection paths lift to ambient partial-order projection paths.
  Selected transitions and retained original places now have checked two-sided
  connectivity in the restricted partial-order projection from explicit
  entry/exit and incidence witnesses; under those same hypotheses, restricted
  partial-order projections can be normalized and packaged as `WorkflowNet`s,
  matching the projection-normalization step in Definition 14. A more general
  raw-projection normalization constructor is also available when connectedness
  is supplied over the ambient raw projection.
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
  POWL transition-map language preservation facts for recursively translated
  projection models, union-list/component-equivalence variants for the XOR,
  loop, and partial-order language preservation arguments, including explicitly
  indexed Lemma 4 and Lemma 6 component-list forms. The target map now also
  includes mapped-component variants of the XOR, loop, and partial-order
  preservation wrappers, so recursive submodel equivalences can be transported
  through transition embeddings before applying the top-level pattern semantics;
  the loop wrappers also support separate mapped transition subtypes for do and
  redo models, plus named checked
  dependencies for Lemma 1 path restriction, reachable-marking lifting,
  selected-sequence restriction, safeness preservation, a checked XOR
  branch-language-to-original-language inclusion, XOR branch-projection
  language equivalence with typed original subtraces, a mapped recursive
  XOR-branch model-to-typed-subtrace equivalence, and a mapped branch-list
  theorem that combines recursive XOR branch models with a top-level XOR model
  under a supplied language decomposition, plus mapped partial-order
  branch-list theorems for subtype components and heterogeneous component
  transition universes, and Lemma 2 loop trace
  closure plus loop projection boundary, restricted-projection lifting, and
  connected-projection-to-`WorkflowNet` packaging facts, including the
  incidence-based full restricted loop-projection connectedness target, and
  Lemma 3
  partial-order projection boundary/internal edge and one-step path
  facts plus restricted-path lifting, generic normalization,
  normalized-firing forward/reverse local, sequence, and boundary-acceptance
  invariants, fresh-boundary enabledness/preservation facts, and
  normalized-language equivalence targets, execution-order, source/sink-aware
  entry/exit point API, and boundary-equivalence consequences, plus
  common-postset same-component consequences.

Build with:

```bash
lake build
```
