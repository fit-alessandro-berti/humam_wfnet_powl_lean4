# Kourani WF-net to POWL Lean formalization

This is a Lean 4-only formalization effort for arXiv:2503.20363,
"Translating Workflow Nets into the Partially Ordered Workflow Language".

The current proof spine is:

- `KouraniWfnetPowl.Basic`: sets-as-predicates, relations, transitive closure,
  strict partial orders, and the checked proof that irreflexive transitive
  relations are asymmetric.
- `KouraniWfnetPowl.PetriNet`: Petri nets, workflow nets, marked-graph and
  free-choice predicates, paths, transition reachability, subtype-restricted
  projections, markings, firing sequences, safeness, and soundness definitions.
  `PathIn` records paths whose nodes stay
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
  equivalent to original accepting firing sequences. The soundness API records
  that option-to-complete, soundness, and safe-and-soundness each yield a
  reachable final marking from the initial marking, and that no-dead-transition
  assumptions yield concrete firing witnesses whose post-markings are reachable
  from the initial marking; combined with option-to-complete, those witnesses
  extend to accepting firing sequences and accepting traces that contain the
  transition. The fresh enter/exit transitions have checked
  enabledness characterizations, and wrapped original
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
  dead transitions and can complete from reachable markings. Definition 6 work
  has started with checked explicit-decision-point predicates, split/join
  decision-place predicates, a checked split-to-join pairing skeleton with
  branch-count equivalence, a disjoint branch-subnet family specification, and
  branch-subnet closure/disjointness API lemmas, exact unique-preset/postset
  API lemmas plus checked split/join consequences of the
  explicit-decision-point condition, and checked free-choice preset equality,
  no-decision-place-to-marked-graph equivalence, marked-graph-to-free-choice,
  and marked-graph non-boundary unique-preset/postset consequences, plus the
  corresponding safe-and-sound,
  explicit-decision, paired-decision, and branch-subnet requirement layers for
  semi-block-structured WF-nets.
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
- `KouraniWfnetPowl.Language`: finite-word languages as predicates, with
  checked extensionality for turning pointwise language equivalences into
  actual language equalities.
- `KouraniWfnetPowl.NetLanguage`: WF-net trace language `L(N)` from firing
  sequences and checked single-transition/base-case language preservation
  lemmas. Accepting traces that contain a transition can now be packaged as
  concrete WF-net language words while retaining the underlying trace
  membership evidence, and visible transitions in such traces yield concrete
  activity membership in the generated word. The language layer also records
  subtype-trace erasure, local
  source-to-sink languages between arbitrary places, generic language transfer
  lemmas between closed restricted subnets and their original WF-nets, and
  local restricted-subnet language equivalence with typed original branch
  traces. Ordinary WF-net language is checked equivalent to local language at
  the net's own source and sink, and mapped subtype POWL models can now be
  related directly to local typed trace languages. Decision-branch WF-net
  certificates now expose checked local-language and mapped-POWL equivalences
  between the restricted branch net and the corresponding split-to-join typed
  trace language. A typed subtype trace is also already an original accepting
  trace. Normalized labels map enter/exit transitions to silent
  labels and preserve trace words for original traces with silent normalization
  boundaries, yielding a checked original-language-to-normalized-language
  inclusion and an equivalence with the normalized language restricted to
  boundary-shaped enter/original/exit traces. Under original proper completion,
  arbitrary accepting traces of the normalized net are also erased back to
  original accepting traces, yielding full normalized-language equivalence.
  Recursively translated POWL models over restricted transition subtypes can be
  mapped back to original transitions and related directly to typed original
  subtrace languages. Normalized subtype transition maps also preserve
  normalized labels, so models from normalized projections can be embedded into
  a common normalized transition universe.
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
  Raw projection edges are checked to stay inside the retained node set, so
  ordinary raw projection paths can be lifted to `PathIn` paths from any
  retained source, and raw ordinary-path connectedness now packages restricted
  projections as normalized `WorkflowNet`s.
  Selected transitions and retained original places now have checked two-sided
  connectivity in the restricted partial-order projection from explicit
  entry/exit and incidence witnesses; under those same hypotheses, restricted
  partial-order projections can be normalized and packaged as `WorkflowNet`s,
  matching the projection-normalization step in Definition 14. The same API now
  includes restricted projection markings and normalized markings for retained
  original places, boundary places, and fresh source/sink places, plus an
  original-transition enabledness bridge for normalized partial-order
  projections under marked entry/exit boundary conditions, with checked firing
  steps, firing witnesses, one-step firing sequences, and reachability witnesses
  for such projected original transitions. Reachable projected markings can now
  be packaged as no-dead-transition witnesses for wrapped original transitions
  in the normalized projection, and fresh enter/exit witnesses now combine with
  the wrapped-original witnesses into a full `noDeadTransitions` constructor
  under explicit reachability and boundary-marking hypotheses. These witnesses
  now package into normalized projection `sound` and `safeAndSound` facts when
  the remaining completion, proper-completion, and safeness obligations are
  supplied. Pointwise marking bounds now show that restricted and normalized
  projection markings preserve safeness from original markings, and a
  three-way reachable-shape invariant, covering the fresh initial marking,
  projected original reachable markings, and the fresh final marking, turns
  original safeness into safeness of the normalized projection; the same
  invariant feeds a `safeAndSound` constructor that only keeps completion and
  proper-completion as supplied residual obligations, and it has checked
  constructor/eliminator lemmas plus a pointwise one-token bound for downstream
  proof scripts. A more general raw-projection normalization constructor is also
  available when connectedness is supplied over the ambient raw projection.
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
  indexed Lemma 4 and Lemma 6 component-list forms, plus a Lemma 6
  partial-order-pattern theorem that combines execution-order asymmetry with
  local subtype branch conversions and exposes the induced strict partial
  order. The target map now also
  includes mapped-component variants of the XOR, loop, and partial-order
  preservation wrappers, so recursive submodel equivalences can be transported
  through transition embeddings before applying the top-level pattern semantics;
  the loop wrappers also support separate mapped transition subtypes for do and
  redo models, plus named checked
  dependencies for Lemma 1 path restriction, reachable-marking lifting,
  selected-sequence restriction, safeness preservation, no-dead-transition,
  soundness, and `safeAndSound` transfer from selected accepting sequences
  plus supplied completion/proper-completion obligations, including variants
  that consume the original net's `safeAndSound` hypothesis directly, a checked XOR
  branch-language-to-original-language inclusion, XOR branch-projection
  language equivalence with typed original subtraces, a mapped recursive
  XOR-branch model-to-typed-subtrace equivalence, and a mapped branch-list
  theorem that combines recursive XOR branch models with a top-level XOR model
  under a supplied language decomposition, plus mapped partial-order
  branch-list theorems for subtype components and heterogeneous component
  transition universes, including normalized subtype projection components.
  Theorem 1 now has checked induction-case combinators for XOR, loop, and
  partial-order conversions, plus a `ConversionCertificate` proof object whose
  preservation theorem turns a certified successful conversion into the language
  equivalence claimed by Theorem 1. Recursive certificate builders assemble
  parent XOR, loop, and partial-order certificates from certified projected
  subcalls, including normalized partial-order components; `CertifiedConversion`
  packages the output model and certificate as the checked successful-conversion
  interface for Theorem 1, with explicit global and local single-transition
  base-case constructors and object-level successful-conversion constructors
  for XOR, loop, ordinary partial-order, and normalized partial-order recursive
  cases. Normalized partial-order component certificates now also expose direct
  Theorem 1 language preservation/equality, semantic conversion, and existential
  POWL-model equality wrappers. A global `SubtypeCertifiedConversion` interface
  supplies mapped language preservation/equality and XOR, loop, and partial-order
  composition wrappers over subtype trace decompositions. A `SemanticCertifiedConversion`
  interface now packages direct global language-equivalence certificates and
  can be built from structural `CertifiedConversion`s, full-transition subtype
  conversions, and subtype-composed XOR/loop/partial-order models, with
  theorem-facing aliases for the Theorem 1 semantic conversion statement,
  including the paper-style `L(N) = L(ψ)` equality form and an explicit
  existential POWL-model form. Visible-activity WF-net language witnesses
  transfer across semantic conversions to accepted POWL-model words. Theorem 2
  now has checked targets for the safe-and-sound,
  explicit-decision-point, split/join pairing, paired branch-equivalence, and
  disjoint branch-subnet requirements of semi-block-structured WF-nets, plus
  an explicit split-decision branch-family package exposing the selected
  branch pair, branch-family evidence, split-transition containment,
  branch nonemptiness, restricted workflow-net subnets, and disjointness,
  checked branch-subnet closure/disjointness, local branch-language transfer,
  mapped local subtype POWL transfer, local XOR/loop/partial-order
  branch-family and certified-branch language-equality forms, direct
  branch-family constructors from restricted recursive branch certificates,
  a list-level bridge from those certificates to `LocalSubtypeCertifiedConversion`
  branch lists, semi-block split-decision continuations that choose the branch
  family and return local XOR/partial-order conversion builders, a
  `LocalCertifiedConversion` interface
  for source-to-sink subproblems, a `LocalSubtypeCertifiedConversion`
  interface for transition-subset subproblems with pointwise and equality forms,
  a checked full-transition-subset equivalence back to ordinary local
  languages, and local-to-global language preservation for source/sink
  certified conversions, including packaging source/sink local conversions as
  global `SemanticCertifiedConversion`s and explicit existential POWL-model
  statements. A `SemiBlockCertifiedConversion` interface packages the
  semi-block completeness hypothesis with a successful source/sink conversion
  and exposes safe-and-soundness, pointwise language preservation, language
  equality, existential POWL-model, and visible-activity witness consequences;
  combined completeness statements now package safe-and-soundness together
  with existential pointwise-equivalent and language-equal POWL models, and
  existentially package visible-activity witness words with the generated
  POWL model;
  theorem-facing constructors now cover the single-transition base case and
  the XOR, loop, and partial-order recursive cases from supplied local subtype
  conversions and global language decompositions, with an additional
  partial-order-pattern package that carries the induced strict partial order
  through to the semi-block certified conversion and combined safe/equivalent
  POWL-model consequence, plus explicit language-equality and visible-activity
  witness theorems for the concrete atom, XOR, loop, and partial-order POWL
  models, bundled into a `ConcretePowlWitness` case/certificate eliminator
  with reusable preservation and safe+existence consequences, and a
  `SemiBlockCompletenessCase`/`SemiBlockCompletenessCertificate` layer packages
  that case split into one algorithm-certificate object; the raw case evidence
  and bundled algorithm certificates both expose language preservation/equality,
  existential POWL-model, safe-and-soundness, combined completeness, and
  visible-activity witness consequences. A
  pattern-aware `SemiBlockPatternCompletenessCase` variant carries detected
  XOR/loop/partial-order pattern evidence, with the partial-order branch using
  the transitive closure of the execution-order relation and exposing the
  corresponding strict-partial-order object; raw pattern cases and bundled
  pattern certificates both expose the same completeness consequence surface.
  Named constructors now package the single-transition,
  XOR-pattern, loop-pattern, and partial-order-pattern cases directly as
  pattern completeness certificates, and direct theorem wrappers turn each
  case's hypotheses into existential POWL-model pointwise language-preservation,
  language-equality, combined safe-and-language-equality completeness, and
  visible-activity witness results,
  plus no-dead-transition, accepting-run trace-membership,
  language-word, visible-activity, semi-block local-conversion language
  equivalences, and local-conversion converted-POWL visible-activity witnesses
  for semi-block requirement layers,
  local XOR composition for decision-branch models and local loop composition
  for source-to-sink/redo-back submodels plus local partial-order composition
  for component submodels under supplied local decompositions, and constructors
  whose certificates are supplied by recursive `ConversionCertificate`s,
  including a bridge from restricted decision-branch certificates to local
  subtype conversions and object-level branch-family XOR/partial-order
  constructors from local subtype conversions, a checked bridge from the
  stronger disjoint branch-subnet requirement to the weaker decision-pairing
  requirement plus per-split branch-family witnesses, direct safe-and-sound,
  Definition 3 soundness-component, explicit-decision, and free-choice
  consequences for the semi-block requirement layers, exact
  uniqueness,
  free-choice preset-equality,
  marked-graph/no-decision equivalence, semi-block no-decision
  safe-and-sound marked-graph consequences, marked-graph/no-decision
  free-choice consequences, a bundled semi-block no-decision
  structural package that carries free-choiceness, bundled marked-graph and
  direct no-decision non-boundary unique-place-flow wrappers with exact `↔`
  rewrite forms and transition-equality corollaries, plus semi-block
  specializations used by the completeness argument, and Lemma 2 loop trace
  closure plus loop projection boundary, restricted-projection lifting, and
  connected-projection-to-`WorkflowNet` packaging facts, no-dead-transition,
  soundness, and `safeAndSound` packaging for connected loop projections from
  accepting-trace/completion/proper-completion obligations, with matching
  no-dead/sound/`safeAndSound` wrappers for reachable-incidence loop-projection
  constructors, including the incidence-based full restricted loop-projection
  connectedness target and pattern-level do/redo loop-projection WF-net
  existence plus `safeAndSound` constructor theorems, and
  Lemma 3
  partial-order projection boundary/internal edge, one-step path, and
  raw-`PathIn` constructor/path-lifting facts plus bidirectional
  restricted-path lifting, ordinary-path and `PathIn`-connected
  restricted projection normalization, restricted and normalized projection
  marking facts, original-transition enabledness, firing witnesses, singleton
  firing sequences, reachability, original-transition and fresh-boundary
  no-dead witnesses, and a full no-dead constructor for normalized projections,
  reachable-shape-based safeness and `safeAndSound` packaging, including
  variants that consume the original net's `safeAndSound` hypothesis directly,
  indexed partial-order-pattern projection WF-net existence plus
  accepting-trace and no-dead-witness `safeAndSound` constructor theorems
  under incidence obligations, sound
  packaging under supplied residual obligations, generic normalization,
  normalized-firing forward/reverse local, sequence, and boundary-acceptance
  invariants, fresh-boundary enabledness/preservation facts, and
  normalized-language equivalence targets, execution-order, source/sink-aware
  entry/exit point API, and boundary-equivalence consequences, plus
  common-postset same-component consequences.

Build with:

```bash
lake build
```
