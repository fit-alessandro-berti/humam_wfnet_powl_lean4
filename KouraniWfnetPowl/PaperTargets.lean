import KouraniWfnetPowl.PetriNet
import KouraniWfnetPowl.Powl
import KouraniWfnetPowl.NetLanguage
import KouraniWfnetPowl.Patterns

namespace KouraniWfnetPowl

namespace Paper2503_20363

/-!
Lean target map for arXiv:2503.20363.

The file records the main proof obligations from Section 5 and contains the
checked parts that currently reduce directly to the foundational definitions:
strict partial-order asymmetry from Section 3.1 and the POWL semantic
preservation shape for XOR and loop operators from Definition 5.
-/

inductive ProofTarget where
  | lemma1_xorProjectionStructuralGuarantees
  | lemma2_loopProjectionStructuralGuarantees
  | lemma3_partialOrderProjectionStructuralGuarantees
  | lemma4_xorPatternLanguagePreservation
  | lemma5_loopPatternLanguagePreservation
  | lemma6_partialOrderPatternLanguagePreservation
  | theorem1_correctness
  | theorem2_completeness
  deriving Repr

theorem strict_partial_order_asymmetric
    {alpha : Sort u}
    {order : Rel alpha}
    (hirrefl : Irreflexive order)
    (htrans : Transitive order) :
    Asymmetric order :=
  irreflexive_transitive_asymmetric hirrefl htrans

theorem xor_pattern_language_preservation
    {Activity : Type u}
    {Trans : Type v}
    {label : Trans -> TransitionLabel Activity}
    {models : List (Powl Trans)}
    {netLanguage : Language Activity}
    (hnet :
      ∀ word,
        netLanguage word ↔
          ∃ model, model ∈ models ∧ Powl.language label model word) :
    ∀ word,
      Powl.language label (Powl.xor models) word ↔ netLanguage word := by
  intro word
  rw [Powl.xor_language_iff]
  exact Iff.symm (hnet word)

theorem loop_pattern_language_preservation
    {Activity : Type u}
    {Trans : Type v}
    {label : Trans -> TransitionLabel Activity}
    {body redo : Powl Trans}
    {netLanguage : Language Activity}
    (hnet :
      ∀ word,
        netLanguage word ↔
          Language.concat (Powl.language label body)
            (Language.Star
              (Language.concat
                (Powl.language label redo)
                (Powl.language label body))) word) :
    ∀ word,
      Powl.language label (Powl.loop body redo) word ↔ netLanguage word := by
  intro word
  rw [Powl.loop_language_iff_concat_star]
  exact Iff.symm (hnet word)

theorem partial_order_pattern_language_preservation
    {Activity : Type u}
    {Trans : Type v}
    {label : Trans -> TransitionLabel Activity}
    {order : Rel Nat}
    {models : List (Powl Trans)}
    {netLanguage : Language Activity}
    (hnet :
      ∀ word,
        netLanguage word ↔
          Powl.partialOrderLanguage label order models word) :
    ∀ word,
      Powl.language label (Powl.partialOrder order models) word ↔
        netLanguage word := by
  intro word
  rw [Powl.partial_order_language_iff]
  exact Iff.symm (hnet word)

theorem theorem1_base_case_single_transition
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {trans : Trans}
    (hall :
      ∀ trace,
        WorkflowNet.FiringSequence
          net
          (WorkflowNet.initial net)
          trace
          (WorkflowNet.final net) ->
          trace = [trans])
    (hfire :
      WorkflowNet.FiringSequence
        net
        (WorkflowNet.initial net)
        [trans]
        (WorkflowNet.final net)) :
    ∀ word,
      WorkflowNet.language net label word ↔
        Powl.language label (Powl.atom trans) word := by
  intro word
  constructor
  · intro hnet
    exact WorkflowNet.atom_language_of_single_trace_net_language hnet hall
  · intro hpowl
    exact WorkflowNet.single_trace_net_language_of_atom_language hfire hpowl

theorem partial_order_pattern_execution_order_asymmetric
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.partialOrderPattern net partition) :
    Asymmetric
      (TransGen (Patterns.executionOrder net partition)) :=
  Patterns.partialOrderPattern_asymmetric net partition hpattern

theorem lemma1_xor_projection_restricts_internal_paths
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {part : Set Trans}
    {source target : PetriNet.Node Place Trans}
    (path :
      PetriNet.PathIn
        net.toPetriNet
        (PetriNet.placesTouching net.toPetriNet part)
        part
        source
        target) :
    PetriNet.Path
      (Patterns.xorProjectionRestricted net part)
      (PetriNet.restrictNode source (PetriNet.PathIn.source_mem path))
      (PetriNet.restrictNode target (PetriNet.PathIn.target_mem path)) :=
  Patterns.xorProjectionRestricted_path_of_pathIn net part path

theorem lemma1_xor_projection_contains_source
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts) :
    PetriNet.placesTouching net.toPetriNet part net.source :=
  Patterns.xorPattern_part_source_touching hpattern hpart

theorem lemma1_xor_projection_contains_sink
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts) :
    PetriNet.placesTouching net.toPetriNet part net.sink :=
  Patterns.xorPattern_part_sink_touching hpattern hpart

theorem lemma1_xor_projection_internal_source_path
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {target : Trans}
    (htargetPart : part target) :
    PetriNet.PathIn
      net.toPetriNet
      (PetriNet.placesTouching net.toPetriNet part)
      part
      (PetriNet.Node.place net.source)
      (PetriNet.Node.trans target) :=
  Patterns.xorPattern_pathIn_source_to_part_transition
    hpattern hpart htargetPart

theorem lemma1_xor_projection_internal_sink_path
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {source : Trans}
    (hsourcePart : part source) :
    PetriNet.PathIn
      net.toPetriNet
      (PetriNet.placesTouching net.toPetriNet part)
      part
      (PetriNet.Node.trans source)
      (PetriNet.Node.place net.sink) :=
  Patterns.xorPattern_pathIn_part_transition_to_sink
    hpattern hpart hsourcePart

theorem lemma1_xor_projection_restricted_transition_connected
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    (transition : {trans : Trans // part trans}) :
    PetriNet.Path
        (Patterns.xorProjectionRestricted net part)
        (PetriNet.Node.place
          ⟨net.source,
            Patterns.xorPattern_part_source_touching hpattern hpart⟩)
        (PetriNet.Node.trans transition) ∧
      PetriNet.Path
        (Patterns.xorProjectionRestricted net part)
        (PetriNet.Node.trans transition)
        (PetriNet.Node.place
          ⟨net.sink,
            Patterns.xorPattern_part_sink_touching hpattern hpart⟩) :=
  Patterns.xorPattern_restricted_transition_connected
    hpattern hpart transition

theorem lemma1_xor_projection_restricted_connected
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    (node :
      PetriNet.Node
        {place : Place // PetriNet.placesTouching net.toPetriNet part place}
        {trans : Trans // part trans}) :
    PetriNet.Path
        (Patterns.xorProjectionRestricted net part)
        (PetriNet.Node.place
          ⟨net.source,
            Patterns.xorPattern_part_source_touching hpattern hpart⟩)
        node ∧
      PetriNet.Path
        (Patterns.xorProjectionRestricted net part)
        node
        (PetriNet.Node.place
          ⟨net.sink,
            Patterns.xorPattern_part_sink_touching hpattern hpart⟩) :=
  Patterns.xorPattern_restricted_connected hpattern hpart node

def lemma1_xor_projection_workflow_net
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts) :
    WorkflowNet
      {place : Place // PetriNet.placesTouching net.toPetriNet part place}
      {trans : Trans // part trans} :=
  Patterns.xorProjectionWorkflowNet hpattern hpart

theorem lemma1_xor_projection_reachable_lifts
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {marking :
      Marking
        {place : Place // PetriNet.placesTouching net.toPetriNet part place}}
    (hreachable :
      WorkflowNet.reachable
        (Patterns.xorProjectionWorkflowNet hpattern hpart)
        (WorkflowNet.initial
          (Patterns.xorProjectionWorkflowNet hpattern hpart))
        marking) :
    WorkflowNet.reachable net (WorkflowNet.initial net) (Marking.extend marking) :=
  Patterns.xorProjectionWorkflowNet_reachable_lift
    hpattern hpart hreachable

theorem lemma1_xor_projection_safe
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    (hsafe : WorkflowNet.safe net) :
    WorkflowNet.safe (Patterns.xorProjectionWorkflowNet hpattern hpart) :=
  Patterns.xorProjectionWorkflowNet_safe hpattern hpart hsafe

theorem lemma1_xor_projection_selected_sequence_restricts
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {before after : Marking Place}
    {trace : List {trans : Trans // part trans}}
    (sequence :
      WorkflowNet.FiringSequence
        net
        before
        (trace.map Subtype.val)
        after) :
    WorkflowNet.FiringSequence
      (Patterns.xorProjectionWorkflowNet hpattern hpart)
      (Marking.restrict before)
      trace
      (Marking.restrict after) :=
  Patterns.xorProjectionWorkflowNet_firingSequence_restrict
    hpattern hpart sequence

theorem lemma2_loop_pattern_trace_closure
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {label : Trans -> TransitionLabel Activity}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.loopPattern label net partition) :
    ∃ doPart redoPart pdo predo,
      doPart ∈ partition.parts ∧
      redoPart ∈ partition.parts ∧
      (∀ trace,
        PetriNet.PlacePathTo net.toPetriNet predo pdo trace ->
          ∀ trans, trans ∈ trace -> doPart trans) ∧
      (∀ trace,
        PetriNet.PlacePathTo net.toPetriNet pdo predo trace ->
          ∀ trans, trans ∈ trace -> redoPart trans) :=
  Patterns.loopPattern_part_trace_closed hpattern

end Paper2503_20363

end KouraniWfnetPowl
