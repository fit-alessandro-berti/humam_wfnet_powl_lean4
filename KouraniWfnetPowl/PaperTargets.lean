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

theorem lemma3_partial_order_projection_start_edge
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part place)
    (hflow : net.placeToTrans place trans) :
    (Patterns.partialOrderProjection net part).placeToTrans
      Patterns.BoundaryPlace.start trans :=
  Patterns.partialOrderProjection_start_placeToTrans
    net hpart hentry hflow

def lemma3_partial_order_projection_restricted
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans) :
    PetriNet
      {place : Patterns.BoundaryPlace Place //
        Patterns.partialOrderProjectionPlaces net part place}
      {trans : Trans // part trans} :=
  Patterns.partialOrderProjectionRestricted net part

theorem lemma3_partial_order_projection_contains_start
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans) :
    Patterns.partialOrderProjectionPlaces
      net part Patterns.BoundaryPlace.start :=
  Patterns.partialOrderProjectionPlaces_start net part

theorem lemma3_partial_order_projection_contains_end
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans) :
    Patterns.partialOrderProjectionPlaces
      net part Patterns.BoundaryPlace.end_ :=
  Patterns.partialOrderProjectionPlaces_end net part

theorem lemma3_partial_order_projection_contains_original
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {part : Set Trans}
    {place : Place}
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hnotEntry : ¬ WorkflowNet.entryPoints net part place)
    (hnotExit : ¬ WorkflowNet.exitPoints net part place) :
    Patterns.partialOrderProjectionPlaces
      net part (Patterns.BoundaryPlace.original place) :=
  Patterns.partialOrderProjectionPlaces_original
    net htouching hnotEntry hnotExit

theorem lemma3_partial_order_projection_end_edge
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (hexit : WorkflowNet.exitPoints net part place)
    (hflow : net.transToPlace trans place) :
    (Patterns.partialOrderProjection net part).transToPlace
      trans Patterns.BoundaryPlace.end_ :=
  Patterns.partialOrderProjection_transToPlace_end
    net hpart hexit hflow

theorem lemma3_partial_order_projection_restricted_start_edge
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part place)
    (hflow : net.placeToTrans place trans) :
    (Patterns.partialOrderProjectionRestricted net part).placeToTrans
      ⟨Patterns.BoundaryPlace.start,
        Patterns.partialOrderProjectionPlaces_start net part⟩
      ⟨trans, hpart⟩ :=
  Patterns.partialOrderProjectionRestricted_start_placeToTrans
    net hpart hentry hflow

theorem lemma3_partial_order_projection_restricted_end_edge
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (hexit : WorkflowNet.exitPoints net part place)
    (hflow : net.transToPlace trans place) :
    (Patterns.partialOrderProjectionRestricted net part).transToPlace
      ⟨trans, hpart⟩
      ⟨Patterns.BoundaryPlace.end_,
        Patterns.partialOrderProjectionPlaces_end net part⟩ :=
  Patterns.partialOrderProjectionRestricted_transToPlace_end
    net hpart hexit hflow

theorem lemma3_partial_order_projection_internal_placeToTrans
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hnotEntry : ¬ WorkflowNet.entryPoints net part place)
    (hnotExit : ¬ WorkflowNet.exitPoints net part place)
    (hflow : net.placeToTrans place trans) :
    (Patterns.partialOrderProjection net part).placeToTrans
      (Patterns.BoundaryPlace.original place) trans :=
  Patterns.partialOrderProjection_original_placeToTrans
    net hpart htouching hnotEntry hnotExit hflow

theorem lemma3_partial_order_projection_restricted_internal_placeToTrans
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hnotEntry : ¬ WorkflowNet.entryPoints net part place)
    (hnotExit : ¬ WorkflowNet.exitPoints net part place)
    (hflow : net.placeToTrans place trans) :
    (Patterns.partialOrderProjectionRestricted net part).placeToTrans
      ⟨Patterns.BoundaryPlace.original place,
        Patterns.partialOrderProjectionPlaces_original
          net htouching hnotEntry hnotExit⟩
      ⟨trans, hpart⟩ :=
  Patterns.partialOrderProjectionRestricted_original_placeToTrans
    net hpart htouching hnotEntry hnotExit hflow

theorem lemma3_partial_order_projection_internal_transToPlace
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hnotEntry : ¬ WorkflowNet.entryPoints net part place)
    (hnotExit : ¬ WorkflowNet.exitPoints net part place)
    (hflow : net.transToPlace trans place) :
    (Patterns.partialOrderProjection net part).transToPlace
      trans (Patterns.BoundaryPlace.original place) :=
  Patterns.partialOrderProjection_transToPlace_original
    net hpart htouching hnotEntry hnotExit hflow

theorem lemma3_partial_order_projection_restricted_internal_transToPlace
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hnotEntry : ¬ WorkflowNet.entryPoints net part place)
    (hnotExit : ¬ WorkflowNet.exitPoints net part place)
    (hflow : net.transToPlace trans place) :
    (Patterns.partialOrderProjectionRestricted net part).transToPlace
      ⟨trans, hpart⟩
      ⟨Patterns.BoundaryPlace.original place,
        Patterns.partialOrderProjectionPlaces_original
          net htouching hnotEntry hnotExit⟩ :=
  Patterns.partialOrderProjectionRestricted_transToPlace_original
    net hpart htouching hnotEntry hnotExit hflow

theorem lemma3_partial_order_projection_restricted_original_to_transition
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hnotEntry : ¬ WorkflowNet.entryPoints net part place)
    (hnotExit : ¬ WorkflowNet.exitPoints net part place)
    (hflow : net.placeToTrans place trans) :
    PetriNet.Path
      (Patterns.partialOrderProjectionRestricted net part)
      (PetriNet.Node.place
        ⟨Patterns.BoundaryPlace.original place,
          Patterns.partialOrderProjectionPlaces_original
            net htouching hnotEntry hnotExit⟩)
      (PetriNet.Node.trans ⟨trans, hpart⟩) :=
  Patterns.partialOrderProjectionRestricted_original_to_transition
    net hpart htouching hnotEntry hnotExit hflow

theorem lemma3_partial_order_projection_restricted_transition_to_original
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hnotEntry : ¬ WorkflowNet.entryPoints net part place)
    (hnotExit : ¬ WorkflowNet.exitPoints net part place)
    (hflow : net.transToPlace trans place) :
    PetriNet.Path
      (Patterns.partialOrderProjectionRestricted net part)
      (PetriNet.Node.trans ⟨trans, hpart⟩)
      (PetriNet.Node.place
        ⟨Patterns.BoundaryPlace.original place,
          Patterns.partialOrderProjectionPlaces_original
            net htouching hnotEntry hnotExit⟩) :=
  Patterns.partialOrderProjectionRestricted_transition_to_original
    net hpart htouching hnotEntry hnotExit hflow

theorem lemma3_partial_order_projection_start_to_end_path
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {entry exit : Place}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part entry)
    (hexit : WorkflowNet.exitPoints net part exit)
    (hstart : net.placeToTrans entry trans)
    (hend : net.transToPlace trans exit) :
    PetriNet.Path
      (Patterns.partialOrderProjection net part)
      (PetriNet.Node.place Patterns.BoundaryPlace.start)
      (PetriNet.Node.place Patterns.BoundaryPlace.end_) :=
  Patterns.partialOrderProjection_start_to_end
    net hpart hentry hexit hstart hend

theorem lemma3_partial_order_projection_restricted_start_to_transition
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part place)
    (hflow : net.placeToTrans place trans) :
    PetriNet.Path
      (Patterns.partialOrderProjectionRestricted net part)
      (PetriNet.Node.place
        ⟨Patterns.BoundaryPlace.start,
          Patterns.partialOrderProjectionPlaces_start net part⟩)
      (PetriNet.Node.trans ⟨trans, hpart⟩) :=
  Patterns.partialOrderProjectionRestricted_start_to_transition
    net hpart hentry hflow

theorem lemma3_partial_order_projection_restricted_transition_to_end
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (hexit : WorkflowNet.exitPoints net part place)
    (hflow : net.transToPlace trans place) :
    PetriNet.Path
      (Patterns.partialOrderProjectionRestricted net part)
      (PetriNet.Node.trans ⟨trans, hpart⟩)
      (PetriNet.Node.place
        ⟨Patterns.BoundaryPlace.end_,
          Patterns.partialOrderProjectionPlaces_end net part⟩) :=
  Patterns.partialOrderProjectionRestricted_transition_to_end
    net hpart hexit hflow

theorem lemma3_partial_order_projection_restricted_start_to_end_path
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {entry exit : Place}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part entry)
    (hexit : WorkflowNet.exitPoints net part exit)
    (hstart : net.placeToTrans entry trans)
    (hend : net.transToPlace trans exit) :
    PetriNet.Path
      (Patterns.partialOrderProjectionRestricted net part)
      (PetriNet.Node.place
        ⟨Patterns.BoundaryPlace.start,
          Patterns.partialOrderProjectionPlaces_start net part⟩)
      (PetriNet.Node.place
        ⟨Patterns.BoundaryPlace.end_,
          Patterns.partialOrderProjectionPlaces_end net part⟩) :=
  Patterns.partialOrderProjectionRestricted_start_to_end
    net hpart hentry hexit hstart hend

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

theorem lemma1_xor_projection_selected_accepting_sequence_restricts
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {trace : List {trans : Trans // part trans}}
    (sequence :
      WorkflowNet.FiringSequence
        net
        (WorkflowNet.initial net)
        (trace.map Subtype.val)
        (WorkflowNet.final net)) :
    WorkflowNet.FiringSequence
      (Patterns.xorProjectionWorkflowNet hpattern hpart)
      (WorkflowNet.initial
        (Patterns.xorProjectionWorkflowNet hpattern hpart))
      trace
      (WorkflowNet.final
        (Patterns.xorProjectionWorkflowNet hpattern hpart)) :=
  Patterns.xorProjectionWorkflowNet_firingSequence_restrict_initial_final
    hpattern hpart sequence

theorem lemma4_xor_projection_language_of_selected_original_sequence
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    {label : Trans -> TransitionLabel Activity}
    (hpattern : Patterns.xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {trace : List {trans : Trans // part trans}}
    {word : List Activity}
    (sequence :
      WorkflowNet.FiringSequence
        net
        (WorkflowNet.initial net)
        (trace.map Subtype.val)
        (WorkflowNet.final net))
    (hword : WorkflowNet.traceWord label (trace.map Subtype.val) = word) :
    WorkflowNet.language
      (Patterns.xorProjectionWorkflowNet hpattern hpart)
      (fun trans : {trans : Trans // part trans} => label trans.val)
      word :=
  WorkflowNet.restricted_language_of_typed_original_sequence
    net
    (Patterns.xorProjectionWorkflowNet hpattern hpart)
    (by rfl)
    (by rfl)
    (by intro place trans; rfl)
    (by intro trans place; rfl)
    sequence
    hword

theorem lemma4_original_language_of_xor_projection_language
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    {label : Trans -> TransitionLabel Activity}
    (hpattern : Patterns.xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {word : List Activity}
    (hlanguage :
      WorkflowNet.language
        (Patterns.xorProjectionWorkflowNet hpattern hpart)
        (fun trans : {trans : Trans // part trans} => label trans.val)
        word) :
    WorkflowNet.language net label word :=
  WorkflowNet.original_language_of_restricted_language
    net
    (Patterns.xorProjectionWorkflowNet hpattern hpart)
    (by rfl)
    (by rfl)
    (by intro place trans; rfl)
    (by intro trans place; rfl)
    (by
      intro place trans htrans hflow
      exact PetriNet.placesTouching_of_placeToTrans
        net.toPetriNet htrans hflow)
    (by
      intro trans place htrans hflow
      exact PetriNet.placesTouching_of_transToPlace
        net.toPetriNet htrans hflow)
    hlanguage

theorem lemma4_xor_projection_language_iff_subtype_trace_language
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    {label : Trans -> TransitionLabel Activity}
    (hpattern : Patterns.xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    (word : List Activity) :
    WorkflowNet.language
        (Patterns.xorProjectionWorkflowNet hpattern hpart)
        (fun trans : {trans : Trans // part trans} => label trans.val)
        word ↔
      WorkflowNet.subtypeTraceLanguage net label part word :=
  WorkflowNet.restricted_language_iff_subtypeTraceLanguage
    net
    (Patterns.xorProjectionWorkflowNet hpattern hpart)
    (by rfl)
    (by rfl)
    (by intro place trans; rfl)
    (by intro trans place; rfl)
    (by
      intro place trans htrans hflow
      exact PetriNet.placesTouching_of_placeToTrans
        net.toPetriNet htrans hflow)
    (by
      intro trans place htrans hflow
      exact PetriNet.placesTouching_of_transToPlace
        net.toPetriNet htrans hflow)
    label
    word

theorem lemma4_xor_projection_language_union_iff_subtype_trace_union
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    {label : Trans -> TransitionLabel Activity}
    (hpattern : Patterns.xorPattern net partition)
    (word : List Activity) :
    (∃ part, ∃ hpart : part ∈ partition.parts,
      WorkflowNet.language
        (Patterns.xorProjectionWorkflowNet hpattern hpart)
        (fun trans : {trans : Trans // part trans} => label trans.val)
        word) ↔
      ∃ part,
        part ∈ partition.parts ∧
          WorkflowNet.subtypeTraceLanguage net label part word := by
  constructor
  · intro h
    rcases h with ⟨part, hpart, hlanguage⟩
    exact ⟨part, hpart,
      (lemma4_xor_projection_language_iff_subtype_trace_language
        hpattern hpart word).mp hlanguage⟩
  · intro h
    rcases h with ⟨part, hpart, hlanguage⟩
    exact ⟨part, hpart,
      (lemma4_xor_projection_language_iff_subtype_trace_language
        hpattern hpart word).mpr hlanguage⟩

theorem lemma4_xor_projection_union_language_preservation
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    {label : Trans -> TransitionLabel Activity}
    (hpattern : Patterns.xorPattern net partition)
    (hdecompose :
      ∀ word,
        WorkflowNet.language net label word ↔
          ∃ part,
            part ∈ partition.parts ∧
              WorkflowNet.subtypeTraceLanguage net label part word) :
    ∀ word,
      (∃ part, ∃ hpart : part ∈ partition.parts,
        WorkflowNet.language
          (Patterns.xorProjectionWorkflowNet hpattern hpart)
          (fun trans : {trans : Trans // part trans} => label trans.val)
          word) ↔
        WorkflowNet.language net label word := by
  intro word
  exact Iff.trans
    (lemma4_xor_projection_language_union_iff_subtype_trace_union
      hpattern word)
    (Iff.symm (hdecompose word))

theorem lemma4_xor_projection_union_language_preservation_of_cover
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    {label : Trans -> TransitionLabel Activity}
    (hpattern : Patterns.xorPattern net partition)
    (hcover :
      ∀ word,
        WorkflowNet.language net label word ->
          ∃ part,
            part ∈ partition.parts ∧
              WorkflowNet.subtypeTraceLanguage net label part word) :
    ∀ word,
      (∃ part, ∃ hpart : part ∈ partition.parts,
        WorkflowNet.language
          (Patterns.xorProjectionWorkflowNet hpattern hpart)
          (fun trans : {trans : Trans // part trans} => label trans.val)
          word) ↔
        WorkflowNet.language net label word := by
  intro word
  constructor
  · intro hprojection
    have hsubtypeUnion :
        ∃ part,
          part ∈ partition.parts ∧
            WorkflowNet.subtypeTraceLanguage net label part word :=
      (lemma4_xor_projection_language_union_iff_subtype_trace_union
        hpattern word).mp hprojection
    rcases hsubtypeUnion with ⟨part, _hpart, hlanguage⟩
    exact WorkflowNet.language_of_subtypeTraceLanguage hlanguage
  · intro horiginal
    exact
      (lemma4_xor_projection_language_union_iff_subtype_trace_union
        hpattern word).mpr (hcover word horiginal)

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

theorem lemma2_loop_projection_boundary_edges
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
      (∀ trans, doPart trans ->
        net.placeToTrans pdo trans ->
          (Patterns.loopProjection net doPart pdo predo).placeToTrans
            net.source trans) ∧
      (∀ trans, doPart trans ->
        net.transToPlace trans predo ->
          (Patterns.loopProjection net doPart pdo predo).transToPlace
            trans net.sink) ∧
      (∀ trans, redoPart trans ->
        net.placeToTrans predo trans ->
          (Patterns.loopProjection net redoPart predo pdo).placeToTrans
            net.source trans) ∧
      (∀ trans, redoPart trans ->
        net.transToPlace trans pdo ->
          (Patterns.loopProjection net redoPart predo pdo).transToPlace
            trans net.sink) :=
  Patterns.loopPattern_projection_boundary_edges hpattern

def lemma2_loop_projection_restricted
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place) :
    PetriNet
      {place : Place //
        Patterns.loopProjectionPlaces net part startPlace endPlace place}
      {trans : Trans // part trans} :=
  Patterns.loopProjectionRestricted net part startPlace endPlace

theorem lemma2_loop_projection_contains_source
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place) :
    Patterns.loopProjectionPlaces net part startPlace endPlace net.source :=
  Patterns.loopProjectionPlaces_source net part startPlace endPlace

theorem lemma2_loop_projection_contains_sink
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place) :
    Patterns.loopProjectionPlaces net part startPlace endPlace net.sink :=
  Patterns.loopProjectionPlaces_sink net part startPlace endPlace

theorem lemma2_loop_projection_contains_internal_place
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {part : Set Trans}
    {startPlace endPlace place : Place}
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hstart : place ≠ startPlace)
    (hend : place ≠ endPlace) :
    Patterns.loopProjectionPlaces net part startPlace endPlace place :=
  Patterns.loopProjectionPlaces_internal net htouching hstart hend

theorem lemma2_loop_projection_restricted_boundary_path
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    {trans : Trans}
    (hpart : part trans)
    (hstart : net.placeToTrans startPlace trans)
    (hend : net.transToPlace trans endPlace) :
    PetriNet.Path
      (Patterns.loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.Node.place
        ⟨net.source,
          Patterns.loopProjectionPlaces_source
            net part startPlace endPlace⟩)
      (PetriNet.Node.place
        ⟨net.sink,
          Patterns.loopProjectionPlaces_sink
            net part startPlace endPlace⟩) :=
  Patterns.loopProjectionRestricted_boundary_path net hpart hstart hend

theorem lemma2_loop_projection_restricted_boundary_paths
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
      (∀ trans, doPart trans ->
        net.placeToTrans pdo trans ->
        net.transToPlace trans predo ->
          PetriNet.Path
            (Patterns.loopProjectionRestricted net doPart pdo predo)
            (PetriNet.Node.place
              ⟨net.source,
                Patterns.loopProjectionPlaces_source
                  net doPart pdo predo⟩)
            (PetriNet.Node.place
              ⟨net.sink,
                Patterns.loopProjectionPlaces_sink
                  net doPart pdo predo⟩)) ∧
      (∀ trans, redoPart trans ->
        net.placeToTrans predo trans ->
        net.transToPlace trans pdo ->
          PetriNet.Path
            (Patterns.loopProjectionRestricted net redoPart predo pdo)
            (PetriNet.Node.place
              ⟨net.source,
                Patterns.loopProjectionPlaces_source
                  net redoPart predo pdo⟩)
            (PetriNet.Node.place
              ⟨net.sink,
                Patterns.loopProjectionPlaces_sink
                  net redoPart predo pdo⟩)) :=
  Patterns.loopPattern_projection_restricted_boundary_paths hpattern

theorem lemma2_loop_pattern_source_ne_sink
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {label : Trans -> TransitionLabel Activity}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.loopPattern label net partition) :
    net.source ≠ net.sink :=
  Patterns.loopPattern_source_ne_sink hpattern

theorem lemma2_loop_projection_source_no_in
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
      (∀ trans : {trans : Trans // doPart trans},
        ¬ (Patterns.loopProjectionRestricted net doPart pdo predo).transToPlace
          trans
          ⟨net.source,
            Patterns.loopProjectionPlaces_source net doPart pdo predo⟩) ∧
      (∀ trans : {trans : Trans // redoPart trans},
        ¬ (Patterns.loopProjectionRestricted net redoPart predo pdo).transToPlace
          trans
          ⟨net.source,
            Patterns.loopProjectionPlaces_source net redoPart predo pdo⟩) :=
  Patterns.loopPattern_projection_source_no_in hpattern

theorem lemma2_loop_projection_sink_no_out
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
      (∀ trans : {trans : Trans // doPart trans},
        ¬ (Patterns.loopProjectionRestricted net doPart pdo predo).placeToTrans
          ⟨net.sink,
            Patterns.loopProjectionPlaces_sink net doPart pdo predo⟩
          trans) ∧
      (∀ trans : {trans : Trans // redoPart trans},
        ¬ (Patterns.loopProjectionRestricted net redoPart predo pdo).placeToTrans
          ⟨net.sink,
            Patterns.loopProjectionPlaces_sink net redoPart predo pdo⟩
          trans) :=
  Patterns.loopPattern_projection_sink_no_out hpattern

theorem lemma2_loop_projection_boundary_paths
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
      (∀ trans, doPart trans ->
        net.placeToTrans pdo trans ->
          PetriNet.Path
            (Patterns.loopProjection net doPart pdo predo)
            (PetriNet.Node.place net.source)
            (PetriNet.Node.trans trans)) ∧
      (∀ trans, doPart trans ->
        net.transToPlace trans predo ->
          PetriNet.Path
            (Patterns.loopProjection net doPart pdo predo)
            (PetriNet.Node.trans trans)
            (PetriNet.Node.place net.sink)) ∧
      (∀ trans, doPart trans ->
        net.placeToTrans pdo trans ->
        net.transToPlace trans predo ->
          PetriNet.Path
            (Patterns.loopProjection net doPart pdo predo)
            (PetriNet.Node.place net.source)
            (PetriNet.Node.place net.sink)) ∧
      (∀ trans, redoPart trans ->
        net.placeToTrans predo trans ->
          PetriNet.Path
            (Patterns.loopProjection net redoPart predo pdo)
            (PetriNet.Node.place net.source)
            (PetriNet.Node.trans trans)) ∧
      (∀ trans, redoPart trans ->
        net.transToPlace trans pdo ->
          PetriNet.Path
            (Patterns.loopProjection net redoPart predo pdo)
            (PetriNet.Node.trans trans)
            (PetriNet.Node.place net.sink)) ∧
      (∀ trans, redoPart trans ->
        net.placeToTrans predo trans ->
        net.transToPlace trans pdo ->
          PetriNet.Path
            (Patterns.loopProjection net redoPart predo pdo)
            (PetriNet.Node.place net.source)
            (PetriNet.Node.place net.sink)) :=
  Patterns.loopPattern_projection_boundary_paths hpattern

theorem lemma2_loop_boundary_places_distinct
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
      pdo ≠ net.source ∧
      pdo ≠ net.sink ∧
      predo ≠ net.source ∧
      predo ≠ net.sink :=
  Patterns.loopPattern_boundary_places_distinct hpattern

theorem lemma2_loop_part_boundary_exclusion
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
      (∀ trans, doPart trans -> ¬ net.transToPlace trans pdo) ∧
      (∀ trans, redoPart trans -> ¬ net.transToPlace trans predo) ∧
      (∀ trans, doPart trans -> ¬ net.placeToTrans predo trans) ∧
      (∀ trans, redoPart trans -> ¬ net.placeToTrans pdo trans) :=
  Patterns.loopPattern_part_boundary_exclusion hpattern

end Paper2503_20363

end KouraniWfnetPowl
