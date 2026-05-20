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

theorem indexed_component_mem
    {alpha : Type u}
    (partition : Partition alpha)
    {index : Nat}
    {part : Set alpha}
    (hpart : Powl.listGet? partition.parts index = some part) :
    part ∈ partition.parts :=
  Partition.mem_of_listGet? partition hpart

theorem indexed_component_nonempty
    {alpha : Type u}
    (partition : Partition alpha)
    {index : Nat}
    {part : Set alpha}
    (hpart : Powl.listGet? partition.parts index = some part) :
    ∃ item, part item :=
  Partition.nonempty_of_listGet? partition hpart

theorem lemma3_entry_point_has_part_output
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hentry : WorkflowNet.entryPoints net part place) :
    ∃ trans, part trans ∧ net.placeToTrans place trans :=
  WorkflowNet.entryPoints_has_part_output net hentry

theorem lemma3_entry_point_source_or_external_input
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hentry : WorkflowNet.entryPoints net part place) :
    place = net.source ∨
      ∃ trans, ¬ part trans ∧ net.transToPlace trans place :=
  WorkflowNet.entryPoints_source_or_external_input net hentry

theorem lemma3_entry_point_of_source_part_output
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hsource : place = net.source)
    (houtput : ∃ trans, part trans ∧ net.placeToTrans place trans) :
    WorkflowNet.entryPoints net part place :=
  WorkflowNet.entryPoints_of_source_part_output net hsource houtput

theorem lemma3_entry_point_of_external_input
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (houtput : ∃ trans, part trans ∧ net.placeToTrans place trans)
    (hexternal : ∃ trans, ¬ part trans ∧ net.transToPlace trans place) :
    WorkflowNet.entryPoints net part place :=
  WorkflowNet.entryPoints_of_external_input net houtput hexternal

theorem lemma3_exit_point_has_part_input
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hexit : WorkflowNet.exitPoints net part place) :
    ∃ trans, part trans ∧ net.transToPlace trans place :=
  WorkflowNet.exitPoints_has_part_input net hexit

theorem lemma3_exit_point_sink_or_external_output
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hexit : WorkflowNet.exitPoints net part place) :
    place = net.sink ∨
      ∃ trans, ¬ part trans ∧ net.placeToTrans place trans :=
  WorkflowNet.exitPoints_sink_or_external_output net hexit

theorem lemma3_exit_point_of_sink_part_input
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hsink : place = net.sink)
    (hinput : ∃ trans, part trans ∧ net.transToPlace trans place) :
    WorkflowNet.exitPoints net part place :=
  WorkflowNet.exitPoints_of_sink_part_input net hsink hinput

theorem lemma3_exit_point_of_external_output
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hinput : ∃ trans, part trans ∧ net.transToPlace trans place)
    (hexternal : ∃ trans, ¬ part trans ∧ net.placeToTrans place trans) :
    WorkflowNet.exitPoints net part place :=
  WorkflowNet.exitPoints_of_external_output net hinput hexternal

theorem lemma3_source_no_input
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (trans : Trans) :
    ¬ net.transToPlace trans net.source :=
  WorkflowNet.source_no_input net trans

theorem lemma3_sink_no_output
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (trans : Trans) :
    ¬ net.placeToTrans net.sink trans :=
  WorkflowNet.sink_no_output net trans

theorem wfnet_transition_has_input
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (trans : Trans) :
    ∃ place, net.placeToTrans place trans :=
  WorkflowNet.transition_has_input net trans

theorem wfnet_transition_has_output
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (trans : Trans) :
    ∃ place, net.transToPlace trans place :=
  WorkflowNet.transition_has_output net trans

theorem normalization_lifts_original_path
    {Place : Type u}
    {Trans : Type v}
    (net : PetriNet Place Trans)
    (source sink : Place)
    {first second : PetriNet.Node Place Trans}
    (path : PetriNet.Path net first second) :
    PetriNet.Path
      (PetriNet.normalize net source sink)
      (PetriNet.normalizedNode first)
      (PetriNet.normalizedNode second) :=
  PetriNet.normalize_path_original net source sink path

theorem normalization_source_no_input
    {Place : Type u}
    {Trans : Type v}
    (net : PetriNet Place Trans)
    (source sink : Place)
    (trans : PetriNet.NormalizedTrans Trans) :
    ¬ (PetriNet.normalize net source sink).transToPlace
      trans
      PetriNet.NormalizedPlace.source :=
  PetriNet.normalize_source_no_input net source sink trans

theorem normalization_sink_no_output
    {Place : Type u}
    {Trans : Type v}
    (net : PetriNet Place Trans)
    (source sink : Place)
    (trans : PetriNet.NormalizedTrans Trans) :
    ¬ (PetriNet.normalize net source sink).placeToTrans
      PetriNet.NormalizedPlace.sink
      trans :=
  PetriNet.normalize_sink_no_output net source sink trans

theorem normalization_connected
    {Place : Type u}
    {Trans : Type v}
    (net : PetriNet Place Trans)
    (source sink : Place)
    (hconnected :
      ∀ node : PetriNet.Node Place Trans,
        PetriNet.Path net (PetriNet.Node.place source) node ∧
        PetriNet.Path net node (PetriNet.Node.place sink)) :
    ∀ node :
      PetriNet.Node
        (PetriNet.NormalizedPlace Place)
        (PetriNet.NormalizedTrans Trans),
      PetriNet.Path
        (PetriNet.normalize net source sink)
        (PetriNet.Node.place PetriNet.NormalizedPlace.source)
        node ∧
      PetriNet.Path
        (PetriNet.normalize net source sink)
        node
        (PetriNet.Node.place PetriNet.NormalizedPlace.sink) :=
  PetriNet.normalize_connected net source sink hconnected

def normalization_workflow_net
    {Place : Type u}
    {Trans : Type v}
    (net : PetriNet Place Trans)
    (source sink : Place)
    (hconnected :
      ∀ node : PetriNet.Node Place Trans,
        PetriNet.Path net (PetriNet.Node.place source) node ∧
        PetriNet.Path net node (PetriNet.Node.place sink)) :
    WorkflowNet
      (PetriNet.NormalizedPlace Place)
      (PetriNet.NormalizedTrans Trans) :=
  WorkflowNet.normalized net source sink hconnected

theorem normalization_original_trace_word
    {Activity : Type u}
    {Trans : Type v}
    (label : Trans -> TransitionLabel Activity)
    (trace : List Trans) :
    WorkflowNet.traceWord (WorkflowNet.normalizedLabel label)
      (trace.map PetriNet.NormalizedTrans.original) =
        WorkflowNet.traceWord label trace :=
  WorkflowNet.traceWord_normalized_original label trace

theorem normalization_boundary_trace_word
    {Activity : Type u}
    {Trans : Type v}
    (label : Trans -> TransitionLabel Activity)
    (trace : List Trans) :
    WorkflowNet.traceWord (WorkflowNet.normalizedLabel label)
      (PetriNet.NormalizedTrans.enter ::
        (trace.map PetriNet.NormalizedTrans.original ++
          [PetriNet.NormalizedTrans.exit])) =
        WorkflowNet.traceWord label trace :=
  WorkflowNet.traceWord_normalized_with_boundary label trace

theorem normalization_accepting_firing_sequence
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    {trace : List Trans}
    (sequence :
      WorkflowNet.FiringSequence
        net
        (WorkflowNet.initial net)
        trace
        (WorkflowNet.final net)) :
    WorkflowNet.FiringSequence
      (WorkflowNet.normalizedNet net)
      (WorkflowNet.initial (WorkflowNet.normalizedNet net))
      (PetriNet.NormalizedTrans.enter ::
        (trace.map PetriNet.NormalizedTrans.original ++
          [PetriNet.NormalizedTrans.exit]))
      (WorkflowNet.final (WorkflowNet.normalizedNet net)) :=
  WorkflowNet.normalized_firingSequence_accepting net sequence

theorem normalization_boundary_accepting_firing_sequence_iff
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    {trace : List Trans} :
    WorkflowNet.FiringSequence
      (WorkflowNet.normalizedNet net)
      (WorkflowNet.initial (WorkflowNet.normalizedNet net))
      (PetriNet.NormalizedTrans.enter ::
        (trace.map PetriNet.NormalizedTrans.original ++
          [PetriNet.NormalizedTrans.exit]))
      (WorkflowNet.final (WorkflowNet.normalizedNet net)) ↔
        WorkflowNet.FiringSequence
          net
          (WorkflowNet.initial net)
          trace
          (WorkflowNet.final net) :=
  WorkflowNet.normalized_firingSequence_accepting_iff net

theorem normalization_exit_fires_iff
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (marking : Marking Place) :
    WorkflowNet.fires
      (WorkflowNet.normalizedNet net)
      (Marking.normalize marking)
      PetriNet.NormalizedTrans.exit
      (WorkflowNet.final (WorkflowNet.normalizedNet net)) ↔
        marking = WorkflowNet.final net :=
  WorkflowNet.normalized_exit_fires_iff net marking

theorem normalization_original_transition_enabled_iff
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (marking : Marking Place)
    (trans : Trans) :
    WorkflowNet.enabled
      (WorkflowNet.normalizedNet net)
      (Marking.normalize marking)
      (PetriNet.NormalizedTrans.original trans) ↔
        WorkflowNet.enabled net marking trans :=
  WorkflowNet.normalized_original_enabled_iff net marking trans

theorem normalization_original_transition_fire_eq
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (marking : Marking Place)
    (trans : Trans) :
    WorkflowNet.fire
      (WorkflowNet.normalizedNet net)
      (Marking.normalize marking)
      (PetriNet.NormalizedTrans.original trans) =
        Marking.normalize (WorkflowNet.fire net marking trans) :=
  WorkflowNet.normalized_original_fire_eq net marking trans

theorem normalization_original_transition_fires_iff
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (before after : Marking Place)
    (trans : Trans) :
    WorkflowNet.fires
      (WorkflowNet.normalizedNet net)
      (Marking.normalize before)
      (PetriNet.NormalizedTrans.original trans)
      (Marking.normalize after) ↔
        WorkflowNet.fires net before trans after :=
  WorkflowNet.normalized_original_fires_iff net before after trans

theorem normalization_original_firing_sequence_iff
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {before after : Marking Place}
    {trace : List Trans} :
    WorkflowNet.FiringSequence
      (WorkflowNet.normalizedNet net)
      (Marking.normalize before)
      (trace.map PetriNet.NormalizedTrans.original)
      (Marking.normalize after) ↔
        WorkflowNet.FiringSequence net before trace after :=
  WorkflowNet.normalized_firingSequence_original_iff net

theorem normalization_language_of_original
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {word : List Activity}
    (hlanguage : WorkflowNet.language net label word) :
    WorkflowNet.language
      (WorkflowNet.normalizedNet net)
      (WorkflowNet.normalizedLabel label)
      word :=
  WorkflowNet.normalized_language_of_original hlanguage

theorem lemma3_entry_point_source_iff
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans) :
    WorkflowNet.entryPoints net part net.source ↔
      ∃ trans, part trans ∧ net.placeToTrans net.source trans :=
  WorkflowNet.entryPoints_source_iff net part

theorem lemma3_exit_point_sink_iff
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans) :
    WorkflowNet.exitPoints net part net.sink ↔
      ∃ trans, part trans ∧ net.transToPlace trans net.sink :=
  WorkflowNet.exitPoints_sink_iff net part

theorem lemma3_entry_point_external_input_of_ne_source
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hentry : WorkflowNet.entryPoints net part place)
    (hplace : place ≠ net.source) :
    ∃ trans, ¬ part trans ∧ net.transToPlace trans place :=
  WorkflowNet.entryPoints_external_input_of_ne_source net hentry hplace

theorem lemma3_exit_point_external_output_of_ne_sink
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hexit : WorkflowNet.exitPoints net part place)
    (hplace : place ≠ net.sink) :
    ∃ trans, ¬ part trans ∧ net.placeToTrans place trans :=
  WorkflowNet.exitPoints_external_output_of_ne_sink net hexit hplace

theorem lemma3_entry_point_not_sink
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hentry : WorkflowNet.entryPoints net part place) :
    place ≠ net.sink :=
  WorkflowNet.entryPoints_ne_sink net hentry

theorem lemma3_exit_point_not_source
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hexit : WorkflowNet.exitPoints net part place) :
    place ≠ net.source :=
  WorkflowNet.exitPoints_ne_source net hexit

theorem lemma3_sink_not_entry_point
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans) :
    ¬ WorkflowNet.entryPoints net part net.sink :=
  WorkflowNet.not_entryPoints_sink net part

theorem lemma3_source_not_exit_point
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans) :
    ¬ WorkflowNet.exitPoints net part net.source :=
  WorkflowNet.not_exitPoints_source net part

theorem lemma3_execution_order_of_boundary
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    {left right : Nat}
    {leftPart rightPart : Set Trans}
    {place : Place}
    (hleft : Powl.listGet? partition.parts left = some leftPart)
    (hright : Powl.listGet? partition.parts right = some rightPart)
    (hexit : WorkflowNet.exitPoints net leftPart place)
    (hentry : WorkflowNet.entryPoints net rightPart place) :
    Patterns.executionOrder net partition left right :=
  Patterns.executionOrder_of_boundary
    net partition hleft hright hexit hentry

theorem lemma3_partial_order_pattern_no_self_execution_order
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.partialOrderPattern net partition)
    (index : Nat) :
    ¬ Patterns.executionOrder net partition index index :=
  Patterns.partialOrderPattern_no_self_executionOrder
    net partition hpattern index

theorem lemma3_partial_order_pattern_no_execution_order_cycle
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.partialOrderPattern net partition)
    {left right : Nat}
    (hleftRight : Patterns.executionOrder net partition left right) :
    ¬ Patterns.executionOrder net partition right left :=
  Patterns.partialOrderPattern_no_executionOrder_cycle
    net partition hpattern hleftRight

theorem lemma3_partial_order_pattern_no_same_part_entry_exit
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.partialOrderPattern net partition)
    {index : Nat}
    {part : Set Trans}
    {place : Place}
    (hpart : Powl.listGet? partition.parts index = some part)
    (hexit : WorkflowNet.exitPoints net part place)
    (hentry : WorkflowNet.entryPoints net part place) :
    False :=
  Patterns.partialOrderPattern_no_same_part_entry_exit
    net partition hpattern hpart hexit hentry

theorem lemma3_partial_order_same_part_of_common_postset_reach
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.partialOrderPattern net partition)
    {place : Place}
    {left right : Trans}
    (hleft : Patterns.reachesFromPostset net place left)
    (hright : Patterns.reachesFromPostset net place right) :
    partition.samePart left right :=
  Patterns.partialOrderPattern_samePart_of_reachesFromPostset
    net partition hpattern hleft hright

theorem lemma3_reaches_from_postset_of_place_to_trans
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {place : Place}
    {trans : Trans}
    (hflow : net.placeToTrans place trans) :
    Patterns.reachesFromPostset net place trans :=
  Patterns.reachesFromPostset_of_placeToTrans net hflow

theorem lemma3_partial_order_same_part_of_common_preset
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.partialOrderPattern net partition)
    {place : Place}
    {left right : Trans}
    (hleft : net.placeToTrans place left)
    (hright : net.placeToTrans place right) :
    partition.samePart left right :=
  Patterns.partialOrderPattern_samePart_of_common_preset
    net partition hpattern hleft hright

theorem lemma3_partial_order_part_eq_of_common_postset_reach
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.partialOrderPattern net partition)
    {leftPart rightPart : Set Trans}
    (hleftPartMem : leftPart ∈ partition.parts)
    (hrightPartMem : rightPart ∈ partition.parts)
    {place : Place}
    {left right : Trans}
    (hleftPart : leftPart left)
    (hrightPart : rightPart right)
    (hleftReach : Patterns.reachesFromPostset net place left)
    (hrightReach : Patterns.reachesFromPostset net place right) :
    leftPart = rightPart :=
  Patterns.partialOrderPattern_part_eq_of_common_postset_reach
    net partition hpattern hleftPartMem hrightPartMem
    hleftPart hrightPart hleftReach hrightReach

theorem lemma3_partial_order_part_eq_of_common_preset
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.partialOrderPattern net partition)
    {leftPart rightPart : Set Trans}
    (hleftPartMem : leftPart ∈ partition.parts)
    (hrightPartMem : rightPart ∈ partition.parts)
    {place : Place}
    {left right : Trans}
    (hleftPart : leftPart left)
    (hrightPart : rightPart right)
    (hleft : net.placeToTrans place left)
    (hright : net.placeToTrans place right) :
    leftPart = rightPart :=
  Patterns.partialOrderPattern_part_eq_of_common_preset
    net partition hpattern hleftPartMem hrightPartMem
    hleftPart hrightPart hleft hright

theorem lemma3_partial_order_indexed_part_eq_of_common_postset_reach
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.partialOrderPattern net partition)
    {leftIndex rightIndex : Nat}
    {leftPart rightPart : Set Trans}
    (hleftGet : Powl.listGet? partition.parts leftIndex = some leftPart)
    (hrightGet : Powl.listGet? partition.parts rightIndex = some rightPart)
    {place : Place}
    {left right : Trans}
    (hleftPart : leftPart left)
    (hrightPart : rightPart right)
    (hleftReach : Patterns.reachesFromPostset net place left)
    (hrightReach : Patterns.reachesFromPostset net place right) :
    leftPart = rightPart :=
  Patterns.partialOrderPattern_indexed_part_eq_of_common_postset_reach
    net partition hpattern hleftGet hrightGet
    hleftPart hrightPart hleftReach hrightReach

theorem lemma3_partial_order_indexed_part_eq_of_common_preset
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.partialOrderPattern net partition)
    {leftIndex rightIndex : Nat}
    {leftPart rightPart : Set Trans}
    (hleftGet : Powl.listGet? partition.parts leftIndex = some leftPart)
    (hrightGet : Powl.listGet? partition.parts rightIndex = some rightPart)
    {place : Place}
    {left right : Trans}
    (hleftPart : leftPart left)
    (hrightPart : rightPart right)
    (hleft : net.placeToTrans place left)
    (hright : net.placeToTrans place right) :
    leftPart = rightPart :=
  Patterns.partialOrderPattern_indexed_part_eq_of_common_preset
    net partition hpattern hleftGet hrightGet
    hleftPart hrightPart hleft hright

theorem lemma3_partial_order_entry_places_equivalent
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.partialOrderPattern net partition)
    {index : Nat}
    {part : Set Trans}
    {leftPlace rightPlace : Place}
    (hpart : Powl.listGet? partition.parts index = some part)
    (hleft : WorkflowNet.entryPoints net part leftPlace)
    (hright : WorkflowNet.entryPoints net part rightPlace) :
    PetriNet.placeEquivalentWrt
      net.toPetriNet part leftPlace rightPlace :=
  Patterns.partialOrderPattern_entry_placeEquivalent
    net partition hpattern hpart hleft hright

theorem lemma3_partial_order_exit_places_equivalent
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.partialOrderPattern net partition)
    {index : Nat}
    {part : Set Trans}
    {leftPlace rightPlace : Place}
    (hpart : Powl.listGet? partition.parts index = some part)
    (hleft : WorkflowNet.exitPoints net part leftPlace)
    (hright : WorkflowNet.exitPoints net part rightPlace) :
    PetriNet.placeEquivalentWrt
      net.toPetriNet part leftPlace rightPlace :=
  Patterns.partialOrderPattern_exit_placeEquivalent
    net partition hpattern hpart hleft hright

theorem lemma3_partial_order_entry_placeToTrans_iff
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.partialOrderPattern net partition)
    {index : Nat}
    {part : Set Trans}
    {leftPlace rightPlace : Place}
    (hpart : Powl.listGet? partition.parts index = some part)
    (hleft : WorkflowNet.entryPoints net part leftPlace)
    (hright : WorkflowNet.entryPoints net part rightPlace)
    {trans : Trans}
    (htrans : part trans) :
    net.placeToTrans leftPlace trans ↔
      net.placeToTrans rightPlace trans :=
  Patterns.partialOrderPattern_entry_placeToTrans_iff
    net partition hpattern hpart hleft hright htrans

theorem lemma3_partial_order_entry_transToPlace_iff
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.partialOrderPattern net partition)
    {index : Nat}
    {part : Set Trans}
    {leftPlace rightPlace : Place}
    (hpart : Powl.listGet? partition.parts index = some part)
    (hleft : WorkflowNet.entryPoints net part leftPlace)
    (hright : WorkflowNet.entryPoints net part rightPlace)
    {trans : Trans}
    (htrans : part trans) :
    net.transToPlace trans leftPlace ↔
      net.transToPlace trans rightPlace :=
  Patterns.partialOrderPattern_entry_transToPlace_iff
    net partition hpattern hpart hleft hright htrans

theorem lemma3_partial_order_exit_placeToTrans_iff
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.partialOrderPattern net partition)
    {index : Nat}
    {part : Set Trans}
    {leftPlace rightPlace : Place}
    (hpart : Powl.listGet? partition.parts index = some part)
    (hleft : WorkflowNet.exitPoints net part leftPlace)
    (hright : WorkflowNet.exitPoints net part rightPlace)
    {trans : Trans}
    (htrans : part trans) :
    net.placeToTrans leftPlace trans ↔
      net.placeToTrans rightPlace trans :=
  Patterns.partialOrderPattern_exit_placeToTrans_iff
    net partition hpattern hpart hleft hright htrans

theorem lemma3_partial_order_exit_transToPlace_iff
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : Patterns.partialOrderPattern net partition)
    {index : Nat}
    {part : Set Trans}
    {leftPlace rightPlace : Place}
    (hpart : Powl.listGet? partition.parts index = some part)
    (hleft : WorkflowNet.exitPoints net part leftPlace)
    (hright : WorkflowNet.exitPoints net part rightPlace)
    {trans : Trans}
    (htrans : part trans) :
    net.transToPlace trans leftPlace ↔
      net.transToPlace trans rightPlace :=
  Patterns.partialOrderPattern_exit_transToPlace_iff
    net partition hpattern hpart hleft hright htrans

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

theorem lemma3_partial_order_projection_start_incoming_edge
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part place)
    (hflow : net.transToPlace trans place) :
    (Patterns.partialOrderProjection net part).transToPlace
      trans Patterns.BoundaryPlace.start :=
  Patterns.partialOrderProjection_transToPlace_start
    net hpart hentry hflow

theorem lemma3_partial_order_projection_end_outgoing_edge
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hexit : WorkflowNet.exitPoints net part place)
    (hflow : net.placeToTrans place trans) :
    (Patterns.partialOrderProjection net part).placeToTrans
      Patterns.BoundaryPlace.end_ trans :=
  Patterns.partialOrderProjection_end_placeToTrans
    net hpart hexit hflow

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

theorem lemma3_partial_order_projection_restricted_flow_original
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    {first second :
      PetriNet.Node
        {place : Patterns.BoundaryPlace Place //
          Patterns.partialOrderProjectionPlaces net part place}
        {trans : Trans // part trans}}
    (hflow :
      PetriNet.flow
        (Patterns.partialOrderProjectionRestricted net part)
        first second) :
    PetriNet.flow
      (Patterns.partialOrderProjection net part)
      (PetriNet.restrictedNode first)
      (PetriNet.restrictedNode second) :=
  Patterns.partialOrderProjectionRestricted_flow_original
    net part hflow

theorem lemma3_partial_order_projection_restricted_path_original
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    {source target :
      PetriNet.Node
        {place : Patterns.BoundaryPlace Place //
          Patterns.partialOrderProjectionPlaces net part place}
        {trans : Trans // part trans}}
    (path :
      PetriNet.Path
        (Patterns.partialOrderProjectionRestricted net part)
        source
        target) :
    PetriNet.Path
      (Patterns.partialOrderProjection net part)
      (PetriNet.restrictedNode source)
      (PetriNet.restrictedNode target) :=
  Patterns.partialOrderProjectionRestricted_path_original
    net part path

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

theorem lemma3_partial_order_projection_restricted_start_edge_iff
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (trans : {trans : Trans // part trans}) :
    (Patterns.partialOrderProjectionRestricted net part).placeToTrans
      ⟨Patterns.BoundaryPlace.start,
        Patterns.partialOrderProjectionPlaces_start net part⟩
      trans ↔
        ∃ original,
          WorkflowNet.entryPoints net part original ∧
          net.placeToTrans original trans.val :=
  Patterns.partialOrderProjectionRestricted_start_placeToTrans_iff'
    net trans

theorem lemma3_partial_order_projection_restricted_start_incoming_edge_iff
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (trans : {trans : Trans // part trans}) :
    (Patterns.partialOrderProjectionRestricted net part).transToPlace
      trans
      ⟨Patterns.BoundaryPlace.start,
        Patterns.partialOrderProjectionPlaces_start net part⟩ ↔
        ∃ original,
          WorkflowNet.entryPoints net part original ∧
          net.transToPlace trans.val original :=
  Patterns.partialOrderProjectionRestricted_transToPlace_start_iff'
    net trans

theorem lemma3_partial_order_projection_restricted_end_outgoing_edge
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hexit : WorkflowNet.exitPoints net part place)
    (hflow : net.placeToTrans place trans) :
    (Patterns.partialOrderProjectionRestricted net part).placeToTrans
      ⟨Patterns.BoundaryPlace.end_,
        Patterns.partialOrderProjectionPlaces_end net part⟩
      ⟨trans, hpart⟩ :=
  Patterns.partialOrderProjectionRestricted_end_placeToTrans
    net hpart hexit hflow

theorem lemma3_partial_order_projection_restricted_end_outgoing_edge_iff
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (trans : {trans : Trans // part trans}) :
    (Patterns.partialOrderProjectionRestricted net part).placeToTrans
      ⟨Patterns.BoundaryPlace.end_,
        Patterns.partialOrderProjectionPlaces_end net part⟩
      trans ↔
        ∃ original,
          WorkflowNet.exitPoints net part original ∧
          net.placeToTrans original trans.val :=
  Patterns.partialOrderProjectionRestricted_end_placeToTrans_iff'
    net trans

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

theorem lemma3_partial_order_projection_restricted_end_edge_iff
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (trans : {trans : Trans // part trans}) :
    (Patterns.partialOrderProjectionRestricted net part).transToPlace
      trans
      ⟨Patterns.BoundaryPlace.end_,
        Patterns.partialOrderProjectionPlaces_end net part⟩ ↔
        ∃ original,
          WorkflowNet.exitPoints net part original ∧
          net.transToPlace trans.val original :=
  Patterns.partialOrderProjectionRestricted_transToPlace_end_iff'
    net trans

theorem lemma3_partial_order_projection_restricted_start_incoming_edge
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part place)
    (hflow : net.transToPlace trans place) :
    (Patterns.partialOrderProjectionRestricted net part).transToPlace
      ⟨trans, hpart⟩
      ⟨Patterns.BoundaryPlace.start,
        Patterns.partialOrderProjectionPlaces_start net part⟩ :=
  Patterns.partialOrderProjectionRestricted_transToPlace_start
    net hpart hentry hflow

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

theorem lemma3_partial_order_projection_restricted_internal_placeToTrans_iff
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hplace :
      Patterns.partialOrderProjectionPlaces
        net part (Patterns.BoundaryPlace.original place))
    (trans : {trans : Trans // part trans}) :
    (Patterns.partialOrderProjectionRestricted net part).placeToTrans
      ⟨Patterns.BoundaryPlace.original place, hplace⟩
      trans ↔
        net.placeToTrans place trans.val :=
  Patterns.partialOrderProjectionRestricted_original_placeToTrans_iff'
    net hplace trans

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

theorem lemma3_partial_order_projection_restricted_internal_transToPlace_iff
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (trans : {trans : Trans // part trans})
    {place : Place}
    (hplace :
      Patterns.partialOrderProjectionPlaces
        net part (Patterns.BoundaryPlace.original place)) :
    (Patterns.partialOrderProjectionRestricted net part).transToPlace
      trans
      ⟨Patterns.BoundaryPlace.original place, hplace⟩ ↔
        net.transToPlace trans.val place :=
  Patterns.partialOrderProjectionRestricted_transToPlace_original_iff'
    net trans hplace

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

theorem lemma3_partial_order_projection_transition_to_start
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part place)
    (hflow : net.transToPlace trans place) :
    PetriNet.Path
      (Patterns.partialOrderProjection net part)
      (PetriNet.Node.trans trans)
      (PetriNet.Node.place Patterns.BoundaryPlace.start) :=
  Patterns.partialOrderProjection_transition_to_start
    net hpart hentry hflow

theorem lemma3_partial_order_projection_end_to_transition
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hexit : WorkflowNet.exitPoints net part place)
    (hflow : net.placeToTrans place trans) :
    PetriNet.Path
      (Patterns.partialOrderProjection net part)
      (PetriNet.Node.place Patterns.BoundaryPlace.end_)
      (PetriNet.Node.trans trans) :=
  Patterns.partialOrderProjection_end_to_transition
    net hpart hexit hflow

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

theorem lemma3_partial_order_projection_restricted_transition_to_start
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part place)
    (hflow : net.transToPlace trans place) :
    PetriNet.Path
      (Patterns.partialOrderProjectionRestricted net part)
      (PetriNet.Node.trans ⟨trans, hpart⟩)
      (PetriNet.Node.place
        ⟨Patterns.BoundaryPlace.start,
          Patterns.partialOrderProjectionPlaces_start net part⟩) :=
  Patterns.partialOrderProjectionRestricted_transition_to_start
    net hpart hentry hflow

theorem lemma3_partial_order_projection_restricted_end_to_transition
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hexit : WorkflowNet.exitPoints net part place)
    (hflow : net.placeToTrans place trans) :
    PetriNet.Path
      (Patterns.partialOrderProjectionRestricted net part)
      (PetriNet.Node.place
        ⟨Patterns.BoundaryPlace.end_,
          Patterns.partialOrderProjectionPlaces_end net part⟩)
      (PetriNet.Node.trans ⟨trans, hpart⟩) :=
  Patterns.partialOrderProjectionRestricted_end_to_transition
    net hpart hexit hflow

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
