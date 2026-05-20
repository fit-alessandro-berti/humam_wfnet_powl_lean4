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

end Paper2503_20363

end KouraniWfnetPowl
