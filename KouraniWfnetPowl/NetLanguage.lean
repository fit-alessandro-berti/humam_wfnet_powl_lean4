import KouraniWfnetPowl.PetriNet
import KouraniWfnetPowl.Powl

namespace KouraniWfnetPowl

namespace WorkflowNet

def traceWord
    {Activity : Type u}
    {Trans : Type v}
    (label : Trans -> TransitionLabel Activity) :
    List Trans -> List Activity
  | [] => []
  | trans :: rest => Powl.transitionWord label trans ++ traceWord label rest

theorem traceWord_nil
    {Activity : Type u}
    {Trans : Type v}
    (label : Trans -> TransitionLabel Activity) :
    traceWord label [] = [] :=
  rfl

theorem traceWord_cons
    {Activity : Type u}
    {Trans : Type v}
    (label : Trans -> TransitionLabel Activity)
    (trans : Trans)
    (rest : List Trans) :
    traceWord label (trans :: rest) =
      Powl.transitionWord label trans ++ traceWord label rest :=
  rfl

theorem traceWord_singleton
    {Activity : Type u}
    {Trans : Type v}
    (label : Trans -> TransitionLabel Activity)
    (trans : Trans) :
    traceWord label [trans] = Powl.transitionWord label trans := by
  simp [traceWord]

def language
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (label : Trans -> TransitionLabel Activity) :
    Language Activity :=
  fun word =>
    ∃ trace,
      FiringSequence net (initial net) trace (final net) ∧
      traceWord label trace = word

theorem language_intro
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {trace : List Trans}
    {word : List Activity}
    (sequence : FiringSequence net (initial net) trace (final net))
    (hword : traceWord label trace = word) :
    language net label word :=
  ⟨trace, sequence, hword⟩

theorem atom_language_of_single_trace_net_language
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {trans : Trans}
    {word : List Activity}
    (hnet : language net label word)
    (hall :
      ∀ trace,
        FiringSequence net (initial net) trace (final net) ->
          trace = [trans]) :
    Powl.language label (Powl.atom trans) word := by
  rcases hnet with ⟨trace, sequence, hword⟩
  have htrace : trace = [trans] := hall trace sequence
  rw [htrace, traceWord_singleton] at hword
  rw [Powl.atom_language_iff]
  exact hword.symm

theorem single_trace_net_language_of_atom_language
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {trans : Trans}
    {word : List Activity}
    (sequence :
      FiringSequence net (initial net) [trans] (final net))
    (hpowl : Powl.language label (Powl.atom trans) word) :
    language net label word := by
  rw [Powl.atom_language_iff] at hpowl
  refine language_intro sequence ?_
  rw [traceWord_singleton]
  exact hpowl.symm

end WorkflowNet

end KouraniWfnetPowl
