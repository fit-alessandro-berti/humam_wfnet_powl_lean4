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

theorem traceWord_append
    {Activity : Type u}
    {Trans : Type v}
    (label : Trans -> TransitionLabel Activity)
    (left right : List Trans) :
    traceWord label (left ++ right) =
      traceWord label left ++ traceWord label right := by
  induction left with
  | nil =>
      rfl
  | cons trans rest ih =>
      simp [traceWord, ih, List.append_assoc]

theorem traceWord_singleton
    {Activity : Type u}
    {Trans : Type v}
    (label : Trans -> TransitionLabel Activity)
    (trans : Trans) :
    traceWord label [trans] = Powl.transitionWord label trans := by
  simp [traceWord]

theorem traceWord_map_subtype
    {Activity : Type u}
    {Trans : Type v}
    {transitions : Set Trans}
    (label : Trans -> TransitionLabel Activity)
    (trace : List {trans : Trans // transitions trans}) :
    traceWord (fun trans => label trans.val) trace =
      traceWord label (trace.map Subtype.val) := by
  induction trace with
  | nil =>
      rfl
  | cons trans rest ih =>
      simp [traceWord, Powl.transitionWord, ih]

def normalizedLabel
    {Activity : Type u}
    {Trans : Type v}
    (label : Trans -> TransitionLabel Activity) :
    PetriNet.NormalizedTrans Trans -> TransitionLabel Activity
  | PetriNet.NormalizedTrans.enter => TransitionLabel.silent
  | PetriNet.NormalizedTrans.original trans => label trans
  | PetriNet.NormalizedTrans.exit => TransitionLabel.silent

theorem normalizedLabel_enter
    {Activity : Type u}
    {Trans : Type v}
    (label : Trans -> TransitionLabel Activity) :
    normalizedLabel label
      (PetriNet.NormalizedTrans.enter : PetriNet.NormalizedTrans Trans) =
      TransitionLabel.silent :=
  rfl

theorem normalizedLabel_exit
    {Activity : Type u}
    {Trans : Type v}
    (label : Trans -> TransitionLabel Activity) :
    normalizedLabel label
      (PetriNet.NormalizedTrans.exit : PetriNet.NormalizedTrans Trans) =
      TransitionLabel.silent :=
  rfl

theorem normalizedLabel_original
    {Activity : Type u}
    {Trans : Type v}
    (label : Trans -> TransitionLabel Activity)
    (trans : Trans) :
    normalizedLabel label (PetriNet.NormalizedTrans.original trans) =
      label trans :=
  rfl

def normalizedSubtypeTransMap
    {Trans : Type u}
    {transitions : Set Trans} :
    PetriNet.NormalizedTrans {trans : Trans // transitions trans} ->
      PetriNet.NormalizedTrans Trans
  | PetriNet.NormalizedTrans.enter => PetriNet.NormalizedTrans.enter
  | PetriNet.NormalizedTrans.original trans =>
      PetriNet.NormalizedTrans.original trans.val
  | PetriNet.NormalizedTrans.exit => PetriNet.NormalizedTrans.exit

theorem normalizedLabel_normalizedSubtypeTransMap
    {Activity : Type u}
    {Trans : Type v}
    {transitions : Set Trans}
    (label : Trans -> TransitionLabel Activity)
    (trans : PetriNet.NormalizedTrans {trans : Trans // transitions trans}) :
    normalizedLabel label (normalizedSubtypeTransMap trans) =
      normalizedLabel
        (fun trans : {trans : Trans // transitions trans} => label trans.val)
        trans := by
  cases trans with
  | enter =>
      rfl
  | original trans =>
      rfl
  | exit =>
      rfl

theorem traceWord_normalized_original
    {Activity : Type u}
    {Trans : Type v}
    (label : Trans -> TransitionLabel Activity)
    (trace : List Trans) :
    traceWord (normalizedLabel label)
      (trace.map PetriNet.NormalizedTrans.original) =
        traceWord label trace := by
  induction trace with
  | nil =>
      rfl
  | cons trans rest ih =>
      simp [traceWord, Powl.transitionWord, normalizedLabel, ih]

theorem traceWord_normalized_enter_cons
    {Activity : Type u}
    {Trans : Type v}
    (label : Trans -> TransitionLabel Activity)
    (trace : List (PetriNet.NormalizedTrans Trans)) :
    traceWord (normalizedLabel label)
      (PetriNet.NormalizedTrans.enter :: trace) =
        traceWord (normalizedLabel label) trace := by
  simp [traceWord, Powl.transitionWord, normalizedLabel, TransitionLabel.word]

theorem traceWord_normalized_exit_singleton
    {Activity : Type u}
    {Trans : Type v}
    (label : Trans -> TransitionLabel Activity) :
    traceWord (normalizedLabel label)
      ([PetriNet.NormalizedTrans.exit] : List (PetriNet.NormalizedTrans Trans)) =
        [] := by
  simp [traceWord, Powl.transitionWord, normalizedLabel, TransitionLabel.word]

theorem traceWord_normalized_with_boundary
    {Activity : Type u}
    {Trans : Type v}
    (label : Trans -> TransitionLabel Activity)
    (trace : List Trans) :
    traceWord (normalizedLabel label)
      (PetriNet.NormalizedTrans.enter ::
        (trace.map PetriNet.NormalizedTrans.original ++
          [PetriNet.NormalizedTrans.exit])) =
        traceWord label trace := by
  simp [traceWord, Powl.transitionWord, normalizedLabel, TransitionLabel.word]
  rw [traceWord_append]
  rw [traceWord_normalized_original]
  simp [traceWord, Powl.transitionWord, normalizedLabel, TransitionLabel.word]

def language
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (label : Trans -> TransitionLabel Activity) :
    Language Activity :=
  fun word =>
    ∃ trace : List Trans,
      FiringSequence net (initial net) trace (final net) ∧
      traceWord label trace = word

def subtypeTraceLanguage
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (label : Trans -> TransitionLabel Activity)
    (transitions : Set Trans) :
    Language Activity :=
  fun word =>
    ∃ trace : List {trans : Trans // transitions trans},
      FiringSequence
        net
        (initial net)
        (trace.map Subtype.val)
        (final net) ∧
      traceWord label (trace.map Subtype.val) = word

def localLanguage
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    (net : WorkflowNet Place Trans)
    (label : Trans -> TransitionLabel Activity)
    (source sink : Place) :
    Language Activity :=
  fun word =>
    ∃ trace : List Trans,
      FiringSequence
        net
        (Marking.single source)
        trace
        (Marking.single sink) ∧
      traceWord label trace = word

def localSubtypeTraceLanguage
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    (net : WorkflowNet Place Trans)
    (label : Trans -> TransitionLabel Activity)
    (transitions : Set Trans)
    (source sink : Place) :
    Language Activity :=
  fun word =>
    ∃ trace : List {trans : Trans // transitions trans},
      FiringSequence
        net
        (Marking.single source)
        (trace.map Subtype.val)
        (Marking.single sink) ∧
      traceWord label (trace.map Subtype.val) = word

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

theorem localLanguage_intro
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    {trace : List Trans}
    {word : List Activity}
    (sequence :
      FiringSequence
        net
        (Marking.single source)
        trace
        (Marking.single sink))
    (hword : traceWord label trace = word) :
    localLanguage net label source sink word :=
  ⟨trace, sequence, hword⟩

theorem language_of_subtypeTraceLanguage
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {transitions : Set Trans}
    {word : List Activity}
    (hlanguage : subtypeTraceLanguage net label transitions word) :
    language net label word := by
  rcases hlanguage with ⟨trace, sequence, hword⟩
  exact language_intro sequence hword

theorem restricted_local_language_iff_localSubtypeTraceLanguage
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (restricted :
      WorkflowNet {place : Place // places place} {trans : Trans // transitions trans})
    (hplaceToTrans :
      ∀ place trans,
        restricted.placeToTrans place trans ↔
          original.placeToTrans place.val trans.val)
    (htransToPlace :
      ∀ trans place,
        restricted.transToPlace trans place ↔
          original.transToPlace trans.val place.val)
    (hpreset :
      ∀ place trans,
        transitions trans ->
          original.placeToTrans place trans ->
            places place)
    (hpostset :
      ∀ trans place,
        transitions trans ->
          original.transToPlace trans place ->
            places place)
    (label : Trans -> TransitionLabel Activity)
    (source sink : {place : Place // places place})
    (word : List Activity) :
    localLanguage restricted (fun trans => label trans.val)
        source sink word ↔
      localSubtypeTraceLanguage original label transitions
        source.val sink.val word := by
  constructor
  · intro hlanguage
    rcases hlanguage with ⟨trace, sequence, hword⟩
    refine ⟨trace, ?_, ?_⟩
    · have lifted :=
        WorkflowNet.restricted_firingSequence_lift
          original restricted hplaceToTrans htransToPlace
          hpreset hpostset sequence
      simpa [Marking.extend_single] using lifted
    · rw [← traceWord_map_subtype label trace]
      exact hword
  · intro htyped
    rcases htyped with ⟨trace, sequence, hword⟩
    refine ⟨trace, ?_, ?_⟩
    · have restrictedSequence :=
        WorkflowNet.restricted_firingSequence_restrict
          original restricted hplaceToTrans htransToPlace sequence
      simpa [Marking.restrict_single] using restrictedSequence
    · rw [traceWord_map_subtype]
      exact hword

theorem restrictedDecisionBranchWorkflowNet_local_language_iff
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {part : Set Trans}
    (hbranch :
      restrictedDecisionBranchWorkflowNet net split join part)
    (label : Trans -> TransitionLabel Activity)
    (word : List Activity) :
    ∃ branchNet :
        WorkflowNet
          {place : Place //
            decisionBranchPlaceSet net split join part place}
          {trans : Trans // part trans},
      branchNet.source.val = split ∧
        branchNet.sink.val = join ∧
        (localLanguage
            branchNet
            (fun trans : {trans : Trans // part trans} =>
              label trans.val)
            branchNet.source
            branchNet.sink
            word ↔
          localSubtypeTraceLanguage
            net
            label
            part
            split
            join
            word) := by
  rcases hbranch with
    ⟨branchNet, hsource, hsink, hplaceToTrans, htransToPlace⟩
  have hiff :
      localLanguage
          branchNet
          (fun trans : {trans : Trans // part trans} =>
            label trans.val)
          branchNet.source
          branchNet.sink
          word ↔
        localSubtypeTraceLanguage
          net
          label
          part
          branchNet.source.val
          branchNet.sink.val
          word :=
    restricted_local_language_iff_localSubtypeTraceLanguage
      net
      branchNet
      hplaceToTrans
      htransToPlace
      (fun place trans hpart hflow =>
        decisionBranchPlaceSet_preset_closed
          net hpart hflow)
      (fun trans place hpart hflow =>
        decisionBranchPlaceSet_postset_closed
          net hpart hflow)
      label
      branchNet.source
      branchNet.sink
      word
  rw [hsource, hsink] at hiff
  exact ⟨branchNet, hsource, hsink, hiff⟩

theorem normalized_language_of_original
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {word : List Activity}
    (hlanguage : language net label word) :
    language (normalizedNet net) (normalizedLabel label) word := by
  rcases hlanguage with ⟨trace, sequence, hword⟩
  refine language_intro
    (normalized_firingSequence_accepting net sequence)
    ?_
  rw [traceWord_normalized_with_boundary, hword]

def normalizedBoundaryLanguage
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (label : Trans -> TransitionLabel Activity) :
    Language Activity :=
  fun word =>
    ∃ trace : List Trans,
      FiringSequence
        (normalizedNet net)
        (initial (normalizedNet net))
        (PetriNet.NormalizedTrans.enter ::
          (trace.map PetriNet.NormalizedTrans.original ++
            [PetriNet.NormalizedTrans.exit]))
        (final (normalizedNet net)) ∧
      traceWord (normalizedLabel label)
        (PetriNet.NormalizedTrans.enter ::
          (trace.map PetriNet.NormalizedTrans.original ++
            [PetriNet.NormalizedTrans.exit])) = word

theorem normalizedBoundaryLanguage_of_original
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {word : List Activity}
    (hlanguage : language net label word) :
    normalizedBoundaryLanguage net label word := by
  rcases hlanguage with ⟨trace, sequence, hword⟩
  refine ⟨trace, normalized_firingSequence_accepting net sequence, ?_⟩
  rw [traceWord_normalized_with_boundary, hword]

theorem original_language_of_normalizedBoundaryLanguage
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {word : List Activity}
    (hlanguage : normalizedBoundaryLanguage net label word) :
    language net label word := by
  rcases hlanguage with ⟨trace, sequence, hword⟩
  refine language_intro
    ((normalized_firingSequence_accepting_iff net).mp sequence)
    ?_
  rw [← hword]
  exact (traceWord_normalized_with_boundary label trace).symm

theorem normalizedBoundaryLanguage_iff_original
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (label : Trans -> TransitionLabel Activity)
    (word : List Activity) :
    normalizedBoundaryLanguage net label word ↔
      language net label word := by
  constructor
  · exact original_language_of_normalizedBoundaryLanguage
  · exact normalizedBoundaryLanguage_of_original

theorem normalized_firingSequence_from_original_or_final_aux
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hproper : properCompletion net)
    (label : Trans -> TransitionLabel Activity)
    {before : Marking Place}
    {start : Marking (PetriNet.NormalizedPlace Place)}
    (hstart : start = Marking.normalize before)
    (hbeforeReachable : reachable net (initial net) before)
    {trace : List (PetriNet.NormalizedTrans Trans)}
    {after : Marking (PetriNet.NormalizedPlace Place)}
    (sequence :
      FiringSequence
        (normalizedNet net)
        start
        trace
        after) :
    (∃ originalAfter originalTrace,
      reachable net (initial net) originalAfter ∧
        after = Marking.normalize originalAfter ∧
        FiringSequence net before originalTrace originalAfter ∧
        traceWord (normalizedLabel label) trace =
          traceWord label originalTrace) ∨
      (∃ originalTrace,
        FiringSequence net before originalTrace (final net) ∧
          after = final (normalizedNet net) ∧
          traceWord (normalizedLabel label) trace =
            traceWord label originalTrace) := by
  induction sequence generalizing before with
  | nil =>
      left
      exact
        ⟨before, [], hbeforeReachable, hstart,
          FiringSequence.nil, rfl⟩
  | cons hfires tail ih =>
      rename_i middle after trans rest
      rw [hstart] at hfires
      cases trans with
      | enter =>
          exact False.elim
            (normalized_original_marking_enter_not_enabled
              net before hfires.1)
      | original trans =>
          have horiginalEnabled :
              enabled net before trans :=
            (normalized_original_enabled_iff net before trans).mp
              hfires.1
          let originalAfter := fire net before trans
          have horiginalFires :
              fires net before trans originalAfter :=
            ⟨horiginalEnabled, rfl⟩
          have hmiddle :
              middle = Marking.normalize originalAfter := by
            rw [hfires.2, normalized_original_fire_eq]
          have horiginalAfterReachable :
              reachable net (initial net) originalAfter := by
            rcases hbeforeReachable with ⟨priorTrace, priorSequence⟩
            exact ⟨priorTrace ++ [trans],
              firingSequence_snoc priorSequence horiginalFires⟩
          rcases ih hmiddle horiginalAfterReachable with hleft | hright
          · rcases hleft with
              ⟨finalOriginal, originalTrace, hfinalReachable,
                hafter, originalSequence, hword⟩
            left
            refine
              ⟨finalOriginal, trans :: originalTrace,
                hfinalReachable, hafter,
                FiringSequence.cons horiginalFires originalSequence,
                ?_⟩
            simp [traceWord, Powl.transitionWord, normalizedLabel, hword]
          · rcases hright with
              ⟨originalTrace, originalSequence, hafter, hword⟩
            right
            refine
              ⟨trans :: originalTrace,
                FiringSequence.cons horiginalFires originalSequence,
                hafter, ?_⟩
            simp [traceWord, Powl.transitionWord, normalizedLabel, hword]
      | exit =>
          have hsinkPositive :
              before net.sink > 0 :=
            (normalized_exit_enabled_iff net
              (Marking.normalize before)).mp hfires.1
          have hbeforeFinal :
              before = final net :=
            hproper before hbeforeReachable hsinkPositive
          subst hbeforeFinal
          have hmiddle :
              middle = final (normalizedNet net) :=
            hfires.2.trans (normalized_exit_fires net).2.symm
          rw [hmiddle] at tail
          rcases normalized_final_firingSequence_nil net tail with
            ⟨hrest, hafter⟩
          subst hrest
          subst hafter
          right
          refine ⟨[], FiringSequence.nil, rfl, ?_⟩
          simp [traceWord, Powl.transitionWord, normalizedLabel,
            TransitionLabel.word]

theorem normalized_firingSequence_from_original_or_final
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hproper : properCompletion net)
    (label : Trans -> TransitionLabel Activity)
    {before : Marking Place}
    (hbeforeReachable : reachable net (initial net) before)
    {trace : List (PetriNet.NormalizedTrans Trans)}
    {after : Marking (PetriNet.NormalizedPlace Place)}
    (sequence :
      FiringSequence
        (normalizedNet net)
        (Marking.normalize before)
        trace
        after) :
    (∃ originalAfter originalTrace,
      reachable net (initial net) originalAfter ∧
        after = Marking.normalize originalAfter ∧
        FiringSequence net before originalTrace originalAfter ∧
        traceWord (normalizedLabel label) trace =
          traceWord label originalTrace) ∨
      (∃ originalTrace,
        FiringSequence net before originalTrace (final net) ∧
          after = final (normalizedNet net) ∧
          traceWord (normalizedLabel label) trace =
            traceWord label originalTrace) :=
  normalized_firingSequence_from_original_or_final_aux
    net hproper label rfl hbeforeReachable sequence

theorem normalized_firingSequence_to_original_accepting_of_proper
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hproper : properCompletion net)
    (label : Trans -> TransitionLabel Activity)
    {before : Marking Place}
    (hbeforeReachable : reachable net (initial net) before)
    {trace : List (PetriNet.NormalizedTrans Trans)}
    (sequence :
      FiringSequence
        (normalizedNet net)
        (Marking.normalize before)
        trace
        (final (normalizedNet net))) :
    ∃ originalTrace,
      FiringSequence net before originalTrace (final net) ∧
        traceWord (normalizedLabel label) trace =
          traceWord label originalTrace := by
  rcases normalized_firingSequence_from_original_or_final
      net hproper label hbeforeReachable sequence with hleft | hright
  · rcases hleft with
      ⟨originalAfter, originalTrace, _hreachable,
        hafter, originalSequence, hword⟩
    exact False.elim
      (normalized_final_ne_normalize net originalAfter hafter)
  · rcases hright with ⟨originalTrace, originalSequence, _hafter, hword⟩
    exact ⟨originalTrace, originalSequence, hword⟩

theorem normalized_accepting_firingSequence_to_original_of_proper
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hproper : properCompletion net)
    (label : Trans -> TransitionLabel Activity)
    {trace : List (PetriNet.NormalizedTrans Trans)}
    (sequence :
      FiringSequence
        (normalizedNet net)
        (initial (normalizedNet net))
        trace
        (final (normalizedNet net))) :
    ∃ originalTrace,
      FiringSequence net (initial net) originalTrace (final net) ∧
        traceWord (normalizedLabel label) trace =
          traceWord label originalTrace := by
  generalize hstart : initial (normalizedNet net) = start at sequence
  generalize hfinish : final (normalizedNet net) = finish at sequence
  cases sequence with
  | nil =>
      exact False.elim
        (normalized_initial_ne_final net (hstart.trans hfinish.symm))
  | cons hfires tail =>
      rename_i middle trans rest
      rw [← hstart] at hfires
      rw [← hfinish] at tail
      cases trans with
      | enter =>
          have hmiddle :
              middle = Marking.normalize (initial net) :=
            hfires.2.trans (normalized_enter_fire_eq net)
          rw [hmiddle] at tail
          exact
            normalized_firingSequence_to_original_accepting_of_proper
              (net := net) (hproper := hproper) (label := label)
              (trace := rest) ⟨[], FiringSequence.nil⟩ tail
      | original trans =>
          exact False.elim
            (normalized_initial_original_not_enabled net trans hfires.1)
      | exit =>
          exact False.elim
            (normalized_initial_exit_not_enabled net hfires.1)

theorem original_language_of_normalized_language_of_proper
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    (hproper : properCompletion net)
    {word : List Activity}
    (hlanguage : language (normalizedNet net) (normalizedLabel label) word) :
    language net label word := by
  rcases hlanguage with ⟨trace, sequence, hword⟩
  rcases normalized_accepting_firingSequence_to_original_of_proper
      net hproper label sequence with
    ⟨originalTrace, originalSequence, htraceWord⟩
  refine language_intro originalSequence ?_
  rw [← hword]
  exact htraceWord.symm

theorem normalized_language_iff_original_of_proper
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (label : Trans -> TransitionLabel Activity)
    (hproper : properCompletion net)
    (word : List Activity) :
    language (normalizedNet net) (normalizedLabel label) word ↔
      language net label word := by
  constructor
  · exact original_language_of_normalized_language_of_proper hproper
  · exact normalized_language_of_original

theorem restricted_language_of_typed_original_sequence
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (restricted :
      WorkflowNet {place : Place // places place} {trans : Trans // transitions trans})
    (hsource : restricted.source.val = original.source)
    (hsink : restricted.sink.val = original.sink)
    (hplaceToTrans :
      ∀ place trans,
        restricted.placeToTrans place trans ↔
          original.placeToTrans place.val trans.val)
    (htransToPlace :
      ∀ trans place,
        restricted.transToPlace trans place ↔
          original.transToPlace trans.val place.val)
    {label : Trans -> TransitionLabel Activity}
    {trace : List {trans : Trans // transitions trans}}
    {word : List Activity}
    (sequence :
      FiringSequence
        original
        (initial original)
        (trace.map Subtype.val)
        (final original))
    (hword : traceWord label (trace.map Subtype.val) = word) :
    language restricted (fun trans => label trans.val) word := by
  refine language_intro
    (WorkflowNet.restricted_firingSequence_restrict_initial_final
      original restricted hsource hsink hplaceToTrans htransToPlace sequence)
    ?_
  rw [traceWord_map_subtype]
  exact hword

theorem original_language_of_restricted_language
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (restricted :
      WorkflowNet {place : Place // places place} {trans : Trans // transitions trans})
    (hsource : restricted.source.val = original.source)
    (hsink : restricted.sink.val = original.sink)
    (hplaceToTrans :
      ∀ place trans,
        restricted.placeToTrans place trans ↔
          original.placeToTrans place.val trans.val)
    (htransToPlace :
      ∀ trans place,
        restricted.transToPlace trans place ↔
          original.transToPlace trans.val place.val)
    (hpreset :
      ∀ place trans,
        transitions trans ->
          original.placeToTrans place trans ->
            places place)
    (hpostset :
      ∀ trans place,
        transitions trans ->
          original.transToPlace trans place ->
            places place)
    {label : Trans -> TransitionLabel Activity}
    {word : List Activity}
    (hlanguage :
      language restricted (fun trans => label trans.val) word) :
    language original label word := by
  rcases hlanguage with ⟨trace, sequence, hword⟩
  refine language_intro
    (WorkflowNet.restricted_firingSequence_lift_initial_final
      original restricted hsource hsink hplaceToTrans htransToPlace
      hpreset hpostset sequence)
    ?_
  rw [← traceWord_map_subtype label trace]
  exact hword

theorem restricted_language_iff_subtypeTraceLanguage
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (restricted :
      WorkflowNet {place : Place // places place} {trans : Trans // transitions trans})
    (hsource : restricted.source.val = original.source)
    (hsink : restricted.sink.val = original.sink)
    (hplaceToTrans :
      ∀ place trans,
        restricted.placeToTrans place trans ↔
          original.placeToTrans place.val trans.val)
    (htransToPlace :
      ∀ trans place,
        restricted.transToPlace trans place ↔
          original.transToPlace trans.val place.val)
    (hpreset :
      ∀ place trans,
        transitions trans ->
          original.placeToTrans place trans ->
            places place)
    (hpostset :
      ∀ trans place,
        transitions trans ->
          original.transToPlace trans place ->
            places place)
    (label : Trans -> TransitionLabel Activity)
    (word : List Activity) :
    language restricted (fun trans => label trans.val) word ↔
      subtypeTraceLanguage original label transitions word := by
  constructor
  · intro hlanguage
    rcases hlanguage with ⟨trace, sequence, hword⟩
    refine ⟨trace, ?_, ?_⟩
    · exact WorkflowNet.restricted_firingSequence_lift_initial_final
        original restricted hsource hsink hplaceToTrans htransToPlace
        hpreset hpostset sequence
    · rw [← traceWord_map_subtype label trace]
      exact hword
  · intro htyped
    rcases htyped with ⟨trace, sequence, hword⟩
    exact restricted_language_of_typed_original_sequence
      original restricted hsource hsink hplaceToTrans htransToPlace
      sequence hword

theorem mapped_subtype_powl_language_iff_subtypeTraceLanguage
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (restricted :
      WorkflowNet {place : Place // places place} {trans : Trans // transitions trans})
    (hsource : restricted.source.val = original.source)
    (hsink : restricted.sink.val = original.sink)
    (hplaceToTrans :
      ∀ place trans,
        restricted.placeToTrans place trans ↔
          original.placeToTrans place.val trans.val)
    (htransToPlace :
      ∀ trans place,
        restricted.transToPlace trans place ↔
          original.transToPlace trans.val place.val)
    (hpreset :
      ∀ place trans,
        transitions trans ->
          original.placeToTrans place trans ->
            places place)
    (hpostset :
      ∀ trans place,
        transitions trans ->
          original.transToPlace trans place ->
            places place)
    (label : Trans -> TransitionLabel Activity)
    (model : Powl {trans : Trans // transitions trans})
    (hmodel :
      ∀ word,
        Powl.language (fun trans : {trans : Trans // transitions trans} =>
            label trans.val) model word ↔
          language restricted
            (fun trans : {trans : Trans // transitions trans} =>
              label trans.val)
            word)
    (word : List Activity) :
    Powl.language label (Powl.map Subtype.val model) word ↔
      subtypeTraceLanguage original label transitions word := by
  exact Iff.trans
    (Powl.language_map Subtype.val label model word)
    (Iff.trans
      (hmodel word)
      (restricted_language_iff_subtypeTraceLanguage
        original restricted hsource hsink hplaceToTrans htransToPlace
        hpreset hpostset label word))

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
