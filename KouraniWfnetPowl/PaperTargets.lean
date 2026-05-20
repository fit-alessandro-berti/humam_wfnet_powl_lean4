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

theorem powl_language_map
    {Trans : Type u}
    {Trans' : Type v}
    {Activity : Type w}
    (f : Trans -> Trans')
    (label : Trans' -> TransitionLabel Activity)
    (model : Powl Trans)
    (word : List Activity) :
    Powl.language label (Powl.map f model) word ↔
      Powl.language (fun trans => label (f trans)) model word :=
  Powl.language_map f label model word

theorem subtype_powl_language_lift
    {Trans : Type u}
    {Activity : Type v}
    {transitions : Set Trans}
    (label : Trans -> TransitionLabel Activity)
    (model : Powl {trans : Trans // transitions trans})
    (word : List Activity) :
    Powl.language label (Powl.map Subtype.val model) word ↔
      Powl.language (fun trans => label trans.val) model word :=
  Powl.language_map Subtype.val label model word

theorem language_iff_local_language_source_sink
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (label : Trans -> TransitionLabel Activity)
    (word : List Activity) :
    WorkflowNet.language net label word ↔
      WorkflowNet.localLanguage net label net.source net.sink word :=
  WorkflowNet.language_iff_localLanguage_source_sink net label word

theorem language_eq_local_language_source_sink
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (label : Trans -> TransitionLabel Activity) :
    WorkflowNet.language net label =
      WorkflowNet.localLanguage net label net.source net.sink :=
  WorkflowNet.language_eq_localLanguage_source_sink net label

theorem normalized_subtype_powl_language_lift
    {Trans : Type u}
    {Activity : Type v}
    {transitions : Set Trans}
    (label : Trans -> TransitionLabel Activity)
    (model :
      Powl
        (PetriNet.NormalizedTrans
          {trans : Trans // transitions trans}))
    (word : List Activity) :
    Powl.language
        (WorkflowNet.normalizedLabel label)
        (Powl.map WorkflowNet.normalizedSubtypeTransMap model)
        word ↔
      Powl.language
        (WorkflowNet.normalizedLabel
          (fun trans : {trans : Trans // transitions trans} =>
            label trans.val))
        model
        word := by
  have hlabel :
      (fun trans :
          PetriNet.NormalizedTrans
            {trans : Trans // transitions trans} =>
        WorkflowNet.normalizedLabel label
          (WorkflowNet.normalizedSubtypeTransMap trans)) =
        WorkflowNet.normalizedLabel
          (fun trans : {trans : Trans // transitions trans} =>
            label trans.val) := by
    funext trans
    exact WorkflowNet.normalizedLabel_normalizedSubtypeTransMap
      label trans
  exact Iff.trans
    (Powl.language_map
      WorkflowNet.normalizedSubtypeTransMap
      (WorkflowNet.normalizedLabel label)
      model
      word)
    (by rw [hlabel])

theorem mapped_subtype_model_language_iff_subtype_trace_language
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
          WorkflowNet.language restricted
            (fun trans : {trans : Trans // transitions trans} =>
              label trans.val)
            word)
    (word : List Activity) :
    Powl.language label (Powl.map Subtype.val model) word ↔
      WorkflowNet.subtypeTraceLanguage original label transitions word :=
  WorkflowNet.mapped_subtype_powl_language_iff_subtypeTraceLanguage
    original restricted hsource hsink hplaceToTrans htransToPlace
    hpreset hpostset label model hmodel word

theorem mapped_subtype_model_language_iff_local_subtype_trace_language
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (restricted :
      WorkflowNet
        {place : Place // places place}
        {trans : Trans // transitions trans})
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
    (model : Powl {trans : Trans // transitions trans})
    (hmodel :
      ∀ word,
        Powl.language (fun trans : {trans : Trans // transitions trans} =>
            label trans.val) model word ↔
          WorkflowNet.localLanguage
            restricted
            (fun trans : {trans : Trans // transitions trans} =>
              label trans.val)
            source
            sink
            word)
    (word : List Activity) :
    Powl.language label (Powl.map Subtype.val model) word ↔
      WorkflowNet.localSubtypeTraceLanguage
        original
        label
        transitions
        source.val
        sink.val
        word :=
  WorkflowNet.mapped_subtype_powl_language_iff_localSubtypeTraceLanguage
    original restricted hplaceToTrans htransToPlace
    hpreset hpostset label source sink model hmodel word

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

theorem xor_pattern_language_preservation_unionList
    {Activity : Type u}
    {Trans : Type v}
    {label : Trans -> TransitionLabel Activity}
    {models : List (Powl Trans)}
    {netLanguage : Language Activity}
    (hnet :
      ∀ word,
        netLanguage word ↔
          Language.unionList (models.map (Powl.language label)) word) :
    ∀ word,
      Powl.language label (Powl.xor models) word ↔ netLanguage word := by
  intro word
  rw [Powl.xor_language_iff_unionList]
  exact Iff.symm (hnet word)

theorem xor_pattern_language_preservation_of_component_equiv
    {Activity : Type u}
    {Trans : Type v}
    {label : Trans -> TransitionLabel Activity}
    {models : List (Powl Trans)}
    {componentLanguage : Powl Trans -> Language Activity}
    {netLanguage : Language Activity}
    (hcomponent :
      ∀ model word,
        Powl.language label model word ↔ componentLanguage model word)
    (hnet :
      ∀ word,
        netLanguage word ↔
          Language.unionList (models.map componentLanguage) word) :
    ∀ word,
      Powl.language label (Powl.xor models) word ↔ netLanguage word := by
  intro word
  rw [Powl.xor_language_iff_unionList]
  exact Iff.trans
    (Language.unionList_map_congr
      models
      (Powl.language label)
      componentLanguage
      hcomponent
      word)
    (Iff.symm (hnet word))

theorem xor_pattern_language_preservation_of_indexed_components
    {Activity : Type u}
    {Trans : Type v}
    {label : Trans -> TransitionLabel Activity}
    {models : List (Powl Trans)}
    {componentLanguages : List (Language Activity)}
    {netLanguage : Language Activity}
    (hlength : componentLanguages.length = models.length)
    (hcomponent :
      ∀ index model componentLanguage,
        Powl.listGet? models index = some model ->
        Powl.listGet? componentLanguages index = some componentLanguage ->
          ∀ word,
            Powl.language label model word ↔ componentLanguage word)
    (hnet :
      ∀ word,
        netLanguage word ↔ Language.unionList componentLanguages word) :
    ∀ word,
      Powl.language label (Powl.xor models) word ↔ netLanguage word := by
  intro word
  rw [Powl.xor_language_iff_unionList]
  have hmappedLength :
      (models.map (Powl.language label)).length =
        componentLanguages.length := by
    simp [hlength]
  exact Iff.trans
    (Powl.unionList_congr_indexed
      hmappedLength
      (by
        intro index modelLanguage componentLanguage hmodelLanguage
          hcomponentLanguage
        rcases Powl.listGet?_map_some hmodelLanguage with
          ⟨model, hmodel, hmodelLanguageEq⟩
        subst hmodelLanguageEq
        exact hcomponent index model componentLanguage
          hmodel hcomponentLanguage)
      word)
    (Iff.symm (hnet word))

theorem xor_pattern_language_preservation_of_mapped_indexed_components
    {Activity : Type u}
    {SubTrans : Type v}
    {Trans : Type w}
    (f : SubTrans -> Trans)
    {label : Trans -> TransitionLabel Activity}
    {models : List (Powl SubTrans)}
    {componentLanguages : List (Language Activity)}
    {netLanguage : Language Activity}
    (hlength : componentLanguages.length = models.length)
    (hcomponent :
      ∀ index model componentLanguage,
        Powl.listGet? models index = some model ->
        Powl.listGet? componentLanguages index = some componentLanguage ->
          ∀ word,
            Powl.language (fun trans => label (f trans)) model word ↔
              componentLanguage word)
    (hnet :
      ∀ word,
        netLanguage word ↔ Language.unionList componentLanguages word) :
    ∀ word,
      Powl.language label
          (Powl.xor (models.map (Powl.map f))) word ↔
        netLanguage word := by
  exact
    xor_pattern_language_preservation_of_indexed_components
      (label := label)
      (models := models.map (Powl.map f))
      (componentLanguages := componentLanguages)
      (netLanguage := netLanguage)
      (by simpa using hlength)
      (by
        intro index mappedModel componentLanguage hmappedModel
          hcomponentLanguage word
        rcases Powl.listGet?_map_some hmappedModel with
          ⟨model, hmodel, hmappedModelEq⟩
        subst hmappedModelEq
        exact Iff.trans
          (Powl.language_map f label model word)
          (hcomponent index model componentLanguage
            hmodel hcomponentLanguage word))
      hnet

theorem local_xor_language_preservation_of_mapped_branch_models
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    (branches : List
      (Σ part : Set Trans, Powl {trans : Trans // part trans}))
    (hmodels :
      ∀ (branch :
          Σ part : Set Trans, Powl {trans : Trans // part trans})
        word,
        Powl.language
            (fun trans : {trans : Trans // branch.1 trans} =>
              label trans.val)
            branch.2
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            branch.1
            source
            sink
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label source sink word ↔
          Language.unionList
            (branches.map
              (fun branch =>
                WorkflowNet.localSubtypeTraceLanguage
                  net label branch.1 source sink))
            word) :
    ∀ word,
      Powl.language label
          (Powl.xor
            (branches.map
              (fun branch => Powl.map Subtype.val branch.2)))
          word ↔
        WorkflowNet.localLanguage net label source sink word := by
  intro word
  rw [Powl.xor_language_iff_unionList]
  exact Iff.trans
    (by
      simpa [List.map_map] using
        Language.unionList_map_congr
          branches
          (fun branch =>
            Powl.language label (Powl.map Subtype.val branch.2))
          (fun branch =>
            WorkflowNet.localSubtypeTraceLanguage
              net label branch.1 source sink)
          (fun branch word =>
            Iff.trans
              (Powl.language_map Subtype.val label branch.2 word)
              (hmodels branch word))
          word)
    (Iff.symm (hdecompose word))

theorem local_xor_language_eq_of_mapped_branch_models
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    (branches : List
      (Σ part : Set Trans, Powl {trans : Trans // part trans}))
    (hmodels :
      ∀ (branch :
          Σ part : Set Trans, Powl {trans : Trans // part trans})
        word,
        Powl.language
            (fun trans : {trans : Trans // branch.1 trans} =>
              label trans.val)
            branch.2
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            branch.1
            source
            sink
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label source sink word ↔
          Language.unionList
            (branches.map
              (fun branch =>
                WorkflowNet.localSubtypeTraceLanguage
                  net label branch.1 source sink))
            word) :
    Powl.language label
        (Powl.xor
          (branches.map
            (fun branch => Powl.map Subtype.val branch.2))) =
      WorkflowNet.localLanguage net label source sink :=
  Language.ext
    (local_xor_language_preservation_of_mapped_branch_models
      branches hmodels hdecompose)

theorem local_loop_language_preservation_of_mapped_subtype_components
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    {bodyPart redoPart : Set Trans}
    {body : Powl {trans : Trans // bodyPart trans}}
    {redo : Powl {trans : Trans // redoPart trans}}
    (hbody :
      ∀ word,
        Powl.language
            (fun trans : {trans : Trans // bodyPart trans} =>
              label trans.val)
            body
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            bodyPart
            source
            sink
            word)
    (hredo :
      ∀ word,
        Powl.language
            (fun trans : {trans : Trans // redoPart trans} =>
              label trans.val)
            redo
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            redoPart
            sink
            source
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label source sink word ↔
          Language.concat
            (WorkflowNet.localSubtypeTraceLanguage
              net label bodyPart source sink)
            (Language.Star
              (Language.concat
                (WorkflowNet.localSubtypeTraceLanguage
                  net label redoPart sink source)
                (WorkflowNet.localSubtypeTraceLanguage
                  net label bodyPart source sink)))
            word) :
    ∀ word,
      Powl.language label
          (Powl.loop
            (Powl.map Subtype.val body)
            (Powl.map Subtype.val redo))
          word ↔
        WorkflowNet.localLanguage net label source sink word := by
  intro word
  rw [Powl.loop_language_iff_concat_star]
  exact Iff.trans
    (Language.concat_congr
      (fun item =>
        Iff.trans
          (Powl.language_map Subtype.val label body item)
          (hbody item))
      (Language.star_congr
        (fun item =>
          Language.concat_congr
            (fun redoWord =>
              Iff.trans
                (Powl.language_map Subtype.val label redo redoWord)
                (hredo redoWord))
            (fun bodyWord =>
              Iff.trans
                (Powl.language_map Subtype.val label body bodyWord)
                (hbody bodyWord))
            item))
      word)
    (Iff.symm (hdecompose word))

theorem local_loop_language_eq_of_mapped_subtype_components
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    {bodyPart redoPart : Set Trans}
    {body : Powl {trans : Trans // bodyPart trans}}
    {redo : Powl {trans : Trans // redoPart trans}}
    (hbody :
      ∀ word,
        Powl.language
            (fun trans : {trans : Trans // bodyPart trans} =>
              label trans.val)
            body
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            bodyPart
            source
            sink
            word)
    (hredo :
      ∀ word,
        Powl.language
            (fun trans : {trans : Trans // redoPart trans} =>
              label trans.val)
            redo
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            redoPart
            sink
            source
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label source sink word ↔
          Language.concat
            (WorkflowNet.localSubtypeTraceLanguage
              net label bodyPart source sink)
            (Language.Star
              (Language.concat
                (WorkflowNet.localSubtypeTraceLanguage
                  net label redoPart sink source)
                (WorkflowNet.localSubtypeTraceLanguage
                  net label bodyPart source sink)))
            word) :
    Powl.language label
        (Powl.loop
          (Powl.map Subtype.val body)
          (Powl.map Subtype.val redo)) =
      WorkflowNet.localLanguage net label source sink :=
  Language.ext
    (local_loop_language_preservation_of_mapped_subtype_components
      hbody hredo hdecompose)

theorem local_partial_order_language_preservation_of_mapped_branch_models
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    {order : Rel Nat}
    (branches : List
      (Σ part : Set Trans, Powl {trans : Trans // part trans}))
    (hmodels :
      ∀ (branch :
          Σ part : Set Trans, Powl {trans : Trans // part trans})
        word,
        Powl.language
            (fun trans : {trans : Trans // branch.1 trans} =>
              label trans.val)
            branch.2
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            branch.1
            source
            sink
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label source sink word ↔
          Powl.partialOrderComponentLanguage
            order
            (branches.map
              (fun branch =>
                WorkflowNet.localSubtypeTraceLanguage
                  net label branch.1 source sink))
            word) :
    ∀ word,
      Powl.language label
          (Powl.partialOrder order
            (branches.map
              (fun branch => Powl.map Subtype.val branch.2)))
          word ↔
        WorkflowNet.localLanguage net label source sink word := by
  intro word
  rw [Powl.partial_order_language_iff_componentLanguage]
  exact Iff.trans
    (by
      simpa [List.map_map] using
        Powl.partialOrderComponentLanguage_map_congr
          order
          branches
          (fun branch =>
            Powl.language label (Powl.map Subtype.val branch.2))
          (fun branch =>
            WorkflowNet.localSubtypeTraceLanguage
              net label branch.1 source sink)
          (fun branch word =>
            Iff.trans
              (Powl.language_map Subtype.val label branch.2 word)
              (hmodels branch word))
          word)
    (Iff.symm (hdecompose word))

theorem local_partial_order_language_eq_of_mapped_branch_models
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    {order : Rel Nat}
    (branches : List
      (Σ part : Set Trans, Powl {trans : Trans // part trans}))
    (hmodels :
      ∀ (branch :
          Σ part : Set Trans, Powl {trans : Trans // part trans})
        word,
        Powl.language
            (fun trans : {trans : Trans // branch.1 trans} =>
              label trans.val)
            branch.2
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            branch.1
            source
            sink
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label source sink word ↔
          Powl.partialOrderComponentLanguage
            order
            (branches.map
              (fun branch =>
                WorkflowNet.localSubtypeTraceLanguage
                  net label branch.1 source sink))
            word) :
    Powl.language label
        (Powl.partialOrder order
          (branches.map
            (fun branch => Powl.map Subtype.val branch.2))) =
      WorkflowNet.localLanguage net label source sink :=
  Language.ext
    (local_partial_order_language_preservation_of_mapped_branch_models
      branches hmodels hdecompose)

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

theorem loop_pattern_language_preservation_of_component_equiv
    {Activity : Type u}
    {Trans : Type v}
    {label : Trans -> TransitionLabel Activity}
    {body redo : Powl Trans}
    {bodyLanguage redoLanguage netLanguage : Language Activity}
    (hbody :
      ∀ word,
        Powl.language label body word ↔ bodyLanguage word)
    (hredo :
      ∀ word,
        Powl.language label redo word ↔ redoLanguage word)
    (hnet :
      ∀ word,
        netLanguage word ↔
          Language.concat bodyLanguage
            (Language.Star
              (Language.concat redoLanguage bodyLanguage)) word) :
    ∀ word,
      Powl.language label (Powl.loop body redo) word ↔ netLanguage word := by
  intro word
  rw [Powl.loop_language_iff_concat_star]
  exact Iff.trans
    (Language.concat_congr
      hbody
      (Language.star_congr
        (fun item =>
          Language.concat_congr hredo hbody item))
      word)
    (Iff.symm (hnet word))

theorem loop_pattern_language_preservation_of_mapped_components
    {Activity : Type u}
    {SubTrans : Type v}
    {Trans : Type w}
    (f : SubTrans -> Trans)
    {label : Trans -> TransitionLabel Activity}
    {body redo : Powl SubTrans}
    {bodyLanguage redoLanguage netLanguage : Language Activity}
    (hbody :
      ∀ word,
        Powl.language (fun trans => label (f trans)) body word ↔
          bodyLanguage word)
    (hredo :
      ∀ word,
        Powl.language (fun trans => label (f trans)) redo word ↔
          redoLanguage word)
    (hnet :
      ∀ word,
        netLanguage word ↔
          Language.concat bodyLanguage
            (Language.Star
              (Language.concat redoLanguage bodyLanguage)) word) :
    ∀ word,
      Powl.language label
          (Powl.loop (Powl.map f body) (Powl.map f redo)) word ↔
        netLanguage word :=
  loop_pattern_language_preservation_of_component_equiv
    (label := label)
    (body := Powl.map f body)
    (redo := Powl.map f redo)
    (bodyLanguage := bodyLanguage)
    (redoLanguage := redoLanguage)
    (netLanguage := netLanguage)
    (fun word =>
      Iff.trans (Powl.language_map f label body word) (hbody word))
    (fun word =>
      Iff.trans (Powl.language_map f label redo word) (hredo word))
    hnet

theorem loop_pattern_language_preservation_of_heterogeneous_mapped_components
    {Activity : Type u}
    {BodyTrans : Type v}
    {RedoTrans : Type w}
    {Trans : Type x}
    (bodyMap : BodyTrans -> Trans)
    (redoMap : RedoTrans -> Trans)
    {label : Trans -> TransitionLabel Activity}
    {body : Powl BodyTrans}
    {redo : Powl RedoTrans}
    {bodyLanguage redoLanguage netLanguage : Language Activity}
    (hbody :
      ∀ word,
        Powl.language (fun trans => label (bodyMap trans)) body word ↔
          bodyLanguage word)
    (hredo :
      ∀ word,
        Powl.language (fun trans => label (redoMap trans)) redo word ↔
          redoLanguage word)
    (hnet :
      ∀ word,
        netLanguage word ↔
          Language.concat bodyLanguage
            (Language.Star
              (Language.concat redoLanguage bodyLanguage)) word) :
    ∀ word,
      Powl.language label
          (Powl.loop (Powl.map bodyMap body) (Powl.map redoMap redo))
          word ↔
        netLanguage word :=
  loop_pattern_language_preservation_of_component_equiv
    (label := label)
    (body := Powl.map bodyMap body)
    (redo := Powl.map redoMap redo)
    (bodyLanguage := bodyLanguage)
    (redoLanguage := redoLanguage)
    (netLanguage := netLanguage)
    (fun word =>
      Iff.trans (Powl.language_map bodyMap label body word)
        (hbody word))
    (fun word =>
      Iff.trans (Powl.language_map redoMap label redo word)
        (hredo word))
    hnet

theorem loop_pattern_language_preservation_of_mapped_subtype_components
    {Activity : Type u}
    {Trans : Type v}
    {label : Trans -> TransitionLabel Activity}
    {bodyPart redoPart : Set Trans}
    {body : Powl {trans : Trans // bodyPart trans}}
    {redo : Powl {trans : Trans // redoPart trans}}
    {bodyLanguage redoLanguage netLanguage : Language Activity}
    (hbody :
      ∀ word,
        Powl.language
            (fun trans : {trans : Trans // bodyPart trans} =>
              label trans.val)
            body
            word ↔
          bodyLanguage word)
    (hredo :
      ∀ word,
        Powl.language
            (fun trans : {trans : Trans // redoPart trans} =>
              label trans.val)
            redo
            word ↔
          redoLanguage word)
    (hnet :
      ∀ word,
        netLanguage word ↔
          Language.concat bodyLanguage
            (Language.Star
              (Language.concat redoLanguage bodyLanguage)) word) :
    ∀ word,
      Powl.language label
          (Powl.loop
            (Powl.map Subtype.val body)
            (Powl.map Subtype.val redo))
          word ↔
        netLanguage word :=
  loop_pattern_language_preservation_of_heterogeneous_mapped_components
    (bodyMap := Subtype.val)
    (redoMap := Subtype.val)
    (label := label)
    (body := body)
    (redo := redo)
    (bodyLanguage := bodyLanguage)
    (redoLanguage := redoLanguage)
    (netLanguage := netLanguage)
    hbody hredo hnet

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

theorem partial_order_pattern_language_preservation_of_component_equiv
    {Activity : Type u}
    {Trans : Type v}
    {label : Trans -> TransitionLabel Activity}
    {order : Rel Nat}
    {models : List (Powl Trans)}
    {componentLanguage : Powl Trans -> Language Activity}
    {netLanguage : Language Activity}
    (hcomponent :
      ∀ model word,
        Powl.language label model word ↔ componentLanguage model word)
    (hnet :
      ∀ word,
        netLanguage word ↔
          Powl.partialOrderComponentLanguage
            order
            (models.map componentLanguage)
            word) :
    ∀ word,
      Powl.language label (Powl.partialOrder order models) word ↔
        netLanguage word := by
  intro word
  rw [Powl.partial_order_language_iff_componentLanguage]
  exact Iff.trans
    (Powl.partialOrderComponentLanguage_map_congr
      order
      models
      (Powl.language label)
      componentLanguage
      hcomponent
      word)
    (Iff.symm (hnet word))

theorem partial_order_pattern_language_preservation_of_indexed_components
    {Activity : Type u}
    {Trans : Type v}
    {label : Trans -> TransitionLabel Activity}
    {order : Rel Nat}
    {models : List (Powl Trans)}
    {componentLanguages : List (Language Activity)}
    {netLanguage : Language Activity}
    (hlength : componentLanguages.length = models.length)
    (hcomponent :
      ∀ index model componentLanguage,
        Powl.listGet? models index = some model ->
        Powl.listGet? componentLanguages index = some componentLanguage ->
          ∀ word,
            Powl.language label model word ↔ componentLanguage word)
    (hnet :
      ∀ word,
        netLanguage word ↔
          Powl.partialOrderComponentLanguage
            order
            componentLanguages
            word) :
    ∀ word,
      Powl.language label (Powl.partialOrder order models) word ↔
        netLanguage word := by
  intro word
  rw [Powl.partial_order_language_iff_componentLanguage]
  have hmappedLength :
      (models.map (Powl.language label)).length =
        componentLanguages.length := by
    simp [hlength]
  exact Iff.trans
    (Powl.partialOrderComponentLanguage_congr
      order
      hmappedLength
      (by
        intro index modelLanguage componentLanguage hmodelLanguage
          hcomponentLanguage
        rcases Powl.listGet?_map_some hmodelLanguage with
          ⟨model, hmodel, hmodelLanguageEq⟩
        subst hmodelLanguageEq
        exact hcomponent index model componentLanguage
          hmodel hcomponentLanguage)
      word)
    (Iff.symm (hnet word))

theorem partial_order_pattern_language_preservation_of_mapped_indexed_components
    {Activity : Type u}
    {SubTrans : Type v}
    {Trans : Type w}
    (f : SubTrans -> Trans)
    {label : Trans -> TransitionLabel Activity}
    {order : Rel Nat}
    {models : List (Powl SubTrans)}
    {componentLanguages : List (Language Activity)}
    {netLanguage : Language Activity}
    (hlength : componentLanguages.length = models.length)
    (hcomponent :
      ∀ index model componentLanguage,
        Powl.listGet? models index = some model ->
        Powl.listGet? componentLanguages index = some componentLanguage ->
          ∀ word,
            Powl.language (fun trans => label (f trans)) model word ↔
              componentLanguage word)
    (hnet :
      ∀ word,
        netLanguage word ↔
          Powl.partialOrderComponentLanguage
            order
            componentLanguages
            word) :
    ∀ word,
      Powl.language label
          (Powl.partialOrder order (models.map (Powl.map f))) word ↔
        netLanguage word := by
  exact
    partial_order_pattern_language_preservation_of_indexed_components
      (label := label)
      (order := order)
      (models := models.map (Powl.map f))
      (componentLanguages := componentLanguages)
      (netLanguage := netLanguage)
      (by simpa using hlength)
      (by
        intro index mappedModel componentLanguage hmappedModel
          hcomponentLanguage word
        rcases Powl.listGet?_map_some hmappedModel with
          ⟨model, hmodel, hmappedModelEq⟩
        subst hmappedModelEq
        exact Iff.trans
          (Powl.language_map f label model word)
          (hcomponent index model componentLanguage
            hmodel hcomponentLanguage word))
      hnet

theorem partial_order_pattern_language_preservation_of_heterogeneous_mapped_components
    {Activity : Type u}
    {Trans : Type v}
    {label : Trans -> TransitionLabel Activity}
    {order : Rel Nat}
    {netLanguage : Language Activity}
    (components :
      List
        (Σ SubTrans : Type w,
          (SubTrans -> Trans) × Powl SubTrans × Language Activity))
    (hcomponent :
      ∀ (component :
          Σ SubTrans : Type w,
            (SubTrans -> Trans) × Powl SubTrans × Language Activity)
        word,
        Powl.language
            (fun trans : component.1 => label (component.2.1 trans))
            component.2.2.1
            word ↔
          component.2.2.2 word)
    (hnet :
      ∀ word,
        netLanguage word ↔
          Powl.partialOrderComponentLanguage
            order
            (components.map (fun component => component.2.2.2))
            word) :
    ∀ word,
      Powl.language label
          (Powl.partialOrder order
            (components.map
              (fun component =>
                Powl.map component.2.1 component.2.2.1)))
          word ↔
        netLanguage word := by
  intro word
  rw [Powl.partial_order_language_iff_componentLanguage]
  exact Iff.trans
    (by
      simpa [List.map_map] using
        Powl.partialOrderComponentLanguage_map_congr
          order
          components
          (fun component =>
            Powl.language label
              (Powl.map component.2.1 component.2.2.1))
          (fun component => component.2.2.2)
          (fun component word =>
            Iff.trans
              (Powl.language_map
                component.2.1 label component.2.2.1 word)
              (hcomponent component word))
          word)
    (Iff.symm (hnet word))

theorem partial_order_pattern_language_preservation_of_mapped_subtype_components
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    {label : Trans -> TransitionLabel Activity}
    {order : Rel Nat}
    (branches :
      List
        (Σ part : {part : Set Trans // part ∈ partition.parts},
          Powl {trans : Trans // part.val trans}))
    (hmodels :
      ∀ (branch :
          Σ part : {part : Set Trans // part ∈ partition.parts},
            Powl {trans : Trans // part.val trans})
        word,
        Powl.language
            (fun trans : {trans : Trans // branch.1.val trans} =>
              label trans.val)
            branch.2
            word ↔
          WorkflowNet.subtypeTraceLanguage net label branch.1.val word)
    (hdecompose :
      ∀ word,
        WorkflowNet.language net label word ↔
          Powl.partialOrderComponentLanguage
            order
            (branches.map
              (fun branch =>
                WorkflowNet.subtypeTraceLanguage net label branch.1.val))
            word) :
    ∀ word,
      Powl.language label
          (Powl.partialOrder order
            (branches.map
              (fun branch => Powl.map Subtype.val branch.2)))
          word ↔
        WorkflowNet.language net label word := by
  intro word
  rw [Powl.partial_order_language_iff_componentLanguage]
  exact Iff.trans
    (by
      simpa [List.map_map] using
        Powl.partialOrderComponentLanguage_map_congr
          order
          branches
          (fun branch =>
            Powl.language label (Powl.map Subtype.val branch.2))
          (fun branch =>
            WorkflowNet.subtypeTraceLanguage net label branch.1.val)
          (fun branch word =>
            Iff.trans
              (Powl.language_map Subtype.val label branch.2 word)
              (hmodels branch word))
          word)
    (Iff.symm (hdecompose word))

theorem partial_order_pattern_language_preservation_of_normalized_mapped_subtype_components
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    {label : Trans -> TransitionLabel Activity}
    {order : Rel Nat}
    (branches :
      List
        (Σ part : {part : Set Trans // part ∈ partition.parts},
          Powl
            (PetriNet.NormalizedTrans
              {trans : Trans // part.val trans})))
    (componentLanguage :
      (Σ part : {part : Set Trans // part ∈ partition.parts},
        Powl
          (PetriNet.NormalizedTrans
            {trans : Trans // part.val trans})) ->
        Language Activity)
    (hmodels :
      ∀ (branch :
          Σ part : {part : Set Trans // part ∈ partition.parts},
            Powl
              (PetriNet.NormalizedTrans
                {trans : Trans // part.val trans}))
        word,
        Powl.language
            (WorkflowNet.normalizedLabel
              (fun trans : {trans : Trans // branch.1.val trans} =>
                label trans.val))
            branch.2
            word ↔
          componentLanguage branch word)
    (hdecompose :
      ∀ word,
        WorkflowNet.language net label word ↔
          Powl.partialOrderComponentLanguage
            order
            (branches.map componentLanguage)
            word) :
    ∀ word,
      Powl.language
          (WorkflowNet.normalizedLabel label)
          (Powl.partialOrder order
            (branches.map
              (fun branch =>
                Powl.map
                  WorkflowNet.normalizedSubtypeTransMap
                  branch.2)))
          word ↔
        WorkflowNet.language net label word := by
  intro word
  rw [Powl.partial_order_language_iff_componentLanguage]
  exact Iff.trans
    (by
      simpa [List.map_map] using
        Powl.partialOrderComponentLanguage_map_congr
          order
          branches
          (fun branch =>
            Powl.language
              (WorkflowNet.normalizedLabel label)
              (Powl.map
                WorkflowNet.normalizedSubtypeTransMap
                branch.2))
          componentLanguage
          (fun branch word =>
            Iff.trans
              (normalized_subtype_powl_language_lift
                label branch.2 word)
              (hmodels branch word))
          word)
    (Iff.symm (hdecompose word))

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

theorem theorem1_loop_case_of_recursive_component_correctness
    {Place : Type u}
    {BodyPlace : Type v}
    {RedoPlace : Type w}
    {Trans : Type x}
    {Activity : Type y}
    [DecidableEq Place]
    [DecidableEq BodyPlace]
    [DecidableEq RedoPlace]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {bodyPart redoPart : Set Trans}
    (bodyNet : WorkflowNet BodyPlace {trans : Trans // bodyPart trans})
    (redoNet : WorkflowNet RedoPlace {trans : Trans // redoPart trans})
    {body : Powl {trans : Trans // bodyPart trans}}
    {redo : Powl {trans : Trans // redoPart trans}}
    (hbody :
      ∀ word,
        WorkflowNet.language
            bodyNet
            (fun trans : {trans : Trans // bodyPart trans} =>
              label trans.val)
            word ↔
          Powl.language
            (fun trans : {trans : Trans // bodyPart trans} =>
              label trans.val)
            body
            word)
    (hredo :
      ∀ word,
        WorkflowNet.language
            redoNet
            (fun trans : {trans : Trans // redoPart trans} =>
              label trans.val)
            word ↔
          Powl.language
            (fun trans : {trans : Trans // redoPart trans} =>
              label trans.val)
            redo
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.language net label word ↔
          Language.concat
            (WorkflowNet.language
              bodyNet
              (fun trans : {trans : Trans // bodyPart trans} =>
                label trans.val))
            (Language.Star
              (Language.concat
                (WorkflowNet.language
                  redoNet
                  (fun trans : {trans : Trans // redoPart trans} =>
                    label trans.val))
                (WorkflowNet.language
                  bodyNet
                  (fun trans : {trans : Trans // bodyPart trans} =>
                    label trans.val))))
            word) :
    ∀ word,
      WorkflowNet.language net label word ↔
        Powl.language label
          (Powl.loop
            (Powl.map Subtype.val body)
            (Powl.map Subtype.val redo))
          word := by
  intro word
  exact Iff.symm
    (loop_pattern_language_preservation_of_mapped_subtype_components
      (label := label)
      (body := body)
      (redo := redo)
      (bodyLanguage :=
        WorkflowNet.language
          bodyNet
          (fun trans : {trans : Trans // bodyPart trans} =>
            label trans.val))
      (redoLanguage :=
        WorkflowNet.language
          redoNet
          (fun trans : {trans : Trans // redoPart trans} =>
            label trans.val))
      (netLanguage := WorkflowNet.language net label)
      (fun word => Iff.symm (hbody word))
      (fun word => Iff.symm (hredo word))
      hdecompose
      word)

theorem theorem1_partial_order_case_of_recursive_component_correctness
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    {label : Trans -> TransitionLabel Activity}
    {order : Rel Nat}
    (branches :
      List
        (Σ part : {part : Set Trans // part ∈ partition.parts},
          Powl {trans : Trans // part.val trans}))
    (hbranches :
      ∀ (branch :
          Σ part : {part : Set Trans // part ∈ partition.parts},
            Powl {trans : Trans // part.val trans})
        word,
        WorkflowNet.subtypeTraceLanguage net label branch.1.val word ↔
          Powl.language
            (fun trans : {trans : Trans // branch.1.val trans} =>
              label trans.val)
            branch.2
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.language net label word ↔
          Powl.partialOrderComponentLanguage
            order
            (branches.map
              (fun branch =>
                WorkflowNet.subtypeTraceLanguage net label branch.1.val))
            word) :
    ∀ word,
      WorkflowNet.language net label word ↔
        Powl.language label
          (Powl.partialOrder order
            (branches.map
              (fun branch => Powl.map Subtype.val branch.2)))
          word := by
  intro word
  exact Iff.symm
    (partial_order_pattern_language_preservation_of_mapped_subtype_components
      (label := label)
      (order := order)
      branches
      (fun branch word => Iff.symm (hbranches branch word))
      hdecompose
      word)

theorem theorem1_partial_order_normalized_case_of_recursive_component_correctness
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    {label : Trans -> TransitionLabel Activity}
    {order : Rel Nat}
    (branches :
      List
        (Σ part : {part : Set Trans // part ∈ partition.parts},
          Powl
            (PetriNet.NormalizedTrans
              {trans : Trans // part.val trans})))
    (componentLanguage :
      (Σ part : {part : Set Trans // part ∈ partition.parts},
        Powl
          (PetriNet.NormalizedTrans
            {trans : Trans // part.val trans})) ->
        Language Activity)
    (hbranches :
      ∀ (branch :
          Σ part : {part : Set Trans // part ∈ partition.parts},
            Powl
              (PetriNet.NormalizedTrans
                {trans : Trans // part.val trans}))
        word,
        componentLanguage branch word ↔
          Powl.language
            (WorkflowNet.normalizedLabel
              (fun trans : {trans : Trans // branch.1.val trans} =>
                label trans.val))
            branch.2
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.language net label word ↔
          Powl.partialOrderComponentLanguage
            order
            (branches.map componentLanguage)
            word) :
    ∀ word,
      WorkflowNet.language net label word ↔
        Powl.language
          (WorkflowNet.normalizedLabel label)
          (Powl.partialOrder order
            (branches.map
              (fun branch =>
                Powl.map
                  WorkflowNet.normalizedSubtypeTransMap
                  branch.2)))
          word := by
  intro word
  exact Iff.symm
    (partial_order_pattern_language_preservation_of_normalized_mapped_subtype_components
      (label := label)
      (order := order)
      branches
      componentLanguage
      (fun branch word => Iff.symm (hbranches branch word))
      hdecompose
      word)

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

def workflow_net_of_connected_no_boundary_edges
    {Place : Type u}
    {Trans : Type v}
    (net : PetriNet Place Trans)
    (source sink : Place)
    (hsourceNoIn : ∀ trans, ¬ net.transToPlace trans source)
    (hsinkNoOut : ∀ trans, ¬ net.placeToTrans sink trans)
    (hconnected :
      ∀ node : PetriNet.Node Place Trans,
        PetriNet.Path net (PetriNet.Node.place source) node ∧
        PetriNet.Path net node (PetriNet.Node.place sink)) :
    WorkflowNet Place Trans :=
  WorkflowNet.ofConnectedNoBoundaryEdges
    net source sink hsourceNoIn hsinkNoOut hconnected

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

theorem normalization_enter_enabled_iff
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (marking : Marking (PetriNet.NormalizedPlace Place)) :
    WorkflowNet.enabled
      (WorkflowNet.normalizedNet net)
      marking
      PetriNet.NormalizedTrans.enter ↔
        marking PetriNet.NormalizedPlace.source > 0 :=
  WorkflowNet.normalized_enter_enabled_iff net marking

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

theorem normalization_exit_enabled_iff
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (marking : Marking (PetriNet.NormalizedPlace Place)) :
    WorkflowNet.enabled
      (WorkflowNet.normalizedNet net)
      marking
      PetriNet.NormalizedTrans.exit ↔
        marking (PetriNet.NormalizedPlace.original net.sink) > 0 :=
  WorkflowNet.normalized_exit_enabled_iff net marking

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

theorem normalization_original_transition_preserves_fresh_source
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (marking : Marking (PetriNet.NormalizedPlace Place))
    (trans : Trans) :
    WorkflowNet.fire
      (WorkflowNet.normalizedNet net)
      marking
      (PetriNet.NormalizedTrans.original trans)
      PetriNet.NormalizedPlace.source =
        marking PetriNet.NormalizedPlace.source :=
  WorkflowNet.normalized_original_fire_fresh_source net marking trans

theorem normalization_original_transition_preserves_fresh_sink
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (marking : Marking (PetriNet.NormalizedPlace Place))
    (trans : Trans) :
    WorkflowNet.fire
      (WorkflowNet.normalizedNet net)
      marking
      (PetriNet.NormalizedTrans.original trans)
      PetriNet.NormalizedPlace.sink =
        marking PetriNet.NormalizedPlace.sink :=
  WorkflowNet.normalized_original_fire_fresh_sink net marking trans

theorem normalization_original_sequence_preserves_fresh_source
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {before after : Marking (PetriNet.NormalizedPlace Place)}
    {trace : List Trans}
    (sequence :
      WorkflowNet.FiringSequence
        (WorkflowNet.normalizedNet net)
        before
        (trace.map PetriNet.NormalizedTrans.original)
        after) :
    after PetriNet.NormalizedPlace.source =
      before PetriNet.NormalizedPlace.source :=
  WorkflowNet.normalized_original_firingSequence_preserves_fresh_source
    net sequence

theorem normalization_original_sequence_preserves_fresh_sink
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {before after : Marking (PetriNet.NormalizedPlace Place)}
    {trace : List Trans}
    (sequence :
      WorkflowNet.FiringSequence
        (WorkflowNet.normalizedNet net)
        before
        (trace.map PetriNet.NormalizedTrans.original)
        after) :
    after PetriNet.NormalizedPlace.sink =
      before PetriNet.NormalizedPlace.sink :=
  WorkflowNet.normalized_original_firingSequence_preserves_fresh_sink
    net sequence

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

theorem normalization_reachable_of_original
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    {marking : Marking Place}
    (hreachable :
      WorkflowNet.reachable net (WorkflowNet.initial net) marking) :
    WorkflowNet.reachable
      (WorkflowNet.normalizedNet net)
      (WorkflowNet.initial (WorkflowNet.normalizedNet net))
      (Marking.normalize marking) :=
  WorkflowNet.normalized_reachable_of_original net hreachable

theorem normalization_complete_from_original_marking
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hcomplete : WorkflowNet.optionToComplete net)
    {marking : Marking Place}
    (hreachable :
      WorkflowNet.reachable net (WorkflowNet.initial net) marking) :
    WorkflowNet.reachable
      (WorkflowNet.normalizedNet net)
      (Marking.normalize marking)
      (WorkflowNet.final (WorkflowNet.normalizedNet net)) :=
  WorkflowNet.normalized_complete_from_original_marking
    net hcomplete hreachable

theorem normalization_complete_from_initial
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hcomplete : WorkflowNet.optionToComplete net) :
    WorkflowNet.reachable
      (WorkflowNet.normalizedNet net)
      (WorkflowNet.initial (WorkflowNet.normalizedNet net))
      (WorkflowNet.final (WorkflowNet.normalizedNet net)) :=
  WorkflowNet.normalized_complete_from_initial net hcomplete

theorem normalization_reachable_shape
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hproper : WorkflowNet.properCompletion net)
    {marking : Marking (PetriNet.NormalizedPlace Place)}
    (hreachable :
      WorkflowNet.reachable
        (WorkflowNet.normalizedNet net)
        (WorkflowNet.initial (WorkflowNet.normalizedNet net))
        marking) :
    WorkflowNet.normalizedReachableShape net marking :=
  WorkflowNet.normalizedReachableShape_of_reachable
    net hproper hreachable

theorem normalization_option_to_complete_of_original
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hcomplete : WorkflowNet.optionToComplete net)
    (hproper : WorkflowNet.properCompletion net) :
    WorkflowNet.optionToComplete (WorkflowNet.normalizedNet net) :=
  WorkflowNet.normalized_optionToComplete_of_original
    net hcomplete hproper

theorem normalization_option_to_complete_of_sound
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hsound : WorkflowNet.sound net) :
    WorkflowNet.optionToComplete (WorkflowNet.normalizedNet net) :=
  WorkflowNet.normalized_optionToComplete_of_sound net hsound

theorem normalization_proper_completion_of_original
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hproper : WorkflowNet.properCompletion net) :
    WorkflowNet.properCompletion (WorkflowNet.normalizedNet net) :=
  WorkflowNet.normalized_properCompletion_of_original net hproper

theorem normalization_safe_of_original
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hsafe : WorkflowNet.safe net)
    (hproper : WorkflowNet.properCompletion net) :
    WorkflowNet.safe (WorkflowNet.normalizedNet net) :=
  WorkflowNet.normalized_safe_of_original net hsafe hproper

theorem normalization_exit_enabled_at_final
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans) :
    WorkflowNet.enabled
      (WorkflowNet.normalizedNet net)
      (Marking.normalize (WorkflowNet.final net))
      PetriNet.NormalizedTrans.exit :=
  WorkflowNet.normalized_exit_enabled_at_final net

theorem normalization_no_dead_transitions_of_original
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hnoDead : WorkflowNet.noDeadTransitions net)
    (hcomplete : WorkflowNet.optionToComplete net) :
    WorkflowNet.noDeadTransitions (WorkflowNet.normalizedNet net) :=
  WorkflowNet.normalized_noDeadTransitions_of_original
    net hnoDead hcomplete

theorem normalization_no_dead_transitions_of_sound
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hsound : WorkflowNet.sound net) :
    WorkflowNet.noDeadTransitions (WorkflowNet.normalizedNet net) :=
  WorkflowNet.normalized_noDeadTransitions_of_sound net hsound

theorem normalization_sound_of_original
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hsound : WorkflowNet.sound net) :
    WorkflowNet.sound (WorkflowNet.normalizedNet net) :=
  WorkflowNet.normalized_sound_of_original net hsound

theorem normalization_safe_and_sound_of_original
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hsafeSound : WorkflowNet.safeAndSound net) :
    WorkflowNet.safeAndSound (WorkflowNet.normalizedNet net) :=
  WorkflowNet.normalized_safeAndSound_of_original net hsafeSound

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

theorem normalization_boundary_language_iff_original
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (label : Trans -> TransitionLabel Activity)
    (word : List Activity) :
    WorkflowNet.normalizedBoundaryLanguage net label word ↔
      WorkflowNet.language net label word :=
  WorkflowNet.normalizedBoundaryLanguage_iff_original net label word

theorem normalization_accepting_sequence_to_original_of_proper
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hproper : WorkflowNet.properCompletion net)
    (label : Trans -> TransitionLabel Activity)
    {trace : List (PetriNet.NormalizedTrans Trans)}
    (sequence :
      WorkflowNet.FiringSequence
        (WorkflowNet.normalizedNet net)
        (WorkflowNet.initial (WorkflowNet.normalizedNet net))
        trace
        (WorkflowNet.final (WorkflowNet.normalizedNet net))) :
    ∃ originalTrace,
      WorkflowNet.FiringSequence
        net
        (WorkflowNet.initial net)
        originalTrace
        (WorkflowNet.final net) ∧
        WorkflowNet.traceWord (WorkflowNet.normalizedLabel label) trace =
          WorkflowNet.traceWord label originalTrace :=
  WorkflowNet.normalized_accepting_firingSequence_to_original_of_proper
    net hproper label sequence

theorem normalization_original_language_of_normalized_language_of_proper
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    (hproper : WorkflowNet.properCompletion net)
    {word : List Activity}
    (hlanguage :
      WorkflowNet.language
        (WorkflowNet.normalizedNet net)
        (WorkflowNet.normalizedLabel label)
        word) :
    WorkflowNet.language net label word :=
  WorkflowNet.original_language_of_normalized_language_of_proper
    hproper hlanguage

theorem normalization_language_iff_original_of_proper
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (label : Trans -> TransitionLabel Activity)
    (hproper : WorkflowNet.properCompletion net)
    (word : List Activity) :
    WorkflowNet.language
      (WorkflowNet.normalizedNet net)
      (WorkflowNet.normalizedLabel label)
      word ↔
        WorkflowNet.language net label word :=
  WorkflowNet.normalized_language_iff_original_of_proper
    net label hproper word

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

theorem lemma3_partial_order_projection_restricted_transition_connected
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (trans : {trans : Trans // part trans})
    (hentry :
      ∃ entry,
        WorkflowNet.entryPoints net part entry ∧
          net.placeToTrans entry trans.val)
    (hexit :
      ∃ exit,
        WorkflowNet.exitPoints net part exit ∧
          net.transToPlace trans.val exit) :
    PetriNet.Path
        (Patterns.partialOrderProjectionRestricted net part)
        (PetriNet.Node.place
          ⟨Patterns.BoundaryPlace.start,
            Patterns.partialOrderProjectionPlaces_start net part⟩)
        (PetriNet.Node.trans trans) ∧
      PetriNet.Path
        (Patterns.partialOrderProjectionRestricted net part)
        (PetriNet.Node.trans trans)
        (PetriNet.Node.place
          ⟨Patterns.BoundaryPlace.end_,
            Patterns.partialOrderProjectionPlaces_end net part⟩) :=
  Patterns.partialOrderProjectionRestricted_transition_connected_of_entry_exit
    net trans hentry hexit

theorem lemma3_partial_order_projection_restricted_original_connected
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hplace :
      Patterns.partialOrderProjectionPlaces
        net part (Patterns.BoundaryPlace.original place))
    (hincoming :
      ∃ trans,
        part trans ∧
          net.transToPlace trans place ∧
          ∃ entry,
            WorkflowNet.entryPoints net part entry ∧
              net.placeToTrans entry trans)
    (houtgoing :
      ∃ trans,
        part trans ∧
          net.placeToTrans place trans ∧
          ∃ exit,
            WorkflowNet.exitPoints net part exit ∧
              net.transToPlace trans exit) :
    PetriNet.Path
        (Patterns.partialOrderProjectionRestricted net part)
        (PetriNet.Node.place
          ⟨Patterns.BoundaryPlace.start,
            Patterns.partialOrderProjectionPlaces_start net part⟩)
        (PetriNet.Node.place
          ⟨Patterns.BoundaryPlace.original place, hplace⟩) ∧
      PetriNet.Path
        (Patterns.partialOrderProjectionRestricted net part)
        (PetriNet.Node.place
          ⟨Patterns.BoundaryPlace.original place, hplace⟩)
        (PetriNet.Node.place
          ⟨Patterns.BoundaryPlace.end_,
            Patterns.partialOrderProjectionPlaces_end net part⟩) :=
  Patterns.partialOrderProjectionRestricted_original_connected_of_incident_transitions
    net hplace hincoming houtgoing

theorem lemma3_partial_order_projection_restricted_connected_of_entry_exit_incidence
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (hnonempty : ∃ trans, part trans)
    (hentry :
      ∀ trans, part trans ->
        ∃ entry,
          WorkflowNet.entryPoints net part entry ∧
            net.placeToTrans entry trans)
    (hexit :
      ∀ trans, part trans ->
        ∃ exit,
          WorkflowNet.exitPoints net part exit ∧
            net.transToPlace trans exit)
    (hincoming :
      ∀ {place : Place},
        Patterns.partialOrderProjectionPlaces
            net part (Patterns.BoundaryPlace.original place) ->
          ∃ trans,
            part trans ∧
              net.transToPlace trans place ∧
              ∃ entry,
                WorkflowNet.entryPoints net part entry ∧
                  net.placeToTrans entry trans)
    (houtgoing :
      ∀ {place : Place},
        Patterns.partialOrderProjectionPlaces
            net part (Patterns.BoundaryPlace.original place) ->
          ∃ trans,
            part trans ∧
              net.placeToTrans place trans ∧
              ∃ exit,
                WorkflowNet.exitPoints net part exit ∧
                  net.transToPlace trans exit) :
    ∀ node :
      PetriNet.Node
        {place : Patterns.BoundaryPlace Place //
          Patterns.partialOrderProjectionPlaces net part place}
        {trans : Trans // part trans},
      PetriNet.Path
          (Patterns.partialOrderProjectionRestricted net part)
          (PetriNet.Node.place
            ⟨Patterns.BoundaryPlace.start,
              Patterns.partialOrderProjectionPlaces_start net part⟩)
          node ∧
        PetriNet.Path
          (Patterns.partialOrderProjectionRestricted net part)
          node
          (PetriNet.Node.place
            ⟨Patterns.BoundaryPlace.end_,
              Patterns.partialOrderProjectionPlaces_end net part⟩) :=
  Patterns.partialOrderProjectionRestricted_connected_of_entry_exit_incidence
    net hnonempty hentry hexit hincoming houtgoing

def lemma3_partial_order_projection_restricted_normalized_workflow_net_of_connected
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : Patterns.BoundaryPlace Place //
            Patterns.partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (Patterns.partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨Patterns.BoundaryPlace.start,
                Patterns.partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (Patterns.partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨Patterns.BoundaryPlace.end_,
                Patterns.partialOrderProjectionPlaces_end net part⟩)) :
    WorkflowNet
      (PetriNet.NormalizedPlace
        {place : Patterns.BoundaryPlace Place //
          Patterns.partialOrderProjectionPlaces net part place})
      (PetriNet.NormalizedTrans {trans : Trans // part trans}) :=
  Patterns.partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
    net part hconnected

def lemma3_partial_order_projection_restricted_normalized_workflow_net_of_incidence
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (hnonempty : ∃ trans, part trans)
    (hentry :
      ∀ trans, part trans ->
        ∃ entry,
          WorkflowNet.entryPoints net part entry ∧
            net.placeToTrans entry trans)
    (hexit :
      ∀ trans, part trans ->
        ∃ exit,
          WorkflowNet.exitPoints net part exit ∧
            net.transToPlace trans exit)
    (hincoming :
      ∀ {place : Place},
        Patterns.partialOrderProjectionPlaces
            net part (Patterns.BoundaryPlace.original place) ->
          ∃ trans,
            part trans ∧
              net.transToPlace trans place ∧
              ∃ entry,
                WorkflowNet.entryPoints net part entry ∧
                  net.placeToTrans entry trans)
    (houtgoing :
      ∀ {place : Place},
        Patterns.partialOrderProjectionPlaces
            net part (Patterns.BoundaryPlace.original place) ->
          ∃ trans,
            part trans ∧
              net.placeToTrans place trans ∧
              ∃ exit,
                WorkflowNet.exitPoints net part exit ∧
                  net.transToPlace trans exit) :
    WorkflowNet
      (PetriNet.NormalizedPlace
        {place : Patterns.BoundaryPlace Place //
          Patterns.partialOrderProjectionPlaces net part place})
      (PetriNet.NormalizedTrans {trans : Trans // part trans}) :=
  Patterns.partialOrderProjectionRestrictedNormalizedWorkflowNetOfIncidence
    net part hnonempty hentry hexit hincoming houtgoing

def lemma3_partial_order_projection_normalized_workflow_net_of_connected
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (hconnected :
      ∀ node : PetriNet.Node (Patterns.BoundaryPlace Place) Trans,
        PetriNet.Path
            (Patterns.partialOrderProjection net part)
            (PetriNet.Node.place Patterns.BoundaryPlace.start)
            node ∧
          PetriNet.Path
            (Patterns.partialOrderProjection net part)
            node
            (PetriNet.Node.place Patterns.BoundaryPlace.end_)) :
    WorkflowNet
      (PetriNet.NormalizedPlace (Patterns.BoundaryPlace Place))
      (PetriNet.NormalizedTrans Trans) :=
  Patterns.partialOrderProjectionNormalizedWorkflowNetOfConnected
    net part hconnected

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

theorem lemma4_xor_projection_mapped_model_language_iff_subtype_trace_language
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
    (model : Powl {trans : Trans // part trans})
    (hmodel :
      ∀ word,
        Powl.language
            (fun trans : {trans : Trans // part trans} => label trans.val)
            model
            word ↔
          WorkflowNet.language
            (Patterns.xorProjectionWorkflowNet hpattern hpart)
            (fun trans : {trans : Trans // part trans} => label trans.val)
            word)
    (word : List Activity) :
    Powl.language label (Powl.map Subtype.val model) word ↔
      WorkflowNet.subtypeTraceLanguage net label part word :=
  mapped_subtype_model_language_iff_subtype_trace_language
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
    model
    hmodel
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

theorem lemma4_xor_pattern_language_preservation_of_mapped_branch_models
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    {label : Trans -> TransitionLabel Activity}
    (hpattern : Patterns.xorPattern net partition)
    (branches :
      List
        (Σ part : {part : Set Trans // part ∈ partition.parts},
          Powl {trans : Trans // part.val trans}))
    (hmodels :
      ∀ (branch :
          Σ part : {part : Set Trans // part ∈ partition.parts},
            Powl {trans : Trans // part.val trans})
        word,
        Powl.language
            (fun trans : {trans : Trans // branch.1.val trans} =>
              label trans.val)
            branch.2
            word ↔
          WorkflowNet.language
            (Patterns.xorProjectionWorkflowNet hpattern branch.1.property)
            (fun trans : {trans : Trans // branch.1.val trans} =>
              label trans.val)
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.language net label word ↔
          Language.unionList
            (branches.map
              (fun branch =>
                WorkflowNet.subtypeTraceLanguage net label branch.1.val))
            word) :
    ∀ word,
      Powl.language label
          (Powl.xor
            (branches.map
              (fun branch => Powl.map Subtype.val branch.2)))
          word ↔
        WorkflowNet.language net label word := by
  intro word
  rw [Powl.xor_language_iff_unionList]
  exact Iff.trans
    (by
      simpa [List.map_map] using
        Language.unionList_map_congr
          branches
          (fun branch =>
            Powl.language label (Powl.map Subtype.val branch.2))
          (fun branch =>
            WorkflowNet.subtypeTraceLanguage net label branch.1.val)
          (fun branch word =>
            lemma4_xor_projection_mapped_model_language_iff_subtype_trace_language
              hpattern branch.1.property branch.2
              (hmodels branch)
              word)
          word)
    (Iff.symm (hdecompose word))

theorem theorem1_xor_case_of_recursive_branch_correctness
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    {label : Trans -> TransitionLabel Activity}
    (hpattern : Patterns.xorPattern net partition)
    (branches :
      List
        (Σ part : {part : Set Trans // part ∈ partition.parts},
          Powl {trans : Trans // part.val trans}))
    (hbranches :
      ∀ (branch :
          Σ part : {part : Set Trans // part ∈ partition.parts},
            Powl {trans : Trans // part.val trans})
        word,
        WorkflowNet.language
            (Patterns.xorProjectionWorkflowNet
              hpattern branch.1.property)
            (fun trans : {trans : Trans // branch.1.val trans} =>
              label trans.val)
            word ↔
          Powl.language
            (fun trans : {trans : Trans // branch.1.val trans} =>
              label trans.val)
            branch.2
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.language net label word ↔
          Language.unionList
            (branches.map
              (fun branch =>
                WorkflowNet.subtypeTraceLanguage net label branch.1.val))
            word) :
    ∀ word,
      WorkflowNet.language net label word ↔
        Powl.language label
          (Powl.xor
            (branches.map
              (fun branch => Powl.map Subtype.val branch.2)))
          word := by
  intro word
  exact Iff.symm
    (lemma4_xor_pattern_language_preservation_of_mapped_branch_models
      hpattern
      branches
      (fun branch word => Iff.symm (hbranches branch word))
      hdecompose
      word)

inductive ConversionCertificate
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (label : Trans -> TransitionLabel Activity) :
    (OutTrans : Type v) ->
      (OutTrans -> TransitionLabel Activity) ->
      Powl OutTrans ->
      Prop where
  | atom
      (trans : Trans)
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
      ConversionCertificate net label Trans label (Powl.atom trans)
  | xor
      {partition : Partition Trans}
      (hpattern : Patterns.xorPattern net partition)
      (branches :
        List
          (Σ part : {part : Set Trans // part ∈ partition.parts},
            Powl {trans : Trans // part.val trans}))
      (hbranches :
        ∀ (branch :
            Σ part : {part : Set Trans // part ∈ partition.parts},
              Powl {trans : Trans // part.val trans})
          word,
          WorkflowNet.language
              (Patterns.xorProjectionWorkflowNet
                hpattern branch.1.property)
              (fun trans : {trans : Trans // branch.1.val trans} =>
                label trans.val)
              word ↔
            Powl.language
              (fun trans : {trans : Trans // branch.1.val trans} =>
                label trans.val)
              branch.2
              word)
      (hdecompose :
        ∀ word,
          WorkflowNet.language net label word ↔
            Language.unionList
              (branches.map
                (fun branch =>
                  WorkflowNet.subtypeTraceLanguage
                    net label branch.1.val))
              word) :
      ConversionCertificate
        net
        label
        Trans
        label
        (Powl.xor
          (branches.map
            (fun branch => Powl.map Subtype.val branch.2)))
  | loop
      {BodyPlace : Type u}
      {RedoPlace : Type u}
      [DecidableEq BodyPlace]
      [DecidableEq RedoPlace]
      {bodyPart redoPart : Set Trans}
      (bodyNet : WorkflowNet BodyPlace {trans : Trans // bodyPart trans})
      (redoNet : WorkflowNet RedoPlace {trans : Trans // redoPart trans})
      {body : Powl {trans : Trans // bodyPart trans}}
      {redo : Powl {trans : Trans // redoPart trans}}
      (hbody :
        ∀ word,
          WorkflowNet.language
              bodyNet
              (fun trans : {trans : Trans // bodyPart trans} =>
                label trans.val)
              word ↔
            Powl.language
              (fun trans : {trans : Trans // bodyPart trans} =>
                label trans.val)
              body
              word)
      (hredo :
        ∀ word,
          WorkflowNet.language
              redoNet
              (fun trans : {trans : Trans // redoPart trans} =>
                label trans.val)
              word ↔
            Powl.language
              (fun trans : {trans : Trans // redoPart trans} =>
                label trans.val)
              redo
              word)
      (hdecompose :
        ∀ word,
          WorkflowNet.language net label word ↔
            Language.concat
              (WorkflowNet.language
                bodyNet
                (fun trans : {trans : Trans // bodyPart trans} =>
                  label trans.val))
              (Language.Star
                (Language.concat
                  (WorkflowNet.language
                    redoNet
                    (fun trans : {trans : Trans // redoPart trans} =>
                      label trans.val))
                  (WorkflowNet.language
                    bodyNet
                    (fun trans : {trans : Trans // bodyPart trans} =>
                      label trans.val))))
              word) :
      ConversionCertificate
        net
        label
        Trans
        label
        (Powl.loop
          (Powl.map Subtype.val body)
          (Powl.map Subtype.val redo))
  | partialOrder
      {partition : Partition Trans}
      {order : Rel Nat}
      (branches :
        List
          (Σ part : {part : Set Trans // part ∈ partition.parts},
            Powl {trans : Trans // part.val trans}))
      (hbranches :
        ∀ (branch :
            Σ part : {part : Set Trans // part ∈ partition.parts},
              Powl {trans : Trans // part.val trans})
          word,
          WorkflowNet.subtypeTraceLanguage
              net label branch.1.val word ↔
            Powl.language
              (fun trans : {trans : Trans // branch.1.val trans} =>
                label trans.val)
              branch.2
              word)
      (hdecompose :
        ∀ word,
          WorkflowNet.language net label word ↔
            Powl.partialOrderComponentLanguage
              order
              (branches.map
                (fun branch =>
                  WorkflowNet.subtypeTraceLanguage
                    net label branch.1.val))
              word) :
      ConversionCertificate
        net
        label
        Trans
        label
        (Powl.partialOrder order
          (branches.map
            (fun branch => Powl.map Subtype.val branch.2)))
  | partialOrderNormalized
      {partition : Partition Trans}
      {order : Rel Nat}
      (branches :
        List
          (Σ part : {part : Set Trans // part ∈ partition.parts},
            Powl
              (PetriNet.NormalizedTrans
                {trans : Trans // part.val trans})))
      (componentLanguage :
        (Σ part : {part : Set Trans // part ∈ partition.parts},
          Powl
            (PetriNet.NormalizedTrans
              {trans : Trans // part.val trans})) ->
          Language Activity)
      (hbranches :
        ∀ (branch :
            Σ part : {part : Set Trans // part ∈ partition.parts},
              Powl
                (PetriNet.NormalizedTrans
                  {trans : Trans // part.val trans}))
          word,
          componentLanguage branch word ↔
            Powl.language
              (WorkflowNet.normalizedLabel
                (fun trans : {trans : Trans // branch.1.val trans} =>
                  label trans.val))
              branch.2
              word)
      (hdecompose :
        ∀ word,
          WorkflowNet.language net label word ↔
            Powl.partialOrderComponentLanguage
              order
              (branches.map componentLanguage)
              word) :
      ConversionCertificate
        net
        label
        (PetriNet.NormalizedTrans Trans)
        (WorkflowNet.normalizedLabel label)
        (Powl.partialOrder order
          (branches.map
            (fun branch =>
              Powl.map
                WorkflowNet.normalizedSubtypeTransMap
                branch.2)))

theorem conversion_certificate_language_preservation
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {OutTrans : Type v}
    {outLabel : OutTrans -> TransitionLabel Activity}
    {model : Powl OutTrans}
    (certificate :
      ConversionCertificate net label OutTrans outLabel model) :
    ∀ word,
      WorkflowNet.language net label word ↔
        Powl.language outLabel model word := by
  intro word
  cases certificate with
  | atom trans hall hfire =>
      exact theorem1_base_case_single_transition hall hfire word
  | xor hpattern branches hbranches hdecompose =>
      exact theorem1_xor_case_of_recursive_branch_correctness
        hpattern branches hbranches hdecompose word
  | loop bodyNet redoNet hbody hredo hdecompose =>
      exact theorem1_loop_case_of_recursive_component_correctness
        bodyNet redoNet hbody hredo hdecompose word
  | partialOrder branches hbranches hdecompose =>
      exact theorem1_partial_order_case_of_recursive_component_correctness
        branches hbranches hdecompose word
  | partialOrderNormalized branches componentLanguage hbranches hdecompose =>
      exact
        theorem1_partial_order_normalized_case_of_recursive_component_correctness
          branches componentLanguage hbranches hdecompose word

theorem conversion_certificate_xor_of_branch_certificates
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    {label : Trans -> TransitionLabel Activity}
    (hpattern : Patterns.xorPattern net partition)
    (branches :
      List
        (Σ part : {part : Set Trans // part ∈ partition.parts},
          Powl {trans : Trans // part.val trans}))
    (certificates :
      ∀ (branch :
          Σ part : {part : Set Trans // part ∈ partition.parts},
            Powl {trans : Trans // part.val trans}),
        ConversionCertificate
          (Patterns.xorProjectionWorkflowNet
            hpattern branch.1.property)
          (fun trans : {trans : Trans // branch.1.val trans} =>
            label trans.val)
          {trans : Trans // branch.1.val trans}
          (fun trans : {trans : Trans // branch.1.val trans} =>
            label trans.val)
          branch.2)
    (hdecompose :
      ∀ word,
        WorkflowNet.language net label word ↔
          Language.unionList
            (branches.map
              (fun branch =>
                WorkflowNet.subtypeTraceLanguage net label branch.1.val))
            word) :
    ConversionCertificate
      net
      label
      Trans
      label
      (Powl.xor
        (branches.map
          (fun branch => Powl.map Subtype.val branch.2))) :=
  ConversionCertificate.xor
    hpattern
    branches
    (fun branch word =>
      conversion_certificate_language_preservation
        (certificates branch)
        word)
    hdecompose

theorem conversion_certificate_loop_of_component_certificates
    {Place : Type u}
    {BodyPlace : Type u}
    {RedoPlace : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    [DecidableEq BodyPlace]
    [DecidableEq RedoPlace]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {bodyPart redoPart : Set Trans}
    (bodyNet : WorkflowNet BodyPlace {trans : Trans // bodyPart trans})
    (redoNet : WorkflowNet RedoPlace {trans : Trans // redoPart trans})
    {body : Powl {trans : Trans // bodyPart trans}}
    {redo : Powl {trans : Trans // redoPart trans}}
    (bodyCertificate :
      ConversionCertificate
        bodyNet
        (fun trans : {trans : Trans // bodyPart trans} =>
          label trans.val)
        {trans : Trans // bodyPart trans}
        (fun trans : {trans : Trans // bodyPart trans} =>
          label trans.val)
        body)
    (redoCertificate :
      ConversionCertificate
        redoNet
        (fun trans : {trans : Trans // redoPart trans} =>
          label trans.val)
        {trans : Trans // redoPart trans}
        (fun trans : {trans : Trans // redoPart trans} =>
          label trans.val)
        redo)
    (hdecompose :
      ∀ word,
        WorkflowNet.language net label word ↔
          Language.concat
            (WorkflowNet.language
              bodyNet
              (fun trans : {trans : Trans // bodyPart trans} =>
                label trans.val))
            (Language.Star
              (Language.concat
                (WorkflowNet.language
                  redoNet
                  (fun trans : {trans : Trans // redoPart trans} =>
                    label trans.val))
                (WorkflowNet.language
                  bodyNet
                  (fun trans : {trans : Trans // bodyPart trans} =>
                    label trans.val))))
            word) :
    ConversionCertificate
      net
      label
      Trans
      label
      (Powl.loop
        (Powl.map Subtype.val body)
        (Powl.map Subtype.val redo)) :=
  ConversionCertificate.loop
    bodyNet
    redoNet
    (fun word =>
      conversion_certificate_language_preservation
        bodyCertificate
        word)
    (fun word =>
      conversion_certificate_language_preservation
        redoCertificate
        word)
    hdecompose

theorem conversion_certificate_partial_order_of_component_certificates
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    {label : Trans -> TransitionLabel Activity}
    {order : Rel Nat}
    (branches :
      List
        (Σ part : {part : Set Trans // part ∈ partition.parts},
          Powl {trans : Trans // part.val trans}))
    (ComponentPlace :
      (Σ part : {part : Set Trans // part ∈ partition.parts},
        Powl {trans : Trans // part.val trans}) -> Type x)
    (componentDecidable :
      ∀ branch, DecidableEq (ComponentPlace branch))
    (componentNet :
      ∀ branch,
        WorkflowNet
          (ComponentPlace branch)
          {trans : Trans // branch.1.val trans})
    (certificates :
      ∀ branch,
        @ConversionCertificate
          (ComponentPlace branch)
          {trans : Trans // branch.1.val trans}
          Activity
          (componentDecidable branch)
          (componentNet branch)
          (fun trans : {trans : Trans // branch.1.val trans} =>
            label trans.val)
          {trans : Trans // branch.1.val trans}
          (fun trans : {trans : Trans // branch.1.val trans} =>
            label trans.val)
          branch.2)
    (hcomponent :
      ∀ branch word,
        WorkflowNet.subtypeTraceLanguage
            net label branch.1.val word ↔
          WorkflowNet.language
            (componentNet branch)
            (fun trans : {trans : Trans // branch.1.val trans} =>
              label trans.val)
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.language net label word ↔
          Powl.partialOrderComponentLanguage
            order
            (branches.map
              (fun branch =>
                WorkflowNet.subtypeTraceLanguage net label branch.1.val))
            word) :
    ConversionCertificate
      net
      label
      Trans
      label
      (Powl.partialOrder order
        (branches.map
          (fun branch => Powl.map Subtype.val branch.2))) :=
  ConversionCertificate.partialOrder
    branches
    (fun branch word =>
      Iff.trans
        (hcomponent branch word)
        (conversion_certificate_language_preservation
          (certificates branch)
          word))
    hdecompose

theorem conversion_certificate_partial_order_normalized_of_component_certificates
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    {label : Trans -> TransitionLabel Activity}
    {order : Rel Nat}
    (branches :
      List
        (Σ part : {part : Set Trans // part ∈ partition.parts},
          Powl
            (PetriNet.NormalizedTrans
              {trans : Trans // part.val trans})))
    (ComponentPlace :
      (Σ part : {part : Set Trans // part ∈ partition.parts},
        Powl
          (PetriNet.NormalizedTrans
            {trans : Trans // part.val trans})) -> Type x)
    (componentDecidable :
      ∀ branch, DecidableEq (ComponentPlace branch))
    (componentNet :
      ∀ branch,
        WorkflowNet
          (ComponentPlace branch)
          (PetriNet.NormalizedTrans
            {trans : Trans // branch.1.val trans}))
    (certificates :
      ∀ branch,
        @ConversionCertificate
          (ComponentPlace branch)
          (PetriNet.NormalizedTrans
            {trans : Trans // branch.1.val trans})
          Activity
          (componentDecidable branch)
          (componentNet branch)
          (WorkflowNet.normalizedLabel
            (fun trans : {trans : Trans // branch.1.val trans} =>
              label trans.val))
          (PetriNet.NormalizedTrans
            {trans : Trans // branch.1.val trans})
          (WorkflowNet.normalizedLabel
            (fun trans : {trans : Trans // branch.1.val trans} =>
              label trans.val))
          branch.2)
    (hdecompose :
      ∀ word,
        WorkflowNet.language net label word ↔
          Powl.partialOrderComponentLanguage
            order
            (branches.map
              (fun branch =>
                WorkflowNet.language
                  (componentNet branch)
                  (WorkflowNet.normalizedLabel
                    (fun trans :
                        {trans : Trans // branch.1.val trans} =>
                      label trans.val))))
            word) :
    ConversionCertificate
      net
      label
      (PetriNet.NormalizedTrans Trans)
      (WorkflowNet.normalizedLabel label)
      (Powl.partialOrder order
        (branches.map
          (fun branch =>
            Powl.map
              WorkflowNet.normalizedSubtypeTransMap
              branch.2))) :=
  ConversionCertificate.partialOrderNormalized
    branches
    (fun branch =>
      WorkflowNet.language
        (componentNet branch)
        (WorkflowNet.normalizedLabel
          (fun trans : {trans : Trans // branch.1.val trans} =>
            label trans.val)))
    (fun branch word =>
      conversion_certificate_language_preservation
        (certificates branch)
        word)
    hdecompose

structure CertifiedConversion
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (label : Trans -> TransitionLabel Activity) where
  OutTrans : Type v
  outLabel : OutTrans -> TransitionLabel Activity
  model : Powl OutTrans
  certificate : ConversionCertificate net label OutTrans outLabel model

theorem certified_conversion_language_preservation
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    (conversion : CertifiedConversion net label) :
    ∀ word,
      WorkflowNet.language net label word ↔
        Powl.language conversion.outLabel conversion.model word :=
  conversion_certificate_language_preservation conversion.certificate

theorem certified_conversion_language_eq
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    (conversion : CertifiedConversion net label) :
    WorkflowNet.language net label =
      Powl.language conversion.outLabel conversion.model :=
  Language.ext
    (certified_conversion_language_preservation conversion)

theorem theorem1_correctness_of_certified_successful_conversion
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    (conversion : CertifiedConversion net label) :
    ∀ word,
      WorkflowNet.language net label word ↔
        Powl.language conversion.outLabel conversion.model word :=
  certified_conversion_language_preservation conversion

theorem theorem1_correctness_language_eq_of_certified_successful_conversion
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    (conversion : CertifiedConversion net label) :
    WorkflowNet.language net label =
      Powl.language conversion.outLabel conversion.model :=
  certified_conversion_language_eq conversion

structure LocalCertifiedConversion
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    (net : WorkflowNet Place Trans)
    (label : Trans -> TransitionLabel Activity)
    (source sink : Place) where
  OutTrans : Type v
  outLabel : OutTrans -> TransitionLabel Activity
  model : Powl OutTrans
  certificate :
    ∀ word,
      WorkflowNet.localLanguage net label source sink word ↔
        Powl.language outLabel model word

theorem local_certified_conversion_language_preservation
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    (conversion :
      LocalCertifiedConversion net label source sink) :
    ∀ word,
      WorkflowNet.localLanguage net label source sink word ↔
        Powl.language conversion.outLabel conversion.model word :=
  conversion.certificate

theorem local_certified_conversion_language_eq
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    (conversion :
      LocalCertifiedConversion net label source sink) :
    WorkflowNet.localLanguage net label source sink =
      Powl.language conversion.outLabel conversion.model :=
  Language.ext
    (local_certified_conversion_language_preservation conversion)

def local_certified_conversion_of_certified_conversion
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    (conversion : CertifiedConversion net label) :
    LocalCertifiedConversion net label net.source net.sink where
  OutTrans := conversion.OutTrans
  outLabel := conversion.outLabel
  model := conversion.model
  certificate := fun word =>
    Iff.trans
      (Iff.symm
        (WorkflowNet.language_iff_localLanguage_source_sink
          net label word))
      (certified_conversion_language_preservation conversion word)

def local_certified_conversion_xor_of_mapped_branch_models
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    (branches : List
      (Σ part : Set Trans, Powl {trans : Trans // part trans}))
    (hmodels :
      ∀ (branch :
          Σ part : Set Trans, Powl {trans : Trans // part trans})
        word,
        Powl.language
            (fun trans : {trans : Trans // branch.1 trans} =>
              label trans.val)
            branch.2
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            branch.1
            source
            sink
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label source sink word ↔
          Language.unionList
            (branches.map
              (fun branch =>
                WorkflowNet.localSubtypeTraceLanguage
                  net label branch.1 source sink))
            word) :
    LocalCertifiedConversion net label source sink where
  OutTrans := Trans
  outLabel := label
  model :=
    Powl.xor
      (branches.map
        (fun branch => Powl.map Subtype.val branch.2))
  certificate := fun word =>
    Iff.symm
      (local_xor_language_preservation_of_mapped_branch_models
        branches hmodels hdecompose word)

def local_certified_conversion_loop_of_mapped_subtype_components
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    {bodyPart redoPart : Set Trans}
    {body : Powl {trans : Trans // bodyPart trans}}
    {redo : Powl {trans : Trans // redoPart trans}}
    (hbody :
      ∀ word,
        Powl.language
            (fun trans : {trans : Trans // bodyPart trans} =>
              label trans.val)
            body
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            bodyPart
            source
            sink
            word)
    (hredo :
      ∀ word,
        Powl.language
            (fun trans : {trans : Trans // redoPart trans} =>
              label trans.val)
            redo
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            redoPart
            sink
            source
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label source sink word ↔
          Language.concat
            (WorkflowNet.localSubtypeTraceLanguage
              net label bodyPart source sink)
            (Language.Star
              (Language.concat
                (WorkflowNet.localSubtypeTraceLanguage
                  net label redoPart sink source)
                (WorkflowNet.localSubtypeTraceLanguage
                  net label bodyPart source sink)))
            word) :
    LocalCertifiedConversion net label source sink where
  OutTrans := Trans
  outLabel := label
  model :=
    Powl.loop
      (Powl.map Subtype.val body)
      (Powl.map Subtype.val redo)
  certificate := fun word =>
    Iff.symm
      (local_loop_language_preservation_of_mapped_subtype_components
        hbody hredo hdecompose word)

def local_certified_conversion_partial_order_of_mapped_branch_models
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    {order : Rel Nat}
    (branches : List
      (Σ part : Set Trans, Powl {trans : Trans // part trans}))
    (hmodels :
      ∀ (branch :
          Σ part : Set Trans, Powl {trans : Trans // part trans})
        word,
        Powl.language
            (fun trans : {trans : Trans // branch.1 trans} =>
              label trans.val)
            branch.2
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            branch.1
            source
            sink
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label source sink word ↔
          Powl.partialOrderComponentLanguage
            order
            (branches.map
              (fun branch =>
                WorkflowNet.localSubtypeTraceLanguage
                  net label branch.1 source sink))
            word) :
    LocalCertifiedConversion net label source sink where
  OutTrans := Trans
  outLabel := label
  model :=
    Powl.partialOrder order
      (branches.map
        (fun branch => Powl.map Subtype.val branch.2))
  certificate := fun word =>
    Iff.symm
      (local_partial_order_language_preservation_of_mapped_branch_models
        branches hmodels hdecompose word)

theorem theorem2_local_certified_conversion_language_preservation
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    (conversion :
      LocalCertifiedConversion net label source sink) :
    ∀ word,
      WorkflowNet.localLanguage net label source sink word ↔
        Powl.language conversion.outLabel conversion.model word :=
  local_certified_conversion_language_preservation conversion

theorem theorem2_local_certified_conversion_language_eq
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    (conversion :
      LocalCertifiedConversion net label source sink) :
    WorkflowNet.localLanguage net label source sink =
      Powl.language conversion.outLabel conversion.model :=
  local_certified_conversion_language_eq conversion

theorem theorem2_semi_block_base_safe_and_sound
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hbase :
      WorkflowNet.semiBlockStructuredBaseRequirements net) :
    WorkflowNet.safeAndSound net :=
  hbase.1

theorem theorem2_semi_block_base_explicit_decision_points
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hbase :
      WorkflowNet.semiBlockStructuredBaseRequirements net) :
    WorkflowNet.explicitDecisionPoints net :=
  hbase.2

theorem theorem2_explicit_decision_points_place_to_transition
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    (hdecision : WorkflowNet.explicitDecisionPoints net)
    {place : Place}
    {trans : Trans}
    (hflow : net.placeToTrans place trans) :
    WorkflowNet.uniquePresetOfTransition net trans ∨
      WorkflowNet.uniquePostsetOfPlace net place :=
  hdecision.1 place trans hflow

theorem theorem2_explicit_decision_points_transition_to_place
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    (hdecision : WorkflowNet.explicitDecisionPoints net)
    {trans : Trans}
    {place : Place}
    (hflow : net.transToPlace trans place) :
    WorkflowNet.uniquePresetOfPlace net place ∨
      WorkflowNet.uniquePostsetOfTransition net trans :=
  hdecision.2 trans place hflow

theorem theorem2_unique_preset_of_transition_exact
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {place other : Place}
    {trans : Trans}
    (hunique : WorkflowNet.uniquePresetOfTransition net trans)
    (hflow : net.placeToTrans place trans) :
    net.placeToTrans other trans ↔ other = place :=
  WorkflowNet.uniquePresetOfTransition_placeToTrans_iff
    hunique hflow other

theorem theorem2_unique_postset_of_place_exact
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {place : Place}
    {trans other : Trans}
    (hunique : WorkflowNet.uniquePostsetOfPlace net place)
    (hflow : net.placeToTrans place trans) :
    net.placeToTrans place other ↔ other = trans :=
  WorkflowNet.uniquePostsetOfPlace_placeToTrans_iff
    hunique hflow other

theorem theorem2_unique_preset_of_place_exact
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {place : Place}
    {trans other : Trans}
    (hunique : WorkflowNet.uniquePresetOfPlace net place)
    (hflow : net.transToPlace trans place) :
    net.transToPlace other place ↔ other = trans :=
  WorkflowNet.uniquePresetOfPlace_transToPlace_iff
    hunique hflow other

theorem theorem2_unique_postset_of_transition_exact
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {place other : Place}
    {trans : Trans}
    (hunique : WorkflowNet.uniquePostsetOfTransition net trans)
    (hflow : net.transToPlace trans place) :
    net.transToPlace trans other ↔ other = place :=
  WorkflowNet.uniquePostsetOfTransition_transToPlace_iff
    hunique hflow other

theorem theorem2_split_decision_place_not_unique_postset
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {place : Place}
    (hsplit : WorkflowNet.splitDecisionPlace net place) :
    ¬ WorkflowNet.uniquePostsetOfPlace net place :=
  WorkflowNet.splitDecisionPlace_not_uniquePostsetOfPlace hsplit

theorem theorem2_join_decision_place_not_unique_preset
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {place : Place}
    (hjoin : WorkflowNet.joinDecisionPlace net place) :
    ¬ WorkflowNet.uniquePresetOfPlace net place :=
  WorkflowNet.joinDecisionPlace_not_uniquePresetOfPlace hjoin

theorem theorem2_explicit_split_decision_transition_unique_preset
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    (hdecision : WorkflowNet.explicitDecisionPoints net)
    {place : Place}
    (hsplit : WorkflowNet.splitDecisionPlace net place)
    {trans : Trans}
    (hflow : net.placeToTrans place trans) :
    WorkflowNet.uniquePresetOfTransition net trans :=
  WorkflowNet.explicitDecisionPoints_split_transition_uniquePreset
    hdecision hsplit hflow

theorem theorem2_explicit_join_decision_transition_unique_postset
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    (hdecision : WorkflowNet.explicitDecisionPoints net)
    {place : Place}
    (hjoin : WorkflowNet.joinDecisionPlace net place)
    {trans : Trans}
    (hflow : net.transToPlace trans place) :
    WorkflowNet.uniquePostsetOfTransition net trans :=
  WorkflowNet.explicitDecisionPoints_join_transition_uniquePostset
    hdecision hjoin hflow

theorem theorem2_explicit_decision_points_free_choice
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    (hdecision : WorkflowNet.explicitDecisionPoints net) :
    PetriNet.freeChoice net.toPetriNet :=
  WorkflowNet.explicitDecisionPoints_freeChoice hdecision

theorem theorem2_free_choice_common_source_same_preset
    {Place : Type u}
    {Trans : Type v}
    {net : PetriNet Place Trans}
    (hfree : PetriNet.freeChoice net)
    {place : Place}
    {left right : Trans}
    (hleft : net.placeToTrans place left)
    (hright : net.placeToTrans place right) :
    PetriNet.transPreset net left =
      PetriNet.transPreset net right :=
  PetriNet.freeChoice_transPreset_eq_of_common_source
    hfree hleft hright

theorem theorem2_free_choice_common_source_preset_iff
    {Place : Type u}
    {Trans : Type v}
    {net : PetriNet Place Trans}
    (hfree : PetriNet.freeChoice net)
    {place other : Place}
    {left right : Trans}
    (hleft : net.placeToTrans place left)
    (hright : net.placeToTrans place right) :
    net.placeToTrans other left ↔
      net.placeToTrans other right :=
  PetriNet.freeChoice_transPreset_iff_of_common_source
    hfree hleft hright other

theorem theorem2_semi_block_base_free_choice
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hbase :
      WorkflowNet.semiBlockStructuredBaseRequirements net) :
    PetriNet.freeChoice net.toPetriNet :=
  WorkflowNet.explicitDecisionPoints_freeChoice hbase.2

theorem theorem2_no_decision_places_marked_graph
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    (hnoDecision : WorkflowNet.noDecisionPlaces net) :
    PetriNet.markedGraph net.toPetriNet :=
  WorkflowNet.noDecisionPlaces_markedGraph hnoDecision

theorem theorem2_marked_graph_no_decision_places
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    (hmarked : PetriNet.markedGraph net.toPetriNet) :
    WorkflowNet.noDecisionPlaces net :=
  WorkflowNet.markedGraph_noDecisionPlaces hmarked

theorem theorem2_no_decision_places_iff_marked_graph
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans} :
    WorkflowNet.noDecisionPlaces net ↔
      PetriNet.markedGraph net.toPetriNet :=
  WorkflowNet.noDecisionPlaces_iff_markedGraph

theorem theorem2_marked_graph_no_split_decision_place
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    (hmarked : PetriNet.markedGraph net.toPetriNet)
    (place : Place) :
    ¬ WorkflowNet.splitDecisionPlace net place :=
  WorkflowNet.markedGraph_noSplitDecisionPlace hmarked place

theorem theorem2_marked_graph_no_join_decision_place
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    (hmarked : PetriNet.markedGraph net.toPetriNet)
    (place : Place) :
    ¬ WorkflowNet.joinDecisionPlace net place :=
  WorkflowNet.markedGraph_noJoinDecisionPlace hmarked place

theorem theorem2_no_decision_places_no_split
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    (hnoDecision : WorkflowNet.noDecisionPlaces net)
    (place : Place) :
    ¬ WorkflowNet.splitDecisionPlace net place :=
  hnoDecision.1 place

theorem theorem2_no_decision_places_no_join
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    (hnoDecision : WorkflowNet.noDecisionPlaces net)
    (place : Place) :
    ¬ WorkflowNet.joinDecisionPlace net place :=
  hnoDecision.2 place

theorem theorem2_workflow_place_has_input_of_ne_source
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {place : Place}
    (hplace : place ≠ net.source) :
    ∃ trans, net.transToPlace trans place :=
  WorkflowNet.place_has_input_of_ne_source net hplace

theorem theorem2_workflow_place_has_output_of_ne_sink
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {place : Place}
    (hplace : place ≠ net.sink) :
    ∃ trans, net.placeToTrans place trans :=
  WorkflowNet.place_has_output_of_ne_sink net hplace

theorem theorem2_marked_graph_unique_preset_of_non_source_place
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    (hmarked : PetriNet.markedGraph net.toPetriNet)
    {place : Place}
    (hplace : place ≠ net.source) :
    WorkflowNet.uniquePresetOfPlace net place :=
  WorkflowNet.markedGraph_uniquePresetOfPlace_of_ne_source
    hmarked hplace

theorem theorem2_marked_graph_unique_postset_of_non_sink_place
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    (hmarked : PetriNet.markedGraph net.toPetriNet)
    {place : Place}
    (hplace : place ≠ net.sink) :
    WorkflowNet.uniquePostsetOfPlace net place :=
  WorkflowNet.markedGraph_uniquePostsetOfPlace_of_ne_sink
    hmarked hplace

theorem theorem2_no_decision_places_unique_preset_of_non_source_place
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    (hnoDecision : WorkflowNet.noDecisionPlaces net)
    {place : Place}
    (hplace : place ≠ net.source) :
    WorkflowNet.uniquePresetOfPlace net place :=
  WorkflowNet.markedGraph_uniquePresetOfPlace_of_ne_source
    (WorkflowNet.noDecisionPlaces_markedGraph hnoDecision)
    hplace

theorem theorem2_no_decision_places_unique_postset_of_non_sink_place
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    (hnoDecision : WorkflowNet.noDecisionPlaces net)
    {place : Place}
    (hplace : place ≠ net.sink) :
    WorkflowNet.uniquePostsetOfPlace net place :=
  WorkflowNet.markedGraph_uniquePostsetOfPlace_of_ne_sink
    (WorkflowNet.noDecisionPlaces_markedGraph hnoDecision)
    hplace

theorem theorem2_decision_pairing_maps_split_to_join
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {pair : Place -> Place}
    (hpair : WorkflowNet.decisionPairing net pair)
    {split : Place}
    (hsplit : WorkflowNet.splitDecisionPlace net split) :
    WorkflowNet.joinDecisionPlace net (pair split) :=
  hpair.1 split hsplit

theorem theorem2_decision_pairing_injective_on_splits
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {pair : Place -> Place}
    (hpair : WorkflowNet.decisionPairing net pair)
    {left right : Place}
    (hleft : WorkflowNet.splitDecisionPlace net left)
    (hright : WorkflowNet.splitDecisionPlace net right)
    (heq : pair left = pair right) :
    left = right :=
  hpair.2.1 left right hleft hright heq

theorem theorem2_decision_pairing_surjective_on_joins
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {pair : Place -> Place}
    (hpair : WorkflowNet.decisionPairing net pair)
    {join : Place}
    (hjoin : WorkflowNet.joinDecisionPlace net join) :
    ∃ split, WorkflowNet.splitDecisionPlace net split ∧ pair split = join :=
  hpair.2.2 join hjoin

theorem theorem2_decision_pairing_branch_equiv
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {pair : Place -> Place}
    (hpair : WorkflowNet.decisionPairingWithBranchEquiv net pair)
    {split : Place}
    (hsplit : WorkflowNet.splitDecisionPlace net split) :
    ∃ (toJoin :
        WorkflowNet.transitionPostsetOfPlace net split ->
          WorkflowNet.transitionPresetOfPlace net (pair split))
      (fromJoin :
        WorkflowNet.transitionPresetOfPlace net (pair split) ->
          WorkflowNet.transitionPostsetOfPlace net split),
      WorkflowNet.placePostsetPresetEquiv
        net split (pair split) toJoin fromJoin :=
  hpair.2 split hsplit

theorem theorem2_place_postset_preset_equiv_left_inverse
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {toJoin :
      WorkflowNet.transitionPostsetOfPlace net split ->
        WorkflowNet.transitionPresetOfPlace net join}
    {fromJoin :
      WorkflowNet.transitionPresetOfPlace net join ->
        WorkflowNet.transitionPostsetOfPlace net split}
    (hequiv :
      WorkflowNet.placePostsetPresetEquiv
        net split join toJoin fromJoin)
    (trans : WorkflowNet.transitionPostsetOfPlace net split) :
    fromJoin (toJoin trans) = trans :=
  hequiv.1 trans

theorem theorem2_place_postset_preset_equiv_right_inverse
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {toJoin :
      WorkflowNet.transitionPostsetOfPlace net split ->
        WorkflowNet.transitionPresetOfPlace net join}
    {fromJoin :
      WorkflowNet.transitionPresetOfPlace net join ->
        WorkflowNet.transitionPostsetOfPlace net split}
    (hequiv :
      WorkflowNet.placePostsetPresetEquiv
        net split join toJoin fromJoin)
    (trans : WorkflowNet.transitionPresetOfPlace net join) :
    toJoin (fromJoin trans) = trans :=
  hequiv.2 trans

theorem theorem2_semi_block_decision_base_requirements
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements :
      WorkflowNet.semiBlockStructuredDecisionRequirements net) :
    WorkflowNet.semiBlockStructuredBaseRequirements net :=
  hrequirements.1

theorem theorem2_semi_block_decision_pairing_exists
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements :
      WorkflowNet.semiBlockStructuredDecisionRequirements net) :
    ∃ pair, WorkflowNet.decisionPairingWithBranchEquiv net pair :=
  hrequirements.2

theorem theorem2_decision_pairing_with_branch_subnets_pairing
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {pair : Place -> Place}
    (hpair : WorkflowNet.decisionPairingWithBranchSubnets net pair) :
    WorkflowNet.decisionPairingWithBranchEquiv net pair :=
  hpair.1

theorem theorem2_decision_pairing_branch_family_exists
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {pair : Place -> Place}
    (hpair : WorkflowNet.decisionPairingWithBranchSubnets net pair)
    {split : Place}
    (hsplit : WorkflowNet.splitDecisionPlace net split) :
    ∃ branches,
      WorkflowNet.decisionBranchFamily net split (pair split) branches :=
  hpair.2 split hsplit

theorem theorem2_decision_branch_family_contains_split_transition
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {branches :
      WorkflowNet.transitionPostsetOfPlace net split -> Set Trans}
    (hfamily : WorkflowNet.decisionBranchFamily net split join branches)
    (branch : WorkflowNet.transitionPostsetOfPlace net split) :
    branches branch branch.val :=
  hfamily.1 branch

theorem theorem2_decision_branch_place_set_contains_split
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (split join : Place)
    (part : Set Trans) :
    WorkflowNet.decisionBranchPlaceSet net split join part split :=
  WorkflowNet.decisionBranchPlaceSet_split net split join part

theorem theorem2_decision_branch_place_set_contains_join
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (split join : Place)
    (part : Set Trans) :
    WorkflowNet.decisionBranchPlaceSet net split join part join :=
  WorkflowNet.decisionBranchPlaceSet_join net split join part

theorem theorem2_decision_branch_place_set_preset_closed
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {split join place : Place}
    {part : Set Trans}
    {trans : Trans}
    (hpart : part trans)
    (hflow : net.placeToTrans place trans) :
    WorkflowNet.decisionBranchPlaceSet net split join part place :=
  WorkflowNet.decisionBranchPlaceSet_preset_closed
    net hpart hflow

theorem theorem2_decision_branch_place_set_postset_closed
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {split join place : Place}
    {part : Set Trans}
    {trans : Trans}
    (hpart : part trans)
    (hflow : net.transToPlace trans place) :
    WorkflowNet.decisionBranchPlaceSet net split join part place :=
  WorkflowNet.decisionBranchPlaceSet_postset_closed
    net hpart hflow

theorem theorem2_decision_branch_family_branch_nonempty
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {branches :
      WorkflowNet.transitionPostsetOfPlace net split -> Set Trans}
    (hfamily : WorkflowNet.decisionBranchFamily net split join branches)
    (branch : WorkflowNet.transitionPostsetOfPlace net split) :
    ∃ trans, branches branch trans :=
  WorkflowNet.decisionBranchFamily_branch_nonempty hfamily branch

theorem theorem2_decision_branch_family_subnet
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {branches :
      WorkflowNet.transitionPostsetOfPlace net split -> Set Trans}
    (hfamily : WorkflowNet.decisionBranchFamily net split join branches)
    (branch : WorkflowNet.transitionPostsetOfPlace net split) :
    WorkflowNet.decisionBranchSubnet net split join (branches branch) :=
  hfamily.2.1 branch

theorem theorem2_decision_branch_family_disjoint
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {branches :
      WorkflowNet.transitionPostsetOfPlace net split -> Set Trans}
    (hfamily : WorkflowNet.decisionBranchFamily net split join branches)
    {left right : WorkflowNet.transitionPostsetOfPlace net split}
    (hne : left ≠ right)
    {trans : Trans}
    (hleft : branches left trans)
    (hright : branches right trans) :
    False :=
  hfamily.2.2 left right hne trans hleft hright

theorem theorem2_decision_branch_family_other_not_mem
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {branches :
      WorkflowNet.transitionPostsetOfPlace net split -> Set Trans}
    (hfamily : WorkflowNet.decisionBranchFamily net split join branches)
    {left right : WorkflowNet.transitionPostsetOfPlace net split}
    (hne : left ≠ right)
    {trans : Trans}
    (hleft : branches left trans) :
    ¬ branches right trans :=
  WorkflowNet.decisionBranchFamily_other_not_mem
    hfamily hne hleft

theorem theorem2_decision_branch_family_source_transition_not_in_other
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {branches :
      WorkflowNet.transitionPostsetOfPlace net split -> Set Trans}
    (hfamily : WorkflowNet.decisionBranchFamily net split join branches)
    {left right : WorkflowNet.transitionPostsetOfPlace net split}
    (hne : left ≠ right) :
    ¬ branches right left.val :=
  WorkflowNet.decisionBranchFamily_source_transition_not_mem_other
    hfamily hne

theorem theorem2_decision_branch_subnet_nonempty
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {part : Set Trans}
    (hsubnet : WorkflowNet.decisionBranchSubnet net split join part) :
    ∃ trans, part trans :=
  hsubnet.1

theorem theorem2_decision_branch_subnet_workflow_net
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {part : Set Trans}
    (hsubnet : WorkflowNet.decisionBranchSubnet net split join part) :
    WorkflowNet.restrictedDecisionBranchWorkflowNet net split join part :=
  hsubnet.2

theorem theorem2_restricted_decision_branch_workflow_net_source
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {part : Set Trans}
    (hbranch :
      WorkflowNet.restrictedDecisionBranchWorkflowNet
        net split join part) :
    ∃ branchNet :
        WorkflowNet
          {place : Place //
            WorkflowNet.decisionBranchPlaceSet net split join part place}
          {trans : Trans // part trans},
      branchNet.source.val = split :=
  let ⟨branchNet, hsource, _⟩ := hbranch
  ⟨branchNet, hsource⟩

theorem theorem2_restricted_decision_branch_workflow_net_sink
    {Place : Type u}
    {Trans : Type v}
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {part : Set Trans}
    (hbranch :
      WorkflowNet.restrictedDecisionBranchWorkflowNet
        net split join part) :
    ∃ branchNet :
        WorkflowNet
          {place : Place //
            WorkflowNet.decisionBranchPlaceSet net split join part place}
          {trans : Trans // part trans},
      branchNet.sink.val = join :=
  let ⟨branchNet, _, hsink, _⟩ := hbranch
  ⟨branchNet, hsink⟩

theorem theorem2_restricted_local_language_iff_local_subtype_trace_language
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (restricted :
      WorkflowNet
        {place : Place // places place}
        {trans : Trans // transitions trans})
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
    WorkflowNet.localLanguage
        restricted
        (fun trans : {trans : Trans // transitions trans} =>
          label trans.val)
        source
        sink
        word ↔
      WorkflowNet.localSubtypeTraceLanguage
        original
        label
        transitions
        source.val
        sink.val
        word :=
  WorkflowNet.restricted_local_language_iff_localSubtypeTraceLanguage
    original restricted hplaceToTrans htransToPlace
    hpreset hpostset label source sink word

theorem theorem2_restricted_decision_branch_local_language_iff
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {part : Set Trans}
    (hbranch :
      WorkflowNet.restrictedDecisionBranchWorkflowNet
        net split join part)
    (label : Trans -> TransitionLabel Activity)
    (word : List Activity) :
    ∃ branchNet :
        WorkflowNet
          {place : Place //
            WorkflowNet.decisionBranchPlaceSet
              net split join part place}
          {trans : Trans // part trans},
      branchNet.source.val = split ∧
        branchNet.sink.val = join ∧
        (WorkflowNet.localLanguage
            branchNet
            (fun trans : {trans : Trans // part trans} =>
              label trans.val)
            branchNet.source
            branchNet.sink
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            part
            split
            join
            word) :=
  WorkflowNet.restrictedDecisionBranchWorkflowNet_local_language_iff
    hbranch label word

theorem theorem2_restricted_decision_branch_mapped_powl_language_iff_local_subtype_trace_language
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {part : Set Trans}
    (hbranch :
      WorkflowNet.restrictedDecisionBranchWorkflowNet
        net split join part)
    (label : Trans -> TransitionLabel Activity)
    (model : Powl {trans : Trans // part trans})
    (hmodel :
      ∀ (branchNet :
          WorkflowNet
            {place : Place //
              WorkflowNet.decisionBranchPlaceSet
                net split join part place}
            {trans : Trans // part trans}),
        branchNet.source.val = split ->
        branchNet.sink.val = join ->
          ∀ word,
            Powl.language
                (fun trans : {trans : Trans // part trans} =>
                  label trans.val)
                model
                word ↔
              WorkflowNet.localLanguage
                branchNet
                (fun trans : {trans : Trans // part trans} =>
                  label trans.val)
                branchNet.source
                branchNet.sink
                word)
    (word : List Activity) :
    Powl.language label (Powl.map Subtype.val model) word ↔
      WorkflowNet.localSubtypeTraceLanguage
        net
        label
        part
        split
        join
        word :=
  WorkflowNet.restrictedDecisionBranchWorkflowNet_mapped_powl_language_iff_localSubtypeTraceLanguage
    hbranch label model hmodel word

theorem theorem2_restricted_decision_branch_mapped_powl_language_iff_local_subtype_trace_language_of_language
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {part : Set Trans}
    (hbranch :
      WorkflowNet.restrictedDecisionBranchWorkflowNet
        net split join part)
    (label : Trans -> TransitionLabel Activity)
    (model : Powl {trans : Trans // part trans})
    (hmodel :
      ∀ (branchNet :
          WorkflowNet
            {place : Place //
              WorkflowNet.decisionBranchPlaceSet
                net split join part place}
            {trans : Trans // part trans}),
        branchNet.source.val = split ->
        branchNet.sink.val = join ->
          ∀ word,
            Powl.language
                (fun trans : {trans : Trans // part trans} =>
                  label trans.val)
                model
                word ↔
              WorkflowNet.language
                branchNet
                (fun trans : {trans : Trans // part trans} =>
                  label trans.val)
                word)
    (word : List Activity) :
    Powl.language label (Powl.map Subtype.val model) word ↔
      WorkflowNet.localSubtypeTraceLanguage
        net
        label
        part
        split
        join
        word :=
  WorkflowNet.restrictedDecisionBranchWorkflowNet_mapped_powl_language_iff_localSubtypeTraceLanguage_of_language
    hbranch label model hmodel word

theorem restricted_decision_branch_powl_language_iff_local_subtype_trace_language_of_certificate
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {part : Set Trans}
    (hbranch :
      WorkflowNet.restrictedDecisionBranchWorkflowNet
        net split join part)
    (label : Trans -> TransitionLabel Activity)
    (model : Powl {trans : Trans // part trans})
    (certificate :
      ∀ (branchNet :
          WorkflowNet
            {place : Place //
              WorkflowNet.decisionBranchPlaceSet
                net split join part place}
            {trans : Trans // part trans}),
        branchNet.source.val = split ->
        branchNet.sink.val = join ->
          ConversionCertificate
            branchNet
            (fun trans : {trans : Trans // part trans} =>
              label trans.val)
            {trans : Trans // part trans}
            (fun trans : {trans : Trans // part trans} =>
              label trans.val)
            model)
    (word : List Activity) :
    Powl.language
        (fun trans : {trans : Trans // part trans} =>
          label trans.val)
        model
        word ↔
      WorkflowNet.localSubtypeTraceLanguage
        net label part split join word := by
  rcases hbranch with
    ⟨branchNet, hsource, hsink, hplaceToTrans, htransToPlace⟩
  have hcertificate := certificate branchNet hsource hsink
  have hlanguage :
      Powl.language
          (fun trans : {trans : Trans // part trans} =>
            label trans.val)
          model
          word ↔
        WorkflowNet.language
          branchNet
          (fun trans : {trans : Trans // part trans} =>
            label trans.val)
          word :=
    Iff.symm
      (conversion_certificate_language_preservation
        hcertificate
        word)
  have hlocal :
      WorkflowNet.language
          branchNet
          (fun trans : {trans : Trans // part trans} =>
            label trans.val)
          word ↔
        WorkflowNet.localLanguage
          branchNet
          (fun trans : {trans : Trans // part trans} =>
            label trans.val)
          branchNet.source
          branchNet.sink
          word :=
    WorkflowNet.language_iff_localLanguage_source_sink
      branchNet
      (fun trans : {trans : Trans // part trans} =>
        label trans.val)
      word
  have hrestricted :
      WorkflowNet.localLanguage
          branchNet
          (fun trans : {trans : Trans // part trans} =>
            label trans.val)
          branchNet.source
          branchNet.sink
          word ↔
        WorkflowNet.localSubtypeTraceLanguage
          net
          label
          part
          branchNet.source.val
          branchNet.sink.val
          word :=
    WorkflowNet.restricted_local_language_iff_localSubtypeTraceLanguage
      net
      branchNet
      hplaceToTrans
      htransToPlace
      (fun place trans hpart hflow =>
        WorkflowNet.decisionBranchPlaceSet_preset_closed
          net hpart hflow)
      (fun trans place hpart hflow =>
        WorkflowNet.decisionBranchPlaceSet_postset_closed
          net hpart hflow)
      label
      branchNet.source
      branchNet.sink
      word
  rw [hsource, hsink] at hrestricted
  exact Iff.trans hlanguage (Iff.trans hlocal hrestricted)

theorem restricted_decision_branch_mapped_powl_language_iff_local_subtype_trace_language_of_certificate
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {part : Set Trans}
    (hbranch :
      WorkflowNet.restrictedDecisionBranchWorkflowNet
        net split join part)
    (label : Trans -> TransitionLabel Activity)
    (model : Powl {trans : Trans // part trans})
    (certificate :
      ∀ (branchNet :
          WorkflowNet
            {place : Place //
              WorkflowNet.decisionBranchPlaceSet
                net split join part place}
            {trans : Trans // part trans}),
        branchNet.source.val = split ->
        branchNet.sink.val = join ->
          ConversionCertificate
            branchNet
            (fun trans : {trans : Trans // part trans} =>
              label trans.val)
            {trans : Trans // part trans}
            (fun trans : {trans : Trans // part trans} =>
              label trans.val)
            model)
    (word : List Activity) :
    Powl.language label (Powl.map Subtype.val model) word ↔
      WorkflowNet.localSubtypeTraceLanguage
        net label part split join word :=
  Iff.trans
    (Powl.language_map Subtype.val label model word)
    (restricted_decision_branch_powl_language_iff_local_subtype_trace_language_of_certificate
      hbranch label model certificate word)

theorem theorem2_decision_branch_local_xor_language_preservation_of_mapped_branch_models
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {split join : Place}
    (branches : List
      (Σ part : Set Trans, Powl {trans : Trans // part trans}))
    (hmodels :
      ∀ (branch :
          Σ part : Set Trans, Powl {trans : Trans // part trans})
        word,
        Powl.language
            (fun trans : {trans : Trans // branch.1 trans} =>
              label trans.val)
            branch.2
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            branch.1
            split
            join
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label split join word ↔
          Language.unionList
            (branches.map
              (fun branch =>
                WorkflowNet.localSubtypeTraceLanguage
                  net label branch.1 split join))
            word) :
    ∀ word,
      Powl.language label
          (Powl.xor
            (branches.map
              (fun branch => Powl.map Subtype.val branch.2)))
          word ↔
        WorkflowNet.localLanguage net label split join word :=
  local_xor_language_preservation_of_mapped_branch_models
    branches hmodels hdecompose

theorem theorem2_decision_branch_local_xor_language_eq_of_mapped_branch_models
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {split join : Place}
    (branches : List
      (Σ part : Set Trans, Powl {trans : Trans // part trans}))
    (hmodels :
      ∀ (branch :
          Σ part : Set Trans, Powl {trans : Trans // part trans})
        word,
        Powl.language
            (fun trans : {trans : Trans // branch.1 trans} =>
              label trans.val)
            branch.2
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            branch.1
            split
            join
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label split join word ↔
          Language.unionList
            (branches.map
              (fun branch =>
                WorkflowNet.localSubtypeTraceLanguage
                  net label branch.1 split join))
            word) :
    Powl.language label
        (Powl.xor
          (branches.map
            (fun branch => Powl.map Subtype.val branch.2))) =
      WorkflowNet.localLanguage net label split join :=
  local_xor_language_eq_of_mapped_branch_models
    branches hmodels hdecompose

theorem theorem2_decision_branch_family_local_xor_language_preservation
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {split join : Place}
    {branchParts :
      WorkflowNet.transitionPostsetOfPlace net split -> Set Trans}
    (hfamily :
      WorkflowNet.decisionBranchFamily net split join branchParts)
    (branches : List
      (Σ branch : WorkflowNet.transitionPostsetOfPlace net split,
        Powl {trans : Trans // branchParts branch trans}))
    (hmodels :
      ∀ (branch :
          Σ branch : WorkflowNet.transitionPostsetOfPlace net split,
            Powl {trans : Trans // branchParts branch trans})
        word,
        Powl.language
            (fun trans :
              {trans : Trans // branchParts branch.1 trans} =>
                label trans.val)
            branch.2
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            (branchParts branch.1)
            split
            join
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label split join word ↔
          Language.unionList
            (branches.map
              (fun branch =>
                WorkflowNet.localSubtypeTraceLanguage
                  net label (branchParts branch.1) split join))
            word) :
    ∀ word,
      Powl.language label
          (Powl.xor
            (branches.map
              (fun branch => Powl.map Subtype.val branch.2)))
          word ↔
        WorkflowNet.localLanguage net label split join word := by
  have hcontainsSource :
      ∀ branch : WorkflowNet.transitionPostsetOfPlace net split,
        branchParts branch branch.val :=
    hfamily.1
  intro word
  rw [Powl.xor_language_iff_unionList]
  exact Iff.trans
    (by
      simpa [List.map_map] using
        Language.unionList_map_congr
          branches
          (fun branch =>
            Powl.language label (Powl.map Subtype.val branch.2))
          (fun branch =>
            WorkflowNet.localSubtypeTraceLanguage
              net label (branchParts branch.1) split join)
          (fun branch word =>
            Iff.trans
              (Powl.language_map Subtype.val label branch.2 word)
              (hmodels branch word))
          word)
    (Iff.symm (hdecompose word))

theorem theorem2_decision_branch_local_xor_language_preservation_of_certified_branch_models
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {split join : Place}
    (branches : List
      (Σ part : Set Trans, Powl {trans : Trans // part trans}))
    (branchNet :
      ∀ branch :
        Σ part : Set Trans, Powl {trans : Trans // part trans},
        WorkflowNet.restrictedDecisionBranchWorkflowNet
          net split join branch.1)
    (certificates :
      ∀ (branch :
          Σ part : Set Trans, Powl {trans : Trans // part trans})
        (restricted :
          WorkflowNet
            {place : Place //
              WorkflowNet.decisionBranchPlaceSet
                net split join branch.1 place}
            {trans : Trans // branch.1 trans}),
        restricted.source.val = split ->
        restricted.sink.val = join ->
          ConversionCertificate
            restricted
            (fun trans : {trans : Trans // branch.1 trans} =>
              label trans.val)
            {trans : Trans // branch.1 trans}
            (fun trans : {trans : Trans // branch.1 trans} =>
              label trans.val)
            branch.2)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label split join word ↔
          Language.unionList
            (branches.map
              (fun branch =>
                WorkflowNet.localSubtypeTraceLanguage
                  net label branch.1 split join))
            word) :
    ∀ word,
      Powl.language label
          (Powl.xor
            (branches.map
              (fun branch => Powl.map Subtype.val branch.2)))
          word ↔
        WorkflowNet.localLanguage net label split join word :=
  theorem2_decision_branch_local_xor_language_preservation_of_mapped_branch_models
    branches
    (fun branch word =>
      restricted_decision_branch_powl_language_iff_local_subtype_trace_language_of_certificate
        (branchNet branch)
        label
        branch.2
        (certificates branch)
        word)
    hdecompose

theorem theorem2_local_loop_language_preservation_of_mapped_subtype_components
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    {bodyPart redoPart : Set Trans}
    {body : Powl {trans : Trans // bodyPart trans}}
    {redo : Powl {trans : Trans // redoPart trans}}
    (hbody :
      ∀ word,
        Powl.language
            (fun trans : {trans : Trans // bodyPart trans} =>
              label trans.val)
            body
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            bodyPart
            source
            sink
            word)
    (hredo :
      ∀ word,
        Powl.language
            (fun trans : {trans : Trans // redoPart trans} =>
              label trans.val)
            redo
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            redoPart
            sink
            source
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label source sink word ↔
          Language.concat
            (WorkflowNet.localSubtypeTraceLanguage
              net label bodyPart source sink)
            (Language.Star
              (Language.concat
                (WorkflowNet.localSubtypeTraceLanguage
                  net label redoPart sink source)
                (WorkflowNet.localSubtypeTraceLanguage
                  net label bodyPart source sink)))
            word) :
    ∀ word,
      Powl.language label
          (Powl.loop
            (Powl.map Subtype.val body)
            (Powl.map Subtype.val redo))
          word ↔
        WorkflowNet.localLanguage net label source sink word :=
  local_loop_language_preservation_of_mapped_subtype_components
    hbody hredo hdecompose

theorem theorem2_local_loop_language_eq_of_mapped_subtype_components
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    {bodyPart redoPart : Set Trans}
    {body : Powl {trans : Trans // bodyPart trans}}
    {redo : Powl {trans : Trans // redoPart trans}}
    (hbody :
      ∀ word,
        Powl.language
            (fun trans : {trans : Trans // bodyPart trans} =>
              label trans.val)
            body
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            bodyPart
            source
            sink
            word)
    (hredo :
      ∀ word,
        Powl.language
            (fun trans : {trans : Trans // redoPart trans} =>
              label trans.val)
            redo
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            redoPart
            sink
            source
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label source sink word ↔
          Language.concat
            (WorkflowNet.localSubtypeTraceLanguage
              net label bodyPart source sink)
            (Language.Star
              (Language.concat
                (WorkflowNet.localSubtypeTraceLanguage
                  net label redoPart sink source)
                (WorkflowNet.localSubtypeTraceLanguage
                  net label bodyPart source sink)))
            word) :
    Powl.language label
        (Powl.loop
          (Powl.map Subtype.val body)
          (Powl.map Subtype.val redo)) =
      WorkflowNet.localLanguage net label source sink :=
  local_loop_language_eq_of_mapped_subtype_components
    hbody hredo hdecompose

theorem theorem2_local_loop_language_preservation_of_certified_subtype_components
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    {bodyPart redoPart : Set Trans}
    {body : Powl {trans : Trans // bodyPart trans}}
    {redo : Powl {trans : Trans // redoPart trans}}
    (bodyBranch :
      WorkflowNet.restrictedDecisionBranchWorkflowNet
        net source sink bodyPart)
    (redoBranch :
      WorkflowNet.restrictedDecisionBranchWorkflowNet
        net sink source redoPart)
    (bodyCertificate :
      ∀ (bodyNet :
          WorkflowNet
            {place : Place //
              WorkflowNet.decisionBranchPlaceSet
                net source sink bodyPart place}
            {trans : Trans // bodyPart trans}),
        bodyNet.source.val = source ->
        bodyNet.sink.val = sink ->
          ConversionCertificate
            bodyNet
            (fun trans : {trans : Trans // bodyPart trans} =>
              label trans.val)
            {trans : Trans // bodyPart trans}
            (fun trans : {trans : Trans // bodyPart trans} =>
              label trans.val)
            body)
    (redoCertificate :
      ∀ (redoNet :
          WorkflowNet
            {place : Place //
              WorkflowNet.decisionBranchPlaceSet
                net sink source redoPart place}
            {trans : Trans // redoPart trans}),
        redoNet.source.val = sink ->
        redoNet.sink.val = source ->
          ConversionCertificate
            redoNet
            (fun trans : {trans : Trans // redoPart trans} =>
              label trans.val)
            {trans : Trans // redoPart trans}
            (fun trans : {trans : Trans // redoPart trans} =>
              label trans.val)
            redo)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label source sink word ↔
          Language.concat
            (WorkflowNet.localSubtypeTraceLanguage
              net label bodyPart source sink)
            (Language.Star
              (Language.concat
                (WorkflowNet.localSubtypeTraceLanguage
                  net label redoPart sink source)
                (WorkflowNet.localSubtypeTraceLanguage
                  net label bodyPart source sink)))
            word) :
    ∀ word,
      Powl.language label
          (Powl.loop
            (Powl.map Subtype.val body)
            (Powl.map Subtype.val redo))
          word ↔
        WorkflowNet.localLanguage net label source sink word :=
  theorem2_local_loop_language_preservation_of_mapped_subtype_components
    (fun word =>
      restricted_decision_branch_powl_language_iff_local_subtype_trace_language_of_certificate
        bodyBranch
        label
        body
        bodyCertificate
        word)
    (fun word =>
      restricted_decision_branch_powl_language_iff_local_subtype_trace_language_of_certificate
        redoBranch
        label
        redo
        redoCertificate
        word)
    hdecompose

theorem theorem2_local_partial_order_language_preservation_of_mapped_branch_models
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    {order : Rel Nat}
    (branches : List
      (Σ part : Set Trans, Powl {trans : Trans // part trans}))
    (hmodels :
      ∀ (branch :
          Σ part : Set Trans, Powl {trans : Trans // part trans})
        word,
        Powl.language
            (fun trans : {trans : Trans // branch.1 trans} =>
              label trans.val)
            branch.2
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            branch.1
            source
            sink
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label source sink word ↔
          Powl.partialOrderComponentLanguage
            order
            (branches.map
              (fun branch =>
                WorkflowNet.localSubtypeTraceLanguage
                  net label branch.1 source sink))
            word) :
    ∀ word,
      Powl.language label
          (Powl.partialOrder order
            (branches.map
              (fun branch => Powl.map Subtype.val branch.2)))
          word ↔
        WorkflowNet.localLanguage net label source sink word :=
  local_partial_order_language_preservation_of_mapped_branch_models
    branches hmodels hdecompose

theorem theorem2_local_partial_order_language_eq_of_mapped_branch_models
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    {order : Rel Nat}
    (branches : List
      (Σ part : Set Trans, Powl {trans : Trans // part trans}))
    (hmodels :
      ∀ (branch :
          Σ part : Set Trans, Powl {trans : Trans // part trans})
        word,
        Powl.language
            (fun trans : {trans : Trans // branch.1 trans} =>
              label trans.val)
            branch.2
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            branch.1
            source
            sink
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label source sink word ↔
          Powl.partialOrderComponentLanguage
            order
            (branches.map
              (fun branch =>
                WorkflowNet.localSubtypeTraceLanguage
                  net label branch.1 source sink))
            word) :
    Powl.language label
        (Powl.partialOrder order
          (branches.map
            (fun branch => Powl.map Subtype.val branch.2))) =
      WorkflowNet.localLanguage net label source sink :=
  local_partial_order_language_eq_of_mapped_branch_models
    branches hmodels hdecompose

theorem theorem2_decision_branch_family_local_partial_order_language_preservation
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {split join : Place}
    {order : Rel Nat}
    {branchParts :
      WorkflowNet.transitionPostsetOfPlace net split -> Set Trans}
    (hfamily :
      WorkflowNet.decisionBranchFamily net split join branchParts)
    (branches : List
      (Σ branch : WorkflowNet.transitionPostsetOfPlace net split,
        Powl {trans : Trans // branchParts branch trans}))
    (hmodels :
      ∀ (branch :
          Σ branch : WorkflowNet.transitionPostsetOfPlace net split,
            Powl {trans : Trans // branchParts branch trans})
        word,
        Powl.language
            (fun trans :
              {trans : Trans // branchParts branch.1 trans} =>
                label trans.val)
            branch.2
            word ↔
          WorkflowNet.localSubtypeTraceLanguage
            net
            label
            (branchParts branch.1)
            split
            join
            word)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label split join word ↔
          Powl.partialOrderComponentLanguage
            order
            (branches.map
              (fun branch =>
                WorkflowNet.localSubtypeTraceLanguage
                  net label (branchParts branch.1) split join))
            word) :
    ∀ word,
      Powl.language label
          (Powl.partialOrder order
            (branches.map
              (fun branch => Powl.map Subtype.val branch.2)))
          word ↔
        WorkflowNet.localLanguage net label split join word := by
  have hcontainsSource :
      ∀ branch : WorkflowNet.transitionPostsetOfPlace net split,
        branchParts branch branch.val :=
    hfamily.1
  intro word
  rw [Powl.partial_order_language_iff_componentLanguage]
  exact Iff.trans
    (by
      simpa [List.map_map] using
        Powl.partialOrderComponentLanguage_map_congr
          order
          branches
          (fun branch =>
            Powl.language label (Powl.map Subtype.val branch.2))
          (fun branch =>
            WorkflowNet.localSubtypeTraceLanguage
              net label (branchParts branch.1) split join)
          (fun branch word =>
            Iff.trans
              (Powl.language_map Subtype.val label branch.2 word)
              (hmodels branch word))
          word)
    (Iff.symm (hdecompose word))

theorem theorem2_local_partial_order_language_preservation_of_certified_branch_models
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    {order : Rel Nat}
    (branches : List
      (Σ part : Set Trans, Powl {trans : Trans // part trans}))
    (branchNet :
      ∀ branch :
        Σ part : Set Trans, Powl {trans : Trans // part trans},
        WorkflowNet.restrictedDecisionBranchWorkflowNet
          net source sink branch.1)
    (certificates :
      ∀ (branch :
          Σ part : Set Trans, Powl {trans : Trans // part trans})
        (restricted :
          WorkflowNet
            {place : Place //
              WorkflowNet.decisionBranchPlaceSet
                net source sink branch.1 place}
            {trans : Trans // branch.1 trans}),
        restricted.source.val = source ->
        restricted.sink.val = sink ->
          ConversionCertificate
            restricted
            (fun trans : {trans : Trans // branch.1 trans} =>
              label trans.val)
            {trans : Trans // branch.1 trans}
            (fun trans : {trans : Trans // branch.1 trans} =>
              label trans.val)
            branch.2)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label source sink word ↔
          Powl.partialOrderComponentLanguage
            order
            (branches.map
              (fun branch =>
                WorkflowNet.localSubtypeTraceLanguage
                  net label branch.1 source sink))
            word) :
    ∀ word,
      Powl.language label
          (Powl.partialOrder order
            (branches.map
              (fun branch => Powl.map Subtype.val branch.2)))
          word ↔
        WorkflowNet.localLanguage net label source sink word :=
  theorem2_local_partial_order_language_preservation_of_mapped_branch_models
    branches
    (fun branch word =>
      restricted_decision_branch_powl_language_iff_local_subtype_trace_language_of_certificate
        (branchNet branch)
        label
        branch.2
        (certificates branch)
        word)
    hdecompose

def theorem2_decision_branch_local_certified_conversion_xor_of_certified_branch_models
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {split join : Place}
    (branches : List
      (Σ part : Set Trans, Powl {trans : Trans // part trans}))
    (branchNet :
      ∀ branch :
        Σ part : Set Trans, Powl {trans : Trans // part trans},
        WorkflowNet.restrictedDecisionBranchWorkflowNet
          net split join branch.1)
    (certificates :
      ∀ (branch :
          Σ part : Set Trans, Powl {trans : Trans // part trans})
        (restricted :
          WorkflowNet
            {place : Place //
              WorkflowNet.decisionBranchPlaceSet
                net split join branch.1 place}
            {trans : Trans // branch.1 trans}),
        restricted.source.val = split ->
        restricted.sink.val = join ->
          ConversionCertificate
            restricted
            (fun trans : {trans : Trans // branch.1 trans} =>
              label trans.val)
            {trans : Trans // branch.1 trans}
            (fun trans : {trans : Trans // branch.1 trans} =>
              label trans.val)
            branch.2)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label split join word ↔
          Language.unionList
            (branches.map
              (fun branch =>
                WorkflowNet.localSubtypeTraceLanguage
                  net label branch.1 split join))
            word) :
    LocalCertifiedConversion net label split join where
  OutTrans := Trans
  outLabel := label
  model :=
    Powl.xor
      (branches.map
        (fun branch => Powl.map Subtype.val branch.2))
  certificate := fun word =>
    Iff.symm
      (theorem2_decision_branch_local_xor_language_preservation_of_certified_branch_models
        branches branchNet certificates hdecompose word)

def theorem2_local_certified_conversion_loop_of_certified_subtype_components
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    {bodyPart redoPart : Set Trans}
    {body : Powl {trans : Trans // bodyPart trans}}
    {redo : Powl {trans : Trans // redoPart trans}}
    (bodyBranch :
      WorkflowNet.restrictedDecisionBranchWorkflowNet
        net source sink bodyPart)
    (redoBranch :
      WorkflowNet.restrictedDecisionBranchWorkflowNet
        net sink source redoPart)
    (bodyCertificate :
      ∀ (bodyNet :
          WorkflowNet
            {place : Place //
              WorkflowNet.decisionBranchPlaceSet
                net source sink bodyPart place}
            {trans : Trans // bodyPart trans}),
        bodyNet.source.val = source ->
        bodyNet.sink.val = sink ->
          ConversionCertificate
            bodyNet
            (fun trans : {trans : Trans // bodyPart trans} =>
              label trans.val)
            {trans : Trans // bodyPart trans}
            (fun trans : {trans : Trans // bodyPart trans} =>
              label trans.val)
            body)
    (redoCertificate :
      ∀ (redoNet :
          WorkflowNet
            {place : Place //
              WorkflowNet.decisionBranchPlaceSet
                net sink source redoPart place}
            {trans : Trans // redoPart trans}),
        redoNet.source.val = sink ->
        redoNet.sink.val = source ->
          ConversionCertificate
            redoNet
            (fun trans : {trans : Trans // redoPart trans} =>
              label trans.val)
            {trans : Trans // redoPart trans}
            (fun trans : {trans : Trans // redoPart trans} =>
              label trans.val)
            redo)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label source sink word ↔
          Language.concat
            (WorkflowNet.localSubtypeTraceLanguage
              net label bodyPart source sink)
            (Language.Star
              (Language.concat
                (WorkflowNet.localSubtypeTraceLanguage
                  net label redoPart sink source)
                (WorkflowNet.localSubtypeTraceLanguage
                  net label bodyPart source sink)))
            word) :
    LocalCertifiedConversion net label source sink where
  OutTrans := Trans
  outLabel := label
  model :=
    Powl.loop
      (Powl.map Subtype.val body)
      (Powl.map Subtype.val redo)
  certificate := fun word =>
    Iff.symm
      (theorem2_local_loop_language_preservation_of_certified_subtype_components
        bodyBranch redoBranch bodyCertificate redoCertificate
        hdecompose word)

def theorem2_local_certified_conversion_partial_order_of_certified_branch_models
    {Place : Type u}
    {Trans : Type v}
    {Activity : Type w}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {label : Trans -> TransitionLabel Activity}
    {source sink : Place}
    {order : Rel Nat}
    (branches : List
      (Σ part : Set Trans, Powl {trans : Trans // part trans}))
    (branchNet :
      ∀ branch :
        Σ part : Set Trans, Powl {trans : Trans // part trans},
        WorkflowNet.restrictedDecisionBranchWorkflowNet
          net source sink branch.1)
    (certificates :
      ∀ (branch :
          Σ part : Set Trans, Powl {trans : Trans // part trans})
        (restricted :
          WorkflowNet
            {place : Place //
              WorkflowNet.decisionBranchPlaceSet
                net source sink branch.1 place}
            {trans : Trans // branch.1 trans}),
        restricted.source.val = source ->
        restricted.sink.val = sink ->
          ConversionCertificate
            restricted
            (fun trans : {trans : Trans // branch.1 trans} =>
              label trans.val)
            {trans : Trans // branch.1 trans}
            (fun trans : {trans : Trans // branch.1 trans} =>
              label trans.val)
            branch.2)
    (hdecompose :
      ∀ word,
        WorkflowNet.localLanguage net label source sink word ↔
          Powl.partialOrderComponentLanguage
            order
            (branches.map
              (fun branch =>
                WorkflowNet.localSubtypeTraceLanguage
                  net label branch.1 source sink))
            word) :
    LocalCertifiedConversion net label source sink where
  OutTrans := Trans
  outLabel := label
  model :=
    Powl.partialOrder order
      (branches.map
        (fun branch => Powl.map Subtype.val branch.2))
  certificate := fun word =>
    Iff.symm
      (theorem2_local_partial_order_language_preservation_of_certified_branch_models
        branches branchNet certificates hdecompose word)

theorem theorem2_semi_block_subnet_base_requirements
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements :
      WorkflowNet.semiBlockStructuredSubnetRequirements net) :
    WorkflowNet.semiBlockStructuredBaseRequirements net :=
  hrequirements.1

theorem theorem2_semi_block_subnet_pairing_exists
    {Place : Type u}
    {Trans : Type v}
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements :
      WorkflowNet.semiBlockStructuredSubnetRequirements net) :
    ∃ pair, WorkflowNet.decisionPairingWithBranchSubnets net pair :=
  hrequirements.2

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

theorem lemma2_loop_projection_restricted_flow_original
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place)
    {first second :
      PetriNet.Node
        {place : Place //
          Patterns.loopProjectionPlaces net part startPlace endPlace place}
        {trans : Trans // part trans}}
    (hflow :
      PetriNet.flow
        (Patterns.loopProjectionRestricted net part startPlace endPlace)
        first second) :
    PetriNet.flow
      (Patterns.loopProjection net part startPlace endPlace)
      (PetriNet.restrictedNode first)
      (PetriNet.restrictedNode second) :=
  Patterns.loopProjectionRestricted_flow_original
    net part startPlace endPlace hflow

theorem lemma2_loop_projection_restricted_path_original
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place)
    {source target :
      PetriNet.Node
        {place : Place //
          Patterns.loopProjectionPlaces net part startPlace endPlace place}
        {trans : Trans // part trans}}
    (path :
      PetriNet.Path
        (Patterns.loopProjectionRestricted net part startPlace endPlace)
        source
        target) :
    PetriNet.Path
      (Patterns.loopProjection net part startPlace endPlace)
      (PetriNet.restrictedNode source)
      (PetriNet.restrictedNode target) :=
  Patterns.loopProjectionRestricted_path_original
    net part startPlace endPlace path

theorem lemma2_loop_projection_restricted_path_of_pathIn
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place)
    {source target : PetriNet.Node Place Trans}
    (path :
      PetriNet.PathIn
        (Patterns.loopProjection net part startPlace endPlace)
        (Patterns.loopProjectionPlaces net part startPlace endPlace)
        part
        source
        target) :
    PetriNet.Path
      (Patterns.loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.restrictNode source (PetriNet.PathIn.source_mem path))
      (PetriNet.restrictNode target (PetriNet.PathIn.target_mem path)) :=
  Patterns.loopProjectionRestricted_path_of_pathIn
    net part startPlace endPlace path

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

theorem lemma2_loop_projection_restricted_source_edge
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    {trans : Trans}
    (hpart : part trans)
    (hflow : net.placeToTrans startPlace trans) :
    (Patterns.loopProjectionRestricted net part startPlace endPlace).placeToTrans
      ⟨net.source,
        Patterns.loopProjectionPlaces_source net part startPlace endPlace⟩
      ⟨trans, hpart⟩ :=
  Patterns.loopProjectionRestricted_source_placeToTrans
    net hpart hflow

theorem lemma2_loop_projection_restricted_sink_edge
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    {trans : Trans}
    (hpart : part trans)
    (hflow : net.transToPlace trans endPlace) :
    (Patterns.loopProjectionRestricted net part startPlace endPlace).transToPlace
      ⟨trans, hpart⟩
      ⟨net.sink,
        Patterns.loopProjectionPlaces_sink net part startPlace endPlace⟩ :=
  Patterns.loopProjectionRestricted_transToPlace_sink
    net hpart hflow

theorem lemma2_loop_projection_restricted_internal_place_edge
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    {trans : Trans}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hstart : place ≠ startPlace)
    (hend : place ≠ endPlace)
    (hflow : net.placeToTrans place trans) :
    (Patterns.loopProjectionRestricted net part startPlace endPlace).placeToTrans
      ⟨place,
        Patterns.loopProjectionPlaces_internal net htouching hstart hend⟩
      ⟨trans, hpart⟩ :=
  Patterns.loopProjectionRestricted_internal_placeToTrans
    net hpart htouching hstart hend hflow

theorem lemma2_loop_projection_restricted_internal_transition_edge
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    {trans : Trans}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hstart : place ≠ startPlace)
    (hend : place ≠ endPlace)
    (hflow : net.transToPlace trans place) :
    (Patterns.loopProjectionRestricted net part startPlace endPlace).transToPlace
      ⟨trans, hpart⟩
      ⟨place,
        Patterns.loopProjectionPlaces_internal net htouching hstart hend⟩ :=
  Patterns.loopProjectionRestricted_internal_transToPlace
    net hpart htouching hstart hend hflow

theorem lemma2_loop_projection_internal_place_to_transition
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    {trans : Trans}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hstart : place ≠ startPlace)
    (hend : place ≠ endPlace)
    (hflow : net.placeToTrans place trans) :
    PetriNet.Path
      (Patterns.loopProjection net part startPlace endPlace)
      (PetriNet.Node.place place)
      (PetriNet.Node.trans trans) :=
  Patterns.loopProjection_internal_place_to_transition
    net hpart htouching hstart hend hflow

theorem lemma2_loop_projection_transition_to_internal_place
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    {trans : Trans}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hstart : place ≠ startPlace)
    (hend : place ≠ endPlace)
    (hflow : net.transToPlace trans place) :
    PetriNet.Path
      (Patterns.loopProjection net part startPlace endPlace)
      (PetriNet.Node.trans trans)
      (PetriNet.Node.place place) :=
  Patterns.loopProjection_transition_to_internal_place
    net hpart htouching hstart hend hflow

theorem lemma2_loop_projection_restricted_internal_place_to_transition
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    {trans : Trans}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hstart : place ≠ startPlace)
    (hend : place ≠ endPlace)
    (hflow : net.placeToTrans place trans) :
    PetriNet.Path
      (Patterns.loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.Node.place
        ⟨place,
          Patterns.loopProjectionPlaces_internal net htouching hstart hend⟩)
      (PetriNet.Node.trans ⟨trans, hpart⟩) :=
  Patterns.loopProjectionRestricted_internal_place_to_transition
    net hpart htouching hstart hend hflow

theorem lemma2_loop_projection_restricted_transition_to_internal_place
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    {trans : Trans}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hstart : place ≠ startPlace)
    (hend : place ≠ endPlace)
    (hflow : net.transToPlace trans place) :
    PetriNet.Path
      (Patterns.loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.Node.trans ⟨trans, hpart⟩)
      (PetriNet.Node.place
        ⟨place,
          Patterns.loopProjectionPlaces_internal net htouching hstart hend⟩) :=
  Patterns.loopProjectionRestricted_transition_to_internal_place
    net hpart htouching hstart hend hflow

theorem lemma2_loop_projection_restricted_internal_to_member_transition
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    {trace : List Trans}
    {target : Trans}
    (path : PetriNet.PlacePathTo net.toPetriNet endPlace place trace)
    (hclosed : ∀ trans, trans ∈ trace -> part trans)
    (hnoInStart : ∀ trans, part trans ->
      ¬ net.transToPlace trans startPlace)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hstart : place ≠ startPlace)
    (hend : place ≠ endPlace)
    (hmem : target ∈ trace) :
    PetriNet.Path
      (Patterns.loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.Node.place
        ⟨place,
          Patterns.loopProjectionPlaces_internal net htouching hstart hend⟩)
      (PetriNet.Node.trans ⟨target, hclosed target hmem⟩) :=
  Patterns.loopProjectionRestricted_internal_to_member_transition_of_placePath
    net path hclosed hnoInStart htouching hstart hend hmem

theorem lemma2_loop_projection_restricted_source_to_member_transition
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    {trace : List Trans}
    {target : Trans}
    (path : PetriNet.PlacePathTo net.toPetriNet endPlace startPlace trace)
    (hclosed : ∀ trans, trans ∈ trace -> part trans)
    (hnoInStart : ∀ trans, part trans ->
      ¬ net.transToPlace trans startPlace)
    (hmem : target ∈ trace) :
    PetriNet.Path
      (Patterns.loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.Node.place
        ⟨net.source,
          Patterns.loopProjectionPlaces_source
            net part startPlace endPlace⟩)
      (PetriNet.Node.trans ⟨target, hclosed target hmem⟩) :=
  Patterns.loopProjectionRestricted_source_to_member_transition_of_placePath
    net path hclosed hnoInStart hmem

theorem lemma2_loop_projection_restricted_internal_to_sink
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    {trace : List Trans}
    (path : PetriNet.PlacePathTo net.toPetriNet endPlace place trace)
    (hclosed : ∀ trans, trans ∈ trace -> part trans)
    (hnoInStart : ∀ trans, part trans ->
      ¬ net.transToPlace trans startPlace)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hstart : place ≠ startPlace)
    (hend : place ≠ endPlace) :
    PetriNet.Path
      (Patterns.loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.Node.place
        ⟨place,
          Patterns.loopProjectionPlaces_internal net htouching hstart hend⟩)
      (PetriNet.Node.place
        ⟨net.sink,
          Patterns.loopProjectionPlaces_sink
            net part startPlace endPlace⟩) :=
  Patterns.loopProjectionRestricted_internal_to_sink_of_placePath
    net path hclosed hnoInStart htouching hstart hend

theorem lemma2_loop_projection_restricted_member_transition_to_sink
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    {trace : List Trans}
    {target : Trans}
    (path : PetriNet.PlacePathTo net.toPetriNet endPlace place trace)
    (hclosed : ∀ trans, trans ∈ trace -> part trans)
    (hnoInStart : ∀ trans, part trans ->
      ¬ net.transToPlace trans startPlace)
    (hmem : target ∈ trace) :
    PetriNet.Path
      (Patterns.loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.Node.trans ⟨target, hclosed target hmem⟩)
      (PetriNet.Node.place
        ⟨net.sink,
          Patterns.loopProjectionPlaces_sink
            net part startPlace endPlace⟩) :=
  Patterns.loopProjectionRestricted_member_transition_to_sink_of_placePath
    net path hclosed hnoInStart hmem

theorem lemma2_loop_projection_restricted_transition_connected
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
        PetriNet.Path
            (Patterns.loopProjectionRestricted net doPart pdo predo)
            (PetriNet.Node.place
              ⟨net.source,
                Patterns.loopProjectionPlaces_source net doPart pdo predo⟩)
            (PetriNet.Node.trans trans) ∧
          PetriNet.Path
            (Patterns.loopProjectionRestricted net doPart pdo predo)
            (PetriNet.Node.trans trans)
            (PetriNet.Node.place
              ⟨net.sink,
                Patterns.loopProjectionPlaces_sink net doPart pdo predo⟩)) ∧
      (∀ trans : {trans : Trans // redoPart trans},
        PetriNet.Path
            (Patterns.loopProjectionRestricted net redoPart predo pdo)
            (PetriNet.Node.place
              ⟨net.source,
                Patterns.loopProjectionPlaces_source net redoPart predo pdo⟩)
            (PetriNet.Node.trans trans) ∧
          PetriNet.Path
            (Patterns.loopProjectionRestricted net redoPart predo pdo)
            (PetriNet.Node.trans trans)
            (PetriNet.Node.place
              ⟨net.sink,
                Patterns.loopProjectionPlaces_sink net redoPart predo pdo⟩)) :=
  Patterns.loopPattern_projection_restricted_transition_connected hpattern

theorem lemma2_loop_projection_restricted_internal_place_directional_connected
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
      (∀ {place trans}, doPart trans ->
        (htouching : PetriNet.placesTouching net.toPetriNet doPart place) ->
        (hstart : place ≠ pdo) ->
        (hend : place ≠ predo) ->
        net.transToPlace trans place ->
          PetriNet.Path
            (Patterns.loopProjectionRestricted net doPart pdo predo)
            (PetriNet.Node.place
              ⟨net.source,
                Patterns.loopProjectionPlaces_source net doPart pdo predo⟩)
            (PetriNet.Node.place
              ⟨place,
                Patterns.loopProjectionPlaces_internal net htouching
                  hstart hend⟩)) ∧
      (∀ {place trans}, doPart trans ->
        (htouching : PetriNet.placesTouching net.toPetriNet doPart place) ->
        (hstart : place ≠ pdo) ->
        (hend : place ≠ predo) ->
        net.placeToTrans place trans ->
          PetriNet.Path
            (Patterns.loopProjectionRestricted net doPart pdo predo)
            (PetriNet.Node.place
              ⟨place,
                Patterns.loopProjectionPlaces_internal net htouching
                  hstart hend⟩)
            (PetriNet.Node.place
              ⟨net.sink,
                Patterns.loopProjectionPlaces_sink net doPart pdo predo⟩)) ∧
      (∀ {place trans}, redoPart trans ->
        (htouching : PetriNet.placesTouching net.toPetriNet redoPart place) ->
        (hstart : place ≠ predo) ->
        (hend : place ≠ pdo) ->
        net.transToPlace trans place ->
          PetriNet.Path
            (Patterns.loopProjectionRestricted net redoPart predo pdo)
            (PetriNet.Node.place
              ⟨net.source,
                Patterns.loopProjectionPlaces_source net redoPart predo pdo⟩)
            (PetriNet.Node.place
              ⟨place,
                Patterns.loopProjectionPlaces_internal net htouching
                  hstart hend⟩)) ∧
      (∀ {place trans}, redoPart trans ->
        (htouching : PetriNet.placesTouching net.toPetriNet redoPart place) ->
        (hstart : place ≠ predo) ->
        (hend : place ≠ pdo) ->
        net.placeToTrans place trans ->
          PetriNet.Path
            (Patterns.loopProjectionRestricted net redoPart predo pdo)
            (PetriNet.Node.place
              ⟨place,
                Patterns.loopProjectionPlaces_internal net htouching
                  hstart hend⟩)
            (PetriNet.Node.place
              ⟨net.sink,
                Patterns.loopProjectionPlaces_sink net redoPart predo pdo⟩)) :=
  Patterns.loopPattern_projection_restricted_internal_place_directional_connected
    hpattern

theorem lemma2_loop_projection_restricted_internal_place_connected_of_incident_transitions
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
      (∀ {place},
        (htouching : PetriNet.placesTouching net.toPetriNet doPart place) ->
        (hstart : place ≠ pdo) ->
        (hend : place ≠ predo) ->
        (∃ trans, doPart trans ∧ net.transToPlace trans place) ->
        (∃ trans, doPart trans ∧ net.placeToTrans place trans) ->
          PetriNet.Path
              (Patterns.loopProjectionRestricted net doPart pdo predo)
              (PetriNet.Node.place
                ⟨net.source,
                  Patterns.loopProjectionPlaces_source
                    net doPart pdo predo⟩)
              (PetriNet.Node.place
                ⟨place,
                  Patterns.loopProjectionPlaces_internal
                    net htouching hstart hend⟩) ∧
            PetriNet.Path
              (Patterns.loopProjectionRestricted net doPart pdo predo)
              (PetriNet.Node.place
                ⟨place,
                  Patterns.loopProjectionPlaces_internal
                    net htouching hstart hend⟩)
              (PetriNet.Node.place
                ⟨net.sink,
                  Patterns.loopProjectionPlaces_sink
                    net doPart pdo predo⟩)) ∧
      (∀ {place},
        (htouching : PetriNet.placesTouching net.toPetriNet redoPart place) ->
        (hstart : place ≠ predo) ->
        (hend : place ≠ pdo) ->
        (∃ trans, redoPart trans ∧ net.transToPlace trans place) ->
        (∃ trans, redoPart trans ∧ net.placeToTrans place trans) ->
          PetriNet.Path
              (Patterns.loopProjectionRestricted net redoPart predo pdo)
              (PetriNet.Node.place
                ⟨net.source,
                  Patterns.loopProjectionPlaces_source
                    net redoPart predo pdo⟩)
              (PetriNet.Node.place
                ⟨place,
                  Patterns.loopProjectionPlaces_internal
                    net htouching hstart hend⟩) ∧
            PetriNet.Path
              (Patterns.loopProjectionRestricted net redoPart predo pdo)
              (PetriNet.Node.place
                ⟨place,
                  Patterns.loopProjectionPlaces_internal
                    net htouching hstart hend⟩)
              (PetriNet.Node.place
                ⟨net.sink,
                  Patterns.loopProjectionPlaces_sink
                    net redoPart predo pdo⟩)) :=
  Patterns.loopPattern_projection_restricted_internal_place_connected_of_incident_transitions
    hpattern

theorem lemma2_loop_projection_restricted_connected_of_reachable_incident
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    (hpartReach :
      ∀ candidate,
        part candidate ↔
          PetriNet.reachableTransitionsBetweenPlaces
            net.toPetriNet startPlace endPlace candidate)
    (hnoInStart : ∀ candidate, part candidate ->
      ¬ net.transToPlace candidate startPlace)
    (hnonempty : ∃ trans, part trans)
    (hincoming :
      ∀ {place : Place},
        PetriNet.placesTouching net.toPetriNet part place ->
        place ≠ startPlace ->
        place ≠ endPlace ->
          ∃ trans, part trans ∧ net.transToPlace trans place)
    (houtgoing :
      ∀ {place : Place},
        PetriNet.placesTouching net.toPetriNet part place ->
        place ≠ startPlace ->
        place ≠ endPlace ->
          ∃ trans, part trans ∧ net.placeToTrans place trans) :
    ∀ node :
      PetriNet.Node
        {place : Place //
          Patterns.loopProjectionPlaces net part startPlace endPlace place}
        {trans : Trans // part trans},
      PetriNet.Path
          (Patterns.loopProjectionRestricted net part startPlace endPlace)
          (PetriNet.Node.place
            ⟨net.source,
              Patterns.loopProjectionPlaces_source
                net part startPlace endPlace⟩)
          node ∧
        PetriNet.Path
          (Patterns.loopProjectionRestricted net part startPlace endPlace)
          node
          (PetriNet.Node.place
            ⟨net.sink,
              Patterns.loopProjectionPlaces_sink
                net part startPlace endPlace⟩) :=
  Patterns.loopProjectionRestricted_connected_of_reachable_incident
    (part := part)
    (startPlace := startPlace)
    (endPlace := endPlace)
    net hpartReach hnoInStart hnonempty hincoming houtgoing

theorem lemma2_loop_pattern_projection_restricted_connected_of_internal_incidence
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
      ((∀ {place : Place},
          PetriNet.placesTouching net.toPetriNet doPart place ->
          place ≠ pdo ->
          place ≠ predo ->
            ∃ trans, doPart trans ∧ net.transToPlace trans place) ->
        (∀ {place : Place},
          PetriNet.placesTouching net.toPetriNet doPart place ->
          place ≠ pdo ->
          place ≠ predo ->
            ∃ trans, doPart trans ∧ net.placeToTrans place trans) ->
        ∀ node :
          PetriNet.Node
            {place : Place //
              Patterns.loopProjectionPlaces net doPart pdo predo place}
            {trans : Trans // doPart trans},
          PetriNet.Path
              (Patterns.loopProjectionRestricted net doPart pdo predo)
              (PetriNet.Node.place
                ⟨net.source,
                  Patterns.loopProjectionPlaces_source
                    net doPart pdo predo⟩)
              node ∧
            PetriNet.Path
              (Patterns.loopProjectionRestricted net doPart pdo predo)
              node
              (PetriNet.Node.place
                ⟨net.sink,
                  Patterns.loopProjectionPlaces_sink
                    net doPart pdo predo⟩)) ∧
      ((∀ {place : Place},
          PetriNet.placesTouching net.toPetriNet redoPart place ->
          place ≠ predo ->
          place ≠ pdo ->
            ∃ trans, redoPart trans ∧ net.transToPlace trans place) ->
        (∀ {place : Place},
          PetriNet.placesTouching net.toPetriNet redoPart place ->
          place ≠ predo ->
          place ≠ pdo ->
            ∃ trans, redoPart trans ∧ net.placeToTrans place trans) ->
        ∀ node :
          PetriNet.Node
            {place : Place //
              Patterns.loopProjectionPlaces net redoPart predo pdo place}
            {trans : Trans // redoPart trans},
          PetriNet.Path
              (Patterns.loopProjectionRestricted net redoPart predo pdo)
              (PetriNet.Node.place
                ⟨net.source,
                  Patterns.loopProjectionPlaces_source
                    net redoPart predo pdo⟩)
              node ∧
            PetriNet.Path
              (Patterns.loopProjectionRestricted net redoPart predo pdo)
              node
              (PetriNet.Node.place
                ⟨net.sink,
                  Patterns.loopProjectionPlaces_sink
                    net redoPart predo pdo⟩)) :=
  Patterns.loopPattern_projection_restricted_connected_of_internal_incidence
    hpattern

theorem lemma2_loop_pattern_projection_workflow_nets_of_internal_incidence
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
      ((∀ {place : Place},
          PetriNet.placesTouching net.toPetriNet doPart place ->
          place ≠ pdo ->
          place ≠ predo ->
            ∃ trans, doPart trans ∧ net.transToPlace trans place) ->
        (∀ {place : Place},
          PetriNet.placesTouching net.toPetriNet doPart place ->
          place ≠ pdo ->
          place ≠ predo ->
            ∃ trans, doPart trans ∧ net.placeToTrans place trans) ->
          Nonempty
            (WorkflowNet
              {place : Place //
                Patterns.loopProjectionPlaces
                  net doPart pdo predo place}
              {trans : Trans // doPart trans})) ∧
      ((∀ {place : Place},
          PetriNet.placesTouching net.toPetriNet redoPart place ->
          place ≠ predo ->
          place ≠ pdo ->
            ∃ trans, redoPart trans ∧ net.transToPlace trans place) ->
        (∀ {place : Place},
          PetriNet.placesTouching net.toPetriNet redoPart place ->
          place ≠ predo ->
          place ≠ pdo ->
            ∃ trans, redoPart trans ∧ net.placeToTrans place trans) ->
          Nonempty
            (WorkflowNet
              {place : Place //
                Patterns.loopProjectionPlaces
                  net redoPart predo pdo place}
              {trans : Trans // redoPart trans})) := by
  rcases
    Patterns.loopPattern_projection_restricted_connected_of_internal_incidence
      hpattern with
    ⟨doPart, redoPart, pdo, predo, hdoMem, hredoMem,
      hdoConnected, hredoConnected⟩
  have hsourceSink : net.source ≠ net.sink :=
    Patterns.loopPattern_source_ne_sink hpattern
  refine
    ⟨doPart, redoPart, pdo, predo, hdoMem, hredoMem, ?_, ?_⟩
  · intro hincoming houtgoing
    exact ⟨
      Patterns.loopProjectionWorkflowNetOfConnected
        net doPart pdo predo hsourceSink
        (hdoConnected hincoming houtgoing)⟩
  · intro hincoming houtgoing
    exact ⟨
      Patterns.loopProjectionWorkflowNetOfConnected
        net redoPart predo pdo hsourceSink
        (hredoConnected hincoming houtgoing)⟩

def lemma2_loop_projection_workflow_net_of_connected
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place)
    (hsourceSink : net.source ≠ net.sink)
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : Place //
            Patterns.loopProjectionPlaces net part startPlace endPlace place}
          {trans : Trans // part trans},
        PetriNet.Path
            (Patterns.loopProjectionRestricted net part startPlace endPlace)
            (PetriNet.Node.place
              ⟨net.source,
                Patterns.loopProjectionPlaces_source
                  net part startPlace endPlace⟩)
            node ∧
          PetriNet.Path
            (Patterns.loopProjectionRestricted net part startPlace endPlace)
            node
            (PetriNet.Node.place
              ⟨net.sink,
                Patterns.loopProjectionPlaces_sink
                  net part startPlace endPlace⟩)) :
    WorkflowNet
      {place : Place //
        Patterns.loopProjectionPlaces net part startPlace endPlace place}
      {trans : Trans // part trans} :=
  Patterns.loopProjectionWorkflowNetOfConnected
    net part startPlace endPlace hsourceSink hconnected

def lemma2_loop_projection_workflow_net_of_reachable_incident
    {Place : Type u}
    {Trans : Type v}
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place)
    (hsourceSink : net.source ≠ net.sink)
    (hpartReach :
      ∀ candidate,
        part candidate ↔
          PetriNet.reachableTransitionsBetweenPlaces
            net.toPetriNet startPlace endPlace candidate)
    (hnoInStart : ∀ candidate, part candidate ->
      ¬ net.transToPlace candidate startPlace)
    (hnonempty : ∃ trans, part trans)
    (hincoming :
      ∀ {place : Place},
        PetriNet.placesTouching net.toPetriNet part place ->
        place ≠ startPlace ->
        place ≠ endPlace ->
          ∃ trans, part trans ∧ net.transToPlace trans place)
    (houtgoing :
      ∀ {place : Place},
        PetriNet.placesTouching net.toPetriNet part place ->
        place ≠ startPlace ->
        place ≠ endPlace ->
          ∃ trans, part trans ∧ net.placeToTrans place trans) :
    WorkflowNet
      {place : Place //
        Patterns.loopProjectionPlaces net part startPlace endPlace place}
      {trans : Trans // part trans} :=
  Patterns.loopProjectionWorkflowNetOfReachableIncident
    net part startPlace endPlace hsourceSink
    hpartReach hnoInStart hnonempty hincoming houtgoing

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
