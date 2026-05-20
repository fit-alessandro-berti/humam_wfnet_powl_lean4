import KouraniWfnetPowl.Language

namespace KouraniWfnetPowl

inductive TransitionLabel (Activity : Type u) where
  | silent : TransitionLabel Activity
  | visible : Activity -> TransitionLabel Activity

namespace TransitionLabel

def word : TransitionLabel Activity -> List Activity
  | silent => []
  | visible activity => [activity]

end TransitionLabel

inductive Powl (Transition : Type u) where
  | atom : Transition -> Powl Transition
  | xor : List (Powl Transition) -> Powl Transition
  | loop : Powl Transition -> Powl Transition -> Powl Transition
  | partialOrder : Rel Nat -> List (Powl Transition) -> Powl Transition

namespace Powl

def map
    {Transition : Type u}
    {Transition' : Type v}
    (f : Transition -> Transition') :
    Powl Transition -> Powl Transition' :=
  Powl.rec
    (motive_1 := fun _ => Powl Transition')
    (motive_2 := fun _ => List (Powl Transition'))
    (fun trans => Powl.atom (f trans))
    (fun _ mappedModels => Powl.xor mappedModels)
    (fun _ _ mappedBody mappedRedo => Powl.loop mappedBody mappedRedo)
    (fun order _ mappedModels => Powl.partialOrder order mappedModels)
    []
    (fun _ _ mappedHead mappedTail => mappedHead :: mappedTail)

theorem map_atom
    {Transition : Type u}
    {Transition' : Type v}
    (f : Transition -> Transition')
    (trans : Transition) :
    map f (Powl.atom trans) = Powl.atom (f trans) :=
  rfl

theorem map_xor
    {Transition : Type u}
    {Transition' : Type v}
    (f : Transition -> Transition')
    (models : List (Powl Transition)) :
    map f (Powl.xor models) = Powl.xor (models.map (map f)) := by
  induction models with
  | nil =>
      rfl
  | cons head tail ih =>
      simp [map, ih]

theorem map_loop
    {Transition : Type u}
    {Transition' : Type v}
    (f : Transition -> Transition')
    (body redo : Powl Transition) :
    map f (Powl.loop body redo) =
      Powl.loop (map f body) (map f redo) :=
  rfl

theorem map_partialOrder
    {Transition : Type u}
    {Transition' : Type v}
    (f : Transition -> Transition')
    (order : Rel Nat)
    (models : List (Powl Transition)) :
    map f (Powl.partialOrder order models) =
      Powl.partialOrder order (models.map (map f)) := by
  induction models with
  | nil =>
      rfl
  | cons head tail ih =>
      simp [map, ih]

def listGet? : List alpha -> Nat -> Option alpha
  | [], _ => none
  | head :: _, 0 => some head
  | _ :: tail, index + 1 => listGet? tail index

theorem listGet?_mem
    {items : List alpha}
    {index : Nat}
    {item : alpha}
    (hget : listGet? items index = some item) :
    item ∈ items := by
  induction items generalizing index with
  | nil =>
      cases index <;> cases hget
  | cons head tail ih =>
      cases index with
      | zero =>
          simp [listGet?] at hget
          simp [hget]
      | succ index =>
          simp [listGet?] at hget
          exact List.Mem.tail head (ih hget)

theorem listGet?_exists_mem
    {items : List alpha}
    {index : Nat}
    {item : alpha}
    (hget : listGet? items index = some item) :
    ∃ member, member ∈ items ∧ member = item :=
  ⟨item, listGet?_mem hget, rfl⟩

theorem listGet?_some_lt_length
    {items : List alpha}
    {index : Nat}
    {item : alpha}
    (hget : listGet? items index = some item) :
    index < items.length := by
  induction items generalizing index with
  | nil =>
      cases index <;> cases hget
  | cons head tail ih =>
      cases index with
      | zero =>
          simp
      | succ index =>
          simp [listGet?] at hget
          exact Nat.succ_lt_succ (ih hget)

theorem listGet?_exists_of_lt_length
    {items : List alpha}
    {index : Nat}
    (hlt : index < items.length) :
    ∃ item, listGet? items index = some item := by
  induction items generalizing index with
  | nil =>
      cases hlt
  | cons head tail ih =>
      cases index with
      | zero =>
          exact ⟨head, rfl⟩
      | succ index =>
          have htail : index < tail.length :=
            Nat.lt_of_succ_lt_succ hlt
          rcases ih htail with ⟨item, hget⟩
          exact ⟨item, by simpa [listGet?] using hget⟩

theorem listGet?_map_eq_some
    {items : List alpha}
    {f : alpha -> beta}
    {index : Nat}
    {item : alpha}
    (hget : listGet? items index = some item) :
    listGet? (items.map f) index = some (f item) := by
  induction items generalizing index with
  | nil =>
      cases index <;> cases hget
  | cons head tail ih =>
      cases index with
      | zero =>
          simp [listGet?] at hget ⊢
          exact congrArg f hget
      | succ index =>
          simp [listGet?] at hget ⊢
          exact ih hget

theorem listGet?_map_some
    {items : List alpha}
    {f : alpha -> beta}
    {index : Nat}
    {mapped : beta}
    (hget : listGet? (items.map f) index = some mapped) :
    ∃ item, listGet? items index = some item ∧ f item = mapped := by
  induction items generalizing index with
  | nil =>
      cases index <;> cases hget
  | cons head tail ih =>
      cases index with
      | zero =>
          simp [listGet?] at hget
          exact ⟨head, by simp [listGet?], hget⟩
      | succ index =>
          simp [listGet?] at hget
          rcases ih hget with ⟨item, hitem, hmapped⟩
          exact ⟨item, by simpa [listGet?] using hitem, hmapped⟩

theorem unionList_congr_indexed
    {Activity : Type u}
    {left right : List (Language Activity)}
    (hlength : left.length = right.length)
    (hcomponent :
      ∀ index leftLanguage rightLanguage,
        listGet? left index = some leftLanguage ->
        listGet? right index = some rightLanguage ->
          ∀ word, leftLanguage word ↔ rightLanguage word)
    (word : List Activity) :
    Language.unionList left word ↔ Language.unionList right word := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil =>
          rfl
      | cons rightHead rightTail =>
          simp at hlength
  | cons leftHead leftTail ih =>
      cases right with
      | nil =>
          simp at hlength
      | cons rightHead rightTail =>
          have htailLength : leftTail.length = rightTail.length := by
            simpa using hlength
          constructor
          · intro h
            cases h with
            | inl hleft =>
                exact Or.inl
                  ((hcomponent 0 leftHead rightHead rfl rfl word).mp
                    hleft)
            | inr hleftTail =>
                exact Or.inr
                  ((ih htailLength
                    (fun index leftLanguage rightLanguage hleft hright =>
                      hcomponent (index + 1) leftLanguage rightLanguage
                        (by simpa [listGet?] using hleft)
                        (by simpa [listGet?] using hright))).mp
                    hleftTail)
          · intro h
            cases h with
            | inl hright =>
                exact Or.inl
                  ((hcomponent 0 leftHead rightHead rfl rfl word).mpr
                    hright)
            | inr hrightTail =>
                exact Or.inr
                  ((ih htailLength
                    (fun index leftLanguage rightLanguage hleft hright =>
                      hcomponent (index + 1) leftLanguage rightLanguage
                        (by simpa [listGet?] using hleft)
                        (by simpa [listGet?] using hright))).mpr
                    hrightTail)

abbrev TaggedTrace (Activity : Type u) := List (Nat × Activity)

def eraseTags : TaggedTrace Activity -> List Activity
  | [] => []
  | (_, activity) :: rest => activity :: eraseTags rest

def component (index : Nat) : TaggedTrace Activity -> List Activity
  | [] => []
  | (tag, activity) :: rest =>
      if tag = index then
        activity :: component index rest
      else
        component index rest

def tagsBounded (bound : Nat) (trace : TaggedTrace Activity) : Prop :=
  ∀ tagged, tagged ∈ trace -> tagged.fst < bound

def orderPreserving
    (order : Rel Nat)
    (trace : TaggedTrace Activity) : Prop :=
  ∀ left right,
    order left right ->
      ¬ ∃ pre mid suf leftActivity rightActivity,
        trace =
          pre ++ ((right, rightActivity) :: mid) ++
            ((left, leftActivity) :: suf)

inductive Semantics
    {Transition : Type u}
    {Activity : Type v}
    (label : Transition -> TransitionLabel Activity) :
    Powl Transition -> List Activity -> Prop where
  | atomSilent {trans : Transition} :
      label trans = TransitionLabel.silent ->
      Semantics label (Powl.atom trans) []
  | atomVisible {trans : Transition} {activity : Activity} :
      label trans = TransitionLabel.visible activity ->
      Semantics label (Powl.atom trans) [activity]
  | xor {models : List (Powl Transition)} {model : Powl Transition}
      {word : List Activity} :
      model ∈ models ->
      Semantics label model word ->
      Semantics label (Powl.xor models) word
  | loopOnce {body redo : Powl Transition} {bodyWord : List Activity} :
      Semantics label body bodyWord ->
      Semantics label (Powl.loop body redo) bodyWord
  | loopMore
      {body redo : Powl Transition}
      {bodyWord redoWord rest : List Activity} :
      Semantics label body bodyWord ->
      Semantics label redo redoWord ->
      Semantics label (Powl.loop body redo) rest ->
      Semantics label (Powl.loop body redo) (bodyWord ++ redoWord ++ rest)
  | partialOrder
      {order : Rel Nat}
      {models : List (Powl Transition)}
      {word : List Activity}
      {tagged : TaggedTrace Activity} :
      eraseTags tagged = word ->
      tagsBounded models.length tagged ->
      orderPreserving order tagged ->
      (∀ index model,
        listGet? models index = some model ->
          Semantics label model (component index tagged)) ->
      Semantics label (Powl.partialOrder order models) word

def language
    {Transition : Type u}
    {Activity : Type v}
    (label : Transition -> TransitionLabel Activity)
    (model : Powl Transition) : Language Activity :=
  fun word => Semantics label model word

def transitionWord
    {Transition : Type u}
    {Activity : Type v}
    (label : Transition -> TransitionLabel Activity)
    (trans : Transition) : List Activity :=
  TransitionLabel.word (label trans)

theorem atom_language_iff
    {Transition : Type u}
    {Activity : Type v}
    {label : Transition -> TransitionLabel Activity}
    {trans : Transition}
    {word : List Activity} :
    language label (Powl.atom trans) word ↔
      word = transitionWord label trans := by
  constructor
  · intro h
    cases h with
    | atomSilent hlabel =>
        unfold transitionWord
        rw [hlabel]
        rfl
    | atomVisible hlabel =>
        unfold transitionWord
        rw [hlabel]
        rfl
  · intro hword
    unfold transitionWord at hword
    cases hlabel : label trans with
    | silent =>
        rw [hlabel] at hword
        rw [hword]
        exact Semantics.atomSilent hlabel
    | visible activity =>
        rw [hlabel] at hword
        rw [hword]
        exact Semantics.atomVisible hlabel

def partialOrderLanguage
    {Transition : Type u}
    {Activity : Type v}
    (label : Transition -> TransitionLabel Activity)
    (order : Rel Nat)
    (models : List (Powl Transition)) :
    Language Activity :=
  fun word =>
    ∃ tagged,
      eraseTags tagged = word ∧
      tagsBounded models.length tagged ∧
      orderPreserving order tagged ∧
      ∀ index model,
        listGet? models index = some model ->
          language label model (component index tagged)

def partialOrderComponentLanguage
    {Activity : Type u}
    (order : Rel Nat)
    (components : List (Language Activity)) :
    Language Activity :=
  fun word =>
    ∃ tagged,
      eraseTags tagged = word ∧
      tagsBounded components.length tagged ∧
      orderPreserving order tagged ∧
      ∀ index componentLanguage,
        listGet? components index = some componentLanguage ->
          componentLanguage (component index tagged)

theorem partialOrderLanguage_iff_componentLanguage
    {Transition : Type u}
    {Activity : Type v}
    {label : Transition -> TransitionLabel Activity}
    {order : Rel Nat}
    {models : List (Powl Transition)}
    {word : List Activity} :
    partialOrderLanguage label order models word ↔
      partialOrderComponentLanguage
        order
        (models.map (language label))
        word := by
  constructor
  · intro h
    rcases h with ⟨tagged, herase, hbounded, horder, hcomponents⟩
    refine ⟨tagged, herase, ?_, horder, ?_⟩
    · simpa using hbounded
    · intro index componentLanguage hget
      rcases listGet?_map_some hget with
        ⟨model, hmodel, hcomponentEq⟩
      subst hcomponentEq
      exact hcomponents index model hmodel
  · intro h
    rcases h with ⟨tagged, herase, hbounded, horder, hcomponents⟩
    refine ⟨tagged, herase, ?_, horder, ?_⟩
    · simpa using hbounded
    · intro index model hget
      exact hcomponents index (language label model)
        (listGet?_map_eq_some hget)

theorem partialOrderComponentLanguage_map_congr
    {Model : Type u}
    {Activity : Type v}
    (order : Rel Nat)
    (models : List Model)
    (left right : Model -> Language Activity)
    (h :
      ∀ model word,
        left model word ↔ right model word)
    (word : List Activity) :
    partialOrderComponentLanguage order (models.map left) word ↔
      partialOrderComponentLanguage order (models.map right) word := by
  constructor
  · intro hlanguage
    rcases hlanguage with
      ⟨tagged, herase, hbounded, horder, hcomponents⟩
    refine ⟨tagged, herase, ?_, horder, ?_⟩
    · simpa using hbounded
    · intro index componentLanguage hget
      rcases listGet?_map_some hget with
        ⟨model, hmodel, hcomponentEq⟩
      subst hcomponentEq
      exact (h model _).mp
        (hcomponents index (left model)
          (listGet?_map_eq_some hmodel))
  · intro hlanguage
    rcases hlanguage with
      ⟨tagged, herase, hbounded, horder, hcomponents⟩
    refine ⟨tagged, herase, ?_, horder, ?_⟩
    · simpa using hbounded
    · intro index componentLanguage hget
      rcases listGet?_map_some hget with
        ⟨model, hmodel, hcomponentEq⟩
      subst hcomponentEq
      exact (h model _).mpr
        (hcomponents index (right model)
          (listGet?_map_eq_some hmodel))

theorem partialOrderComponentLanguage_congr
    {Activity : Type u}
    (order : Rel Nat)
    {left right : List (Language Activity)}
    (hlength : left.length = right.length)
    (hcomponent :
      ∀ index leftLanguage rightLanguage,
        listGet? left index = some leftLanguage ->
        listGet? right index = some rightLanguage ->
          ∀ word, leftLanguage word ↔ rightLanguage word)
    (word : List Activity) :
    partialOrderComponentLanguage order left word ↔
      partialOrderComponentLanguage order right word := by
  constructor
  · intro hlanguage
    rcases hlanguage with
      ⟨tagged, herase, hbounded, horder, hcomponents⟩
    refine ⟨tagged, herase, ?_, horder, ?_⟩
    · intro taggedItem hmem
      have hbound := hbounded taggedItem hmem
      simpa [← hlength] using hbound
    · intro index rightLanguage hright
      have hltRight := listGet?_some_lt_length hright
      have hltLeft : index < left.length := by
        simpa [hlength] using hltRight
      rcases listGet?_exists_of_lt_length hltLeft with
        ⟨leftLanguage, hleft⟩
      exact
        (hcomponent index leftLanguage rightLanguage hleft hright
          (component index tagged)).mp
          (hcomponents index leftLanguage hleft)
  · intro hlanguage
    rcases hlanguage with
      ⟨tagged, herase, hbounded, horder, hcomponents⟩
    refine ⟨tagged, herase, ?_, horder, ?_⟩
    · intro taggedItem hmem
      have hbound := hbounded taggedItem hmem
      simpa [hlength] using hbound
    · intro index leftLanguage hleft
      have hltLeft := listGet?_some_lt_length hleft
      have hltRight : index < right.length := by
        simpa [← hlength] using hltLeft
      rcases listGet?_exists_of_lt_length hltRight with
        ⟨rightLanguage, hright⟩
      exact
        (hcomponent index leftLanguage rightLanguage hleft hright
          (component index tagged)).mpr
          (hcomponents index rightLanguage hright)

theorem xor_language_iff
    {Transition : Type u}
    {Activity : Type v}
    {label : Transition -> TransitionLabel Activity}
    {models : List (Powl Transition)}
    {word : List Activity} :
    language label (Powl.xor models) word ↔
      ∃ model, model ∈ models ∧ language label model word := by
  constructor
  · intro h
    cases h with
    | xor hmem hsem =>
        exact ⟨_, hmem, hsem⟩
  · intro h
    rcases h with ⟨model, hmem, hsem⟩
    exact Semantics.xor hmem hsem

theorem xor_language_iff_unionList
    {Transition : Type u}
    {Activity : Type v}
    {label : Transition -> TransitionLabel Activity}
    {models : List (Powl Transition)}
    {word : List Activity} :
    language label (Powl.xor models) word ↔
      Language.unionList (models.map (language label)) word := by
  rw [xor_language_iff]
  constructor
  · intro h
    rcases h with ⟨model, hmem, hsemantics⟩
    exact Language.unionList_iff_exists_mem.mpr
      ⟨language label model, List.mem_map.mpr ⟨model, hmem, rfl⟩,
        hsemantics⟩
  · intro h
    rcases Language.unionList_iff_exists_mem.mp h with
      ⟨component, hcomponent, hsemantics⟩
    rcases List.mem_map.mp hcomponent with ⟨model, hmem, hcomponentEq⟩
    subst hcomponentEq
    exact ⟨model, hmem, hsemantics⟩

theorem loop_language_iff_loop
    {Transition : Type u}
    {Activity : Type v}
    {label : Transition -> TransitionLabel Activity}
    {body redo : Powl Transition}
    {word : List Activity} :
    language label (Powl.loop body redo) word ↔
      Language.Loop (language label body) (language label redo) word := by
  constructor
  · intro h
    generalize hmodel : Powl.loop body redo = model at h
    induction h with
    | atomSilent _ =>
        cases hmodel
    | atomVisible _ =>
        cases hmodel
    | xor _ _ _ =>
        cases hmodel
    | loopOnce hbody _ =>
        cases hmodel
        exact Language.Loop.once hbody
    | loopMore hbody hredo _ _ _ ih =>
        cases hmodel
        exact Language.Loop.more hbody hredo (ih rfl)
    | partialOrder _ _ _ _ _ =>
        cases hmodel
  · intro h
    induction h with
    | once hbody =>
        exact Semantics.loopOnce hbody
    | more hbody hredo _ ih =>
        exact Semantics.loopMore hbody hredo ih

theorem loop_language_congr
    {Transition : Type u}
    {Activity : Type v}
    {label : Transition -> TransitionLabel Activity}
    {body redo body' redo' : Powl Transition}
    (hbody :
      ∀ word,
        language label body word ↔ language label body' word)
    (hredo :
      ∀ word,
        language label redo word ↔ language label redo' word)
    (word : List Activity) :
    language label (Powl.loop body redo) word ↔
      language label (Powl.loop body' redo') word :=
  Iff.trans loop_language_iff_loop
    (Iff.trans
      (Language.loop_congr hbody hredo word)
      loop_language_iff_loop.symm)

theorem loop_language_iff_concat_star
    {Transition : Type u}
    {Activity : Type v}
    {label : Transition -> TransitionLabel Activity}
    {body redo : Powl Transition}
    {word : List Activity} :
    language label (Powl.loop body redo) word ↔
      Language.concat (language label body)
        (Language.Star
          (Language.concat (language label redo) (language label body))) word := by
  exact Iff.trans loop_language_iff_loop Language.loop_iff_concat_star

theorem partial_order_language_iff
    {Transition : Type u}
    {Activity : Type v}
    {label : Transition -> TransitionLabel Activity}
    {order : Rel Nat}
    {models : List (Powl Transition)}
    {word : List Activity} :
    language label (Powl.partialOrder order models) word ↔
      partialOrderLanguage label order models word := by
  constructor
  · intro h
    cases h with
    | partialOrder herase hbounded horder hcomponents =>
        exact ⟨_, herase, hbounded, horder, hcomponents⟩
  · intro h
    rcases h with ⟨tagged, herase, hbounded, horder, hcomponents⟩
    exact Semantics.partialOrder herase hbounded horder hcomponents

theorem partial_order_language_iff_componentLanguage
    {Transition : Type u}
    {Activity : Type v}
    {label : Transition -> TransitionLabel Activity}
    {order : Rel Nat}
    {models : List (Powl Transition)}
    {word : List Activity} :
    language label (Powl.partialOrder order models) word ↔
      partialOrderComponentLanguage
        order
        (models.map (language label))
        word :=
  Iff.trans partial_order_language_iff
    partialOrderLanguage_iff_componentLanguage

end Powl

end KouraniWfnetPowl
