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

end Powl

end KouraniWfnetPowl
