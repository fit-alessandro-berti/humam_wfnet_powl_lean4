import KouraniWfnetPowl.Basic

namespace KouraniWfnetPowl

abbrev Language (alpha : Type u) := List alpha -> Prop

namespace Language

def empty : Language alpha := fun _ => False

def epsilon : Language alpha := fun word => word = []

def word (target : List alpha) : Language alpha := fun word => word = target

def union (left right : Language alpha) : Language alpha :=
  fun word => left word ∨ right word

def unionList : List (Language alpha) -> Language alpha
  | [] => empty
  | language :: rest => fun word => language word ∨ unionList rest word

theorem unionList_iff_exists_mem
    {languages : List (Language alpha)}
    {word : List alpha} :
    unionList languages word ↔
      ∃ language, language ∈ languages ∧ language word := by
  induction languages with
  | nil =>
      constructor
      · intro h
        exact False.elim h
      · intro h
        rcases h with ⟨_, hmem, _⟩
        cases hmem
  | cons language rest ih =>
      constructor
      · intro h
        cases h with
        | inl hword =>
            exact ⟨language, List.Mem.head _, hword⟩
        | inr hrest =>
            rcases ih.mp hrest with ⟨member, hmem, hword⟩
            exact ⟨member, List.Mem.tail language hmem, hword⟩
      · intro h
        rcases h with ⟨member, hmem, hword⟩
        cases hmem with
        | head =>
            exact Or.inl hword
        | tail _ htail =>
            exact Or.inr (ih.mpr ⟨member, htail, hword⟩)

theorem unionList_map_congr
    {beta : Type v}
    (items : List beta)
    (left right : beta -> Language alpha)
    (h : ∀ item word, left item word ↔ right item word)
    (word : List alpha) :
    unionList (items.map left) word ↔
      unionList (items.map right) word := by
  induction items with
  | nil =>
      rfl
  | cons item rest ih =>
      constructor
      · intro hunion
        cases hunion with
        | inl hleft =>
            exact Or.inl ((h item word).mp hleft)
        | inr hrest =>
            exact Or.inr (ih.mp hrest)
      · intro hunion
        cases hunion with
        | inl hright =>
            exact Or.inl ((h item word).mpr hright)
        | inr hrest =>
            exact Or.inr (ih.mpr hrest)

def concat (left right : Language alpha) : Language alpha :=
  fun word => ∃ leftWord rightWord,
    left leftWord ∧ right rightWord ∧ word = leftWord ++ rightWord

theorem concat_congr
    {left right left' right' : Language alpha}
    (hleft : ∀ word, left word ↔ left' word)
    (hright : ∀ word, right word ↔ right' word)
    (word : List alpha) :
    concat left right word ↔ concat left' right' word := by
  constructor
  · intro h
    rcases h with ⟨leftWord, rightWord, hleftWord, hrightWord, hword⟩
    exact
      ⟨leftWord, rightWord,
        (hleft leftWord).mp hleftWord,
        (hright rightWord).mp hrightWord,
        hword⟩
  · intro h
    rcases h with ⟨leftWord, rightWord, hleftWord, hrightWord, hword⟩
    exact
      ⟨leftWord, rightWord,
        (hleft leftWord).mpr hleftWord,
        (hright rightWord).mpr hrightWord,
        hword⟩

inductive Star (language : Language alpha) : Language alpha where
  | nil : Star language []
  | cons {head tail : List alpha} :
      language head -> Star language tail -> Star language (head ++ tail)

theorem star_mono
    {left right : Language alpha}
    (h : ∀ word, left word -> right word)
    {word : List alpha}
    (hstar : Star left word) :
    Star right word := by
  induction hstar with
  | nil =>
      exact Star.nil
  | cons hhead _ ih =>
      exact Star.cons (h _ hhead) ih

theorem star_congr
    {left right : Language alpha}
    (h : ∀ word, left word ↔ right word)
    (word : List alpha) :
    Star left word ↔ Star right word := by
  constructor
  · exact star_mono (fun item hitem => (h item).mp hitem)
  · exact star_mono (fun item hitem => (h item).mpr hitem)

inductive Loop (body redo : Language alpha) : Language alpha where
  | once {bodyWord : List alpha} :
      body bodyWord -> Loop body redo bodyWord
  | more {bodyWord redoWord rest : List alpha} :
      body bodyWord ->
      redo redoWord ->
      Loop body redo rest ->
      Loop body redo (bodyWord ++ redoWord ++ rest)

theorem loop_congr
    {body redo body' redo' : Language alpha}
    (hbody : ∀ word, body word ↔ body' word)
    (hredo : ∀ word, redo word ↔ redo' word)
    (word : List alpha) :
    Loop body redo word ↔ Loop body' redo' word := by
  constructor
  · intro hloop
    induction hloop with
    | once hbodyWord =>
        exact Loop.once ((hbody _).mp hbodyWord)
    | more hbodyWord hredoWord _ ih =>
        exact
          Loop.more
            ((hbody _).mp hbodyWord)
            ((hredo _).mp hredoWord)
            ih
  · intro hloop
    induction hloop with
    | once hbodyWord =>
        exact Loop.once ((hbody _).mpr hbodyWord)
    | more hbodyWord hredoWord _ ih =>
        exact
          Loop.more
            ((hbody _).mpr hbodyWord)
            ((hredo _).mpr hredoWord)
            ih

theorem loop_to_concat_star
    {body redo : Language alpha} {word : List alpha}
    (h : Loop body redo word) :
    concat body (Star (concat redo body)) word := by
  induction h with
  | once hbody =>
      exact ⟨_, [], hbody, Star.nil, by simp⟩
  | more hbody hredo _ ih =>
      rename_i bodyWord redoWord rest
      rcases ih with ⟨nextBody, tail, hnextBody, htail, hrest⟩
      refine ⟨_, bodyWord ++ nextBody ++ tail, hbody, ?_, ?_⟩
      · exact Star.cons (head := bodyWord ++ nextBody) (tail := tail)
          ⟨bodyWord, nextBody, hredo, hnextBody, rfl⟩ htail
      · rw [hrest]
        simp [List.append_assoc]

theorem concat_star_to_loop
    {body redo : Language alpha} {word : List alpha}
    (h : concat body (Star (concat redo body)) word) :
    Loop body redo word := by
  rcases h with ⟨bodyWord, tail, hbody, htail, hword⟩
  rw [hword]
  clear hword word
  induction htail generalizing bodyWord with
  | nil =>
      simpa using Loop.once (body := body) (redo := redo) hbody
  | cons hhead htail ih =>
      rcases hhead with ⟨redoWord, nextBody, hredo, hnextBody, hheadEq⟩
      rw [hheadEq]
      simpa [List.append_assoc] using
        Loop.more hbody hredo (ih nextBody hnextBody)

theorem loop_iff_concat_star
    {body redo : Language alpha} {word : List alpha} :
    Loop body redo word ↔ concat body (Star (concat redo body)) word := by
  constructor
  · exact loop_to_concat_star
  · exact concat_star_to_loop

end Language

end KouraniWfnetPowl
