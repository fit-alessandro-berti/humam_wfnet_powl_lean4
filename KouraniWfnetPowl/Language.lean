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

def concat (left right : Language alpha) : Language alpha :=
  fun word => ∃ leftWord rightWord,
    left leftWord ∧ right rightWord ∧ word = leftWord ++ rightWord

inductive Star (language : Language alpha) : Language alpha where
  | nil : Star language []
  | cons {head tail : List alpha} :
      language head -> Star language tail -> Star language (head ++ tail)

inductive Loop (body redo : Language alpha) : Language alpha where
  | once {bodyWord : List alpha} :
      body bodyWord -> Loop body redo bodyWord
  | more {bodyWord redoWord rest : List alpha} :
      body bodyWord ->
      redo redoWord ->
      Loop body redo rest ->
      Loop body redo (bodyWord ++ redoWord ++ rest)

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
