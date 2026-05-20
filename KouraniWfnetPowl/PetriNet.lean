import KouraniWfnetPowl.Basic

namespace KouraniWfnetPowl

structure PetriNet (Place : Type u) (Trans : Type v) where
  placeToTrans : Place -> Trans -> Prop
  transToPlace : Trans -> Place -> Prop

namespace PetriNet

variable {Place : Type u} {Trans : Type v}

inductive Node (Place : Type u) (Trans : Type v) where
  | place : Place -> Node Place Trans
  | trans : Trans -> Node Place Trans

namespace Node

def map
    {Place' : Type w}
    {Trans' : Type x}
    (placeMap : Place -> Place')
    (transMap : Trans -> Trans') :
    Node Place Trans -> Node Place' Trans' :=
  fun node =>
    match node with
    | .place p => .place (placeMap p)
    | .trans t => .trans (transMap t)

end Node

def flow (net : PetriNet Place Trans) : Rel (Node Place Trans)
  | Node.place place, Node.trans trans => net.placeToTrans place trans
  | Node.trans trans, Node.place place => net.transToPlace trans place
  | _, _ => False

inductive Path (net : PetriNet Place Trans) :
    Node Place Trans -> Node Place Trans -> Prop where
  | refl {node : Node Place Trans} : Path net node node
  | step {first second third : Node Place Trans} :
      flow net first second ->
      Path net second third ->
      Path net first third

namespace Path

theorem mono
    {left right : PetriNet Place Trans}
    (hflow : ∀ first second, flow left first second -> flow right first second)
    {source target : Node Place Trans}
    (path : Path left source target) :
    Path right source target := by
  induction path with
  | refl =>
      exact Path.refl
  | step hstep _ ih =>
      exact Path.step (hflow _ _ hstep) ih

theorem trans
    {net : PetriNet Place Trans}
    {first second third : Node Place Trans}
    (left : Path net first second)
    (right : Path net second third) :
    Path net first third := by
  induction left generalizing third with
  | refl =>
      exact right
  | step hstep _ ih =>
      exact Path.step hstep (ih right)

theorem snoc
    {net : PetriNet Place Trans}
    {first second third : Node Place Trans}
    (path : Path net first second)
    (hflow : flow net second third) :
    Path net first third :=
  trans path (Path.step hflow Path.refl)

end Path

inductive ReversePath (net : PetriNet Place Trans) :
    Node Place Trans -> Node Place Trans -> Prop where
  | refl {node : Node Place Trans} : ReversePath net node node
  | snoc {first second third : Node Place Trans} :
      ReversePath net first second ->
      flow net second third ->
      ReversePath net first third

namespace ReversePath

theorem cons
    {net : PetriNet Place Trans}
    {first second third : Node Place Trans}
    (hflow : flow net first second)
    (path : ReversePath net second third) :
    ReversePath net first third := by
  induction path with
  | refl =>
      exact ReversePath.snoc ReversePath.refl hflow
  | snoc path hlast ih =>
      exact ReversePath.snoc ih hlast

theorem to_path
    {net : PetriNet Place Trans}
    {first second : Node Place Trans}
    (path : ReversePath net first second) :
    Path net first second := by
  induction path with
  | refl =>
      exact Path.refl
  | snoc path hflow ih =>
      exact Path.snoc ih hflow

theorem of_path
    {net : PetriNet Place Trans}
    {first second : Node Place Trans}
    (path : Path net first second) :
    ReversePath net first second := by
  induction path with
  | refl =>
      exact ReversePath.refl
  | step hflow _ ih =>
      exact ReversePath.cons hflow ih

end ReversePath

def placePreset (net : PetriNet Place Trans) (place : Place) : Set Trans :=
  fun trans => net.transToPlace trans place

def placePostset (net : PetriNet Place Trans) (place : Place) : Set Trans :=
  fun trans => net.placeToTrans place trans

def transPreset (net : PetriNet Place Trans) (trans : Trans) : Set Place :=
  fun place => net.placeToTrans place trans

def transPostset (net : PetriNet Place Trans) (trans : Trans) : Set Place :=
  fun place => net.transToPlace trans place

def placesTouching (net : PetriNet Place Trans) (transitions : Set Trans) :
    Set Place :=
  fun place =>
    ∃ trans, transitions trans ∧
      (net.placeToTrans place trans ∨ net.transToPlace trans place)

theorem placesTouching_of_placeToTrans
    (net : PetriNet Place Trans)
    {transitions : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : transitions trans)
    (hflow : net.placeToTrans place trans) :
    placesTouching net transitions place :=
  ⟨trans, hpart, Or.inl hflow⟩

theorem placesTouching_of_transToPlace
    (net : PetriNet Place Trans)
    {transitions : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : transitions trans)
    (hflow : net.transToPlace trans place) :
    placesTouching net transitions place :=
  ⟨trans, hpart, Or.inr hflow⟩

def projectedFlow
    (net : PetriNet Place Trans)
    (places : Set Place)
    (transitions : Set Trans) :
    PetriNet Place Trans where
  placeToTrans := fun place trans =>
    places place ∧ transitions trans ∧ net.placeToTrans place trans
  transToPlace := fun trans place =>
    transitions trans ∧ places place ∧ net.transToPlace trans place

theorem projectedFlow_placeToTrans_iff
    (net : PetriNet Place Trans)
    (places : Set Place)
    (transitions : Set Trans)
    (place : Place)
    (trans : Trans) :
    (projectedFlow net places transitions).placeToTrans place trans ↔
      places place ∧ transitions trans ∧ net.placeToTrans place trans :=
  Iff.rfl

theorem projectedFlow_transToPlace_iff
    (net : PetriNet Place Trans)
    (places : Set Place)
    (transitions : Set Trans)
    (trans : Trans)
    (place : Place) :
    (projectedFlow net places transitions).transToPlace trans place ↔
      transitions trans ∧ places place ∧ net.transToPlace trans place :=
  Iff.rfl

theorem projectedFlow_flow_original
    (net : PetriNet Place Trans)
    (places : Set Place)
    (transitions : Set Trans)
    {first second : Node Place Trans}
    (hflow : flow (projectedFlow net places transitions) first second) :
    flow net first second := by
  cases first with
  | place place =>
      cases second with
      | place place' =>
          exact hflow
      | trans trans =>
          exact hflow.2.2
  | trans trans =>
      cases second with
      | place place =>
          exact hflow.2.2
      | trans trans' =>
          exact hflow

theorem projectedFlow_path_original
    (net : PetriNet Place Trans)
    (places : Set Place)
    (transitions : Set Trans)
    {source target : Node Place Trans}
    (path : Path (projectedFlow net places transitions) source target) :
    Path net source target :=
  Path.mono
    (fun _ _ hflow =>
      projectedFlow_flow_original net places transitions hflow)
    path

def restrict
    (net : PetriNet Place Trans)
    (places : Set Place)
    (transitions : Set Trans) :
    PetriNet {place : Place // places place} {trans : Trans // transitions trans} where
  placeToTrans := fun place trans => net.placeToTrans place.val trans.val
  transToPlace := fun trans place => net.transToPlace trans.val place.val

def restrictedNode
    {places : Set Place}
    {transitions : Set Trans} :
    Node {place : Place // places place} {trans : Trans // transitions trans} ->
      Node Place Trans :=
  Node.map Subtype.val Subtype.val

theorem restrict_placeToTrans_iff
    (net : PetriNet Place Trans)
    (places : Set Place)
    (transitions : Set Trans)
    (place : {place : Place // places place})
    (trans : {trans : Trans // transitions trans}) :
    (restrict net places transitions).placeToTrans place trans ↔
      net.placeToTrans place.val trans.val :=
  Iff.rfl

theorem restrict_transToPlace_iff
    (net : PetriNet Place Trans)
    (places : Set Place)
    (transitions : Set Trans)
    (trans : {trans : Trans // transitions trans})
    (place : {place : Place // places place}) :
    (restrict net places transitions).transToPlace trans place ↔
      net.transToPlace trans.val place.val :=
  Iff.rfl

theorem restrict_flow_original
    (net : PetriNet Place Trans)
    (places : Set Place)
    (transitions : Set Trans)
    {first second :
      Node {place : Place // places place} {trans : Trans // transitions trans}}
    (hflow : flow (restrict net places transitions) first second) :
    flow net (restrictedNode first) (restrictedNode second) := by
  cases first with
  | place place =>
      cases second with
      | place place' =>
          exact hflow
      | trans trans =>
          simpa [restrictedNode, Node.map, flow, restrict] using hflow
  | trans trans =>
      cases second with
      | place place =>
          simpa [restrictedNode, Node.map, flow, restrict] using hflow
      | trans trans' =>
          exact hflow

theorem restrict_path_original
    (net : PetriNet Place Trans)
    (places : Set Place)
    (transitions : Set Trans)
    {source target :
      Node {place : Place // places place} {trans : Trans // transitions trans}}
    (path : Path (restrict net places transitions) source target) :
    Path net (restrictedNode source) (restrictedNode target) := by
  induction path with
  | refl =>
      exact Path.refl
  | step hstep _ ih =>
      exact Path.step
        (restrict_flow_original net places transitions hstep)
        ih

def nodeIn
    (places : Set Place)
    (transitions : Set Trans) :
    Node Place Trans -> Prop
  | .place place => places place
  | .trans trans => transitions trans

def restrictNode
    {places : Set Place}
    {transitions : Set Trans}
    (node : Node Place Trans)
    (hnode : nodeIn places transitions node) :
    Node {place : Place // places place} {trans : Trans // transitions trans} :=
  match node with
  | .place place => .place ⟨place, hnode⟩
  | .trans trans => .trans ⟨trans, hnode⟩

@[simp] theorem restrictedNode_restrictNode
    {places : Set Place}
    {transitions : Set Trans}
    (node : Node Place Trans)
    (hnode : nodeIn places transitions node) :
    restrictedNode (restrictNode node hnode) = node := by
  cases node <;> rfl

theorem restrictNode_irrel
    {places : Set Place}
    {transitions : Set Trans}
    (node : Node Place Trans)
    (left right : nodeIn places transitions node) :
    restrictNode node left = restrictNode node right := by
  cases node <;> simp [restrictNode]

theorem restrict_flow_of_original
    (net : PetriNet Place Trans)
    (places : Set Place)
    (transitions : Set Trans)
    {first second : Node Place Trans}
    (hflow : flow net first second)
    (hfirst : nodeIn places transitions first)
    (hsecond : nodeIn places transitions second) :
    flow
      (restrict net places transitions)
      (restrictNode first hfirst)
      (restrictNode second hsecond) := by
  cases first <;> cases second <;> exact hflow

inductive PathIn
    (net : PetriNet Place Trans)
    (places : Set Place)
    (transitions : Set Trans) :
    Node Place Trans -> Node Place Trans -> Prop where
  | refl {node : Node Place Trans} :
      nodeIn places transitions node ->
      PathIn net places transitions node node
  | step {first second third : Node Place Trans} :
      nodeIn places transitions first ->
      nodeIn places transitions second ->
      flow net first second ->
      PathIn net places transitions second third ->
      PathIn net places transitions first third

namespace PathIn

theorem source_mem
    {net : PetriNet Place Trans}
    {places : Set Place}
    {transitions : Set Trans}
    {source target : Node Place Trans}
    (path : PathIn net places transitions source target) :
    nodeIn places transitions source := by
  cases path with
  | refl hnode =>
      exact hnode
  | step hfirst _ _ _ =>
      exact hfirst

theorem target_mem
    {net : PetriNet Place Trans}
    {places : Set Place}
    {transitions : Set Trans}
    {source target : Node Place Trans}
    (path : PathIn net places transitions source target) :
    nodeIn places transitions target := by
  induction path with
  | refl hnode =>
      exact hnode
  | step _ _ _ _ ih =>
      exact ih

theorem to_path
    {net : PetriNet Place Trans}
    {places : Set Place}
    {transitions : Set Trans}
    {source target : Node Place Trans}
    (path : PathIn net places transitions source target) :
    Path net source target := by
  induction path with
  | refl _ =>
      exact Path.refl
  | step _ _ hflow _ ih =>
      exact Path.step hflow ih

theorem to_restrict_path
    {net : PetriNet Place Trans}
    {places : Set Place}
    {transitions : Set Trans}
    {source target : Node Place Trans}
    (path : PathIn net places transitions source target) :
    Path
      (restrict net places transitions)
      (restrictNode source (source_mem path))
      (restrictNode target (target_mem path)) := by
  induction path with
  | refl hnode =>
      exact Path.refl
  | step hfirst hsecond hflow rest ih =>
      have htail :
          Path
            (restrict net places transitions)
            (restrictNode _ hsecond)
            (restrictNode _ (target_mem rest)) := by
        simpa [restrictNode_irrel _ hsecond (source_mem rest)] using ih
      exact
        Path.step
          (restrict_flow_of_original net places transitions hflow hfirst hsecond)
          htail

theorem trans
    {net : PetriNet Place Trans}
    {places : Set Place}
    {transitions : Set Trans}
    {first second third : Node Place Trans}
    (left : PathIn net places transitions first second)
    (right : PathIn net places transitions second third) :
    PathIn net places transitions first third := by
  induction left generalizing third with
  | refl _ =>
      exact right
  | step hfirst hsecond hflow _ ih =>
      exact PathIn.step hfirst hsecond hflow (ih right)

theorem snoc
    {net : PetriNet Place Trans}
    {places : Set Place}
    {transitions : Set Trans}
    {first second third : Node Place Trans}
    (path : PathIn net places transitions first second)
    (hsecond : nodeIn places transitions second)
    (hthird : nodeIn places transitions third)
    (hflow : flow net second third) :
    PathIn net places transitions first third :=
  trans path (PathIn.step hsecond hthird hflow (PathIn.refl hthird))

end PathIn

def placeEquivalentWrt
    (net : PetriNet Place Trans)
    (transitions : Set Trans)
    (left right : Place) : Prop :=
  (∀ trans, transitions trans ->
    (net.transToPlace trans left ↔ net.transToPlace trans right)) ∧
  (∀ trans, transitions trans ->
    (net.placeToTrans left trans ↔ net.placeToTrans right trans))

def transitionReachable
    (net : PetriNet Place Trans)
    (source target : Trans) : Prop :=
  Path net (Node.trans source) (Node.trans target)

theorem path_from_place_first_transition_aux
    (net : PetriNet Place Trans)
    {sourceNode target : Node Place Trans}
    {source : Place}
    (path : Path net sourceNode target)
    (hsource : sourceNode = Node.place source) :
    target = Node.place source ∨
      ∃ first,
        net.placeToTrans source first ∧
        Path net (Node.trans first) target := by
  cases path with
  | refl =>
      exact Or.inl hsource
  | step hflow rest =>
      right
      subst hsource
      rename_i second
      cases second with
      | place place =>
          exact False.elim hflow
      | trans trans =>
          exact ⟨trans, hflow, rest⟩

theorem path_from_place_first_transition
    (net : PetriNet Place Trans)
    {source : Place}
    {target : Node Place Trans}
    (path : Path net (Node.place source) target) :
    target = Node.place source ∨
      ∃ first,
        net.placeToTrans source first ∧
        Path net (Node.trans first) target :=
  path_from_place_first_transition_aux net path rfl

theorem path_place_to_transition_first
    (net : PetriNet Place Trans)
    {source : Place}
    {target : Trans}
    (path : Path net (Node.place source) (Node.trans target)) :
    ∃ first,
      net.placeToTrans source first ∧
      transitionReachable net first target := by
  rcases path_from_place_first_transition net path with hsame | hfirst
  · cases hsame
  · exact hfirst

theorem reversePath_to_place_last_transition
    (net : PetriNet Place Trans)
    {source : Node Place Trans}
    {target : Place}
    (path : ReversePath net source (Node.place target)) :
    source = Node.place target ∨
      ∃ last,
        ReversePath net source (Node.trans last) ∧
        net.transToPlace last target := by
  cases path with
  | refl =>
      exact Or.inl rfl
  | snoc path hflow =>
      right
      rename_i second
      cases second with
      | place place =>
          exact False.elim hflow
      | trans trans =>
          exact ⟨trans, path, hflow⟩

theorem path_to_place_last_transition
    (net : PetriNet Place Trans)
    {source : Node Place Trans}
    {target : Place}
    (path : Path net source (Node.place target)) :
    source = Node.place target ∨
      ∃ last,
        Path net source (Node.trans last) ∧
        net.transToPlace last target := by
  rcases reversePath_to_place_last_transition
      net
      (ReversePath.of_path path) with hsame | hlast
  · exact Or.inl hsame
  · right
    rcases hlast with ⟨last, rpath, hflow⟩
    exact ⟨last, ReversePath.to_path rpath, hflow⟩

theorem path_transition_to_place_last
    (net : PetriNet Place Trans)
    {source : Trans}
    {target : Place}
    (path : Path net (Node.trans source) (Node.place target)) :
    ∃ last,
      transitionReachable net source last ∧
      net.transToPlace last target := by
  rcases path_to_place_last_transition net path with hsame | hlast
  · cases hsame
  · exact hlast

theorem uniqueSource_of_connected_no_in
    (net : PetriNet Place Trans)
    (source sink : Place)
    (hsourceNoIn : ∀ trans, ¬ net.transToPlace trans source)
    (hconnected :
      ∀ node : Node Place Trans,
        Path net (Node.place source) node ∧
        Path net node (Node.place sink)) :
    ∀ place,
      (∀ trans, ¬ net.transToPlace trans place) ↔ place = source := by
  intro place
  constructor
  · intro hnoIn
    have hpath : Path net (Node.place source) (Node.place place) :=
      (hconnected (Node.place place)).1
    rcases path_to_place_last_transition net hpath with hsame | hlast
    · cases hsame
      rfl
    · rcases hlast with ⟨last, _path, hlastFlow⟩
      exact False.elim (hnoIn last hlastFlow)
  · intro hplace trans hflow
    rw [hplace] at hflow
    exact hsourceNoIn trans hflow

theorem uniqueSink_of_connected_no_out
    (net : PetriNet Place Trans)
    (source sink : Place)
    (hsinkNoOut : ∀ trans, ¬ net.placeToTrans sink trans)
    (hconnected :
      ∀ node : Node Place Trans,
        Path net (Node.place source) node ∧
        Path net node (Node.place sink)) :
    ∀ place,
      (∀ trans, ¬ net.placeToTrans place trans) ↔ place = sink := by
  intro place
  constructor
  · intro hnoOut
    have hpath : Path net (Node.place place) (Node.place sink) :=
      (hconnected (Node.place place)).2
    rcases path_from_place_first_transition net hpath with hsame | hfirst
    · cases hsame
      rfl
    · rcases hfirst with ⟨first, hfirstFlow, _path⟩
      exact False.elim (hnoOut first hfirstFlow)
  · intro hplace trans hflow
    rw [hplace] at hflow
    exact hsinkNoOut trans hflow

inductive PlacePathTo
    (net : PetriNet Place Trans)
    (target : Place) :
    Place -> List Trans -> Prop where
  | done : PlacePathTo net target target []
  | step {place next : Place} {trans : Trans} {rest : List Trans} :
      place ≠ target ->
      net.placeToTrans place trans ->
      net.transToPlace trans next ->
      PlacePathTo net target next rest ->
      PlacePathTo net target place (trans :: rest)

namespace PlacePathTo

theorem to_path
    {net : PetriNet Place Trans}
    {source target : Place}
    {trace : List Trans}
    (path : PlacePathTo net target source trace) :
    Path net (Node.place source) (Node.place target) := by
  induction path with
  | done =>
      exact Path.refl
  | step _ hplace htrans _ ih =>
      exact
        @Path.step Place Trans net (Node.place _) (Node.trans _) _ hplace
          (@Path.step Place Trans net (Node.trans _) (Node.place _) _ htrans ih)

theorem path_to_member_transition
    {net : PetriNet Place Trans}
    {source target : Place}
    {trace : List Trans}
    {member : Trans}
    (path : PlacePathTo net target source trace)
    (hmem : member ∈ trace) :
    Path net (Node.place source) (Node.trans member) := by
  induction path with
  | done =>
      simp at hmem
  | step _ hplace htrans _ ih =>
      simp at hmem
      rcases hmem with hhead | htail
      · subst hhead
        exact
          @Path.step Place Trans net (Node.place _) (Node.trans _) _ hplace
            Path.refl
      · exact
          @Path.step Place Trans net (Node.place _) (Node.trans _) _ hplace
            (@Path.step Place Trans net (Node.trans _) (Node.place _) _
              htrans
              (ih htail))

theorem member_transition_to_path
    {net : PetriNet Place Trans}
    {source target : Place}
    {trace : List Trans}
    {member : Trans}
    (path : PlacePathTo net target source trace)
    (hmem : member ∈ trace) :
    Path net (Node.trans member) (Node.place target) := by
  induction path with
  | done =>
      simp at hmem
  | step _ _ htrans restPath ih =>
      simp at hmem
      rcases hmem with hhead | htail
      · subst hhead
        exact
          @Path.step Place Trans net (Node.trans _) (Node.place _) _
            htrans
            (to_path restPath)
      · exact ih htail

end PlacePathTo

def reachableTransitionsBetweenPlaces
    (net : PetriNet Place Trans)
    (source target : Place) : Set Trans :=
  fun trans => ∃ trace,
    PlacePathTo net target source trace ∧ trans ∈ trace

theorem reachableTransitionsBetweenPlaces_of_mem_placePath
    (net : PetriNet Place Trans)
    {source target : Place}
    {trace : List Trans}
    {trans : Trans}
    (path : PlacePathTo net target source trace)
    (hmem : trans ∈ trace) :
    reachableTransitionsBetweenPlaces net source target trans :=
  ⟨trace, path, hmem⟩

theorem reachableTransitionsBetweenPlaces_paths
    (net : PetriNet Place Trans)
    {source target : Place}
    {trans : Trans}
    (hreachable : reachableTransitionsBetweenPlaces net source target trans) :
    Path net (Node.place source) (Node.trans trans) ∧
      Path net (Node.trans trans) (Node.place target) := by
  rcases hreachable with ⟨trace, path, hmem⟩
  exact
    ⟨PlacePathTo.path_to_member_transition path hmem,
      PlacePathTo.member_transition_to_path path hmem⟩

end PetriNet

abbrev Marking (Place : Type u) := Place -> Nat

namespace Marking

variable {Place : Type u}

noncomputable def single (marked : Place) : Marking Place := by
  classical
  exact fun place => if place = marked then 1 else 0

def restrict
    {places : Set Place}
    (marking : Marking Place) :
    Marking {place : Place // places place} :=
  fun place => marking place.val

noncomputable def extend
    {places : Set Place}
    (marking : Marking {place : Place // places place}) :
    Marking Place := by
  classical
  exact fun place => if hplace : places place then marking ⟨place, hplace⟩ else 0

@[simp] theorem restrict_apply
    {places : Set Place}
    (marking : Marking Place)
    (place : {place : Place // places place}) :
    restrict marking place = marking place.val :=
  rfl

theorem extend_apply_mem
    {places : Set Place}
    (marking : Marking {place : Place // places place})
    (place : Place)
    (hplace : places place) :
    extend marking place = marking ⟨place, hplace⟩ := by
  simp [extend, hplace]

@[simp] theorem extend_apply_subtype
    {places : Set Place}
    (marking : Marking {place : Place // places place})
    (place : {place : Place // places place}) :
    extend marking place.val = marking place := by
  cases place with
  | mk place hplace =>
      exact extend_apply_mem marking place hplace

theorem extend_apply_of_not_mem
    {places : Set Place}
    (marking : Marking {place : Place // places place})
    (place : Place)
    (hplace : ¬ places place) :
    extend marking place = 0 := by
  simp [extend, hplace]

theorem extend_single
    {places : Set Place}
    (marked : {place : Place // places place}) :
    extend (single marked) = single marked.val := by
  cases marked with
  | mk marked hmarked =>
      funext place
      by_cases hplace : places place
      · by_cases hsame : place = marked
        · subst hsame
          simp [extend, single, hmarked]
        · have hsubne :
              (⟨place, hplace⟩ : {place : Place // places place}) ≠
                ⟨marked, hmarked⟩ := by
            intro h
            exact hsame (congrArg Subtype.val h)
          simp [extend, single, hplace, hsame, hsubne]
      · have hne : place ≠ marked := by
          intro hsame
          subst hsame
          exact hplace hmarked
        simp [extend, single, hplace, hne]

end Marking

structure WorkflowNet (Place : Type u) (Trans : Type v) extends
    PetriNet Place Trans where
  source : Place
  sink : Place
  uniqueSource : ∀ place,
    (∀ trans, ¬ toPetriNet.transToPlace trans place) ↔ place = source
  uniqueSink : ∀ place,
    (∀ trans, ¬ toPetriNet.placeToTrans place trans) ↔ place = sink
  connected : ∀ node : PetriNet.Node Place Trans,
    PetriNet.Path toPetriNet (PetriNet.Node.place source) node ∧
    PetriNet.Path toPetriNet node (PetriNet.Node.place sink)

namespace WorkflowNet

variable {Place : Type u} {Trans : Type v}

def entryPoints (net : WorkflowNet Place Trans) (part : Set Trans) : Set Place :=
  fun place =>
    (∃ trans, part trans ∧ net.placeToTrans place trans) ∧
    (place = net.source ∨ ∃ trans, ¬ part trans ∧ net.transToPlace trans place)

def exitPoints (net : WorkflowNet Place Trans) (part : Set Trans) : Set Place :=
  fun place =>
    (∃ trans, part trans ∧ net.transToPlace trans place) ∧
    (place = net.sink ∨ ∃ trans, ¬ part trans ∧ net.placeToTrans place trans)

def enabled
    (net : WorkflowNet Place Trans)
    (marking : Marking Place)
    (trans : Trans) : Prop :=
  ∀ place, net.placeToTrans place trans -> marking place > 0

noncomputable def consumed
    (net : WorkflowNet Place Trans)
    (trans : Trans)
    (place : Place) : Nat := by
  classical
  exact if net.placeToTrans place trans then 1 else 0

noncomputable def produced
    (net : WorkflowNet Place Trans)
    (trans : Trans)
    (place : Place) : Nat := by
  classical
  exact if net.transToPlace trans place then 1 else 0

noncomputable def fire
    (net : WorkflowNet Place Trans)
    (marking : Marking Place)
    (trans : Trans) : Marking Place :=
  fun place => marking place - consumed net trans place + produced net trans place

def fires
    (net : WorkflowNet Place Trans)
    (before : Marking Place)
    (trans : Trans)
    (after : Marking Place) : Prop :=
  enabled net before trans ∧ after = fire net before trans

inductive FiringSequence
    (net : WorkflowNet Place Trans) :
    Marking Place -> List Trans -> Marking Place -> Prop where
  | nil {marking : Marking Place} :
      FiringSequence net marking [] marking
  | cons {before middle after : Marking Place} {trans : Trans} {trace : List Trans} :
      fires net before trans middle ->
      FiringSequence net middle trace after ->
      FiringSequence net before (trans :: trace) after

def reachable
    (net : WorkflowNet Place Trans)
    (before after : Marking Place) : Prop :=
  ∃ trace, FiringSequence net before trace after

noncomputable def initial [DecidableEq Place]
    (net : WorkflowNet Place Trans) : Marking Place :=
  Marking.single net.source

noncomputable def final [DecidableEq Place]
    (net : WorkflowNet Place Trans) : Marking Place :=
  Marking.single net.sink

def safe [DecidableEq Place] (net : WorkflowNet Place Trans) : Prop :=
  ∀ marking, reachable net (initial net) marking -> ∀ place, marking place ≤ 1

def noDeadTransitions [DecidableEq Place] (net : WorkflowNet Place Trans) : Prop :=
  ∀ trans, ∃ marking, reachable net (initial net) marking ∧ enabled net marking trans

def optionToComplete [DecidableEq Place] (net : WorkflowNet Place Trans) : Prop :=
  ∀ marking, reachable net (initial net) marking -> reachable net marking (final net)

def properCompletion [DecidableEq Place] (net : WorkflowNet Place Trans) : Prop :=
  ∀ marking, reachable net (initial net) marking -> marking net.sink > 0 -> marking = final net

def sound [DecidableEq Place] (net : WorkflowNet Place Trans) : Prop :=
  noDeadTransitions net ∧ optionToComplete net ∧ properCompletion net

def safeAndSound [DecidableEq Place] (net : WorkflowNet Place Trans) : Prop :=
  safe net ∧ sound net

theorem restricted_enabled_lift
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (restricted :
      WorkflowNet {place : Place // places place} {trans : Trans // transitions trans})
    (hplaceToTrans :
      ∀ place trans,
        restricted.placeToTrans place trans ↔
          original.placeToTrans place.val trans.val)
    (hpreset :
      ∀ place trans,
        transitions trans ->
          original.placeToTrans place trans ->
            places place)
    (marking : Marking {place : Place // places place})
    (trans : {trans : Trans // transitions trans})
    (henabled : enabled restricted marking trans) :
    enabled original (Marking.extend marking) trans.val := by
  intro place hflow
  have hplace : places place := hpreset place trans.val trans.property hflow
  rw [Marking.extend_apply_mem marking place hplace]
  exact henabled ⟨place, hplace⟩
    ((hplaceToTrans ⟨place, hplace⟩ trans).mpr hflow)

theorem restricted_consumed_apply_subtype
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (restricted :
      WorkflowNet {place : Place // places place} {trans : Trans // transitions trans})
    (hplaceToTrans :
      ∀ place trans,
        restricted.placeToTrans place trans ↔
          original.placeToTrans place.val trans.val)
    (place : {place : Place // places place})
    (trans : {trans : Trans // transitions trans}) :
    consumed restricted trans place = consumed original trans.val place.val := by
  by_cases hflow : restricted.placeToTrans place trans
  · have horiginal : original.placeToTrans place.val trans.val :=
      (hplaceToTrans place trans).mp hflow
    simp [consumed, hflow, horiginal]
  · have horiginal : ¬ original.placeToTrans place.val trans.val := by
      intro horiginal
      exact hflow ((hplaceToTrans place trans).mpr horiginal)
    simp [consumed, hflow, horiginal]

theorem restricted_produced_apply_subtype
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (restricted :
      WorkflowNet {place : Place // places place} {trans : Trans // transitions trans})
    (htransToPlace :
      ∀ trans place,
        restricted.transToPlace trans place ↔
          original.transToPlace trans.val place.val)
    (place : {place : Place // places place})
    (trans : {trans : Trans // transitions trans}) :
    produced restricted trans place = produced original trans.val place.val := by
  by_cases hflow : restricted.transToPlace trans place
  · have horiginal : original.transToPlace trans.val place.val :=
      (htransToPlace trans place).mp hflow
    simp [produced, hflow, horiginal]
  · have horiginal : ¬ original.transToPlace trans.val place.val := by
      intro horiginal
      exact hflow ((htransToPlace trans place).mpr horiginal)
    simp [produced, hflow, horiginal]

theorem restricted_consumed_apply_not_mem
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (hpreset :
      ∀ place trans,
        transitions trans ->
          original.placeToTrans place trans ->
            places place)
    (place : Place)
    (hplace : ¬ places place)
    (trans : {trans : Trans // transitions trans}) :
    consumed original trans.val place = 0 := by
  have hnoFlow : ¬ original.placeToTrans place trans.val := by
    intro hflow
    exact hplace (hpreset place trans.val trans.property hflow)
  simp [consumed, hnoFlow]

theorem restricted_produced_apply_not_mem
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (hpostset :
      ∀ trans place,
        transitions trans ->
          original.transToPlace trans place ->
            places place)
    (place : Place)
    (hplace : ¬ places place)
    (trans : {trans : Trans // transitions trans}) :
    produced original trans.val place = 0 := by
  have hnoFlow : ¬ original.transToPlace trans.val place := by
    intro hflow
    exact hplace (hpostset trans.val place trans.property hflow)
  simp [produced, hnoFlow]

theorem restricted_fire_lift
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
    (marking : Marking {place : Place // places place})
    (trans : {trans : Trans // transitions trans}) :
    fire original (Marking.extend marking) trans.val =
      Marking.extend (fire restricted marking trans) := by
  funext place
  by_cases hplace : places place
  · simp [fire, Marking.extend_apply_mem, hplace,
      ← restricted_consumed_apply_subtype
        original restricted hplaceToTrans ⟨place, hplace⟩ trans,
      ← restricted_produced_apply_subtype
        original restricted htransToPlace ⟨place, hplace⟩ trans]
  · simp [fire, Marking.extend_apply_of_not_mem, hplace,
      restricted_consumed_apply_not_mem original hpreset place hplace trans,
      restricted_produced_apply_not_mem original hpostset place hplace trans]

theorem restricted_fires_lift
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
    {before after : Marking {place : Place // places place}}
    {trans : {trans : Trans // transitions trans}}
    (hfires : fires restricted before trans after) :
    fires original (Marking.extend before) trans.val (Marking.extend after) := by
  constructor
  · exact restricted_enabled_lift
      original restricted hplaceToTrans hpreset before trans hfires.1
  · rw [hfires.2]
    exact (restricted_fire_lift
      original restricted hplaceToTrans htransToPlace
      hpreset hpostset before trans).symm

theorem restricted_firingSequence_lift
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
    {before after : Marking {place : Place // places place}}
    {trace : List {trans : Trans // transitions trans}}
    (sequence : FiringSequence restricted before trace after) :
    FiringSequence
      original
      (Marking.extend before)
      (trace.map Subtype.val)
      (Marking.extend after) := by
  induction sequence with
  | nil =>
      exact FiringSequence.nil
  | cons hfires _ ih =>
      exact FiringSequence.cons
        (restricted_fires_lift
          original restricted hplaceToTrans htransToPlace
          hpreset hpostset hfires)
        ih

theorem restricted_enabled_restrict
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (restricted :
      WorkflowNet {place : Place // places place} {trans : Trans // transitions trans})
    (hplaceToTrans :
      ∀ place trans,
        restricted.placeToTrans place trans ↔
          original.placeToTrans place.val trans.val)
    (marking : Marking Place)
    (trans : {trans : Trans // transitions trans})
    (henabled : enabled original marking trans.val) :
    enabled restricted (Marking.restrict marking) trans := by
  intro place hflow
  exact henabled place.val ((hplaceToTrans place trans).mp hflow)

theorem restricted_fire_restrict
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
    (marking : Marking Place)
    (trans : {trans : Trans // transitions trans}) :
    Marking.restrict (fire original marking trans.val) =
      fire restricted (Marking.restrict marking) trans := by
  funext place
  simp [fire, Marking.restrict,
    restricted_consumed_apply_subtype original restricted hplaceToTrans place trans,
    restricted_produced_apply_subtype original restricted htransToPlace place trans]

theorem restricted_fires_restrict
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
    {before after : Marking Place}
    {trans : {trans : Trans // transitions trans}}
    (hfires : fires original before trans.val after) :
    fires restricted
      (Marking.restrict before)
      trans
      (Marking.restrict after) := by
  constructor
  · exact restricted_enabled_restrict
      original restricted hplaceToTrans before trans hfires.1
  · rw [hfires.2]
    exact restricted_fire_restrict
      original restricted hplaceToTrans htransToPlace before trans

theorem restricted_firingSequence_restrict
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
    {before after : Marking Place}
    {trace : List {trans : Trans // transitions trans}}
    (sequence :
      FiringSequence original before (trace.map Subtype.val) after) :
    FiringSequence
      restricted
      (Marking.restrict before)
      trace
      (Marking.restrict after) := by
  induction trace generalizing before with
  | nil =>
      cases sequence with
      | nil =>
          exact FiringSequence.nil
  | cons trans rest ih =>
      cases sequence with
      | cons hfires tail =>
          exact FiringSequence.cons
            (restricted_fires_restrict
              original restricted hplaceToTrans htransToPlace hfires)
            (ih tail)

theorem restricted_reachable_lift
    [DecidableEq Place]
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (restricted :
      WorkflowNet {place : Place // places place} {trans : Trans // transitions trans})
    (hsource : restricted.source.val = original.source)
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
    {marking : Marking {place : Place // places place}}
    (hreachable : reachable restricted (initial restricted) marking) :
    reachable original (initial original) (Marking.extend marking) := by
  rcases hreachable with ⟨trace, sequence⟩
  refine ⟨trace.map Subtype.val, ?_⟩
  have lifted :=
    restricted_firingSequence_lift
      original restricted hplaceToTrans htransToPlace
      hpreset hpostset sequence
  simpa [initial, Marking.extend_single, hsource] using lifted

theorem restricted_safe_of_original_safe
    [DecidableEq Place]
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (restricted :
      WorkflowNet {place : Place // places place} {trans : Trans // transitions trans})
    (hsource : restricted.source.val = original.source)
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
    (horiginalSafe : safe original) :
    safe restricted := by
  intro marking hreachable place
  have liftedReachable :
      reachable original (initial original) (Marking.extend marking) :=
    restricted_reachable_lift
      original restricted hsource hplaceToTrans htransToPlace
      hpreset hpostset hreachable
  have hsafe := horiginalSafe (Marking.extend marking) liftedReachable place.val
  simpa using hsafe

end WorkflowNet

end KouraniWfnetPowl
