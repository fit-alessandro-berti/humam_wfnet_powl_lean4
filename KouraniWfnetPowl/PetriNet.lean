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

def markedGraph (net : PetriNet Place Trans) : Prop :=
  (∀ place left right,
    net.transToPlace left place ->
      net.transToPlace right place ->
        left = right) ∧
    ∀ place left right,
      net.placeToTrans place left ->
        net.placeToTrans place right ->
          left = right

def freeChoice (net : PetriNet Place Trans) : Prop :=
  ∀ place left right,
    net.placeToTrans place left ->
      net.placeToTrans place right ->
        ∀ other,
          net.placeToTrans other left ↔
            net.placeToTrans other right

theorem markedGraph_placePreset_subsingleton
    {net : PetriNet Place Trans}
    (hmarked : markedGraph net)
    (place : Place) :
    ∀ left right,
      net.transToPlace left place ->
        net.transToPlace right place ->
          left = right :=
  hmarked.1 place

theorem markedGraph_placePostset_subsingleton
    {net : PetriNet Place Trans}
    (hmarked : markedGraph net)
    (place : Place) :
    ∀ left right,
      net.placeToTrans place left ->
        net.placeToTrans place right ->
          left = right :=
  hmarked.2 place

theorem freeChoice_transPreset_iff_of_common_source
    {net : PetriNet Place Trans}
    (hfree : freeChoice net)
    {place : Place}
    {left right : Trans}
    (hleft : net.placeToTrans place left)
    (hright : net.placeToTrans place right)
    (other : Place) :
    net.placeToTrans other left ↔
      net.placeToTrans other right :=
  hfree place left right hleft hright other

theorem freeChoice_transPreset_eq_of_common_source
    {net : PetriNet Place Trans}
    (hfree : freeChoice net)
    {place : Place}
    {left right : Trans}
    (hleft : net.placeToTrans place left)
    (hright : net.placeToTrans place right) :
    transPreset net left = transPreset net right :=
  Set.ext
    (fun other =>
      freeChoice_transPreset_iff_of_common_source
        hfree hleft hright other)

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

theorem path_from_transition_first_place_aux
    (net : PetriNet Place Trans)
    {sourceNode target : Node Place Trans}
    {source : Trans}
    (path : Path net sourceNode target)
    (hsource : sourceNode = Node.trans source) :
    target = Node.trans source ∨
      ∃ first,
        net.transToPlace source first ∧
        Path net (Node.place first) target := by
  cases path with
  | refl =>
      exact Or.inl hsource
  | step hflow rest =>
      right
      subst hsource
      rename_i second
      cases second with
      | place place =>
          exact ⟨place, hflow, rest⟩
      | trans trans =>
          exact False.elim hflow

theorem path_from_transition_first_place
    (net : PetriNet Place Trans)
    {source : Trans}
    {target : Node Place Trans}
    (path : Path net (Node.trans source) target) :
    target = Node.trans source ∨
      ∃ first,
        net.transToPlace source first ∧
        Path net (Node.place first) target :=
  path_from_transition_first_place_aux net path rfl

theorem path_transition_to_place_first
    (net : PetriNet Place Trans)
    {source : Trans}
    {target : Place}
    (path : Path net (Node.trans source) (Node.place target)) :
    ∃ first,
      net.transToPlace source first ∧
      Path net (Node.place first) (Node.place target) := by
  rcases path_from_transition_first_place net path with hsame | hfirst
  · cases hsame
  · exact hfirst

theorem reversePath_to_transition_last_place
    (net : PetriNet Place Trans)
    {source : Node Place Trans}
    {target : Trans}
    (path : ReversePath net source (Node.trans target)) :
    source = Node.trans target ∨
      ∃ last,
        ReversePath net source (Node.place last) ∧
        net.placeToTrans last target := by
  cases path with
  | refl =>
      exact Or.inl rfl
  | snoc path hflow =>
      right
      rename_i second
      cases second with
      | place place =>
          exact ⟨place, path, hflow⟩
      | trans trans =>
          exact False.elim hflow

theorem path_to_transition_last_place
    (net : PetriNet Place Trans)
    {source : Node Place Trans}
    {target : Trans}
    (path : Path net source (Node.trans target)) :
    source = Node.trans target ∨
      ∃ last,
        Path net source (Node.place last) ∧
        net.placeToTrans last target := by
  rcases reversePath_to_transition_last_place
      net
      (ReversePath.of_path path) with hsame | hlast
  · exact Or.inl hsame
  · right
    rcases hlast with ⟨last, rpath, hflow⟩
    exact ⟨last, ReversePath.to_path rpath, hflow⟩

theorem path_place_to_transition_last
    (net : PetriNet Place Trans)
    {source : Place}
    {target : Trans}
    (path : Path net (Node.place source) (Node.trans target)) :
    ∃ last,
      Path net (Node.place source) (Node.place last) ∧
      net.placeToTrans last target := by
  rcases path_to_transition_last_place net path with hsame | hlast
  · cases hsame
  · exact hlast

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

inductive NormalizedPlace (Place : Type u) where
  | source : NormalizedPlace Place
  | original : Place -> NormalizedPlace Place
  | sink : NormalizedPlace Place
  deriving DecidableEq

inductive NormalizedTrans (Trans : Type u) where
  | enter : NormalizedTrans Trans
  | original : Trans -> NormalizedTrans Trans
  | exit : NormalizedTrans Trans
  deriving DecidableEq

def normalize
    (net : PetriNet Place Trans)
    (source sink : Place) :
    PetriNet (NormalizedPlace Place) (NormalizedTrans Trans) where
  placeToTrans := fun place trans =>
    match place, trans with
    | NormalizedPlace.source, NormalizedTrans.enter => True
    | NormalizedPlace.original place, NormalizedTrans.original trans =>
        net.placeToTrans place trans
    | NormalizedPlace.original place, NormalizedTrans.exit =>
        place = sink
    | _, _ => False
  transToPlace := fun trans place =>
    match trans, place with
    | NormalizedTrans.enter, NormalizedPlace.original place =>
        place = source
    | NormalizedTrans.original trans, NormalizedPlace.original place =>
        net.transToPlace trans place
    | NormalizedTrans.exit, NormalizedPlace.sink => True
    | _, _ => False

def normalizedNode :
    Node Place Trans ->
      Node (NormalizedPlace Place) (NormalizedTrans Trans)
  | Node.place place => Node.place (NormalizedPlace.original place)
  | Node.trans trans => Node.trans (NormalizedTrans.original trans)

theorem normalize_flow_original
    (net : PetriNet Place Trans)
    (source sink : Place)
    {first second : Node Place Trans}
    (hflow : flow net first second) :
    flow (normalize net source sink)
      (normalizedNode first)
      (normalizedNode second) := by
  cases first <;> cases second <;>
    simp [flow, normalize, normalizedNode] at hflow ⊢
  all_goals exact hflow

theorem normalize_path_original
    (net : PetriNet Place Trans)
    (source sink : Place)
    {first second : Node Place Trans}
    (path : Path net first second) :
    Path (normalize net source sink)
      (normalizedNode first)
      (normalizedNode second) := by
  induction path with
  | refl =>
      exact Path.refl
  | step hflow _ ih =>
      exact
        Path.step
          (normalize_flow_original net source sink hflow)
          ih

theorem normalize_source_to_enter
    (net : PetriNet Place Trans)
    (source sink : Place) :
    Path (normalize net source sink)
      (Node.place (NormalizedPlace.source : NormalizedPlace Place))
      (Node.trans (NormalizedTrans.enter : NormalizedTrans Trans)) :=
  Path.step (by simp [flow, normalize]) Path.refl

theorem normalize_enter_to_original_source
    (net : PetriNet Place Trans)
    (source sink : Place) :
    Path (normalize net source sink)
      (Node.trans (NormalizedTrans.enter : NormalizedTrans Trans))
      (Node.place (NormalizedPlace.original source)) :=
  Path.step (by simp [flow, normalize]) Path.refl

theorem normalize_source_to_original_source
    (net : PetriNet Place Trans)
    (source sink : Place) :
    Path (normalize net source sink)
      (Node.place (NormalizedPlace.source : NormalizedPlace Place))
      (Node.place (NormalizedPlace.original source)) :=
  Path.trans
    (normalize_source_to_enter net source sink)
    (normalize_enter_to_original_source net source sink)

theorem normalize_original_sink_to_exit
    (net : PetriNet Place Trans)
    (source sink : Place) :
    Path (normalize net source sink)
      (Node.place (NormalizedPlace.original sink))
      (Node.trans (NormalizedTrans.exit : NormalizedTrans Trans)) :=
  Path.step (by simp [flow, normalize]) Path.refl

theorem normalize_exit_to_sink
    (net : PetriNet Place Trans)
    (source sink : Place) :
    Path (normalize net source sink)
      (Node.trans (NormalizedTrans.exit : NormalizedTrans Trans))
      (Node.place (NormalizedPlace.sink : NormalizedPlace Place)) :=
  Path.step (by simp [flow, normalize]) Path.refl

theorem normalize_original_sink_to_sink
    (net : PetriNet Place Trans)
    (source sink : Place) :
    Path (normalize net source sink)
      (Node.place (NormalizedPlace.original sink))
      (Node.place (NormalizedPlace.sink : NormalizedPlace Place)) :=
  Path.trans
    (normalize_original_sink_to_exit net source sink)
    (normalize_exit_to_sink net source sink)

theorem normalize_source_to_sink
    (net : PetriNet Place Trans)
    (source sink : Place)
    (path : Path net (Node.place source) (Node.place sink)) :
    Path (normalize net source sink)
      (Node.place (NormalizedPlace.source : NormalizedPlace Place))
      (Node.place (NormalizedPlace.sink : NormalizedPlace Place)) :=
  Path.trans
    (normalize_source_to_original_source net source sink)
    (Path.trans
      (normalize_path_original net source sink path)
      (normalize_original_sink_to_sink net source sink))

theorem normalize_connected
    (net : PetriNet Place Trans)
    (source sink : Place)
    (hconnected :
      ∀ node : Node Place Trans,
        Path net (Node.place source) node ∧
        Path net node (Node.place sink)) :
    ∀ node : Node (NormalizedPlace Place) (NormalizedTrans Trans),
      Path (normalize net source sink)
        (Node.place (NormalizedPlace.source : NormalizedPlace Place))
        node ∧
      Path (normalize net source sink)
        node
        (Node.place (NormalizedPlace.sink : NormalizedPlace Place)) := by
  intro node
  cases node with
  | place place =>
      cases place with
      | source =>
          exact
            ⟨Path.refl,
              normalize_source_to_sink
                net source sink (hconnected (Node.place source)).2⟩
      | original place =>
          exact
            ⟨Path.trans
                (normalize_source_to_original_source net source sink)
                (normalize_path_original
                  net source sink (hconnected (Node.place place)).1),
              Path.trans
                (normalize_path_original
                  net source sink (hconnected (Node.place place)).2)
                (normalize_original_sink_to_sink net source sink)⟩
      | sink =>
          exact
            ⟨normalize_source_to_sink
                net source sink (hconnected (Node.place source)).2,
              Path.refl⟩
  | trans trans =>
      cases trans with
      | enter =>
          exact
            ⟨normalize_source_to_enter net source sink,
              Path.trans
                (normalize_enter_to_original_source net source sink)
                (Path.trans
                  (normalize_path_original
                    net source sink (hconnected (Node.place source)).2)
                  (normalize_original_sink_to_sink net source sink))⟩
      | original trans =>
          exact
            ⟨Path.trans
                (normalize_source_to_original_source net source sink)
                (normalize_path_original
                  net source sink (hconnected (Node.trans trans)).1),
              Path.trans
                (normalize_path_original
                  net source sink (hconnected (Node.trans trans)).2)
                (normalize_original_sink_to_sink net source sink)⟩
      | exit =>
          exact
            ⟨Path.trans
                (normalize_source_to_original_source net source sink)
                (Path.trans
                  (normalize_path_original
                    net source sink (hconnected (Node.place sink)).1)
                  (normalize_original_sink_to_exit net source sink)),
              normalize_exit_to_sink net source sink⟩

theorem normalize_source_no_input
    (net : PetriNet Place Trans)
    (source sink : Place)
    (trans : NormalizedTrans Trans) :
    ¬ (normalize net source sink).transToPlace
      trans
      (NormalizedPlace.source : NormalizedPlace Place) := by
  cases trans <;> simp [normalize]

theorem normalize_sink_no_output
    (net : PetriNet Place Trans)
    (source sink : Place)
    (trans : NormalizedTrans Trans) :
    ¬ (normalize net source sink).placeToTrans
      (NormalizedPlace.sink : NormalizedPlace Place)
      trans := by
  cases trans <;> simp [normalize]

end PetriNet

abbrev Marking (Place : Type u) := Place -> Nat

namespace Marking

variable {Place : Type u}

noncomputable def single (marked : Place) : Marking Place := by
  classical
  exact fun place => if place = marked then 1 else 0

def normalize
    (marking : Marking Place) :
    Marking (PetriNet.NormalizedPlace Place)
  | PetriNet.NormalizedPlace.source => 0
  | PetriNet.NormalizedPlace.original place => marking place
  | PetriNet.NormalizedPlace.sink => 0

theorem normalize_original_apply
    (marking : Marking Place)
    (place : Place) :
    normalize marking (PetriNet.NormalizedPlace.original place) =
      marking place :=
  rfl

theorem normalize_source_apply
    (marking : Marking Place) :
    normalize marking (PetriNet.NormalizedPlace.source :
      PetriNet.NormalizedPlace Place) = 0 :=
  rfl

theorem normalize_sink_apply
    (marking : Marking Place) :
    normalize marking (PetriNet.NormalizedPlace.sink :
      PetriNet.NormalizedPlace Place) = 0 :=
  rfl

theorem normalize_injective
    {left right : Marking Place}
    (hmarking : normalize left = normalize right) :
    left = right := by
  funext place
  have happly :=
    congrFun hmarking (PetriNet.NormalizedPlace.original place)
  exact happly

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

theorem restrict_single
    {places : Set Place}
    (marked : {place : Place // places place}) :
    restrict (single marked.val) = single marked := by
  funext place
  by_cases hsame : place.val = marked.val
  · have hsub : place = marked := by
      exact Subtype.ext hsame
    subst hsub
    simp [restrict, single]
  · have hsub : place ≠ marked := by
      intro h
      exact hsame (congrArg Subtype.val h)
    simp [restrict, single, hsame, hsub]

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

def ofConnectedNoBoundaryEdges
    (net : PetriNet Place Trans)
    (source sink : Place)
    (hsourceNoIn : ∀ trans, ¬ net.transToPlace trans source)
    (hsinkNoOut : ∀ trans, ¬ net.placeToTrans sink trans)
    (hconnected :
      ∀ node : PetriNet.Node Place Trans,
        PetriNet.Path net (PetriNet.Node.place source) node ∧
        PetriNet.Path net node (PetriNet.Node.place sink)) :
    WorkflowNet Place Trans where
  toPetriNet := net
  source := source
  sink := sink
  uniqueSource :=
    PetriNet.uniqueSource_of_connected_no_in
      net source sink hsourceNoIn hconnected
  uniqueSink :=
    PetriNet.uniqueSink_of_connected_no_out
      net source sink hsinkNoOut hconnected
  connected := hconnected

def entryPoints (net : WorkflowNet Place Trans) (part : Set Trans) : Set Place :=
  fun place =>
    (∃ trans, part trans ∧ net.placeToTrans place trans) ∧
    (place = net.source ∨ ∃ trans, ¬ part trans ∧ net.transToPlace trans place)

def exitPoints (net : WorkflowNet Place Trans) (part : Set Trans) : Set Place :=
  fun place =>
    (∃ trans, part trans ∧ net.transToPlace trans place) ∧
    (place = net.sink ∨ ∃ trans, ¬ part trans ∧ net.placeToTrans place trans)

def uniquePresetOfTransition
    (net : WorkflowNet Place Trans)
    (trans : Trans) : Prop :=
  ∃ place,
    net.placeToTrans place trans ∧
      ∀ other, net.placeToTrans other trans -> other = place

def uniquePostsetOfPlace
    (net : WorkflowNet Place Trans)
    (place : Place) : Prop :=
  ∃ trans,
    net.placeToTrans place trans ∧
      ∀ other, net.placeToTrans place other -> other = trans

def uniquePresetOfPlace
    (net : WorkflowNet Place Trans)
    (place : Place) : Prop :=
  ∃ trans,
    net.transToPlace trans place ∧
      ∀ other, net.transToPlace other place -> other = trans

def uniquePostsetOfTransition
    (net : WorkflowNet Place Trans)
    (trans : Trans) : Prop :=
  ∃ place,
    net.transToPlace trans place ∧
      ∀ other, net.transToPlace trans other -> other = place

theorem uniquePresetOfTransition_placeToTrans_iff
    {net : WorkflowNet Place Trans}
    {place : Place}
    {trans : Trans}
    (hunique : uniquePresetOfTransition net trans)
    (hflow : net.placeToTrans place trans)
    (other : Place) :
    net.placeToTrans other trans ↔ other = place := by
  rcases hunique with ⟨only, _honlyFlow, honly⟩
  have hplace : place = only := honly place hflow
  constructor
  · intro hother
    exact (honly other hother).trans hplace.symm
  · intro hother
    rw [hother]
    exact hflow

theorem uniquePostsetOfPlace_placeToTrans_iff
    {net : WorkflowNet Place Trans}
    {place : Place}
    {trans : Trans}
    (hunique : uniquePostsetOfPlace net place)
    (hflow : net.placeToTrans place trans)
    (other : Trans) :
    net.placeToTrans place other ↔ other = trans := by
  rcases hunique with ⟨only, _honlyFlow, honly⟩
  have htrans : trans = only := honly trans hflow
  constructor
  · intro hother
    exact (honly other hother).trans htrans.symm
  · intro hother
    rw [hother]
    exact hflow

theorem uniquePresetOfPlace_transToPlace_iff
    {net : WorkflowNet Place Trans}
    {place : Place}
    {trans : Trans}
    (hunique : uniquePresetOfPlace net place)
    (hflow : net.transToPlace trans place)
    (other : Trans) :
    net.transToPlace other place ↔ other = trans := by
  rcases hunique with ⟨only, _honlyFlow, honly⟩
  have htrans : trans = only := honly trans hflow
  constructor
  · intro hother
    exact (honly other hother).trans htrans.symm
  · intro hother
    rw [hother]
    exact hflow

theorem uniquePostsetOfTransition_transToPlace_iff
    {net : WorkflowNet Place Trans}
    {place : Place}
    {trans : Trans}
    (hunique : uniquePostsetOfTransition net trans)
    (hflow : net.transToPlace trans place)
    (other : Place) :
    net.transToPlace trans other ↔ other = place := by
  rcases hunique with ⟨only, _honlyFlow, honly⟩
  have hplace : place = only := honly place hflow
  constructor
  · intro hother
    exact (honly other hother).trans hplace.symm
  · intro hother
    rw [hother]
    exact hflow

def explicitDecisionPoints
    (net : WorkflowNet Place Trans) : Prop :=
  (∀ place trans,
    net.placeToTrans place trans ->
      uniquePresetOfTransition net trans ∨
        uniquePostsetOfPlace net place) ∧
  (∀ trans place,
    net.transToPlace trans place ->
      uniquePresetOfPlace net place ∨
        uniquePostsetOfTransition net trans)

def splitDecisionPlace
    (net : WorkflowNet Place Trans)
    (place : Place) : Prop :=
  ∃ left right,
    net.placeToTrans place left ∧
      net.placeToTrans place right ∧
      left ≠ right

def joinDecisionPlace
    (net : WorkflowNet Place Trans)
    (place : Place) : Prop :=
  ∃ left right,
    net.transToPlace left place ∧
      net.transToPlace right place ∧
      left ≠ right

def transitionPostsetOfPlace
    (net : WorkflowNet Place Trans)
    (place : Place) : Type v :=
  {trans : Trans // net.placeToTrans place trans}

def transitionPresetOfPlace
    (net : WorkflowNet Place Trans)
    (place : Place) : Type v :=
  {trans : Trans // net.transToPlace trans place}

def placePostsetPresetEquiv
    (net : WorkflowNet Place Trans)
    (split join : Place)
    (toJoin :
      transitionPostsetOfPlace net split ->
        transitionPresetOfPlace net join)
    (fromJoin :
      transitionPresetOfPlace net join ->
        transitionPostsetOfPlace net split) : Prop :=
  (∀ trans, fromJoin (toJoin trans) = trans) ∧
    ∀ trans, toJoin (fromJoin trans) = trans

def decisionPairing
    (net : WorkflowNet Place Trans)
    (pair : Place -> Place) : Prop :=
  (∀ split, splitDecisionPlace net split ->
      joinDecisionPlace net (pair split)) ∧
    (∀ left right,
      splitDecisionPlace net left ->
      splitDecisionPlace net right ->
      pair left = pair right ->
        left = right) ∧
    (∀ join, joinDecisionPlace net join ->
      ∃ split, splitDecisionPlace net split ∧ pair split = join)

def decisionPairingWithBranchEquiv
    (net : WorkflowNet Place Trans)
    (pair : Place -> Place) : Prop :=
  decisionPairing net pair ∧
    ∀ split, splitDecisionPlace net split ->
      ∃ (toJoin :
          transitionPostsetOfPlace net split ->
            transitionPresetOfPlace net (pair split))
        (fromJoin :
          transitionPresetOfPlace net (pair split) ->
            transitionPostsetOfPlace net split),
        placePostsetPresetEquiv net split (pair split) toJoin fromJoin

def decisionBranchPlaceSet
    (net : WorkflowNet Place Trans)
    (split join : Place)
    (part : Set Trans) : Set Place :=
  fun place =>
    place = split ∨ place = join ∨
      PetriNet.placesTouching net.toPetriNet part place

def restrictedDecisionBranchWorkflowNet
    (net : WorkflowNet Place Trans)
    (split join : Place)
    (part : Set Trans) : Prop :=
  ∃ branchNet :
      WorkflowNet
        {place : Place // decisionBranchPlaceSet net split join part place}
        {trans : Trans // part trans},
    branchNet.source.val = split ∧
      branchNet.sink.val = join ∧
      (∀ place trans,
        branchNet.placeToTrans place trans ↔
          net.placeToTrans place.val trans.val) ∧
      (∀ trans place,
        branchNet.transToPlace trans place ↔
          net.transToPlace trans.val place.val)

def decisionBranchSubnet
    (net : WorkflowNet Place Trans)
    (split join : Place)
    (part : Set Trans) : Prop :=
  (∃ trans, part trans) ∧
    restrictedDecisionBranchWorkflowNet net split join part

def decisionBranchFamily
    (net : WorkflowNet Place Trans)
    (split join : Place)
    (branches : transitionPostsetOfPlace net split -> Set Trans) : Prop :=
  (∀ branch, branches branch branch.val) ∧
    (∀ branch, decisionBranchSubnet net split join (branches branch)) ∧
    (∀ left right,
      left ≠ right ->
        ∀ trans, branches left trans -> branches right trans -> False)

def decisionPairingWithBranchSubnets
    (net : WorkflowNet Place Trans)
    (pair : Place -> Place) : Prop :=
  decisionPairingWithBranchEquiv net pair ∧
    ∀ split, splitDecisionPlace net split ->
      ∃ branches,
        decisionBranchFamily net split (pair split) branches

theorem decisionBranchPlaceSet_split
    (net : WorkflowNet Place Trans)
    (split join : Place)
    (part : Set Trans) :
    decisionBranchPlaceSet net split join part split :=
  Or.inl rfl

theorem decisionBranchPlaceSet_join
    (net : WorkflowNet Place Trans)
    (split join : Place)
    (part : Set Trans) :
    decisionBranchPlaceSet net split join part join :=
  Or.inr (Or.inl rfl)

theorem decisionBranchPlaceSet_of_placeToTrans
    (net : WorkflowNet Place Trans)
    {split join : Place}
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hflow : net.placeToTrans place trans) :
    decisionBranchPlaceSet net split join part place :=
  Or.inr (Or.inr
    (PetriNet.placesTouching_of_placeToTrans
      net.toPetriNet hpart hflow))

theorem decisionBranchPlaceSet_of_transToPlace
    (net : WorkflowNet Place Trans)
    {split join : Place}
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hflow : net.transToPlace trans place) :
    decisionBranchPlaceSet net split join part place :=
  Or.inr (Or.inr
    (PetriNet.placesTouching_of_transToPlace
      net.toPetriNet hpart hflow))

theorem decisionBranchPlaceSet_preset_closed
    (net : WorkflowNet Place Trans)
    {split join : Place}
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hflow : net.placeToTrans place trans) :
    decisionBranchPlaceSet net split join part place :=
  decisionBranchPlaceSet_of_placeToTrans net hpart hflow

theorem decisionBranchPlaceSet_postset_closed
    (net : WorkflowNet Place Trans)
    {split join : Place}
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hflow : net.transToPlace trans place) :
    decisionBranchPlaceSet net split join part place :=
  decisionBranchPlaceSet_of_transToPlace net hpart hflow

theorem decisionBranchFamily_branch_nonempty
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {branches : transitionPostsetOfPlace net split -> Set Trans}
    (hfamily : decisionBranchFamily net split join branches)
    (branch : transitionPostsetOfPlace net split) :
    ∃ trans, branches branch trans :=
  (hfamily.2.1 branch).1

theorem decisionBranchFamily_source_transition_mem
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {branches : transitionPostsetOfPlace net split -> Set Trans}
    (hfamily : decisionBranchFamily net split join branches)
    (branch : transitionPostsetOfPlace net split) :
    branches branch branch.val :=
  hfamily.1 branch

theorem decisionBranchFamily_other_not_mem
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {branches : transitionPostsetOfPlace net split -> Set Trans}
    (hfamily : decisionBranchFamily net split join branches)
    {left right : transitionPostsetOfPlace net split}
    (hne : left ≠ right)
    {trans : Trans}
    (hleft : branches left trans) :
    ¬ branches right trans := by
  intro hright
  exact hfamily.2.2 left right hne trans hleft hright

theorem decisionBranchFamily_source_transition_not_mem_other
    {net : WorkflowNet Place Trans}
    {split join : Place}
    {branches : transitionPostsetOfPlace net split -> Set Trans}
    (hfamily : decisionBranchFamily net split join branches)
    {left right : transitionPostsetOfPlace net split}
    (hne : left ≠ right) :
    ¬ branches right left.val :=
  decisionBranchFamily_other_not_mem
    hfamily hne (hfamily.1 left)

def noDecisionPlaces
    (net : WorkflowNet Place Trans) : Prop :=
  (∀ place, ¬ splitDecisionPlace net place) ∧
    ∀ place, ¬ joinDecisionPlace net place

theorem splitDecisionPlace_not_uniquePostsetOfPlace
    {net : WorkflowNet Place Trans}
    {place : Place}
    (hsplit : splitDecisionPlace net place) :
    ¬ uniquePostsetOfPlace net place := by
  intro hunique
  rcases hsplit with ⟨left, right, hleft, hright, hne⟩
  rcases hunique with ⟨only, _honlyFlow, honly⟩
  exact hne ((honly left hleft).trans (honly right hright).symm)

theorem joinDecisionPlace_not_uniquePresetOfPlace
    {net : WorkflowNet Place Trans}
    {place : Place}
    (hjoin : joinDecisionPlace net place) :
    ¬ uniquePresetOfPlace net place := by
  intro hunique
  rcases hjoin with ⟨left, right, hleft, hright, hne⟩
  rcases hunique with ⟨only, _honlyFlow, honly⟩
  exact hne ((honly left hleft).trans (honly right hright).symm)

theorem explicitDecisionPoints_split_transition_uniquePreset
    {net : WorkflowNet Place Trans}
    (hdecision : explicitDecisionPoints net)
    {place : Place}
    (hsplit : splitDecisionPlace net place)
    {trans : Trans}
    (hflow : net.placeToTrans place trans) :
    uniquePresetOfTransition net trans := by
  cases hdecision.1 place trans hflow with
  | inl hpreset =>
      exact hpreset
  | inr hpostset =>
      exact False.elim
        (splitDecisionPlace_not_uniquePostsetOfPlace hsplit hpostset)

theorem explicitDecisionPoints_join_transition_uniquePostset
    {net : WorkflowNet Place Trans}
    (hdecision : explicitDecisionPoints net)
    {place : Place}
    (hjoin : joinDecisionPlace net place)
    {trans : Trans}
    (hflow : net.transToPlace trans place) :
    uniquePostsetOfTransition net trans := by
  cases hdecision.2 trans place hflow with
  | inl hpreset =>
      exact False.elim
        (joinDecisionPlace_not_uniquePresetOfPlace hjoin hpreset)
  | inr hpostset =>
      exact hpostset

theorem explicitDecisionPoints_freeChoice
    {net : WorkflowNet Place Trans}
    (hdecision : explicitDecisionPoints net) :
    PetriNet.freeChoice net.toPetriNet := by
  intro place left right hleft hright other
  by_cases hsame : left = right
  · subst right
    exact Iff.rfl
  · have hnotUniquePostset : ¬ uniquePostsetOfPlace net place := by
      intro hunique
      rcases hunique with ⟨only, _honlyFlow, honly⟩
      exact hsame ((honly left hleft).trans (honly right hright).symm)
    have hleftUnique : uniquePresetOfTransition net left := by
      cases hdecision.1 place left hleft with
      | inl hpreset =>
          exact hpreset
      | inr hpostset =>
          exact False.elim (hnotUniquePostset hpostset)
    have hrightUnique : uniquePresetOfTransition net right := by
      cases hdecision.1 place right hright with
      | inl hpreset =>
          exact hpreset
      | inr hpostset =>
          exact False.elim (hnotUniquePostset hpostset)
    constructor
    · intro hother
      rcases hleftUnique with ⟨only, _honlyFlow, honly⟩
      have hotherEq : other = only := honly other hother
      have hplaceEq : place = only := honly place hleft
      rw [hotherEq.trans hplaceEq.symm]
      exact hright
    · intro hother
      rcases hrightUnique with ⟨only, _honlyFlow, honly⟩
      have hotherEq : other = only := honly other hother
      have hplaceEq : place = only := honly place hright
      rw [hotherEq.trans hplaceEq.symm]
      exact hleft

theorem noDecisionPlaces_markedGraph
    {net : WorkflowNet Place Trans}
    (hnoDecision : noDecisionPlaces net) :
    PetriNet.markedGraph net.toPetriNet := by
  constructor
  · intro place left right hleft hright
    by_cases hsame : left = right
    · exact hsame
    · exact False.elim
        (hnoDecision.2 place
          ⟨left, right, hleft, hright, hsame⟩)
  · intro place left right hleft hright
    by_cases hsame : left = right
    · exact hsame
    · exact False.elim
        (hnoDecision.1 place
          ⟨left, right, hleft, hright, hsame⟩)

theorem markedGraph_noSplitDecisionPlace
    {net : WorkflowNet Place Trans}
    (hmarked : PetriNet.markedGraph net.toPetriNet)
    (place : Place) :
    ¬ splitDecisionPlace net place := by
  intro hsplit
  rcases hsplit with ⟨left, right, hleft, hright, hne⟩
  exact hne
    (PetriNet.markedGraph_placePostset_subsingleton
      hmarked place left right hleft hright)

theorem markedGraph_noJoinDecisionPlace
    {net : WorkflowNet Place Trans}
    (hmarked : PetriNet.markedGraph net.toPetriNet)
    (place : Place) :
    ¬ joinDecisionPlace net place := by
  intro hjoin
  rcases hjoin with ⟨left, right, hleft, hright, hne⟩
  exact hne
    (PetriNet.markedGraph_placePreset_subsingleton
      hmarked place left right hleft hright)

theorem markedGraph_noDecisionPlaces
    {net : WorkflowNet Place Trans}
    (hmarked : PetriNet.markedGraph net.toPetriNet) :
    noDecisionPlaces net :=
  ⟨markedGraph_noSplitDecisionPlace hmarked,
    markedGraph_noJoinDecisionPlace hmarked⟩

theorem noDecisionPlaces_iff_markedGraph
    {net : WorkflowNet Place Trans} :
    noDecisionPlaces net ↔
      PetriNet.markedGraph net.toPetriNet :=
  ⟨noDecisionPlaces_markedGraph, markedGraph_noDecisionPlaces⟩

theorem source_no_input
    (net : WorkflowNet Place Trans)
    (trans : Trans) :
    ¬ net.transToPlace trans net.source :=
  ((net.uniqueSource net.source).2 rfl) trans

theorem sink_no_output
    (net : WorkflowNet Place Trans)
    (trans : Trans) :
    ¬ net.placeToTrans net.sink trans :=
  ((net.uniqueSink net.sink).2 rfl) trans

theorem transition_has_input
    (net : WorkflowNet Place Trans)
    (trans : Trans) :
    ∃ place, net.placeToTrans place trans := by
  have hpath :
      PetriNet.Path
        net.toPetriNet
        (PetriNet.Node.place net.source)
        (PetriNet.Node.trans trans) :=
    (net.connected (PetriNet.Node.trans trans)).1
  rcases PetriNet.path_place_to_transition_last net.toPetriNet hpath with
    ⟨place, _path, hflow⟩
  exact ⟨place, hflow⟩

theorem transition_has_output
    (net : WorkflowNet Place Trans)
    (trans : Trans) :
    ∃ place, net.transToPlace trans place := by
  have hpath :
      PetriNet.Path
        net.toPetriNet
        (PetriNet.Node.trans trans)
        (PetriNet.Node.place net.sink) :=
    (net.connected (PetriNet.Node.trans trans)).2
  rcases PetriNet.path_transition_to_place_first net.toPetriNet hpath with
    ⟨place, hflow, _path⟩
  exact ⟨place, hflow⟩

theorem place_has_input_of_ne_source
    (net : WorkflowNet Place Trans)
    {place : Place}
    (hplace : place ≠ net.source) :
    ∃ trans, net.transToPlace trans place := by
  have hpath :
      PetriNet.Path
        net.toPetriNet
        (PetriNet.Node.place net.source)
        (PetriNet.Node.place place) :=
    (net.connected (PetriNet.Node.place place)).1
  rcases PetriNet.path_to_place_last_transition net.toPetriNet hpath with
    hsame | hlast
  · cases hsame
    exact False.elim (hplace rfl)
  · rcases hlast with ⟨last, _path, hflow⟩
    exact ⟨last, hflow⟩

theorem place_has_output_of_ne_sink
    (net : WorkflowNet Place Trans)
    {place : Place}
    (hplace : place ≠ net.sink) :
    ∃ trans, net.placeToTrans place trans := by
  have hpath :
      PetriNet.Path
        net.toPetriNet
        (PetriNet.Node.place place)
        (PetriNet.Node.place net.sink) :=
    (net.connected (PetriNet.Node.place place)).2
  rcases PetriNet.path_from_place_first_transition net.toPetriNet hpath with
    hsame | hfirst
  · cases hsame
    exact False.elim (hplace rfl)
  · rcases hfirst with ⟨first, hflow, _path⟩
    exact ⟨first, hflow⟩

theorem markedGraph_uniquePresetOfPlace_of_ne_source
    {net : WorkflowNet Place Trans}
    (hmarked : PetriNet.markedGraph net.toPetriNet)
    {place : Place}
    (hplace : place ≠ net.source) :
    uniquePresetOfPlace net place := by
  rcases place_has_input_of_ne_source net hplace with ⟨trans, hflow⟩
  exact
    ⟨trans, hflow,
      fun other hother =>
        hmarked.1 place other trans hother hflow⟩

theorem markedGraph_uniquePostsetOfPlace_of_ne_sink
    {net : WorkflowNet Place Trans}
    (hmarked : PetriNet.markedGraph net.toPetriNet)
    {place : Place}
    (hplace : place ≠ net.sink) :
    uniquePostsetOfPlace net place := by
  rcases place_has_output_of_ne_sink net hplace with ⟨trans, hflow⟩
  exact
    ⟨trans, hflow,
      fun other hother =>
        hmarked.2 place other trans hother hflow⟩

def normalized
    (net : PetriNet Place Trans)
    (source sink : Place)
    (hconnected :
      ∀ node : PetriNet.Node Place Trans,
        PetriNet.Path net (PetriNet.Node.place source) node ∧
        PetriNet.Path net node (PetriNet.Node.place sink)) :
    WorkflowNet
      (PetriNet.NormalizedPlace Place)
      (PetriNet.NormalizedTrans Trans) where
  toPetriNet := PetriNet.normalize net source sink
  source := PetriNet.NormalizedPlace.source
  sink := PetriNet.NormalizedPlace.sink
  uniqueSource := by
    apply PetriNet.uniqueSource_of_connected_no_in
    · exact PetriNet.normalize_source_no_input net source sink
    · exact PetriNet.normalize_connected net source sink hconnected
  uniqueSink := by
    apply PetriNet.uniqueSink_of_connected_no_out
    · exact PetriNet.normalize_sink_no_output net source sink
    · exact PetriNet.normalize_connected net source sink hconnected
  connected := PetriNet.normalize_connected net source sink hconnected

def normalizedNet (net : WorkflowNet Place Trans) :
    WorkflowNet
      (PetriNet.NormalizedPlace Place)
      (PetriNet.NormalizedTrans Trans) :=
  normalized net.toPetriNet net.source net.sink net.connected

theorem entryPoints_has_part_output
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hentry : entryPoints net part place) :
    ∃ trans, part trans ∧ net.placeToTrans place trans :=
  hentry.1

theorem entryPoints_source_or_external_input
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hentry : entryPoints net part place) :
    place = net.source ∨
      ∃ trans, ¬ part trans ∧ net.transToPlace trans place :=
  hentry.2

theorem exitPoints_has_part_input
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hexit : exitPoints net part place) :
    ∃ trans, part trans ∧ net.transToPlace trans place :=
  hexit.1

theorem exitPoints_sink_or_external_output
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hexit : exitPoints net part place) :
    place = net.sink ∨
      ∃ trans, ¬ part trans ∧ net.placeToTrans place trans :=
  hexit.2

theorem entryPoints_of_source_part_output
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hsource : place = net.source)
    (houtput : ∃ trans, part trans ∧ net.placeToTrans place trans) :
    entryPoints net part place :=
  ⟨houtput, Or.inl hsource⟩

theorem exitPoints_of_sink_part_input
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hsink : place = net.sink)
    (hinput : ∃ trans, part trans ∧ net.transToPlace trans place) :
    exitPoints net part place :=
  ⟨hinput, Or.inl hsink⟩

theorem entryPoints_of_external_input
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (houtput : ∃ trans, part trans ∧ net.placeToTrans place trans)
    (hexternal : ∃ trans, ¬ part trans ∧ net.transToPlace trans place) :
    entryPoints net part place :=
  ⟨houtput, Or.inr hexternal⟩

theorem exitPoints_of_external_output
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hinput : ∃ trans, part trans ∧ net.transToPlace trans place)
    (hexternal : ∃ trans, ¬ part trans ∧ net.placeToTrans place trans) :
    exitPoints net part place :=
  ⟨hinput, Or.inr hexternal⟩

theorem entryPoints_source_iff
    (net : WorkflowNet Place Trans)
    (part : Set Trans) :
    entryPoints net part net.source ↔
      ∃ trans, part trans ∧ net.placeToTrans net.source trans := by
  constructor
  · intro hentry
    exact hentry.1
  · intro houtput
    exact ⟨houtput, Or.inl rfl⟩

theorem exitPoints_sink_iff
    (net : WorkflowNet Place Trans)
    (part : Set Trans) :
    exitPoints net part net.sink ↔
      ∃ trans, part trans ∧ net.transToPlace trans net.sink := by
  constructor
  · intro hexit
    exact hexit.1
  · intro hinput
    exact ⟨hinput, Or.inl rfl⟩

theorem entryPoints_external_input_of_ne_source
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hentry : entryPoints net part place)
    (hplace : place ≠ net.source) :
    ∃ trans, ¬ part trans ∧ net.transToPlace trans place := by
  rcases hentry.2 with hsource | hexternal
  · exact False.elim (hplace hsource)
  · exact hexternal

theorem exitPoints_external_output_of_ne_sink
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hexit : exitPoints net part place)
    (hplace : place ≠ net.sink) :
    ∃ trans, ¬ part trans ∧ net.placeToTrans place trans := by
  rcases hexit.2 with hsink | hexternal
  · exact False.elim (hplace hsink)
  · exact hexternal

theorem entryPoints_ne_sink
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hentry : entryPoints net part place) :
    place ≠ net.sink := by
  intro hsink
  rcases hentry.1 with ⟨trans, _hpart, hflow⟩
  rw [hsink] at hflow
  exact sink_no_output net trans hflow

theorem exitPoints_ne_source
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hexit : exitPoints net part place) :
    place ≠ net.source := by
  intro hsource
  rcases hexit.1 with ⟨trans, _hpart, hflow⟩
  rw [hsource] at hflow
  exact source_no_input net trans hflow

theorem not_entryPoints_sink
    (net : WorkflowNet Place Trans)
    (part : Set Trans) :
    ¬ entryPoints net part net.sink := by
  intro hentry
  exact entryPoints_ne_sink net hentry rfl

theorem not_exitPoints_source
    (net : WorkflowNet Place Trans)
    (part : Set Trans) :
    ¬ exitPoints net part net.source := by
  intro hexit
  exact exitPoints_ne_source net hexit rfl

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

theorem firingSequence_append
    {net : WorkflowNet Place Trans}
    {before middle after : Marking Place}
    {left right : List Trans}
    (leftSequence : FiringSequence net before left middle)
    (rightSequence : FiringSequence net middle right after) :
    FiringSequence net before (left ++ right) after := by
  induction leftSequence with
  | nil =>
      exact rightSequence
  | cons hfires _ ih =>
      exact FiringSequence.cons hfires (ih rightSequence)

theorem firingSequence_split_append
    {net : WorkflowNet Place Trans}
    {before after : Marking Place}
    (left right : List Trans)
    (sequence : FiringSequence net before (left ++ right) after) :
    ∃ middle,
      FiringSequence net before left middle ∧
      FiringSequence net middle right after := by
  induction left generalizing before with
  | nil =>
      exact ⟨before, FiringSequence.nil, sequence⟩
  | cons trans rest ih =>
      cases sequence with
      | cons hfires tail =>
          rcases ih tail with ⟨middle, leftSequence, rightSequence⟩
          exact
            ⟨middle,
              FiringSequence.cons hfires leftSequence,
              rightSequence⟩

theorem firingSequence_snoc
    {net : WorkflowNet Place Trans}
    {before middle after : Marking Place}
    {trace : List Trans}
    {trans : Trans}
    (sequence : FiringSequence net before trace middle)
    (hfires : fires net middle trans after) :
    FiringSequence net before (trace ++ [trans]) after :=
  firingSequence_append sequence
    (FiringSequence.cons hfires FiringSequence.nil)

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

theorem sound_noDeadTransitions
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hsound : sound net) :
    noDeadTransitions net :=
  hsound.1

theorem sound_optionToComplete
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hsound : sound net) :
    optionToComplete net :=
  hsound.2.1

theorem sound_properCompletion
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hsound : sound net) :
    properCompletion net :=
  hsound.2.2

theorem safeAndSound_safe
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hsafeSound : safeAndSound net) :
    safe net :=
  hsafeSound.1

theorem safeAndSound_sound
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hsafeSound : safeAndSound net) :
    sound net :=
  hsafeSound.2

theorem safeAndSound_noDeadTransitions
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hsafeSound : safeAndSound net) :
    noDeadTransitions net :=
  sound_noDeadTransitions (safeAndSound_sound hsafeSound)

theorem safeAndSound_optionToComplete
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hsafeSound : safeAndSound net) :
    optionToComplete net :=
  sound_optionToComplete (safeAndSound_sound hsafeSound)

theorem safeAndSound_properCompletion
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hsafeSound : safeAndSound net) :
    properCompletion net :=
  sound_properCompletion (safeAndSound_sound hsafeSound)

def semiBlockStructuredBaseRequirements
    [DecidableEq Place]
    (net : WorkflowNet Place Trans) : Prop :=
  safeAndSound net ∧ explicitDecisionPoints net

def semiBlockStructuredDecisionRequirements
    [DecidableEq Place]
    (net : WorkflowNet Place Trans) : Prop :=
  semiBlockStructuredBaseRequirements net ∧
    ∃ pair, decisionPairingWithBranchEquiv net pair

def semiBlockStructuredSubnetRequirements
    [DecidableEq Place]
    (net : WorkflowNet Place Trans) : Prop :=
  semiBlockStructuredBaseRequirements net ∧
    ∃ pair, decisionPairingWithBranchSubnets net pair

theorem semiBlockStructuredBaseRequirements_safeAndSound
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredBaseRequirements net) :
    safeAndSound net :=
  hrequirements.1

theorem semiBlockStructuredBaseRequirements_safe
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredBaseRequirements net) :
    safe net :=
  safeAndSound_safe
    (semiBlockStructuredBaseRequirements_safeAndSound hrequirements)

theorem semiBlockStructuredBaseRequirements_sound
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredBaseRequirements net) :
    sound net :=
  safeAndSound_sound
    (semiBlockStructuredBaseRequirements_safeAndSound hrequirements)

theorem semiBlockStructuredBaseRequirements_noDeadTransitions
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredBaseRequirements net) :
    noDeadTransitions net :=
  safeAndSound_noDeadTransitions
    (semiBlockStructuredBaseRequirements_safeAndSound hrequirements)

theorem semiBlockStructuredBaseRequirements_optionToComplete
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredBaseRequirements net) :
    optionToComplete net :=
  safeAndSound_optionToComplete
    (semiBlockStructuredBaseRequirements_safeAndSound hrequirements)

theorem semiBlockStructuredBaseRequirements_properCompletion
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredBaseRequirements net) :
    properCompletion net :=
  safeAndSound_properCompletion
    (semiBlockStructuredBaseRequirements_safeAndSound hrequirements)

theorem semiBlockStructuredBaseRequirements_explicitDecisionPoints
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredBaseRequirements net) :
    explicitDecisionPoints net :=
  hrequirements.2

theorem semiBlockStructuredBaseRequirements_freeChoice
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredBaseRequirements net) :
    PetriNet.freeChoice net.toPetriNet :=
  explicitDecisionPoints_freeChoice
    (semiBlockStructuredBaseRequirements_explicitDecisionPoints
      hrequirements)

theorem semiBlockStructuredDecisionRequirements_base
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredDecisionRequirements net) :
    semiBlockStructuredBaseRequirements net :=
  hrequirements.1

theorem semiBlockStructuredDecisionRequirements_safeAndSound
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredDecisionRequirements net) :
    safeAndSound net :=
  semiBlockStructuredBaseRequirements_safeAndSound
    (semiBlockStructuredDecisionRequirements_base hrequirements)

theorem semiBlockStructuredDecisionRequirements_safe
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredDecisionRequirements net) :
    safe net :=
  semiBlockStructuredBaseRequirements_safe
    (semiBlockStructuredDecisionRequirements_base hrequirements)

theorem semiBlockStructuredDecisionRequirements_sound
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredDecisionRequirements net) :
    sound net :=
  semiBlockStructuredBaseRequirements_sound
    (semiBlockStructuredDecisionRequirements_base hrequirements)

theorem semiBlockStructuredDecisionRequirements_noDeadTransitions
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredDecisionRequirements net) :
    noDeadTransitions net :=
  semiBlockStructuredBaseRequirements_noDeadTransitions
    (semiBlockStructuredDecisionRequirements_base hrequirements)

theorem semiBlockStructuredDecisionRequirements_optionToComplete
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredDecisionRequirements net) :
    optionToComplete net :=
  semiBlockStructuredBaseRequirements_optionToComplete
    (semiBlockStructuredDecisionRequirements_base hrequirements)

theorem semiBlockStructuredDecisionRequirements_properCompletion
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredDecisionRequirements net) :
    properCompletion net :=
  semiBlockStructuredBaseRequirements_properCompletion
    (semiBlockStructuredDecisionRequirements_base hrequirements)

theorem semiBlockStructuredDecisionRequirements_explicitDecisionPoints
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredDecisionRequirements net) :
    explicitDecisionPoints net :=
  semiBlockStructuredBaseRequirements_explicitDecisionPoints
    (semiBlockStructuredDecisionRequirements_base hrequirements)

theorem semiBlockStructuredDecisionRequirements_freeChoice
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredDecisionRequirements net) :
    PetriNet.freeChoice net.toPetriNet :=
  semiBlockStructuredBaseRequirements_freeChoice
    (semiBlockStructuredDecisionRequirements_base hrequirements)

theorem semiBlockStructuredSubnetRequirements_base
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredSubnetRequirements net) :
    semiBlockStructuredBaseRequirements net :=
  hrequirements.1

theorem semiBlockStructuredSubnetRequirements_safeAndSound
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredSubnetRequirements net) :
    safeAndSound net :=
  semiBlockStructuredBaseRequirements_safeAndSound
    (semiBlockStructuredSubnetRequirements_base hrequirements)

theorem semiBlockStructuredSubnetRequirements_safe
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredSubnetRequirements net) :
    safe net :=
  semiBlockStructuredBaseRequirements_safe
    (semiBlockStructuredSubnetRequirements_base hrequirements)

theorem semiBlockStructuredSubnetRequirements_sound
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredSubnetRequirements net) :
    sound net :=
  semiBlockStructuredBaseRequirements_sound
    (semiBlockStructuredSubnetRequirements_base hrequirements)

theorem semiBlockStructuredSubnetRequirements_noDeadTransitions
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredSubnetRequirements net) :
    noDeadTransitions net :=
  semiBlockStructuredBaseRequirements_noDeadTransitions
    (semiBlockStructuredSubnetRequirements_base hrequirements)

theorem semiBlockStructuredSubnetRequirements_optionToComplete
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredSubnetRequirements net) :
    optionToComplete net :=
  semiBlockStructuredBaseRequirements_optionToComplete
    (semiBlockStructuredSubnetRequirements_base hrequirements)

theorem semiBlockStructuredSubnetRequirements_properCompletion
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredSubnetRequirements net) :
    properCompletion net :=
  semiBlockStructuredBaseRequirements_properCompletion
    (semiBlockStructuredSubnetRequirements_base hrequirements)

theorem semiBlockStructuredSubnetRequirements_explicitDecisionPoints
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredSubnetRequirements net) :
    explicitDecisionPoints net :=
  semiBlockStructuredBaseRequirements_explicitDecisionPoints
    (semiBlockStructuredSubnetRequirements_base hrequirements)

theorem semiBlockStructuredSubnetRequirements_freeChoice
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredSubnetRequirements net) :
    PetriNet.freeChoice net.toPetriNet :=
  semiBlockStructuredBaseRequirements_freeChoice
    (semiBlockStructuredSubnetRequirements_base hrequirements)

theorem decisionPairingWithBranchEquiv_pairing
    {net : WorkflowNet Place Trans}
    {pair : Place -> Place}
    (hpair : decisionPairingWithBranchEquiv net pair) :
    decisionPairing net pair :=
  hpair.1

theorem decisionPairingWithBranchSubnets_pairingEquiv
    {net : WorkflowNet Place Trans}
    {pair : Place -> Place}
    (hpair : decisionPairingWithBranchSubnets net pair) :
    decisionPairingWithBranchEquiv net pair :=
  hpair.1

theorem decisionPairingWithBranchSubnets_branchFamily
    {net : WorkflowNet Place Trans}
    {pair : Place -> Place}
    (hpair : decisionPairingWithBranchSubnets net pair)
    {split : Place}
    (hsplit : splitDecisionPlace net split) :
    ∃ branches,
      decisionBranchFamily net split (pair split) branches :=
  hpair.2 split hsplit

theorem semiBlockStructuredSubnetRequirements_decisionRequirements
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredSubnetRequirements net) :
    semiBlockStructuredDecisionRequirements net := by
  rcases hrequirements.2 with ⟨pair, hpair⟩
  exact
    ⟨hrequirements.1,
      ⟨pair, decisionPairingWithBranchSubnets_pairingEquiv hpair⟩⟩

theorem semiBlockStructuredSubnetRequirements_branchEquiv
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredSubnetRequirements net) :
    ∃ pair, decisionPairingWithBranchEquiv net pair := by
  rcases hrequirements.2 with ⟨pair, hpair⟩
  exact ⟨pair, decisionPairingWithBranchSubnets_pairingEquiv hpair⟩

theorem semiBlockStructuredSubnetRequirements_branchFamily
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    (hrequirements : semiBlockStructuredSubnetRequirements net)
    {split : Place}
    (hsplit : splitDecisionPlace net split) :
    ∃ (pair : Place -> Place)
      (branches : transitionPostsetOfPlace net split -> Set Trans),
      decisionPairingWithBranchEquiv net pair ∧
        decisionBranchFamily net split (pair split) branches := by
  rcases hrequirements.2 with ⟨pair, hpair⟩
  rcases
    decisionPairingWithBranchSubnets_branchFamily hpair hsplit with
    ⟨branches, hbranches⟩
  exact
    ⟨pair, branches,
      decisionPairingWithBranchSubnets_pairingEquiv hpair,
      hbranches⟩

theorem normalized_enter_enabled_iff
    (net : WorkflowNet Place Trans)
    (marking : Marking (PetriNet.NormalizedPlace Place)) :
    enabled (normalizedNet net) marking PetriNet.NormalizedTrans.enter ↔
      marking PetriNet.NormalizedPlace.source > 0 := by
  constructor
  · intro henabled
    exact henabled PetriNet.NormalizedPlace.source
      (by simp [normalizedNet, normalized, PetriNet.normalize])
  · intro hsource place hflow
    cases place with
    | source =>
        exact hsource
    | original place =>
        simp [normalizedNet, normalized, PetriNet.normalize] at hflow
    | sink =>
        simp [normalizedNet, normalized, PetriNet.normalize] at hflow

theorem normalized_enter_fires
    [DecidableEq Place]
    (net : WorkflowNet Place Trans) :
    fires
      (normalizedNet net)
      (initial (normalizedNet net))
      PetriNet.NormalizedTrans.enter
      (Marking.normalize (initial net)) := by
  constructor
  · intro place hflow
    cases place with
    | source =>
        simp [normalizedNet, normalized, PetriNet.normalize, initial,
          Marking.single]
    | original place =>
        simp [normalizedNet, normalized, PetriNet.normalize] at hflow
    | sink =>
        simp [normalizedNet, normalized, PetriNet.normalize] at hflow
  · funext place
    cases place with
    | source =>
        simp [fire, consumed, produced, normalizedNet, normalized,
          PetriNet.normalize, initial, Marking.single, Marking.normalize]
    | original place =>
        simp [fire, consumed, produced, normalizedNet, normalized,
          PetriNet.normalize, initial, Marking.single, Marking.normalize]
    | sink =>
        simp [fire, consumed, produced, normalizedNet, normalized,
          PetriNet.normalize, initial, Marking.single, Marking.normalize]

theorem normalized_enter_fire_eq
    [DecidableEq Place]
    (net : WorkflowNet Place Trans) :
    fire
      (normalizedNet net)
      (initial (normalizedNet net))
      PetriNet.NormalizedTrans.enter =
        Marking.normalize (initial net) :=
  (normalized_enter_fires net).2.symm

theorem normalized_exit_enabled_iff
    (net : WorkflowNet Place Trans)
    (marking : Marking (PetriNet.NormalizedPlace Place)) :
    enabled (normalizedNet net) marking PetriNet.NormalizedTrans.exit ↔
      marking (PetriNet.NormalizedPlace.original net.sink) > 0 := by
  constructor
  · intro henabled
    exact henabled (PetriNet.NormalizedPlace.original net.sink)
      (by simp [normalizedNet, normalized, PetriNet.normalize])
  · intro hsink place hflow
    cases place with
    | source =>
        simp [normalizedNet, normalized, PetriNet.normalize] at hflow
    | original place =>
        have hplace : place = net.sink := by
          simpa [normalizedNet, normalized, PetriNet.normalize] using hflow
        subst hplace
        exact hsink
    | sink =>
        simp [normalizedNet, normalized, PetriNet.normalize] at hflow

theorem normalized_original_fires
    (net : WorkflowNet Place Trans)
    {before after : Marking Place}
    {trans : Trans}
    (hfires : fires net before trans after) :
    fires
      (normalizedNet net)
      (Marking.normalize before)
      (PetriNet.NormalizedTrans.original trans)
      (Marking.normalize after) := by
  constructor
  · intro place hflow
    cases place with
    | source =>
        simp [normalizedNet, normalized, PetriNet.normalize] at hflow
    | original place =>
        exact hfires.1 place
          (by
            simpa [normalizedNet, normalized, PetriNet.normalize] using hflow)
    | sink =>
        simp [normalizedNet, normalized, PetriNet.normalize] at hflow
  · rw [hfires.2]
    funext place
    cases place with
    | source =>
        simp [fire, consumed, produced, normalizedNet, normalized,
          PetriNet.normalize, Marking.normalize]
    | original place =>
        simp [fire, consumed, produced, normalizedNet, normalized,
          PetriNet.normalize, Marking.normalize]
        rfl
    | sink =>
        simp [fire, consumed, produced, normalizedNet, normalized,
          PetriNet.normalize, Marking.normalize]

theorem normalized_original_enabled_iff
    (net : WorkflowNet Place Trans)
    (marking : Marking Place)
    (trans : Trans) :
    enabled
      (normalizedNet net)
      (Marking.normalize marking)
      (PetriNet.NormalizedTrans.original trans) ↔
        enabled net marking trans := by
  constructor
  · intro henabled place hflow
    exact henabled (PetriNet.NormalizedPlace.original place)
      (by
        simpa [normalizedNet, normalized, PetriNet.normalize] using hflow)
  · intro henabled place hflow
    cases place with
    | source =>
        simp [normalizedNet, normalized, PetriNet.normalize] at hflow
    | original place =>
        exact henabled place
          (by
            simpa [normalizedNet, normalized, PetriNet.normalize] using hflow)
    | sink =>
        simp [normalizedNet, normalized, PetriNet.normalize] at hflow

theorem normalized_original_fire_eq
    (net : WorkflowNet Place Trans)
    (marking : Marking Place)
    (trans : Trans) :
    fire
      (normalizedNet net)
      (Marking.normalize marking)
      (PetriNet.NormalizedTrans.original trans) =
        Marking.normalize (fire net marking trans) := by
  funext place
  cases place with
  | source =>
      simp [fire, consumed, produced, normalizedNet, normalized,
        PetriNet.normalize, Marking.normalize]
  | original place =>
      simp [fire, consumed, produced, normalizedNet, normalized,
        PetriNet.normalize, Marking.normalize]
      rfl
  | sink =>
      simp [fire, consumed, produced, normalizedNet, normalized,
        PetriNet.normalize, Marking.normalize]

theorem normalized_original_fire_fresh_source
    (net : WorkflowNet Place Trans)
    (marking : Marking (PetriNet.NormalizedPlace Place))
    (trans : Trans) :
    fire
      (normalizedNet net)
      marking
      (PetriNet.NormalizedTrans.original trans)
      PetriNet.NormalizedPlace.source =
        marking PetriNet.NormalizedPlace.source := by
  simp [fire, consumed, produced, normalizedNet, normalized,
    PetriNet.normalize]

theorem normalized_original_fire_fresh_sink
    (net : WorkflowNet Place Trans)
    (marking : Marking (PetriNet.NormalizedPlace Place))
    (trans : Trans) :
    fire
      (normalizedNet net)
      marking
      (PetriNet.NormalizedTrans.original trans)
      PetriNet.NormalizedPlace.sink =
        marking PetriNet.NormalizedPlace.sink := by
  simp [fire, consumed, produced, normalizedNet, normalized,
    PetriNet.normalize]

theorem normalized_original_firingSequence_preserves_fresh_source
    (net : WorkflowNet Place Trans)
    {before after : Marking (PetriNet.NormalizedPlace Place)}
    {trace : List Trans}
    (sequence :
      FiringSequence
        (normalizedNet net)
        before
        (trace.map PetriNet.NormalizedTrans.original)
        after) :
    after PetriNet.NormalizedPlace.source =
      before PetriNet.NormalizedPlace.source := by
  induction trace generalizing before after with
  | nil =>
      cases sequence with
      | nil =>
          rfl
  | cons trans rest ih =>
      cases sequence with
      | cons hfires tail =>
          have htail := ih tail
          rw [hfires.2] at htail
          have hmiddle :
              fire
                (normalizedNet net)
                before
                (PetriNet.NormalizedTrans.original trans)
                PetriNet.NormalizedPlace.source =
                  before PetriNet.NormalizedPlace.source :=
            normalized_original_fire_fresh_source net before trans
          exact htail.trans hmiddle

theorem normalized_original_firingSequence_preserves_fresh_sink
    (net : WorkflowNet Place Trans)
    {before after : Marking (PetriNet.NormalizedPlace Place)}
    {trace : List Trans}
    (sequence :
      FiringSequence
        (normalizedNet net)
        before
        (trace.map PetriNet.NormalizedTrans.original)
        after) :
    after PetriNet.NormalizedPlace.sink =
      before PetriNet.NormalizedPlace.sink := by
  induction trace generalizing before after with
  | nil =>
      cases sequence with
      | nil =>
          rfl
  | cons trans rest ih =>
      cases sequence with
      | cons hfires tail =>
          have htail := ih tail
          rw [hfires.2] at htail
          have hmiddle :
              fire
                (normalizedNet net)
                before
                (PetriNet.NormalizedTrans.original trans)
                PetriNet.NormalizedPlace.sink =
                  before PetriNet.NormalizedPlace.sink :=
            normalized_original_fire_fresh_sink net before trans
          exact htail.trans hmiddle

theorem normalized_original_fires_iff
    (net : WorkflowNet Place Trans)
    (before after : Marking Place)
    (trans : Trans) :
    fires
      (normalizedNet net)
      (Marking.normalize before)
      (PetriNet.NormalizedTrans.original trans)
      (Marking.normalize after) ↔
        fires net before trans after := by
  constructor
  · intro hfires
    constructor
    · exact
        (normalized_original_enabled_iff net before trans).mp
          hfires.1
    · apply Marking.normalize_injective
      rw [hfires.2, normalized_original_fire_eq]
  · intro hfires
    exact normalized_original_fires net hfires

theorem normalized_firingSequence_original
    (net : WorkflowNet Place Trans)
    {before after : Marking Place}
    {trace : List Trans}
    (sequence : FiringSequence net before trace after) :
    FiringSequence
      (normalizedNet net)
      (Marking.normalize before)
      (trace.map PetriNet.NormalizedTrans.original)
      (Marking.normalize after) := by
  induction sequence with
  | nil =>
      exact FiringSequence.nil
  | cons hfires _ ih =>
      exact FiringSequence.cons
        (normalized_original_fires net hfires)
        ih

theorem normalized_firingSequence_original_reverse_aux
    (net : WorkflowNet Place Trans)
    {before : Marking Place}
    {normalizedAfter : Marking (PetriNet.NormalizedPlace Place)}
    {trace : List Trans}
    (sequence :
      FiringSequence
        (normalizedNet net)
        (Marking.normalize before)
        (trace.map PetriNet.NormalizedTrans.original)
        normalizedAfter) :
    ∃ after,
      normalizedAfter = Marking.normalize after ∧
      FiringSequence net before trace after := by
  induction trace generalizing before normalizedAfter with
  | nil =>
    cases sequence with
    | nil =>
        exact ⟨before, rfl, FiringSequence.nil⟩
  | cons trans rest ih =>
    cases sequence with
    | cons hfires tail =>
        rw [hfires.2, normalized_original_fire_eq] at tail
        rcases ih tail with ⟨after, hafter, restSequence⟩
        exact
          ⟨after, hafter,
            FiringSequence.cons
              ⟨(normalized_original_enabled_iff net before trans).mp hfires.1,
                rfl⟩
              restSequence⟩

theorem normalized_firingSequence_original_reverse
    (net : WorkflowNet Place Trans)
    {before after : Marking Place}
    {trace : List Trans}
    (sequence :
      FiringSequence
        (normalizedNet net)
        (Marking.normalize before)
        (trace.map PetriNet.NormalizedTrans.original)
        (Marking.normalize after)) :
    FiringSequence net before trace after := by
  rcases normalized_firingSequence_original_reverse_aux net sequence with
    ⟨actualAfter, hactual, actualSequence⟩
  have hafter : actualAfter = after :=
    Marking.normalize_injective hactual.symm
  subst hafter
  exact actualSequence

theorem normalized_firingSequence_original_iff
    (net : WorkflowNet Place Trans)
    {before after : Marking Place}
    {trace : List Trans} :
    FiringSequence
      (normalizedNet net)
      (Marking.normalize before)
      (trace.map PetriNet.NormalizedTrans.original)
      (Marking.normalize after) ↔
        FiringSequence net before trace after := by
  constructor
  · exact normalized_firingSequence_original_reverse net
  · exact normalized_firingSequence_original net

theorem normalized_exit_fires
    [DecidableEq Place]
    (net : WorkflowNet Place Trans) :
    fires
      (normalizedNet net)
      (Marking.normalize (final net))
      PetriNet.NormalizedTrans.exit
      (final (normalizedNet net)) := by
  constructor
  · intro place hflow
    cases place with
    | source =>
        simp [normalizedNet, normalized, PetriNet.normalize] at hflow
    | original place =>
        simp [normalizedNet, normalized, PetriNet.normalize] at hflow
        subst hflow
        simp [final, Marking.single, Marking.normalize]
    | sink =>
        simp [normalizedNet, normalized, PetriNet.normalize] at hflow
  · funext place
    cases place with
    | source =>
        simp [fire, consumed, produced, normalizedNet, normalized,
          PetriNet.normalize, final, Marking.single, Marking.normalize]
    | original place =>
        by_cases hsink : place = net.sink
        · simp [fire, consumed, produced, normalizedNet, normalized,
            PetriNet.normalize, final, Marking.single, Marking.normalize,
            hsink]
        · simp [fire, consumed, produced, normalizedNet, normalized,
            PetriNet.normalize, final, Marking.single, Marking.normalize,
            hsink]
    | sink =>
        simp [fire, consumed, produced, normalizedNet, normalized,
          PetriNet.normalize, final, Marking.single, Marking.normalize]

theorem normalized_exit_fires_iff
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (marking : Marking Place) :
    fires
      (normalizedNet net)
      (Marking.normalize marking)
      PetriNet.NormalizedTrans.exit
      (final (normalizedNet net)) ↔
        marking = final net := by
  constructor
  · intro hfires
    funext place
    by_cases hsink : place = net.sink
    · subst hsink
      have hpositive :
          marking net.sink > 0 :=
        hfires.1
          (PetriNet.NormalizedPlace.original net.sink)
          (by
            simp [normalizedNet, normalized, PetriNet.normalize])
      have heq :=
        congrFun hfires.2
          (PetriNet.NormalizedPlace.original net.sink)
      simp [fire, consumed, produced, normalizedNet, normalized,
        PetriNet.normalize, final, Marking.single, Marking.normalize] at heq
      cases hmark : marking net.sink with
      | zero =>
          rw [hmark] at hpositive
          exact False.elim (Nat.not_succ_le_zero 0 hpositive)
      | succ count =>
          rw [hmark] at heq
          simp at heq
          rw [← heq]
          simp [final, Marking.single]
    · have heq :=
        congrFun hfires.2 (PetriNet.NormalizedPlace.original place)
      simp [fire, consumed, produced, normalizedNet, normalized,
        PetriNet.normalize, final, Marking.single, Marking.normalize,
        hsink] at heq
      rw [final, Marking.single]
      simp [hsink]
      exact heq.symm
  · intro hmarking
    subst hmarking
    exact normalized_exit_fires net

theorem normalized_firingSequence_accepting
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    {trace : List Trans}
    (sequence : FiringSequence net (initial net) trace (final net)) :
    FiringSequence
      (normalizedNet net)
      (initial (normalizedNet net))
      (PetriNet.NormalizedTrans.enter ::
        (trace.map PetriNet.NormalizedTrans.original ++
          [PetriNet.NormalizedTrans.exit]))
      (final (normalizedNet net)) :=
  FiringSequence.cons
    (normalized_enter_fires net)
    (firingSequence_snoc
      (normalized_firingSequence_original net sequence)
      (normalized_exit_fires net))

theorem normalized_firingSequence_accepting_reverse
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    {trace : List Trans}
    (sequence :
      FiringSequence
        (normalizedNet net)
        (initial (normalizedNet net))
        (PetriNet.NormalizedTrans.enter ::
          (trace.map PetriNet.NormalizedTrans.original ++
            [PetriNet.NormalizedTrans.exit]))
        (final (normalizedNet net))) :
    FiringSequence net (initial net) trace (final net) := by
  cases sequence with
  | cons hfires tail =>
      rw [hfires.2, normalized_enter_fire_eq] at tail
      rcases firingSequence_split_append
          (trace.map PetriNet.NormalizedTrans.original)
          [PetriNet.NormalizedTrans.exit]
          tail with
        ⟨middle, originalTail, exitTail⟩
      rcases normalized_firingSequence_original_reverse_aux
          net originalTail with
        ⟨after, hmiddle, originalSequence⟩
      rw [hmiddle] at exitTail
      cases exitTail with
      | cons hexit exitDone =>
          cases exitDone with
          | nil =>
              have hafter : after = final net :=
                (normalized_exit_fires_iff net after).mp hexit
              subst hafter
              exact originalSequence

theorem normalized_firingSequence_accepting_iff
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    {trace : List Trans} :
    FiringSequence
      (normalizedNet net)
      (initial (normalizedNet net))
      (PetriNet.NormalizedTrans.enter ::
        (trace.map PetriNet.NormalizedTrans.original ++
          [PetriNet.NormalizedTrans.exit]))
      (final (normalizedNet net)) ↔
        FiringSequence net (initial net) trace (final net) := by
  constructor
  · exact normalized_firingSequence_accepting_reverse net
  · exact normalized_firingSequence_accepting net

theorem normalized_reachable_of_original
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    {marking : Marking Place}
    (hreachable : reachable net (initial net) marking) :
    reachable
      (normalizedNet net)
      (initial (normalizedNet net))
      (Marking.normalize marking) := by
  rcases hreachable with ⟨trace, sequence⟩
  refine ⟨PetriNet.NormalizedTrans.enter ::
    trace.map PetriNet.NormalizedTrans.original, ?_⟩
  exact
    FiringSequence.cons
      (normalized_enter_fires net)
      (normalized_firingSequence_original net sequence)

theorem normalized_complete_from_original_marking
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hcomplete : optionToComplete net)
    {marking : Marking Place}
    (hreachable : reachable net (initial net) marking) :
    reachable
      (normalizedNet net)
      (Marking.normalize marking)
      (final (normalizedNet net)) := by
  rcases hcomplete marking hreachable with ⟨trace, sequence⟩
  refine
    ⟨trace.map PetriNet.NormalizedTrans.original ++
        [PetriNet.NormalizedTrans.exit],
      ?_⟩
  exact
    firingSequence_snoc
      (normalized_firingSequence_original net sequence)
      (normalized_exit_fires net)

theorem normalized_complete_from_initial
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hcomplete : optionToComplete net) :
    reachable
      (normalizedNet net)
      (initial (normalizedNet net))
      (final (normalizedNet net)) := by
  have hinitialReachable :
      reachable net (initial net) (initial net) :=
    ⟨[], FiringSequence.nil⟩
  rcases normalized_complete_from_original_marking
      net hcomplete hinitialReachable with
    ⟨trace, sequence⟩
  refine ⟨PetriNet.NormalizedTrans.enter :: trace, ?_⟩
  exact FiringSequence.cons (normalized_enter_fires net) sequence

def normalizedReachableShape
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (marking : Marking (PetriNet.NormalizedPlace Place)) : Prop :=
  marking = initial (normalizedNet net) ∨
    (∃ original,
      reachable net (initial net) original ∧
        marking = Marking.normalize original) ∨
    marking = final (normalizedNet net)

theorem normalized_initial_original_not_enabled
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (trans : Trans) :
    ¬ enabled
      (normalizedNet net)
      (initial (normalizedNet net))
      (PetriNet.NormalizedTrans.original trans) := by
  intro henabled
  rcases transition_has_input net trans with ⟨place, hflow⟩
  have hpositive :
      initial (normalizedNet net)
        (PetriNet.NormalizedPlace.original place) > 0 :=
    henabled
      (PetriNet.NormalizedPlace.original place)
      (by
        simpa [normalizedNet, normalized, PetriNet.normalize] using hflow)
  simp [normalizedNet, normalized, initial, Marking.single] at hpositive

theorem normalized_initial_exit_not_enabled
    [DecidableEq Place]
    (net : WorkflowNet Place Trans) :
    ¬ enabled
      (normalizedNet net)
      (initial (normalizedNet net))
      PetriNet.NormalizedTrans.exit := by
  intro henabled
  have hpositive :=
    (normalized_exit_enabled_iff net (initial (normalizedNet net))).mp
      henabled
  simp [normalizedNet, normalized, initial, Marking.single] at hpositive

theorem normalized_original_marking_enter_not_enabled
    (net : WorkflowNet Place Trans)
    (marking : Marking Place) :
    ¬ enabled
      (normalizedNet net)
      (Marking.normalize marking)
      PetriNet.NormalizedTrans.enter := by
  intro henabled
  have hpositive :=
    (normalized_enter_enabled_iff net (Marking.normalize marking)).mp
      henabled
  simp [Marking.normalize] at hpositive

theorem normalized_final_no_enabled
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (trans : PetriNet.NormalizedTrans Trans) :
    ¬ enabled
      (normalizedNet net)
      (final (normalizedNet net))
      trans := by
  intro henabled
  cases trans with
  | enter =>
      have hpositive :=
        (normalized_enter_enabled_iff net (final (normalizedNet net))).mp
          henabled
      simp [normalizedNet, normalized, final, Marking.single] at hpositive
  | original trans =>
      rcases transition_has_input net trans with ⟨place, hflow⟩
      have hpositive :
          final (normalizedNet net)
            (PetriNet.NormalizedPlace.original place) > 0 :=
        henabled
          (PetriNet.NormalizedPlace.original place)
          (by
            simpa [normalizedNet, normalized, PetriNet.normalize] using hflow)
      simp [normalizedNet, normalized, final, Marking.single] at hpositive
  | exit =>
      have hpositive :=
        (normalized_exit_enabled_iff net (final (normalizedNet net))).mp
          henabled
      simp [normalizedNet, normalized, final, Marking.single] at hpositive

theorem normalized_final_ne_normalize
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (marking : Marking Place) :
    final (normalizedNet net) ≠ Marking.normalize marking := by
  intro hmarking
  have hsink :=
    congrFun hmarking
      (PetriNet.NormalizedPlace.sink :
        PetriNet.NormalizedPlace Place)
  simp [normalizedNet, normalized, final, Marking.single,
    Marking.normalize] at hsink

theorem normalized_initial_ne_final
    [DecidableEq Place]
    (net : WorkflowNet Place Trans) :
    initial (normalizedNet net) ≠ final (normalizedNet net) := by
  intro hmarking
  have hsource :=
    congrFun hmarking
      (PetriNet.NormalizedPlace.source :
        PetriNet.NormalizedPlace Place)
  simp [normalizedNet, normalized, initial, final, Marking.single] at hsource

theorem normalized_final_firingSequence_nil
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    {trace : List (PetriNet.NormalizedTrans Trans)}
    {after : Marking (PetriNet.NormalizedPlace Place)}
    (sequence :
      FiringSequence
        (normalizedNet net)
        (final (normalizedNet net))
        trace
        after) :
    trace = [] ∧ after = final (normalizedNet net) := by
  cases sequence with
  | nil =>
      exact ⟨rfl, rfl⟩
  | cons hfires _ =>
      exact False.elim
        (normalized_final_no_enabled net _ hfires.1)

theorem normalizedReachableShape_step
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hproper : properCompletion net)
    {before after : Marking (PetriNet.NormalizedPlace Place)}
    {trans : PetriNet.NormalizedTrans Trans}
    (hshape : normalizedReachableShape net before)
    (hfires : fires (normalizedNet net) before trans after) :
    normalizedReachableShape net after := by
  rcases hshape with hinitial | hrest
  · subst hinitial
    cases trans with
    | enter =>
        right
        left
        refine
          ⟨initial net, ⟨[], FiringSequence.nil⟩, ?_⟩
        exact hfires.2.trans (normalized_enter_fire_eq net)
    | original trans =>
        exact False.elim
          (normalized_initial_original_not_enabled net trans hfires.1)
    | exit =>
        exact False.elim
          (normalized_initial_exit_not_enabled net hfires.1)
  · rcases hrest with horiginal | hfinal
    · rcases horiginal with ⟨original, horiginalReachable, hbefore⟩
      subst hbefore
      cases trans with
      | enter =>
          exact False.elim
            (normalized_original_marking_enter_not_enabled
              net original hfires.1)
      | original trans =>
          have horiginalEnabled :
              enabled net original trans :=
            (normalized_original_enabled_iff net original trans).mp
              hfires.1
          let originalAfter := fire net original trans
          have horiginalFires :
              fires net original trans originalAfter :=
            ⟨horiginalEnabled, rfl⟩
          have hafter :
              after = Marking.normalize originalAfter := by
            rw [hfires.2, normalized_original_fire_eq]
          right
          left
          refine ⟨originalAfter, ?_, hafter⟩
          rcases horiginalReachable with ⟨trace, sequence⟩
          exact ⟨trace ++ [trans],
            firingSequence_snoc sequence horiginalFires⟩
      | exit =>
          have hsinkPositive :
              original net.sink > 0 :=
            (normalized_exit_enabled_iff net
              (Marking.normalize original)).mp hfires.1
          have horiginalFinal :
              original = final net :=
            hproper original horiginalReachable hsinkPositive
          subst horiginalFinal
          right
          right
          exact hfires.2.trans (normalized_exit_fires net).2.symm
    · subst hfinal
      exact False.elim (normalized_final_no_enabled net trans hfires.1)

theorem normalizedReachableShape_of_firingSequence
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hproper : properCompletion net)
    {before after : Marking (PetriNet.NormalizedPlace Place)}
    {trace : List (PetriNet.NormalizedTrans Trans)}
    (hshape : normalizedReachableShape net before)
    (sequence :
      FiringSequence (normalizedNet net) before trace after) :
    normalizedReachableShape net after := by
  induction sequence with
  | nil =>
      exact hshape
  | cons hfires _ ih =>
      exact ih (normalizedReachableShape_step net hproper hshape hfires)

theorem normalizedReachableShape_of_reachable
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hproper : properCompletion net)
    {marking : Marking (PetriNet.NormalizedPlace Place)}
    (hreachable :
      reachable
        (normalizedNet net)
        (initial (normalizedNet net))
        marking) :
    normalizedReachableShape net marking := by
  rcases hreachable with ⟨trace, sequence⟩
  exact
    normalizedReachableShape_of_firingSequence
      net hproper (Or.inl rfl) sequence

theorem normalized_optionToComplete_of_original
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hcomplete : optionToComplete net)
    (hproper : properCompletion net) :
    optionToComplete (normalizedNet net) := by
  intro marking hreachable
  have hshape :=
    normalizedReachableShape_of_reachable net hproper hreachable
  rcases hshape with hinitial | hrest
  · subst hinitial
    exact normalized_complete_from_initial net hcomplete
  · rcases hrest with horiginal | hfinal
    · rcases horiginal with ⟨original, horiginalReachable, hmarking⟩
      subst hmarking
      exact normalized_complete_from_original_marking
        net hcomplete horiginalReachable
    · subst hfinal
      exact ⟨[], FiringSequence.nil⟩

theorem normalized_optionToComplete_of_sound
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hsound : sound net) :
    optionToComplete (normalizedNet net) :=
  normalized_optionToComplete_of_original
    net hsound.2.1 hsound.2.2

theorem normalized_properCompletion_of_original
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hproper : properCompletion net) :
    properCompletion (normalizedNet net) := by
  intro marking hreachable hsinkPositive
  have hshape :=
    normalizedReachableShape_of_reachable net hproper hreachable
  rcases hshape with hinitial | hrest
  · subst hinitial
    simp [normalizedNet, normalized, initial, Marking.single] at hsinkPositive
  · rcases hrest with horiginal | hfinal
    · rcases horiginal with ⟨original, _horiginalReachable, hmarking⟩
      subst hmarking
      simp [normalizedNet, normalized, Marking.normalize] at hsinkPositive
    · exact hfinal

theorem normalized_safe_of_original
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hsafe : safe net)
    (hproper : properCompletion net) :
    safe (normalizedNet net) := by
  intro marking hreachable place
  have hshape :=
    normalizedReachableShape_of_reachable net hproper hreachable
  rcases hshape with hinitial | hrest
  · subst hinitial
    cases place with
    | source =>
        simp [normalizedNet, normalized, initial, Marking.single]
    | original place =>
        simp [normalizedNet, normalized, initial, Marking.single]
    | sink =>
        simp [normalizedNet, normalized, initial, Marking.single]
  · rcases hrest with horiginal | hfinal
    · rcases horiginal with ⟨original, horiginalReachable, hmarking⟩
      subst hmarking
      cases place with
      | source =>
          simp [Marking.normalize]
      | original place =>
          simpa [Marking.normalize] using
            hsafe original horiginalReachable place
      | sink =>
          simp [Marking.normalize]
    · subst hfinal
      cases place with
      | source =>
          simp [normalizedNet, normalized, final, Marking.single]
      | original place =>
          simp [normalizedNet, normalized, final, Marking.single]
      | sink =>
          simp [normalizedNet, normalized, final, Marking.single]

theorem normalized_exit_enabled_at_final
    [DecidableEq Place]
    (net : WorkflowNet Place Trans) :
    enabled
      (normalizedNet net)
      (Marking.normalize (final net))
      PetriNet.NormalizedTrans.exit := by
  exact
    (normalized_exit_enabled_iff net (Marking.normalize (final net))).mpr
      (by simp [final, Marking.single, Marking.normalize])

theorem normalized_noDeadTransitions_of_original
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hnoDead : noDeadTransitions net)
    (hcomplete : optionToComplete net) :
    noDeadTransitions (normalizedNet net) := by
  intro trans
  cases trans with
  | enter =>
      refine
        ⟨initial (normalizedNet net),
          ⟨[], FiringSequence.nil⟩, ?_⟩
      exact
        (normalized_enter_enabled_iff
          net (initial (normalizedNet net))).mpr
          (by
            change
              Marking.single
                  (PetriNet.NormalizedPlace.source :
                    PetriNet.NormalizedPlace Place)
                PetriNet.NormalizedPlace.source > 0
            simp [Marking.single])
  | original trans =>
      rcases hnoDead trans with ⟨marking, hreachable, henabled⟩
      exact
        ⟨Marking.normalize marking,
          normalized_reachable_of_original net hreachable,
          (normalized_original_enabled_iff net marking trans).mpr
            henabled⟩
  | exit =>
      have hfinalReachable :
          reachable
            (normalizedNet net)
            (initial (normalizedNet net))
            (Marking.normalize (final net)) :=
        normalized_reachable_of_original
          net
          (hcomplete (initial net) ⟨[], FiringSequence.nil⟩)
      exact
        ⟨Marking.normalize (final net),
          hfinalReachable,
          normalized_exit_enabled_at_final net⟩

theorem normalized_noDeadTransitions_of_sound
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hsound : sound net) :
    noDeadTransitions (normalizedNet net) :=
  normalized_noDeadTransitions_of_original net
    hsound.1 hsound.2.1

theorem normalized_sound_of_original
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hsound : sound net) :
    sound (normalizedNet net) :=
  ⟨normalized_noDeadTransitions_of_sound net hsound,
    normalized_optionToComplete_of_sound net hsound,
    normalized_properCompletion_of_original net hsound.2.2⟩

theorem normalized_safeAndSound_of_original
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (hsafeSound : safeAndSound net) :
    safeAndSound (normalizedNet net) :=
  ⟨normalized_safe_of_original net hsafeSound.1 hsafeSound.2.2.2,
    normalized_sound_of_original net hsafeSound.2⟩

theorem restricted_initial_eq
    [DecidableEq Place]
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (restricted :
      WorkflowNet {place : Place // places place} {trans : Trans // transitions trans})
    (hsource : restricted.source.val = original.source) :
    Marking.restrict (initial original) = initial restricted := by
  rw [initial, initial, ← hsource]
  exact Marking.restrict_single restricted.source

theorem restricted_final_eq
    [DecidableEq Place]
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (restricted :
      WorkflowNet {place : Place // places place} {trans : Trans // transitions trans})
    (hsink : restricted.sink.val = original.sink) :
    Marking.restrict (final original) = final restricted := by
  rw [final, final, ← hsink]
  exact Marking.restrict_single restricted.sink

theorem restricted_initial_extend_eq
    [DecidableEq Place]
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (restricted :
      WorkflowNet {place : Place // places place} {trans : Trans // transitions trans})
    (hsource : restricted.source.val = original.source) :
    Marking.extend (initial restricted) = initial original := by
  rw [initial, initial, Marking.extend_single, hsource]

theorem restricted_final_extend_eq
    [DecidableEq Place]
    {places : Set Place}
    {transitions : Set Trans}
    (original : WorkflowNet Place Trans)
    (restricted :
      WorkflowNet {place : Place // places place} {trans : Trans // transitions trans})
    (hsink : restricted.sink.val = original.sink) :
    Marking.extend (final restricted) = final original := by
  rw [final, final, Marking.extend_single, hsink]

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

theorem restricted_firingSequence_lift_initial_final
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
    {trace : List {trans : Trans // transitions trans}}
    (sequence :
      FiringSequence restricted (initial restricted) trace (final restricted)) :
    FiringSequence
      original
      (initial original)
      (trace.map Subtype.val)
      (final original) := by
  have lifted :=
    restricted_firingSequence_lift
      original restricted hplaceToTrans htransToPlace
      hpreset hpostset sequence
  simpa [
    restricted_initial_extend_eq original restricted hsource,
    restricted_final_extend_eq original restricted hsink] using lifted

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

theorem restricted_firingSequence_restrict_initial_final
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
    {trace : List {trans : Trans // transitions trans}}
    (sequence :
      FiringSequence
        original
        (initial original)
        (trace.map Subtype.val)
        (final original)) :
    FiringSequence restricted (initial restricted) trace (final restricted) := by
  have restrictedSequence :=
    restricted_firingSequence_restrict
      original restricted hplaceToTrans htransToPlace sequence
  simpa [
    restricted_initial_eq original restricted hsource,
    restricted_final_eq original restricted hsink] using restrictedSequence

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
