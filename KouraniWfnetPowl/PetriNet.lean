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

end Path

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

end WorkflowNet

end KouraniWfnetPowl
