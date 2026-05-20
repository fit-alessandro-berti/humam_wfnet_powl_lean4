import KouraniWfnetPowl.PetriNet
import KouraniWfnetPowl.Powl

namespace KouraniWfnetPowl

structure Partition (alpha : Type u) where
  parts : List (Set alpha)
  covers : ∀ item, ∃ part, part ∈ parts ∧ part item
  disjoint :
    ∀ {left right item},
      left ∈ parts ->
      right ∈ parts ->
      left item ->
      right item ->
      left = right
  nonempty : ∀ part, part ∈ parts -> ∃ item, part item

namespace Partition

def hasAtLeastTwoParts (partition : Partition alpha) : Prop :=
  ∃ left right,
    left ∈ partition.parts ∧
    right ∈ partition.parts ∧
    left ≠ right

def samePart (partition : Partition alpha) (left right : alpha) : Prop :=
  ∃ part, part ∈ partition.parts ∧ part left ∧ part right

theorem samePart_refl (partition : Partition alpha) (item : alpha) :
    samePart partition item item := by
  rcases partition.covers item with ⟨part, hmem, hpart⟩
  exact ⟨part, hmem, hpart, hpart⟩

theorem samePart_symm
    (partition : Partition alpha)
    {left right : alpha}
    (h : samePart partition left right) :
    samePart partition right left := by
  rcases h with ⟨part, hmem, hleft, hright⟩
  exact ⟨part, hmem, hright, hleft⟩

end Partition

namespace Patterns

variable {Place : Type u} {Trans : Type v}

def isSilent
    {Activity : Type w}
    (label : Trans -> TransitionLabel Activity)
    (trans : Trans) : Prop :=
  label trans = TransitionLabel.silent

def xorPattern
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans) : Prop :=
  partition.hasAtLeastTwoParts ∧
  ∀ left right,
    PetriNet.transitionReachable net.toPetriNet left right ->
      partition.samePart left right

def xorProjection
    (net : WorkflowNet Place Trans)
    (part : Set Trans) : PetriNet Place Trans :=
  PetriNet.projectedFlow
    net.toPetriNet
    (PetriNet.placesTouching net.toPetriNet part)
    part

def xorProjectionRestricted
    (net : WorkflowNet Place Trans)
    (part : Set Trans) :
    PetriNet
      {place : Place // PetriNet.placesTouching net.toPetriNet part place}
      {trans : Trans // part trans} :=
  PetriNet.restrict
    net.toPetriNet
    (PetriNet.placesTouching net.toPetriNet part)
    part

theorem xorProjection_placeToTrans_iff
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (place : Place)
    (trans : Trans) :
    (xorProjection net part).placeToTrans place trans ↔
      PetriNet.placesTouching net.toPetriNet part place ∧
      part trans ∧
      net.placeToTrans place trans :=
  Iff.rfl

theorem xorProjection_transToPlace_iff
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (trans : Trans)
    (place : Place) :
    (xorProjection net part).transToPlace trans place ↔
      part trans ∧
      PetriNet.placesTouching net.toPetriNet part place ∧
      net.transToPlace trans place :=
  Iff.rfl

theorem xorProjection_flow_original
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    {first second : PetriNet.Node Place Trans}
    (hflow : PetriNet.flow (xorProjection net part) first second) :
    PetriNet.flow net.toPetriNet first second :=
  PetriNet.projectedFlow_flow_original
    net.toPetriNet
    (PetriNet.placesTouching net.toPetriNet part)
    part
    hflow

theorem xorProjection_path_original
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    {source target : PetriNet.Node Place Trans}
    (path : PetriNet.Path (xorProjection net part) source target) :
    PetriNet.Path net.toPetriNet source target :=
  PetriNet.projectedFlow_path_original
    net.toPetriNet
    (PetriNet.placesTouching net.toPetriNet part)
    part
    path

theorem xorProjectionRestricted_placeToTrans_iff
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (place : {place : Place // PetriNet.placesTouching net.toPetriNet part place})
    (trans : {trans : Trans // part trans}) :
    (xorProjectionRestricted net part).placeToTrans place trans ↔
      net.placeToTrans place.val trans.val :=
  Iff.rfl

theorem xorProjectionRestricted_transToPlace_iff
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (trans : {trans : Trans // part trans})
    (place : {place : Place // PetriNet.placesTouching net.toPetriNet part place}) :
    (xorProjectionRestricted net part).transToPlace trans place ↔
      net.transToPlace trans.val place.val :=
  Iff.rfl

theorem xorProjectionRestricted_flow_original
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    {first second :
      PetriNet.Node
        {place : Place // PetriNet.placesTouching net.toPetriNet part place}
        {trans : Trans // part trans}}
    (hflow : PetriNet.flow (xorProjectionRestricted net part) first second) :
    PetriNet.flow
      net.toPetriNet
      (PetriNet.restrictedNode first)
      (PetriNet.restrictedNode second) :=
  PetriNet.restrict_flow_original
    net.toPetriNet
    (PetriNet.placesTouching net.toPetriNet part)
    part
    hflow

theorem xorProjectionRestricted_path_original
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    {source target :
      PetriNet.Node
        {place : Place // PetriNet.placesTouching net.toPetriNet part place}
        {trans : Trans // part trans}}
    (path : PetriNet.Path (xorProjectionRestricted net part) source target) :
    PetriNet.Path
      net.toPetriNet
      (PetriNet.restrictedNode source)
      (PetriNet.restrictedNode target) :=
  PetriNet.restrict_path_original
    net.toPetriNet
    (PetriNet.placesTouching net.toPetriNet part)
    part
    path

theorem xorProjectionRestricted_path_of_pathIn
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    {source target : PetriNet.Node Place Trans}
    (path :
      PetriNet.PathIn
        net.toPetriNet
        (PetriNet.placesTouching net.toPetriNet part)
        part
        source
        target) :
    PetriNet.Path
      (xorProjectionRestricted net part)
      (PetriNet.restrictNode source (PetriNet.PathIn.source_mem path))
      (PetriNet.restrictNode target (PetriNet.PathIn.target_mem path)) :=
  PetriNet.PathIn.to_restrict_path path

def loopPattern
    {Activity : Type w}
    (label : Trans -> TransitionLabel Activity)
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans) : Prop :=
  ∃ doPart redoPart silentPart,
    doPart ∈ partition.parts ∧
    redoPart ∈ partition.parts ∧
    silentPart ∈ partition.parts ∧
    ∃ pdo predo sourceTrans sinkTrans,
      sourceTrans ≠ sinkTrans ∧
      (∀ trans, silentPart trans ↔
        trans = sourceTrans ∨ trans = sinkTrans) ∧
      isSilent label sourceTrans ∧
      isSilent label sinkTrans ∧
      (∀ trans, net.placeToTrans net.source trans ↔ trans = sourceTrans) ∧
      (∀ trans, net.transToPlace trans net.sink ↔ trans = sinkTrans) ∧
      (∀ place, net.placeToTrans place sourceTrans ↔ place = net.source) ∧
      (∀ place, net.transToPlace sourceTrans place ↔ place = pdo) ∧
      (∀ place, net.placeToTrans place sinkTrans ↔ place = predo) ∧
      (∀ place, net.transToPlace sinkTrans place ↔ place = net.sink) ∧
      (∀ trans,
        doPart trans ↔
          PetriNet.reachableTransitionsBetweenPlaces
            net.toPetriNet pdo predo trans) ∧
      (∀ trans,
        redoPart trans ↔
          PetriNet.reachableTransitionsBetweenPlaces
            net.toPetriNet predo pdo trans) ∧
      (∀ trans, doPart trans -> ¬ net.transToPlace trans pdo) ∧
      (∀ trans, redoPart trans -> ¬ net.transToPlace trans predo) ∧
      (∀ trans, doPart trans -> ¬ net.placeToTrans predo trans) ∧
      (∀ trans, redoPart trans -> ¬ net.placeToTrans pdo trans)

def loopProjection
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place) : PetriNet Place Trans where
  placeToTrans := fun place trans =>
    part trans ∧
      ((PetriNet.placesTouching net.toPetriNet part place ∧
          place ≠ startPlace ∧ place ≠ endPlace ∧
          net.placeToTrans place trans) ∨
        (place = net.source ∧ net.placeToTrans startPlace trans))
  transToPlace := fun trans place =>
    part trans ∧
      ((PetriNet.placesTouching net.toPetriNet part place ∧
          place ≠ startPlace ∧ place ≠ endPlace ∧
          net.transToPlace trans place) ∨
        (place = net.sink ∧ net.transToPlace trans endPlace))

theorem loopPattern_part_paths
    {Activity : Type w}
    {label : Trans -> TransitionLabel Activity}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : loopPattern label net partition) :
    ∃ doPart redoPart pdo predo,
      doPart ∈ partition.parts ∧
      redoPart ∈ partition.parts ∧
      (∀ trans, doPart trans ->
        PetriNet.Path net.toPetriNet
          (PetriNet.Node.place pdo)
          (PetriNet.Node.trans trans) ∧
        PetriNet.Path net.toPetriNet
          (PetriNet.Node.trans trans)
          (PetriNet.Node.place predo)) ∧
      (∀ trans, redoPart trans ->
        PetriNet.Path net.toPetriNet
          (PetriNet.Node.place predo)
          (PetriNet.Node.trans trans) ∧
        PetriNet.Path net.toPetriNet
          (PetriNet.Node.trans trans)
          (PetriNet.Node.place pdo)) := by
  rcases hpattern with
    ⟨doPart, redoPart, _silentPart,
      hdoMem, hredoMem, _hsilentMem,
      pdo, predo, _sourceTrans, _sinkTrans,
      _hne, _hsilentSet, _hsourceSilent, _hsinkSilent,
      _hsourcePost, _hsinkPre, _hsourcePre, _hsourceOut,
      _hsinkIn, _hsinkOut,
      hdoReach, hredoReach,
      _hdoNoIn, _hredoNoIn, _hdoNoOut, _hredoNoOut⟩
  refine ⟨doPart, redoPart, pdo, predo, hdoMem, hredoMem, ?_, ?_⟩
  · intro trans hdo
    exact PetriNet.reachableTransitionsBetweenPlaces_paths
      net.toPetriNet
      ((hdoReach trans).mp hdo)
  · intro trans hredo
    exact PetriNet.reachableTransitionsBetweenPlaces_paths
      net.toPetriNet
      ((hredoReach trans).mp hredo)

theorem loopPattern_part_trace_closed
    {Activity : Type w}
    {label : Trans -> TransitionLabel Activity}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : loopPattern label net partition) :
    ∃ doPart redoPart pdo predo,
      doPart ∈ partition.parts ∧
      redoPart ∈ partition.parts ∧
      (∀ trace,
        PetriNet.PlacePathTo net.toPetriNet predo pdo trace ->
          ∀ trans, trans ∈ trace -> doPart trans) ∧
      (∀ trace,
        PetriNet.PlacePathTo net.toPetriNet pdo predo trace ->
          ∀ trans, trans ∈ trace -> redoPart trans) := by
  rcases hpattern with
    ⟨doPart, redoPart, _silentPart,
      hdoMem, hredoMem, _hsilentMem,
      pdo, predo, _sourceTrans, _sinkTrans,
      _hne, _hsilentSet, _hsourceSilent, _hsinkSilent,
      _hsourcePost, _hsinkPre, _hsourcePre, _hsourceOut,
      _hsinkIn, _hsinkOut,
      hdoReach, hredoReach,
      _hdoNoIn, _hredoNoIn, _hdoNoOut, _hredoNoOut⟩
  refine ⟨doPart, redoPart, pdo, predo, hdoMem, hredoMem, ?_, ?_⟩
  · intro trace path trans hmem
    exact (hdoReach trans).mpr
      (PetriNet.reachableTransitionsBetweenPlaces_of_mem_placePath
        net.toPetriNet path hmem)
  · intro trace path trans hmem
    exact (hredoReach trans).mpr
      (PetriNet.reachableTransitionsBetweenPlaces_of_mem_placePath
        net.toPetriNet path hmem)

def reachesFromPostset
    (net : WorkflowNet Place Trans)
    (place : Place)
    (target : Trans) : Prop :=
  ∃ first,
    net.placeToTrans place first ∧
    PetriNet.transitionReachable net.toPetriNet first target

def executionOrder
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans) : Rel Nat :=
  fun left right =>
    ∃ leftPart rightPart place,
      Powl.listGet? partition.parts left = some leftPart ∧
      Powl.listGet? partition.parts right = some rightPart ∧
      WorkflowNet.exitPoints net leftPart place ∧
      WorkflowNet.entryPoints net rightPart place

def partialOrderPattern
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans) : Prop :=
  partition.hasAtLeastTwoParts ∧
  (∀ place left right,
    reachesFromPostset net place left ->
    reachesFromPostset net place right ->
      partition.samePart left right) ∧
  Irreflexive (TransGen (executionOrder net partition)) ∧
  (∀ index part leftPlace rightPlace,
    Powl.listGet? partition.parts index = some part ->
    WorkflowNet.entryPoints net part leftPlace ->
    WorkflowNet.entryPoints net part rightPlace ->
      PetriNet.placeEquivalentWrt
        net.toPetriNet part leftPlace rightPlace) ∧
  (∀ index part leftPlace rightPlace,
    Powl.listGet? partition.parts index = some part ->
    WorkflowNet.exitPoints net part leftPlace ->
    WorkflowNet.exitPoints net part rightPlace ->
      PetriNet.placeEquivalentWrt
        net.toPetriNet part leftPlace rightPlace)

def partialOrderPattern_strictPartialOrder
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    (hpattern : partialOrderPattern net partition) :
    StrictPartialOrder Nat :=
  { rel := TransGen (executionOrder net partition)
    irrefl := hpattern.2.2.1
    trans := TransGen.trans }

theorem partialOrderPattern_asymmetric
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    (hpattern : partialOrderPattern net partition) :
    Asymmetric (TransGen (executionOrder net partition)) := by
  change Asymmetric (partialOrderPattern_strictPartialOrder net partition hpattern).rel
  exact (partialOrderPattern_strictPartialOrder net partition hpattern).asymmetric

inductive BoundaryPlace (Place : Type u) where
  | original : Place -> BoundaryPlace Place
  | start : BoundaryPlace Place
  | end_ : BoundaryPlace Place

def partialOrderProjection
    (net : WorkflowNet Place Trans)
    (part : Set Trans) : PetriNet (BoundaryPlace Place) Trans where
  placeToTrans := fun place trans =>
    part trans ∧
      match place with
      | BoundaryPlace.original original =>
          PetriNet.placesTouching net.toPetriNet part original ∧
          ¬ WorkflowNet.entryPoints net part original ∧
          ¬ WorkflowNet.exitPoints net part original ∧
          net.placeToTrans original trans
      | BoundaryPlace.start =>
          ∃ original,
            WorkflowNet.entryPoints net part original ∧
            net.placeToTrans original trans
      | BoundaryPlace.end_ =>
          ∃ original,
            WorkflowNet.exitPoints net part original ∧
            net.placeToTrans original trans
  transToPlace := fun trans place =>
    part trans ∧
      match place with
      | BoundaryPlace.original original =>
          PetriNet.placesTouching net.toPetriNet part original ∧
          ¬ WorkflowNet.entryPoints net part original ∧
          ¬ WorkflowNet.exitPoints net part original ∧
          net.transToPlace trans original
      | BoundaryPlace.start =>
          ∃ original,
            WorkflowNet.entryPoints net part original ∧
            net.transToPlace trans original
      | BoundaryPlace.end_ =>
          ∃ original,
            WorkflowNet.exitPoints net part original ∧
            net.transToPlace trans original

end Patterns

end KouraniWfnetPowl
