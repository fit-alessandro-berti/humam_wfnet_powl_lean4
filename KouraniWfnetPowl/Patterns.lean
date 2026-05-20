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

theorem left_mem_of_samePart_right_mem
    (partition : Partition alpha)
    {part : Set alpha}
    (hpart : part ∈ partition.parts)
    {left right : alpha}
    (hright : part right)
    (hsame : samePart partition left right) :
    part left := by
  rcases hsame with ⟨same, hsameMem, hleft, hrightSame⟩
  have heq : part = same :=
    partition.disjoint hpart hsameMem hright hrightSame
  rw [heq]
  exact hleft

theorem right_mem_of_samePart_left_mem
    (partition : Partition alpha)
    {part : Set alpha}
    (hpart : part ∈ partition.parts)
    {left right : alpha}
    (hleft : part left)
    (hsame : samePart partition left right) :
    part right :=
  left_mem_of_samePart_right_mem
    partition hpart hleft (samePart_symm partition hsame)

theorem mem_of_listGet?
    (partition : Partition alpha)
    {index : Nat}
    {part : Set alpha}
    (hpart : Powl.listGet? partition.parts index = some part) :
    part ∈ partition.parts :=
  Powl.listGet?_mem hpart

theorem nonempty_of_listGet?
    (partition : Partition alpha)
    {index : Nat}
    {part : Set alpha}
    (hpart : Powl.listGet? partition.parts index = some part) :
    ∃ item, part item :=
  partition.nonempty part (mem_of_listGet? partition hpart)

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

theorem xorPattern_part_source_touching
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts) :
    PetriNet.placesTouching net.toPetriNet part net.source := by
  rcases partition.nonempty part hpart with ⟨target, htargetPart⟩
  have hsourcePath :
      PetriNet.Path
        net.toPetriNet
        (PetriNet.Node.place net.source)
        (PetriNet.Node.trans target) :=
    (net.connected (PetriNet.Node.trans target)).1
  rcases PetriNet.path_place_to_transition_first net.toPetriNet hsourcePath with
    ⟨first, hsourceFirst, hfirstReachTarget⟩
  have hsame : partition.samePart first target :=
    hpattern.2 first target hfirstReachTarget
  have hfirstPart : part first :=
    Partition.left_mem_of_samePart_right_mem
      partition hpart htargetPart hsame
  exact PetriNet.placesTouching_of_placeToTrans
    net.toPetriNet hfirstPart hsourceFirst

theorem xorPattern_part_sink_touching
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts) :
    PetriNet.placesTouching net.toPetriNet part net.sink := by
  rcases partition.nonempty part hpart with ⟨source, hsourcePart⟩
  have hsinkPath :
      PetriNet.Path
        net.toPetriNet
        (PetriNet.Node.trans source)
        (PetriNet.Node.place net.sink) :=
    (net.connected (PetriNet.Node.trans source)).2
  rcases PetriNet.path_transition_to_place_last net.toPetriNet hsinkPath with
    ⟨last, hsourceReachLast, hlastSink⟩
  have hsame : partition.samePart source last :=
    hpattern.2 source last hsourceReachLast
  have hlastPart : part last :=
    Partition.right_mem_of_samePart_left_mem
      partition hpart hsourcePart hsame
  exact PetriNet.placesTouching_of_transToPlace
    net.toPetriNet hlastPart hlastSink

theorem xorPattern_node_mem_of_reachable_from_part
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {start : Trans}
    (hstartPart : part start)
    {node : PetriNet.Node Place Trans}
    (path : PetriNet.Path net.toPetriNet (PetriNet.Node.trans start) node) :
    PetriNet.nodeIn
      (PetriNet.placesTouching net.toPetriNet part)
      part
      node := by
  cases node with
  | trans target =>
      have hsame : partition.samePart start target :=
        hpattern.2 start target path
      exact Partition.right_mem_of_samePart_left_mem
        partition hpart hstartPart hsame
  | place place =>
      rcases PetriNet.path_to_place_last_transition net.toPetriNet path with
        hsame | hlast
      · cases hsame
      · rcases hlast with ⟨last, hpath, hlastFlow⟩
        have hsame : partition.samePart start last :=
          hpattern.2 start last hpath
        have hlastPart : part last :=
          Partition.right_mem_of_samePart_left_mem
            partition hpart hstartPart hsame
        exact PetriNet.placesTouching_of_transToPlace
          net.toPetriNet hlastPart hlastFlow

theorem xorPattern_pathIn_from_part_transition
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {start : Trans}
    (hstartPart : part start)
    {node target : PetriNet.Node Place Trans}
    (prior :
      PetriNet.Path net.toPetriNet (PetriNet.Node.trans start) node)
    (path : PetriNet.Path net.toPetriNet node target) :
    PetriNet.PathIn
      net.toPetriNet
      (PetriNet.placesTouching net.toPetriNet part)
      part
      node
      target := by
  induction path with
  | refl =>
      exact PetriNet.PathIn.refl
        (xorPattern_node_mem_of_reachable_from_part
          hpattern hpart hstartPart prior)
  | step hflow rest ih =>
      have hfirst :=
        xorPattern_node_mem_of_reachable_from_part
          hpattern hpart hstartPart prior
      have hsecond :=
        xorPattern_node_mem_of_reachable_from_part
          hpattern hpart hstartPart
          (PetriNet.Path.snoc prior hflow)
      exact PetriNet.PathIn.step hfirst hsecond hflow
        (ih (PetriNet.Path.snoc prior hflow))

theorem xorPattern_pathIn_source_to_part_transition
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {target : Trans}
    (htargetPart : part target) :
    PetriNet.PathIn
      net.toPetriNet
      (PetriNet.placesTouching net.toPetriNet part)
      part
      (PetriNet.Node.place net.source)
      (PetriNet.Node.trans target) := by
  have hsourcePath :
      PetriNet.Path
        net.toPetriNet
        (PetriNet.Node.place net.source)
        (PetriNet.Node.trans target) :=
    (net.connected (PetriNet.Node.trans target)).1
  rcases PetriNet.path_place_to_transition_first net.toPetriNet hsourcePath with
    ⟨first, hsourceFirst, hfirstReachTarget⟩
  have hsame : partition.samePart first target :=
    hpattern.2 first target hfirstReachTarget
  have hfirstPart : part first :=
    Partition.left_mem_of_samePart_right_mem
      partition hpart htargetPart hsame
  have hsourceIn :
      PetriNet.nodeIn
        (PetriNet.placesTouching net.toPetriNet part)
        part
        (PetriNet.Node.place net.source) :=
    xorPattern_part_source_touching hpattern hpart
  have hfirstIn :
      PetriNet.nodeIn
        (PetriNet.placesTouching net.toPetriNet part)
        part
        (PetriNet.Node.trans first) :=
    hfirstPart
  exact PetriNet.PathIn.step hsourceIn hfirstIn hsourceFirst
    (xorPattern_pathIn_from_part_transition
      hpattern hpart hfirstPart PetriNet.Path.refl hfirstReachTarget)

theorem xorPattern_pathIn_part_transition_to_sink
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {source : Trans}
    (hsourcePart : part source) :
    PetriNet.PathIn
      net.toPetriNet
      (PetriNet.placesTouching net.toPetriNet part)
      part
      (PetriNet.Node.trans source)
      (PetriNet.Node.place net.sink) := by
  have hsinkPath :
      PetriNet.Path
        net.toPetriNet
        (PetriNet.Node.trans source)
        (PetriNet.Node.place net.sink) :=
    (net.connected (PetriNet.Node.trans source)).2
  rcases PetriNet.path_transition_to_place_last net.toPetriNet hsinkPath with
    ⟨last, hsourceReachLast, hlastSink⟩
  have hsame : partition.samePart source last :=
    hpattern.2 source last hsourceReachLast
  have hlastPart : part last :=
    Partition.right_mem_of_samePart_left_mem
      partition hpart hsourcePart hsame
  have htoLast :
      PetriNet.PathIn
        net.toPetriNet
        (PetriNet.placesTouching net.toPetriNet part)
        part
        (PetriNet.Node.trans source)
        (PetriNet.Node.trans last) :=
    xorPattern_pathIn_from_part_transition
      hpattern hpart hsourcePart PetriNet.Path.refl hsourceReachLast
  have hlastIn :
      PetriNet.nodeIn
        (PetriNet.placesTouching net.toPetriNet part)
        part
        (PetriNet.Node.trans last) :=
    hlastPart
  have hsinkIn :
      PetriNet.nodeIn
        (PetriNet.placesTouching net.toPetriNet part)
        part
        (PetriNet.Node.place net.sink) :=
    xorPattern_part_sink_touching hpattern hpart
  exact PetriNet.PathIn.snoc htoLast hlastIn hsinkIn hlastSink

theorem xorPattern_restricted_source_to_part_transition
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {target : Trans}
    (htargetPart : part target) :
    PetriNet.Path
      (xorProjectionRestricted net part)
      (PetriNet.Node.place
        ⟨net.source, xorPattern_part_source_touching hpattern hpart⟩)
      (PetriNet.Node.trans ⟨target, htargetPart⟩) := by
  have hpath :=
    xorProjectionRestricted_path_of_pathIn net part
      (xorPattern_pathIn_source_to_part_transition
        hpattern hpart htargetPart)
  simpa [PetriNet.restrictNode] using hpath

theorem xorPattern_restricted_part_transition_to_sink
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {source : Trans}
    (hsourcePart : part source) :
    PetriNet.Path
      (xorProjectionRestricted net part)
      (PetriNet.Node.trans ⟨source, hsourcePart⟩)
      (PetriNet.Node.place
        ⟨net.sink, xorPattern_part_sink_touching hpattern hpart⟩) := by
  have hpath :=
    xorProjectionRestricted_path_of_pathIn net part
      (xorPattern_pathIn_part_transition_to_sink
        hpattern hpart hsourcePart)
  simpa [PetriNet.restrictNode] using hpath

theorem xorPattern_restricted_transition_connected
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    (transition : {trans : Trans // part trans}) :
    PetriNet.Path
        (xorProjectionRestricted net part)
        (PetriNet.Node.place
          ⟨net.source, xorPattern_part_source_touching hpattern hpart⟩)
        (PetriNet.Node.trans transition) ∧
      PetriNet.Path
        (xorProjectionRestricted net part)
        (PetriNet.Node.trans transition)
        (PetriNet.Node.place
          ⟨net.sink, xorPattern_part_sink_touching hpattern hpart⟩) :=
  ⟨xorPattern_restricted_source_to_part_transition
      hpattern hpart transition.property,
    xorPattern_restricted_part_transition_to_sink
      hpattern hpart transition.property⟩

theorem xorPattern_node_mem_of_reaches_part
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {target : Trans}
    (htargetPart : part target)
    {node : PetriNet.Node Place Trans}
    (path : PetriNet.Path net.toPetriNet node (PetriNet.Node.trans target)) :
    PetriNet.nodeIn
      (PetriNet.placesTouching net.toPetriNet part)
      part
      node := by
  cases node with
  | trans source =>
      have hsame : partition.samePart source target :=
        hpattern.2 source target path
      exact Partition.left_mem_of_samePart_right_mem
        partition hpart htargetPart hsame
  | place place =>
      rcases PetriNet.path_place_to_transition_first net.toPetriNet path with
        ⟨first, hplaceFirst, hfirstReachTarget⟩
      have hsame : partition.samePart first target :=
        hpattern.2 first target hfirstReachTarget
      have hfirstPart : part first :=
        Partition.left_mem_of_samePart_right_mem
          partition hpart htargetPart hsame
      exact PetriNet.placesTouching_of_placeToTrans
        net.toPetriNet hfirstPart hplaceFirst

theorem xorPattern_pathIn_to_part_transition_aux
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {target : Trans}
    (htargetPart : part target)
    {node targetNode : PetriNet.Node Place Trans}
    (path : PetriNet.Path net.toPetriNet node targetNode)
    (htargetNode : targetNode = PetriNet.Node.trans target) :
    PetriNet.PathIn
      net.toPetriNet
      (PetriNet.placesTouching net.toPetriNet part)
      part
      node
      targetNode := by
  induction path with
  | refl =>
      subst htargetNode
      exact PetriNet.PathIn.refl htargetPart
  | step hflow rest ih =>
      have hfirst :=
        xorPattern_node_mem_of_reaches_part
          hpattern hpart htargetPart
          (by
            rw [← htargetNode]
            exact PetriNet.Path.step hflow rest)
      have hsecond :=
        xorPattern_node_mem_of_reaches_part
          hpattern hpart htargetPart
          (by
            rw [← htargetNode]
            exact rest)
      exact PetriNet.PathIn.step hfirst hsecond hflow (ih htargetNode)

theorem xorPattern_pathIn_to_part_transition
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {target : Trans}
    (htargetPart : part target)
    {node : PetriNet.Node Place Trans}
    (path : PetriNet.Path net.toPetriNet node (PetriNet.Node.trans target)) :
    PetriNet.PathIn
      net.toPetriNet
      (PetriNet.placesTouching net.toPetriNet part)
      part
      node
      (PetriNet.Node.trans target) :=
  xorPattern_pathIn_to_part_transition_aux
    hpattern hpart htargetPart path rfl

theorem xorPattern_pathIn_prefix_to_part_transition
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {target : Trans}
    (htargetPart : part target)
    {node middle : PetriNet.Node Place Trans}
    (path : PetriNet.Path net.toPetriNet node middle)
    (suffix : PetriNet.Path net.toPetriNet middle (PetriNet.Node.trans target)) :
    PetriNet.PathIn
      net.toPetriNet
      (PetriNet.placesTouching net.toPetriNet part)
      part
      node
      middle := by
  induction path with
  | refl =>
      exact PetriNet.PathIn.refl
        (xorPattern_node_mem_of_reaches_part
          hpattern hpart htargetPart suffix)
  | step hflow rest ih =>
      have hfirst :=
        xorPattern_node_mem_of_reaches_part
          hpattern hpart htargetPart
          (PetriNet.Path.trans (PetriNet.Path.step hflow rest) suffix)
      have hsecond :=
        xorPattern_node_mem_of_reaches_part
          hpattern hpart htargetPart
          (PetriNet.Path.trans rest suffix)
      exact PetriNet.PathIn.step hfirst hsecond hflow (ih suffix)

theorem xorPattern_pathIn_touching_place_connected
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {place : Place}
    (hplace : PetriNet.placesTouching net.toPetriNet part place) :
    PetriNet.PathIn
        net.toPetriNet
        (PetriNet.placesTouching net.toPetriNet part)
        part
        (PetriNet.Node.place net.source)
        (PetriNet.Node.place place) ∧
      PetriNet.PathIn
        net.toPetriNet
        (PetriNet.placesTouching net.toPetriNet part)
        part
        (PetriNet.Node.place place)
        (PetriNet.Node.place net.sink) := by
  rcases hplace with ⟨trans, htransPart, hflow | hflow⟩
  · have hsourcePath :
        PetriNet.Path
          net.toPetriNet
          (PetriNet.Node.place net.source)
          (PetriNet.Node.place place) :=
      (net.connected (PetriNet.Node.place place)).1
    have hsourceToPlace :
        PetriNet.PathIn
          net.toPetriNet
          (PetriNet.placesTouching net.toPetriNet part)
          part
          (PetriNet.Node.place net.source)
          (PetriNet.Node.place place) :=
      xorPattern_pathIn_prefix_to_part_transition
        hpattern hpart htransPart hsourcePath
        (@PetriNet.Path.step Place Trans net.toPetriNet
          (PetriNet.Node.place place)
          (PetriNet.Node.trans trans)
          (PetriNet.Node.trans trans)
          hflow
          PetriNet.Path.refl)
    have hplaceIn :
        PetriNet.nodeIn
          (PetriNet.placesTouching net.toPetriNet part)
          part
          (PetriNet.Node.place place) :=
      ⟨trans, htransPart, Or.inl hflow⟩
    have htransIn :
        PetriNet.nodeIn
          (PetriNet.placesTouching net.toPetriNet part)
          part
          (PetriNet.Node.trans trans) :=
      htransPart
    have hplaceToSink :
        PetriNet.PathIn
          net.toPetriNet
          (PetriNet.placesTouching net.toPetriNet part)
          part
          (PetriNet.Node.place place)
          (PetriNet.Node.place net.sink) :=
      PetriNet.PathIn.step hplaceIn htransIn hflow
        (xorPattern_pathIn_part_transition_to_sink
          hpattern hpart htransPart)
    exact ⟨hsourceToPlace, hplaceToSink⟩
  · have hsourceToPlace :
        PetriNet.PathIn
          net.toPetriNet
          (PetriNet.placesTouching net.toPetriNet part)
          part
          (PetriNet.Node.place net.source)
          (PetriNet.Node.place place) :=
      PetriNet.PathIn.snoc
        (xorPattern_pathIn_source_to_part_transition
          hpattern hpart htransPart)
        htransPart
        ⟨trans, htransPart, Or.inr hflow⟩
        hflow
    have hsinkPath :
        PetriNet.Path
          net.toPetriNet
          (PetriNet.Node.place place)
          (PetriNet.Node.place net.sink) :=
      (net.connected (PetriNet.Node.place place)).2
    have hplaceToSink :
        PetriNet.PathIn
          net.toPetriNet
          (PetriNet.placesTouching net.toPetriNet part)
          part
          (PetriNet.Node.place place)
          (PetriNet.Node.place net.sink) :=
      xorPattern_pathIn_from_part_transition
        hpattern hpart htransPart
        (@PetriNet.Path.step Place Trans net.toPetriNet
          (PetriNet.Node.trans trans)
          (PetriNet.Node.place place)
          (PetriNet.Node.place place)
          hflow
          PetriNet.Path.refl)
        hsinkPath
    exact ⟨hsourceToPlace, hplaceToSink⟩

theorem xorPattern_restricted_place_connected
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    (place :
      {place : Place // PetriNet.placesTouching net.toPetriNet part place}) :
    PetriNet.Path
        (xorProjectionRestricted net part)
        (PetriNet.Node.place
          ⟨net.source, xorPattern_part_source_touching hpattern hpart⟩)
        (PetriNet.Node.place place) ∧
      PetriNet.Path
        (xorProjectionRestricted net part)
        (PetriNet.Node.place place)
        (PetriNet.Node.place
          ⟨net.sink, xorPattern_part_sink_touching hpattern hpart⟩) := by
  have hconnected :=
    xorPattern_pathIn_touching_place_connected
      hpattern hpart place.property
  constructor
  · have hpath :=
      xorProjectionRestricted_path_of_pathIn net part hconnected.1
    simpa [PetriNet.restrictNode] using hpath
  · have hpath :=
      xorProjectionRestricted_path_of_pathIn net part hconnected.2
    simpa [PetriNet.restrictNode] using hpath

theorem xorPattern_restricted_connected
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    (node :
      PetriNet.Node
        {place : Place // PetriNet.placesTouching net.toPetriNet part place}
        {trans : Trans // part trans}) :
    PetriNet.Path
        (xorProjectionRestricted net part)
        (PetriNet.Node.place
          ⟨net.source, xorPattern_part_source_touching hpattern hpart⟩)
        node ∧
      PetriNet.Path
        (xorProjectionRestricted net part)
        node
        (PetriNet.Node.place
          ⟨net.sink, xorPattern_part_sink_touching hpattern hpart⟩) := by
  cases node with
  | place place =>
      exact xorPattern_restricted_place_connected hpattern hpart place
  | trans trans =>
      exact xorPattern_restricted_transition_connected hpattern hpart trans

def xorProjectionWorkflowNet
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts) :
    WorkflowNet
      {place : Place // PetriNet.placesTouching net.toPetriNet part place}
      {trans : Trans // part trans} where
  toPetriNet := xorProjectionRestricted net part
  source := ⟨net.source, xorPattern_part_source_touching hpattern hpart⟩
  sink := ⟨net.sink, xorPattern_part_sink_touching hpattern hpart⟩
  uniqueSource := by
    apply PetriNet.uniqueSource_of_connected_no_in
    · intro trans hflow
      exact ((net.uniqueSource net.source).2 rfl trans.val) hflow
    · exact xorPattern_restricted_connected hpattern hpart
  uniqueSink := by
    apply PetriNet.uniqueSink_of_connected_no_out
    · intro trans hflow
      exact ((net.uniqueSink net.sink).2 rfl trans.val) hflow
    · exact xorPattern_restricted_connected hpattern hpart
  connected := xorPattern_restricted_connected hpattern hpart

theorem xorProjectionWorkflowNet_reachable_lift
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    {marking :
      Marking
        {place : Place // PetriNet.placesTouching net.toPetriNet part place}}
    (hreachable :
      WorkflowNet.reachable
        (xorProjectionWorkflowNet hpattern hpart)
        (WorkflowNet.initial (xorProjectionWorkflowNet hpattern hpart))
        marking) :
    WorkflowNet.reachable net (WorkflowNet.initial net) (Marking.extend marking) :=
  WorkflowNet.restricted_reachable_lift
    net
    (xorProjectionWorkflowNet hpattern hpart)
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
    hreachable

theorem xorProjectionWorkflowNet_safe
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
    {part : Set Trans}
    (hpart : part ∈ partition.parts)
    (hsafe : WorkflowNet.safe net) :
    WorkflowNet.safe (xorProjectionWorkflowNet hpattern hpart) :=
  WorkflowNet.restricted_safe_of_original_safe
    net
    (xorProjectionWorkflowNet hpattern hpart)
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
    hsafe

theorem xorProjectionWorkflowNet_firingSequence_restrict
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
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
      (xorProjectionWorkflowNet hpattern hpart)
      (Marking.restrict before)
      trace
      (Marking.restrict after) :=
  WorkflowNet.restricted_firingSequence_restrict
    net
    (xorProjectionWorkflowNet hpattern hpart)
    (by intro place trans; rfl)
    (by intro trans place; rfl)
    sequence

theorem xorProjectionWorkflowNet_firingSequence_restrict_initial_final
    [DecidableEq Place]
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : xorPattern net partition)
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
      (xorProjectionWorkflowNet hpattern hpart)
      (WorkflowNet.initial (xorProjectionWorkflowNet hpattern hpart))
      trace
      (WorkflowNet.final (xorProjectionWorkflowNet hpattern hpart)) :=
  WorkflowNet.restricted_firingSequence_restrict_initial_final
    net
    (xorProjectionWorkflowNet hpattern hpart)
    (by rfl)
    (by rfl)
    (by intro place trans; rfl)
    (by intro trans place; rfl)
    sequence

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

def loopProjectionPlaces
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place) : Set Place :=
  fun place =>
    place = net.source ∨
      place = net.sink ∨
        (PetriNet.placesTouching net.toPetriNet part place ∧
          place ≠ startPlace ∧
          place ≠ endPlace)

theorem loopProjectionPlaces_source
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place) :
    loopProjectionPlaces net part startPlace endPlace net.source :=
  Or.inl rfl

theorem loopProjectionPlaces_sink
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place) :
    loopProjectionPlaces net part startPlace endPlace net.sink :=
  Or.inr (Or.inl rfl)

theorem loopProjectionPlaces_internal
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hstart : place ≠ startPlace)
    (hend : place ≠ endPlace) :
    loopProjectionPlaces net part startPlace endPlace place :=
  Or.inr (Or.inr ⟨htouching, hstart, hend⟩)

def loopProjectionRestricted
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place) :
    PetriNet
      {place : Place // loopProjectionPlaces net part startPlace endPlace place}
      {trans : Trans // part trans} :=
  PetriNet.restrict
    (loopProjection net part startPlace endPlace)
    (loopProjectionPlaces net part startPlace endPlace)
    part

theorem loopProjectionRestricted_placeToTrans_iff
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place)
    (place :
      {place : Place // loopProjectionPlaces net part startPlace endPlace place})
    (trans : {trans : Trans // part trans}) :
    (loopProjectionRestricted net part startPlace endPlace).placeToTrans
      place trans ↔
        (loopProjection net part startPlace endPlace).placeToTrans
          place.val trans.val :=
  Iff.rfl

theorem loopProjectionRestricted_transToPlace_iff
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place)
    (trans : {trans : Trans // part trans})
    (place :
      {place : Place // loopProjectionPlaces net part startPlace endPlace place}) :
    (loopProjectionRestricted net part startPlace endPlace).transToPlace
      trans place ↔
        (loopProjection net part startPlace endPlace).transToPlace
          trans.val place.val :=
  Iff.rfl

theorem loopProjectionRestricted_flow_original
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place)
    {first second :
      PetriNet.Node
        {place : Place //
          loopProjectionPlaces net part startPlace endPlace place}
        {trans : Trans // part trans}}
    (hflow :
      PetriNet.flow
        (loopProjectionRestricted net part startPlace endPlace)
        first second) :
    PetriNet.flow
      (loopProjection net part startPlace endPlace)
      (PetriNet.restrictedNode first)
      (PetriNet.restrictedNode second) :=
  PetriNet.restrict_flow_original
    (loopProjection net part startPlace endPlace)
    (loopProjectionPlaces net part startPlace endPlace)
    part
    hflow

theorem loopProjectionRestricted_path_original
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place)
    {source target :
      PetriNet.Node
        {place : Place //
          loopProjectionPlaces net part startPlace endPlace place}
        {trans : Trans // part trans}}
    (path :
      PetriNet.Path
        (loopProjectionRestricted net part startPlace endPlace)
        source
        target) :
    PetriNet.Path
      (loopProjection net part startPlace endPlace)
      (PetriNet.restrictedNode source)
      (PetriNet.restrictedNode target) :=
  PetriNet.restrict_path_original
    (loopProjection net part startPlace endPlace)
    (loopProjectionPlaces net part startPlace endPlace)
    part
    path

theorem loopProjectionRestricted_path_of_pathIn
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place)
    {source target : PetriNet.Node Place Trans}
    (path :
      PetriNet.PathIn
        (loopProjection net part startPlace endPlace)
        (loopProjectionPlaces net part startPlace endPlace)
        part
        source
        target) :
    PetriNet.Path
      (loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.restrictNode source (PetriNet.PathIn.source_mem path))
      (PetriNet.restrictNode target (PetriNet.PathIn.target_mem path)) :=
  PetriNet.PathIn.to_restrict_path path

theorem loopProjection_source_placeToTrans
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    {trans : Trans}
    (hpart : part trans)
    (hflow : net.placeToTrans startPlace trans) :
    (loopProjection net part startPlace endPlace).placeToTrans net.source trans :=
  ⟨hpart, Or.inr ⟨rfl, hflow⟩⟩

theorem loopProjection_transToPlace_sink
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    {trans : Trans}
    (hpart : part trans)
    (hflow : net.transToPlace trans endPlace) :
    (loopProjection net part startPlace endPlace).transToPlace trans net.sink :=
  ⟨hpart, Or.inr ⟨rfl, hflow⟩⟩

theorem loopProjection_internal_placeToTrans
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    {trans : Trans}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hstart : place ≠ startPlace)
    (hend : place ≠ endPlace)
    (hflow : net.placeToTrans place trans) :
    (loopProjection net part startPlace endPlace).placeToTrans place trans :=
  ⟨hpart, Or.inl ⟨htouching, hstart, hend, hflow⟩⟩

theorem loopProjection_internal_transToPlace
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    {trans : Trans}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hstart : place ≠ startPlace)
    (hend : place ≠ endPlace)
    (hflow : net.transToPlace trans place) :
    (loopProjection net part startPlace endPlace).transToPlace trans place :=
  ⟨hpart, Or.inl ⟨htouching, hstart, hend, hflow⟩⟩

theorem loopProjectionRestricted_source_placeToTrans
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    {trans : Trans}
    (hpart : part trans)
    (hflow : net.placeToTrans startPlace trans) :
    (loopProjectionRestricted net part startPlace endPlace).placeToTrans
      ⟨net.source, loopProjectionPlaces_source net part startPlace endPlace⟩
      ⟨trans, hpart⟩ := by
  simpa [loopProjectionRestricted, PetriNet.restrict] using
    loopProjection_source_placeToTrans
      (startPlace := startPlace)
      (endPlace := endPlace)
      net hpart hflow

theorem loopProjectionRestricted_transToPlace_sink
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    {trans : Trans}
    (hpart : part trans)
    (hflow : net.transToPlace trans endPlace) :
    (loopProjectionRestricted net part startPlace endPlace).transToPlace
      ⟨trans, hpart⟩
      ⟨net.sink, loopProjectionPlaces_sink net part startPlace endPlace⟩ := by
  simpa [loopProjectionRestricted, PetriNet.restrict] using
    loopProjection_transToPlace_sink
      (startPlace := startPlace)
      (endPlace := endPlace)
      net hpart hflow

theorem loopProjectionRestricted_internal_placeToTrans
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    {trans : Trans}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hstart : place ≠ startPlace)
    (hend : place ≠ endPlace)
    (hflow : net.placeToTrans place trans) :
    (loopProjectionRestricted net part startPlace endPlace).placeToTrans
      ⟨place, loopProjectionPlaces_internal net htouching hstart hend⟩
      ⟨trans, hpart⟩ := by
  simpa [loopProjectionRestricted, PetriNet.restrict] using
    loopProjection_internal_placeToTrans
      (startPlace := startPlace)
      (endPlace := endPlace)
      net hpart htouching hstart hend hflow

theorem loopProjectionRestricted_internal_transToPlace
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    {trans : Trans}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hstart : place ≠ startPlace)
    (hend : place ≠ endPlace)
    (hflow : net.transToPlace trans place) :
    (loopProjectionRestricted net part startPlace endPlace).transToPlace
      ⟨trans, hpart⟩
      ⟨place, loopProjectionPlaces_internal net htouching hstart hend⟩ := by
  simpa [loopProjectionRestricted, PetriNet.restrict] using
    loopProjection_internal_transToPlace
      (startPlace := startPlace)
      (endPlace := endPlace)
      net hpart htouching hstart hend hflow

theorem loopProjection_internal_place_to_transition
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
      (loopProjection net part startPlace endPlace)
      (PetriNet.Node.place place)
      (PetriNet.Node.trans trans) :=
  PetriNet.Path.step
    (by
      simpa [PetriNet.flow] using
        loopProjection_internal_placeToTrans
          (startPlace := startPlace)
          (endPlace := endPlace)
          net hpart htouching hstart hend hflow)
    PetriNet.Path.refl

theorem loopProjection_transition_to_internal_place
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
      (loopProjection net part startPlace endPlace)
      (PetriNet.Node.trans trans)
      (PetriNet.Node.place place) :=
  PetriNet.Path.step
    (by
      simpa [PetriNet.flow] using
        loopProjection_internal_transToPlace
          (startPlace := startPlace)
          (endPlace := endPlace)
          net hpart htouching hstart hend hflow)
    PetriNet.Path.refl

theorem loopProjectionRestricted_internal_place_to_transition
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
      (loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.Node.place
        ⟨place, loopProjectionPlaces_internal net htouching hstart hend⟩)
      (PetriNet.Node.trans ⟨trans, hpart⟩) :=
  PetriNet.Path.step
    (by
      simpa [PetriNet.flow] using
        loopProjectionRestricted_internal_placeToTrans
          (startPlace := startPlace)
          (endPlace := endPlace)
          net hpart htouching hstart hend hflow)
    PetriNet.Path.refl

theorem loopProjectionRestricted_transition_to_internal_place
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
      (loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.Node.trans ⟨trans, hpart⟩)
      (PetriNet.Node.place
        ⟨place, loopProjectionPlaces_internal net htouching hstart hend⟩) :=
  PetriNet.Path.step
    (by
      simpa [PetriNet.flow] using
        loopProjectionRestricted_internal_transToPlace
          (startPlace := startPlace)
          (endPlace := endPlace)
          net hpart htouching hstart hend hflow)
    PetriNet.Path.refl

theorem loopProjection_source_to_transition
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    {trans : Trans}
    (hpart : part trans)
    (hflow : net.placeToTrans startPlace trans) :
    PetriNet.Path
      (loopProjection net part startPlace endPlace)
      (PetriNet.Node.place net.source)
      (PetriNet.Node.trans trans) :=
  PetriNet.Path.step
    (by
      simpa [PetriNet.flow] using
        loopProjection_source_placeToTrans
          (startPlace := startPlace)
          (endPlace := endPlace)
          net hpart hflow)
    PetriNet.Path.refl

theorem loopProjection_transition_to_sink
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    {trans : Trans}
    (hpart : part trans)
    (hflow : net.transToPlace trans endPlace) :
    PetriNet.Path
      (loopProjection net part startPlace endPlace)
      (PetriNet.Node.trans trans)
      (PetriNet.Node.place net.sink) :=
  PetriNet.Path.step
    (by
      simpa [PetriNet.flow] using
        loopProjection_transToPlace_sink
          (startPlace := startPlace)
          (endPlace := endPlace)
          net hpart hflow)
    PetriNet.Path.refl

theorem loopProjection_boundary_path
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    {trans : Trans}
    (hpart : part trans)
    (hstart : net.placeToTrans startPlace trans)
    (hend : net.transToPlace trans endPlace) :
    PetriNet.Path
      (loopProjection net part startPlace endPlace)
      (PetriNet.Node.place net.source)
      (PetriNet.Node.place net.sink) :=
  PetriNet.Path.trans
    (loopProjection_source_to_transition net hpart hstart)
    (loopProjection_transition_to_sink net hpart hend)

theorem loopProjectionRestricted_source_to_transition
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    {trans : Trans}
    (hpart : part trans)
    (hflow : net.placeToTrans startPlace trans) :
    PetriNet.Path
      (loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.Node.place
        ⟨net.source,
          loopProjectionPlaces_source net part startPlace endPlace⟩)
      (PetriNet.Node.trans ⟨trans, hpart⟩) :=
  PetriNet.Path.step
    (by
      simpa [PetriNet.flow, loopProjectionRestricted, PetriNet.restrict] using
        loopProjection_source_placeToTrans
          (startPlace := startPlace)
          (endPlace := endPlace)
          net hpart hflow)
    PetriNet.Path.refl

theorem loopProjectionRestricted_transition_to_sink
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    {trans : Trans}
    (hpart : part trans)
    (hflow : net.transToPlace trans endPlace) :
    PetriNet.Path
      (loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.Node.trans ⟨trans, hpart⟩)
      (PetriNet.Node.place
        ⟨net.sink,
          loopProjectionPlaces_sink net part startPlace endPlace⟩) :=
  PetriNet.Path.step
    (by
      simpa [PetriNet.flow, loopProjectionRestricted, PetriNet.restrict] using
        loopProjection_transToPlace_sink
          (startPlace := startPlace)
          (endPlace := endPlace)
          net hpart hflow)
    PetriNet.Path.refl

theorem loopProjectionRestricted_boundary_path
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    {trans : Trans}
    (hpart : part trans)
    (hstart : net.placeToTrans startPlace trans)
    (hend : net.transToPlace trans endPlace) :
    PetriNet.Path
      (loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.Node.place
        ⟨net.source,
          loopProjectionPlaces_source net part startPlace endPlace⟩)
      (PetriNet.Node.place
        ⟨net.sink,
          loopProjectionPlaces_sink net part startPlace endPlace⟩) :=
  PetriNet.Path.trans
    (loopProjectionRestricted_source_to_transition net hpart hstart)
    (loopProjectionRestricted_transition_to_sink net hpart hend)

theorem loopProjectionRestricted_internal_to_member_transition_of_placePath
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    {trace : List Trans}
    {target : Trans}
    (path : PetriNet.PlacePathTo net.toPetriNet endPlace place trace)
    (hclosed : ∀ trans, trans ∈ trace -> part trans)
    (hnoInStart : ∀ trans, part trans -> ¬ net.transToPlace trans startPlace)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hstart : place ≠ startPlace)
    (hend : place ≠ endPlace)
    (hmem : target ∈ trace) :
    PetriNet.Path
      (loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.Node.place
        ⟨place, loopProjectionPlaces_internal net htouching hstart hend⟩)
      (PetriNet.Node.trans ⟨target, hclosed target hmem⟩) := by
  induction path generalizing target with
  | done =>
      simp at hmem
  | step hnotTarget hplaceToTrans htransToPlace restPath ih =>
      rename_i current next head rest
      have hheadPart : part head := hclosed head (by simp)
      simp at hmem
      rcases hmem with hhead | htail
      · subst hhead
        exact
          loopProjectionRestricted_internal_place_to_transition
            net hheadPart htouching hstart hend hplaceToTrans
      · by_cases hnextEnd : next = endPlace
        · subst hnextEnd
          cases restPath with
          | done =>
              simp at htail
          | step hne _ _ _ =>
              exact False.elim (hne rfl)
        · have hnextTouching :
              PetriNet.placesTouching net.toPetriNet part next :=
            PetriNet.placesTouching_of_transToPlace
              net.toPetriNet hheadPart htransToPlace
          have hnextStart : next ≠ startPlace := by
            intro hsame
            apply hnoInStart head hheadPart
            rwa [hsame] at htransToPlace
          have hclosedTail :
              ∀ trans, trans ∈ rest -> part trans := by
            intro trans htrans
            exact hclosed trans (by simp [htrans])
          have htailPath :=
            ih hclosedTail hnextTouching hnextStart hnextEnd htail
          exact
            PetriNet.Path.trans
              (loopProjectionRestricted_internal_place_to_transition
                net hheadPart htouching hstart hend hplaceToTrans)
              (PetriNet.Path.trans
                (loopProjectionRestricted_transition_to_internal_place
                  net hheadPart hnextTouching hnextStart hnextEnd
                  htransToPlace)
                htailPath)

theorem loopProjectionRestricted_source_to_member_transition_of_placePath
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    {trace : List Trans}
    {target : Trans}
    (path : PetriNet.PlacePathTo net.toPetriNet endPlace startPlace trace)
    (hclosed : ∀ trans, trans ∈ trace -> part trans)
    (hnoInStart : ∀ trans, part trans -> ¬ net.transToPlace trans startPlace)
    (hmem : target ∈ trace) :
    PetriNet.Path
      (loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.Node.place
        ⟨net.source,
          loopProjectionPlaces_source net part startPlace endPlace⟩)
      (PetriNet.Node.trans ⟨target, hclosed target hmem⟩) := by
  induction path generalizing target with
  | done =>
      simp at hmem
  | step hnotTarget hplaceToTrans htransToPlace restPath ih =>
      rename_i current next head rest
      have hheadPart : part head := hclosed head (by simp)
      simp at hmem
      rcases hmem with hhead | htail
      · subst hhead
        exact loopProjectionRestricted_source_to_transition
          net hheadPart hplaceToTrans
      · by_cases hnextEnd : next = endPlace
        · subst hnextEnd
          cases restPath with
          | done =>
              simp at htail
          | step hne _ _ _ =>
              exact False.elim (hne rfl)
        · have hnextTouching :
              PetriNet.placesTouching net.toPetriNet part next :=
            PetriNet.placesTouching_of_transToPlace
              net.toPetriNet hheadPart htransToPlace
          have hnextStart : next ≠ current := by
            intro hsame
            apply hnoInStart head hheadPart
            rwa [hsame] at htransToPlace
          have hclosedTail :
              ∀ trans, trans ∈ rest -> part trans := by
            intro trans htrans
            exact hclosed trans (by simp [htrans])
          have htailPath :=
            loopProjectionRestricted_internal_to_member_transition_of_placePath
              net restPath hclosedTail hnoInStart hnextTouching
              hnextStart hnextEnd htail
          exact
            PetriNet.Path.trans
              (loopProjectionRestricted_source_to_transition
                net hheadPart hplaceToTrans)
              (PetriNet.Path.trans
                (loopProjectionRestricted_transition_to_internal_place
                  net hheadPart hnextTouching hnextStart hnextEnd
                  htransToPlace)
                htailPath)

theorem loopProjectionRestricted_internal_to_sink_of_placePath
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    {trace : List Trans}
    (path : PetriNet.PlacePathTo net.toPetriNet endPlace place trace)
    (hclosed : ∀ trans, trans ∈ trace -> part trans)
    (hnoInStart : ∀ trans, part trans -> ¬ net.transToPlace trans startPlace)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hstart : place ≠ startPlace)
    (hend : place ≠ endPlace) :
    PetriNet.Path
      (loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.Node.place
        ⟨place, loopProjectionPlaces_internal net htouching hstart hend⟩)
      (PetriNet.Node.place
        ⟨net.sink,
          loopProjectionPlaces_sink net part startPlace endPlace⟩) := by
  induction path with
  | done =>
      exact False.elim (hend rfl)
  | step hnotTarget hplaceToTrans htransToPlace restPath ih =>
      rename_i current next head rest
      have hheadPart : part head := hclosed head (by simp)
      by_cases hnextEnd : next = endPlace
      · exact
          PetriNet.Path.trans
            (loopProjectionRestricted_internal_place_to_transition
              net hheadPart htouching hstart hend hplaceToTrans)
            (loopProjectionRestricted_transition_to_sink
              net hheadPart (by rwa [hnextEnd] at htransToPlace))
      · have hnextTouching :
            PetriNet.placesTouching net.toPetriNet part next :=
          PetriNet.placesTouching_of_transToPlace
            net.toPetriNet hheadPart htransToPlace
        have hnextStart : next ≠ startPlace := by
          intro hsame
          apply hnoInStart head hheadPart
          rwa [hsame] at htransToPlace
        have hclosedTail :
            ∀ trans, trans ∈ rest -> part trans := by
          intro trans htrans
          exact hclosed trans (by simp [htrans])
        have htailPath :=
          ih hclosedTail hnextTouching hnextStart hnextEnd
        exact
          PetriNet.Path.trans
            (loopProjectionRestricted_internal_place_to_transition
              net hheadPart htouching hstart hend hplaceToTrans)
            (PetriNet.Path.trans
              (loopProjectionRestricted_transition_to_internal_place
                net hheadPart hnextTouching hnextStart hnextEnd
                htransToPlace)
              htailPath)

theorem loopProjectionRestricted_member_transition_to_sink_of_placePath
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    {trace : List Trans}
    {target : Trans}
    (path : PetriNet.PlacePathTo net.toPetriNet endPlace place trace)
    (hclosed : ∀ trans, trans ∈ trace -> part trans)
    (hnoInStart : ∀ trans, part trans -> ¬ net.transToPlace trans startPlace)
    (hmem : target ∈ trace) :
    PetriNet.Path
      (loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.Node.trans ⟨target, hclosed target hmem⟩)
      (PetriNet.Node.place
        ⟨net.sink,
          loopProjectionPlaces_sink net part startPlace endPlace⟩) := by
  induction path generalizing target with
  | done =>
      simp at hmem
  | step hnotTarget hplaceToTrans htransToPlace restPath ih =>
      rename_i current next head rest
      have hheadPart : part head := hclosed head (by simp)
      simp at hmem
      rcases hmem with hhead | htail
      · subst hhead
        by_cases hnextEnd : next = endPlace
        · exact loopProjectionRestricted_transition_to_sink
            net hheadPart (by rwa [hnextEnd] at htransToPlace)
        · have hnextTouching :
              PetriNet.placesTouching net.toPetriNet part next :=
            PetriNet.placesTouching_of_transToPlace
              net.toPetriNet hheadPart htransToPlace
          have hnextStart : next ≠ startPlace := by
            intro hsame
            apply hnoInStart target hheadPart
            rwa [hsame] at htransToPlace
          have hclosedTail :
              ∀ trans, trans ∈ rest -> part trans := by
            intro trans htrans
            exact hclosed trans (by simp [htrans])
          exact
            PetriNet.Path.trans
              (loopProjectionRestricted_transition_to_internal_place
                net hheadPart hnextTouching hnextStart hnextEnd
                htransToPlace)
              (loopProjectionRestricted_internal_to_sink_of_placePath
                net restPath hclosedTail hnoInStart
                hnextTouching hnextStart hnextEnd)
      · have hclosedTail :
            ∀ trans, trans ∈ rest -> part trans := by
          intro trans htrans
          exact hclosed trans (by simp [htrans])
        exact ih hclosedTail htail

theorem loopProjectionRestricted_source_to_internal_place_of_part_transition
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    {trans : Trans}
    (hpartReach :
      ∀ candidate,
        part candidate ↔
          PetriNet.reachableTransitionsBetweenPlaces
            net.toPetriNet startPlace endPlace candidate)
    (hnoInStart : ∀ candidate, part candidate ->
      ¬ net.transToPlace candidate startPlace)
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hstart : place ≠ startPlace)
    (hend : place ≠ endPlace)
    (hflow : net.transToPlace trans place) :
    PetriNet.Path
      (loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.Node.place
        ⟨net.source,
          loopProjectionPlaces_source net part startPlace endPlace⟩)
      (PetriNet.Node.place
        ⟨place, loopProjectionPlaces_internal net htouching hstart hend⟩) := by
  rcases (hpartReach trans).mp hpart with ⟨trace, path, hmem⟩
  have hclosed :
      ∀ candidate, candidate ∈ trace -> part candidate := by
    intro candidate hcandidate
    exact (hpartReach candidate).mpr ⟨trace, path, hcandidate⟩
  exact
    PetriNet.Path.trans
      (loopProjectionRestricted_source_to_member_transition_of_placePath
        net path hclosed hnoInStart hmem)
      (loopProjectionRestricted_transition_to_internal_place
        net (hclosed trans hmem) htouching hstart hend hflow)

theorem loopProjectionRestricted_internal_place_to_sink_of_part_transition
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace place : Place}
    {trans : Trans}
    (hpartReach :
      ∀ candidate,
        part candidate ↔
          PetriNet.reachableTransitionsBetweenPlaces
            net.toPetriNet startPlace endPlace candidate)
    (hnoInStart : ∀ candidate, part candidate ->
      ¬ net.transToPlace candidate startPlace)
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hstart : place ≠ startPlace)
    (hend : place ≠ endPlace)
    (hflow : net.placeToTrans place trans) :
    PetriNet.Path
      (loopProjectionRestricted net part startPlace endPlace)
      (PetriNet.Node.place
        ⟨place, loopProjectionPlaces_internal net htouching hstart hend⟩)
      (PetriNet.Node.place
        ⟨net.sink,
          loopProjectionPlaces_sink net part startPlace endPlace⟩) := by
  rcases (hpartReach trans).mp hpart with ⟨trace, path, hmem⟩
  have hclosed :
      ∀ candidate, candidate ∈ trace -> part candidate := by
    intro candidate hcandidate
    exact (hpartReach candidate).mpr ⟨trace, path, hcandidate⟩
  exact
    PetriNet.Path.trans
      (loopProjectionRestricted_internal_place_to_transition
        net (hclosed trans hmem) htouching hstart hend hflow)
      (loopProjectionRestricted_member_transition_to_sink_of_placePath
        net path hclosed hnoInStart hmem)

theorem loopProjectionRestricted_source_no_in
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    (hsourceSink : net.source ≠ net.sink)
    (trans : {trans : Trans // part trans}) :
    ¬ (loopProjectionRestricted net part startPlace endPlace).transToPlace
      trans
      ⟨net.source,
        loopProjectionPlaces_source net part startPlace endPlace⟩ := by
  intro hflow
  rcases hflow with ⟨_hpart, hcase⟩
  rcases hcase with hinternal | hsink
  · exact ((net.uniqueSource net.source).2 rfl trans.val) hinternal.2.2.2
  · exact hsourceSink hsink.1

theorem loopProjectionRestricted_sink_no_out
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    (hsourceSink : net.source ≠ net.sink)
    (trans : {trans : Trans // part trans}) :
    ¬ (loopProjectionRestricted net part startPlace endPlace).placeToTrans
      ⟨net.sink,
        loopProjectionPlaces_sink net part startPlace endPlace⟩
      trans := by
  intro hflow
  rcases hflow with ⟨_hpart, hcase⟩
  rcases hcase with hinternal | hsource
  · exact ((net.uniqueSink net.sink).2 rfl trans.val) hinternal.2.2.2
  · exact hsourceSink hsource.1.symm

def loopProjectionWorkflowNetOfConnected
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (startPlace endPlace : Place)
    (hsourceSink : net.source ≠ net.sink)
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : Place //
            loopProjectionPlaces net part startPlace endPlace place}
          {trans : Trans // part trans},
        PetriNet.Path
            (loopProjectionRestricted net part startPlace endPlace)
            (PetriNet.Node.place
              ⟨net.source,
                loopProjectionPlaces_source net part startPlace endPlace⟩)
            node ∧
          PetriNet.Path
            (loopProjectionRestricted net part startPlace endPlace)
            node
            (PetriNet.Node.place
              ⟨net.sink,
                loopProjectionPlaces_sink net part startPlace endPlace⟩)) :
    WorkflowNet
      {place : Place //
        loopProjectionPlaces net part startPlace endPlace place}
      {trans : Trans // part trans} :=
  WorkflowNet.ofConnectedNoBoundaryEdges
    (loopProjectionRestricted net part startPlace endPlace)
    ⟨net.source, loopProjectionPlaces_source net part startPlace endPlace⟩
    ⟨net.sink, loopProjectionPlaces_sink net part startPlace endPlace⟩
    (loopProjectionRestricted_source_no_in net hsourceSink)
    (loopProjectionRestricted_sink_no_out net hsourceSink)
    hconnected

theorem loopProjectionRestricted_connected_of_incident_transitions
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {startPlace endPlace : Place}
    (hsourceToSink :
      PetriNet.Path
        (loopProjectionRestricted net part startPlace endPlace)
        (PetriNet.Node.place
          ⟨net.source,
            loopProjectionPlaces_source net part startPlace endPlace⟩)
        (PetriNet.Node.place
          ⟨net.sink,
            loopProjectionPlaces_sink net part startPlace endPlace⟩))
    (htransConnected :
      ∀ trans : {trans : Trans // part trans},
        PetriNet.Path
            (loopProjectionRestricted net part startPlace endPlace)
            (PetriNet.Node.place
              ⟨net.source,
                loopProjectionPlaces_source net part startPlace endPlace⟩)
            (PetriNet.Node.trans trans) ∧
          PetriNet.Path
            (loopProjectionRestricted net part startPlace endPlace)
            (PetriNet.Node.trans trans)
            (PetriNet.Node.place
              ⟨net.sink,
                loopProjectionPlaces_sink net part startPlace endPlace⟩))
    (hplaceConnected :
      ∀ {place : Place},
        (htouching : PetriNet.placesTouching net.toPetriNet part place) ->
        (hstart : place ≠ startPlace) ->
        (hend : place ≠ endPlace) ->
          PetriNet.Path
              (loopProjectionRestricted net part startPlace endPlace)
              (PetriNet.Node.place
                ⟨net.source,
                  loopProjectionPlaces_source
                    net part startPlace endPlace⟩)
              (PetriNet.Node.place
                ⟨place,
                  loopProjectionPlaces_internal
                    net htouching hstart hend⟩) ∧
            PetriNet.Path
              (loopProjectionRestricted net part startPlace endPlace)
              (PetriNet.Node.place
                ⟨place,
                  loopProjectionPlaces_internal
                    net htouching hstart hend⟩)
              (PetriNet.Node.place
                ⟨net.sink,
                  loopProjectionPlaces_sink
                    net part startPlace endPlace⟩)) :
    ∀ node :
      PetriNet.Node
        {place : Place //
          loopProjectionPlaces net part startPlace endPlace place}
        {trans : Trans // part trans},
      PetriNet.Path
          (loopProjectionRestricted net part startPlace endPlace)
          (PetriNet.Node.place
            ⟨net.source,
              loopProjectionPlaces_source net part startPlace endPlace⟩)
          node ∧
        PetriNet.Path
          (loopProjectionRestricted net part startPlace endPlace)
          node
          (PetriNet.Node.place
            ⟨net.sink,
              loopProjectionPlaces_sink net part startPlace endPlace⟩) := by
  intro node
  cases node with
  | place place =>
      rcases place with ⟨place, hplace⟩
      rcases hplace with hsource | hrest
      · cases hsource
        exact ⟨PetriNet.Path.refl, hsourceToSink⟩
      · rcases hrest with hsink | hinternal
        · cases hsink
          exact ⟨hsourceToSink, PetriNet.Path.refl⟩
        · rcases hinternal with ⟨htouching, hstart, hend⟩
          exact hplaceConnected htouching hstart hend
  | trans trans =>
      exact htransConnected trans

theorem loopProjectionRestricted_connected_of_reachable_incident
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
          loopProjectionPlaces net part startPlace endPlace place}
        {trans : Trans // part trans},
      PetriNet.Path
          (loopProjectionRestricted net part startPlace endPlace)
          (PetriNet.Node.place
            ⟨net.source,
              loopProjectionPlaces_source net part startPlace endPlace⟩)
          node ∧
        PetriNet.Path
          (loopProjectionRestricted net part startPlace endPlace)
          node
          (PetriNet.Node.place
            ⟨net.sink,
              loopProjectionPlaces_sink net part startPlace endPlace⟩) := by
  have htransConnected :
      ∀ trans : {trans : Trans // part trans},
        PetriNet.Path
            (loopProjectionRestricted net part startPlace endPlace)
            (PetriNet.Node.place
              ⟨net.source,
                loopProjectionPlaces_source net part startPlace endPlace⟩)
            (PetriNet.Node.trans trans) ∧
          PetriNet.Path
            (loopProjectionRestricted net part startPlace endPlace)
            (PetriNet.Node.trans trans)
            (PetriNet.Node.place
              ⟨net.sink,
                loopProjectionPlaces_sink net part startPlace endPlace⟩) := by
    intro trans
    rcases (hpartReach trans.val).mp trans.property with
      ⟨trace, path, hmem⟩
    have hclosed :
        ∀ candidate, candidate ∈ trace -> part candidate := by
      intro candidate hcandidate
      exact (hpartReach candidate).mpr ⟨trace, path, hcandidate⟩
    constructor
    · have hpath :=
        loopProjectionRestricted_source_to_member_transition_of_placePath
          net path hclosed hnoInStart hmem
      simpa using hpath
    · have hpath :=
        loopProjectionRestricted_member_transition_to_sink_of_placePath
          net path hclosed hnoInStart hmem
      simpa using hpath
  have hsourceToSink :
      PetriNet.Path
        (loopProjectionRestricted net part startPlace endPlace)
        (PetriNet.Node.place
          ⟨net.source,
            loopProjectionPlaces_source net part startPlace endPlace⟩)
        (PetriNet.Node.place
          ⟨net.sink,
            loopProjectionPlaces_sink net part startPlace endPlace⟩) := by
    rcases hnonempty with ⟨trans, hpart⟩
    exact PetriNet.Path.trans
      (htransConnected ⟨trans, hpart⟩).1
      (htransConnected ⟨trans, hpart⟩).2
  have hplaceConnected :
      ∀ {place : Place},
        (htouching : PetriNet.placesTouching net.toPetriNet part place) ->
        (hstart : place ≠ startPlace) ->
        (hend : place ≠ endPlace) ->
          PetriNet.Path
              (loopProjectionRestricted net part startPlace endPlace)
              (PetriNet.Node.place
                ⟨net.source,
                  loopProjectionPlaces_source
                    net part startPlace endPlace⟩)
              (PetriNet.Node.place
                ⟨place,
                  loopProjectionPlaces_internal
                    net htouching hstart hend⟩) ∧
            PetriNet.Path
              (loopProjectionRestricted net part startPlace endPlace)
              (PetriNet.Node.place
                ⟨place,
                  loopProjectionPlaces_internal
                    net htouching hstart hend⟩)
              (PetriNet.Node.place
                ⟨net.sink,
                  loopProjectionPlaces_sink
                    net part startPlace endPlace⟩) := by
    intro place htouching hstart hend
    rcases hincoming htouching hstart hend with
      ⟨inTrans, hinPart, hinFlow⟩
    rcases houtgoing htouching hstart hend with
      ⟨outTrans, houtPart, houtFlow⟩
    constructor
    · exact
        loopProjectionRestricted_source_to_internal_place_of_part_transition
          net hpartReach hnoInStart hinPart htouching hstart hend hinFlow
    · exact
        loopProjectionRestricted_internal_place_to_sink_of_part_transition
          net hpartReach hnoInStart houtPart htouching hstart hend houtFlow
  exact
    loopProjectionRestricted_connected_of_incident_transitions
      net hsourceToSink htransConnected hplaceConnected

def loopProjectionWorkflowNetOfReachableIncident
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
        loopProjectionPlaces net part startPlace endPlace place}
      {trans : Trans // part trans} :=
  loopProjectionWorkflowNetOfConnected
    net part startPlace endPlace hsourceSink
    (loopProjectionRestricted_connected_of_reachable_incident
      (part := part)
      (startPlace := startPlace)
      (endPlace := endPlace)
      net hpartReach hnoInStart hnonempty hincoming houtgoing)

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

theorem loopPattern_projection_restricted_transition_connected
    {Activity : Type w}
    {label : Trans -> TransitionLabel Activity}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : loopPattern label net partition) :
    ∃ doPart redoPart pdo predo,
      doPart ∈ partition.parts ∧
      redoPart ∈ partition.parts ∧
      (∀ trans : {trans : Trans // doPart trans},
        PetriNet.Path
            (loopProjectionRestricted net doPart pdo predo)
            (PetriNet.Node.place
              ⟨net.source,
                loopProjectionPlaces_source net doPart pdo predo⟩)
            (PetriNet.Node.trans trans) ∧
          PetriNet.Path
            (loopProjectionRestricted net doPart pdo predo)
            (PetriNet.Node.trans trans)
            (PetriNet.Node.place
              ⟨net.sink,
                loopProjectionPlaces_sink net doPart pdo predo⟩)) ∧
      (∀ trans : {trans : Trans // redoPart trans},
        PetriNet.Path
            (loopProjectionRestricted net redoPart predo pdo)
            (PetriNet.Node.place
              ⟨net.source,
                loopProjectionPlaces_source net redoPart predo pdo⟩)
            (PetriNet.Node.trans trans) ∧
          PetriNet.Path
            (loopProjectionRestricted net redoPart predo pdo)
            (PetriNet.Node.trans trans)
            (PetriNet.Node.place
              ⟨net.sink,
                loopProjectionPlaces_sink net redoPart predo pdo⟩)) := by
  rcases hpattern with
    ⟨doPart, redoPart, _silentPart,
      hdoMem, hredoMem, _hsilentMem,
      pdo, predo, _sourceTrans, _sinkTrans,
      _hne, _hsilentSet, _hsourceSilent, _hsinkSilent,
      _hsourcePost, _hsinkPre, _hsourcePre, _hsourceOut,
      _hsinkIn, _hsinkOut,
      hdoReach, hredoReach,
      hdoNoIn, hredoNoIn, _hdoNoOut, _hredoNoOut⟩
  refine ⟨doPart, redoPart, pdo, predo, hdoMem, hredoMem, ?_, ?_⟩
  · intro trans
    rcases (hdoReach trans.val).mp trans.property with
      ⟨trace, path, hmem⟩
    have hclosed :
        ∀ candidate, candidate ∈ trace -> doPart candidate := by
      intro candidate hcandidate
      exact (hdoReach candidate).mpr ⟨trace, path, hcandidate⟩
    constructor
    · have hpath :=
        loopProjectionRestricted_source_to_member_transition_of_placePath
          net path hclosed hdoNoIn hmem
      simpa using hpath
    · have hpath :=
        loopProjectionRestricted_member_transition_to_sink_of_placePath
          net path hclosed hdoNoIn hmem
      simpa using hpath
  · intro trans
    rcases (hredoReach trans.val).mp trans.property with
      ⟨trace, path, hmem⟩
    have hclosed :
        ∀ candidate, candidate ∈ trace -> redoPart candidate := by
      intro candidate hcandidate
      exact (hredoReach candidate).mpr ⟨trace, path, hcandidate⟩
    constructor
    · have hpath :=
        loopProjectionRestricted_source_to_member_transition_of_placePath
          net path hclosed hredoNoIn hmem
      simpa using hpath
    · have hpath :=
        loopProjectionRestricted_member_transition_to_sink_of_placePath
          net path hclosed hredoNoIn hmem
      simpa using hpath

theorem loopPattern_projection_restricted_internal_place_directional_connected
    {Activity : Type w}
    {label : Trans -> TransitionLabel Activity}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : loopPattern label net partition) :
    ∃ doPart redoPart pdo predo,
      doPart ∈ partition.parts ∧
      redoPart ∈ partition.parts ∧
        (∀ {place trans}, doPart trans ->
          (htouching : PetriNet.placesTouching net.toPetriNet doPart place) ->
          (hstart : place ≠ pdo) ->
          (hend : place ≠ predo) ->
          net.transToPlace trans place ->
            PetriNet.Path
              (loopProjectionRestricted net doPart pdo predo)
            (PetriNet.Node.place
              ⟨net.source,
                loopProjectionPlaces_source net doPart pdo predo⟩)
              (PetriNet.Node.place
                ⟨place,
                  loopProjectionPlaces_internal net htouching
                    hstart hend⟩)) ∧
        (∀ {place trans}, doPart trans ->
          (htouching : PetriNet.placesTouching net.toPetriNet doPart place) ->
          (hstart : place ≠ pdo) ->
          (hend : place ≠ predo) ->
          net.placeToTrans place trans ->
            PetriNet.Path
              (loopProjectionRestricted net doPart pdo predo)
              (PetriNet.Node.place
                ⟨place,
                  loopProjectionPlaces_internal net htouching
                    hstart hend⟩)
              (PetriNet.Node.place
                ⟨net.sink,
                  loopProjectionPlaces_sink net doPart pdo predo⟩)) ∧
        (∀ {place trans}, redoPart trans ->
          (htouching : PetriNet.placesTouching net.toPetriNet redoPart place) ->
          (hstart : place ≠ predo) ->
          (hend : place ≠ pdo) ->
          net.transToPlace trans place ->
            PetriNet.Path
              (loopProjectionRestricted net redoPart predo pdo)
            (PetriNet.Node.place
              ⟨net.source,
                loopProjectionPlaces_source net redoPart predo pdo⟩)
              (PetriNet.Node.place
                ⟨place,
                  loopProjectionPlaces_internal net htouching
                    hstart hend⟩)) ∧
        (∀ {place trans}, redoPart trans ->
          (htouching : PetriNet.placesTouching net.toPetriNet redoPart place) ->
          (hstart : place ≠ predo) ->
          (hend : place ≠ pdo) ->
          net.placeToTrans place trans ->
            PetriNet.Path
              (loopProjectionRestricted net redoPart predo pdo)
              (PetriNet.Node.place
                ⟨place,
                  loopProjectionPlaces_internal net htouching
                    hstart hend⟩)
              (PetriNet.Node.place
              ⟨net.sink,
                loopProjectionPlaces_sink net redoPart predo pdo⟩)) := by
  rcases hpattern with
    ⟨doPart, redoPart, _silentPart,
      hdoMem, hredoMem, _hsilentMem,
      pdo, predo, _sourceTrans, _sinkTrans,
      _hne, _hsilentSet, _hsourceSilent, _hsinkSilent,
      _hsourcePost, _hsinkPre, _hsourcePre, _hsourceOut,
      _hsinkIn, _hsinkOut,
      hdoReach, hredoReach,
      hdoNoIn, hredoNoIn, _hdoNoOut, _hredoNoOut⟩
  refine
    ⟨doPart, redoPart, pdo, predo, hdoMem, hredoMem,
      ?_, ?_, ?_, ?_⟩
  · intro place trans hpart htouching hstart hend hflow
    exact
      loopProjectionRestricted_source_to_internal_place_of_part_transition
        net hdoReach hdoNoIn hpart htouching hstart hend hflow
  · intro place trans hpart htouching hstart hend hflow
    exact
      loopProjectionRestricted_internal_place_to_sink_of_part_transition
        net hdoReach hdoNoIn hpart htouching hstart hend hflow
  · intro place trans hpart htouching hstart hend hflow
    exact
      loopProjectionRestricted_source_to_internal_place_of_part_transition
        net hredoReach hredoNoIn hpart htouching hstart hend hflow
  · intro place trans hpart htouching hstart hend hflow
    exact
      loopProjectionRestricted_internal_place_to_sink_of_part_transition
        net hredoReach hredoNoIn hpart htouching hstart hend hflow

theorem loopPattern_projection_restricted_internal_place_connected_of_incident_transitions
    {Activity : Type w}
    {label : Trans -> TransitionLabel Activity}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : loopPattern label net partition) :
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
              (loopProjectionRestricted net doPart pdo predo)
              (PetriNet.Node.place
                ⟨net.source,
                  loopProjectionPlaces_source net doPart pdo predo⟩)
              (PetriNet.Node.place
                ⟨place,
                  loopProjectionPlaces_internal net htouching hstart hend⟩) ∧
            PetriNet.Path
              (loopProjectionRestricted net doPart pdo predo)
              (PetriNet.Node.place
                ⟨place,
                  loopProjectionPlaces_internal net htouching hstart hend⟩)
              (PetriNet.Node.place
                ⟨net.sink,
                  loopProjectionPlaces_sink net doPart pdo predo⟩)) ∧
      (∀ {place},
        (htouching : PetriNet.placesTouching net.toPetriNet redoPart place) ->
        (hstart : place ≠ predo) ->
        (hend : place ≠ pdo) ->
        (∃ trans, redoPart trans ∧ net.transToPlace trans place) ->
        (∃ trans, redoPart trans ∧ net.placeToTrans place trans) ->
          PetriNet.Path
              (loopProjectionRestricted net redoPart predo pdo)
              (PetriNet.Node.place
                ⟨net.source,
                  loopProjectionPlaces_source net redoPart predo pdo⟩)
              (PetriNet.Node.place
                ⟨place,
                  loopProjectionPlaces_internal net htouching hstart hend⟩) ∧
            PetriNet.Path
              (loopProjectionRestricted net redoPart predo pdo)
              (PetriNet.Node.place
                ⟨place,
                  loopProjectionPlaces_internal net htouching hstart hend⟩)
              (PetriNet.Node.place
                ⟨net.sink,
                  loopProjectionPlaces_sink net redoPart predo pdo⟩)) := by
  rcases hpattern with
    ⟨doPart, redoPart, _silentPart,
      hdoMem, hredoMem, _hsilentMem,
      pdo, predo, _sourceTrans, _sinkTrans,
      _hne, _hsilentSet, _hsourceSilent, _hsinkSilent,
      _hsourcePost, _hsinkPre, _hsourcePre, _hsourceOut,
      _hsinkIn, _hsinkOut,
      hdoReach, hredoReach,
      hdoNoIn, hredoNoIn, _hdoNoOut, _hredoNoOut⟩
  refine ⟨doPart, redoPart, pdo, predo, hdoMem, hredoMem, ?_, ?_⟩
  · intro place htouching hstart hend hinput houtput
    rcases hinput with ⟨inTrans, hinPart, hinFlow⟩
    rcases houtput with ⟨outTrans, houtPart, houtFlow⟩
    constructor
    · exact
        loopProjectionRestricted_source_to_internal_place_of_part_transition
          net hdoReach hdoNoIn hinPart htouching hstart hend hinFlow
    · exact
        loopProjectionRestricted_internal_place_to_sink_of_part_transition
          net hdoReach hdoNoIn houtPart htouching hstart hend houtFlow
  · intro place htouching hstart hend hinput houtput
    rcases hinput with ⟨inTrans, hinPart, hinFlow⟩
    rcases houtput with ⟨outTrans, houtPart, houtFlow⟩
    constructor
    · exact
        loopProjectionRestricted_source_to_internal_place_of_part_transition
          net hredoReach hredoNoIn hinPart htouching hstart hend hinFlow
    · exact
        loopProjectionRestricted_internal_place_to_sink_of_part_transition
          net hredoReach hredoNoIn houtPart htouching hstart hend houtFlow

theorem loopPattern_projection_restricted_connected_of_internal_incidence
    {Activity : Type w}
    {label : Trans -> TransitionLabel Activity}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : loopPattern label net partition) :
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
              loopProjectionPlaces net doPart pdo predo place}
            {trans : Trans // doPart trans},
          PetriNet.Path
              (loopProjectionRestricted net doPart pdo predo)
              (PetriNet.Node.place
                ⟨net.source,
                  loopProjectionPlaces_source net doPart pdo predo⟩)
              node ∧
            PetriNet.Path
              (loopProjectionRestricted net doPart pdo predo)
              node
              (PetriNet.Node.place
                ⟨net.sink,
                  loopProjectionPlaces_sink net doPart pdo predo⟩)) ∧
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
              loopProjectionPlaces net redoPart predo pdo place}
            {trans : Trans // redoPart trans},
          PetriNet.Path
              (loopProjectionRestricted net redoPart predo pdo)
              (PetriNet.Node.place
                ⟨net.source,
                  loopProjectionPlaces_source net redoPart predo pdo⟩)
              node ∧
            PetriNet.Path
              (loopProjectionRestricted net redoPart predo pdo)
              node
              (PetriNet.Node.place
                ⟨net.sink,
                  loopProjectionPlaces_sink net redoPart predo pdo⟩)) := by
  rcases hpattern with
    ⟨doPart, redoPart, _silentPart,
      hdoMem, hredoMem, _hsilentMem,
      pdo, predo, _sourceTrans, _sinkTrans,
      _hne, _hsilentSet, _hsourceSilent, _hsinkSilent,
      _hsourcePost, _hsinkPre, _hsourcePre, _hsourceOut,
      _hsinkIn, _hsinkOut,
      hdoReach, hredoReach,
      hdoNoIn, hredoNoIn, _hdoNoOut, _hredoNoOut⟩
  refine ⟨doPart, redoPart, pdo, predo, hdoMem, hredoMem, ?_, ?_⟩
  · intro hincoming houtgoing
    exact
      loopProjectionRestricted_connected_of_reachable_incident
        (part := doPart)
        (startPlace := pdo)
        (endPlace := predo)
        net hdoReach hdoNoIn
        (partition.nonempty doPart hdoMem)
        hincoming
        houtgoing
  · intro hincoming houtgoing
    exact
      loopProjectionRestricted_connected_of_reachable_incident
        (part := redoPart)
        (startPlace := predo)
        (endPlace := pdo)
        net hredoReach hredoNoIn
        (partition.nonempty redoPart hredoMem)
        hincoming
        houtgoing

theorem loopPattern_projection_boundary_edges
    {Activity : Type w}
    {label : Trans -> TransitionLabel Activity}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : loopPattern label net partition) :
    ∃ doPart redoPart pdo predo,
      doPart ∈ partition.parts ∧
      redoPart ∈ partition.parts ∧
      (∀ trans, doPart trans ->
        net.placeToTrans pdo trans ->
          (loopProjection net doPart pdo predo).placeToTrans
            net.source trans) ∧
      (∀ trans, doPart trans ->
        net.transToPlace trans predo ->
          (loopProjection net doPart pdo predo).transToPlace
            trans net.sink) ∧
      (∀ trans, redoPart trans ->
        net.placeToTrans predo trans ->
          (loopProjection net redoPart predo pdo).placeToTrans
            net.source trans) ∧
      (∀ trans, redoPart trans ->
        net.transToPlace trans pdo ->
          (loopProjection net redoPart predo pdo).transToPlace
            trans net.sink) := by
  rcases hpattern with
    ⟨doPart, redoPart, _silentPart,
      hdoMem, hredoMem, _hsilentMem,
      pdo, predo, _sourceTrans, _sinkTrans,
      _hne, _hsilentSet, _hsourceSilent, _hsinkSilent,
      _hsourcePost, _hsinkPre, _hsourcePre, _hsourceOut,
      _hsinkIn, _hsinkOut,
      _hdoReach, _hredoReach,
      _hdoNoIn, _hredoNoIn, _hdoNoOut, _hredoNoOut⟩
  refine ⟨doPart, redoPart, pdo, predo, hdoMem, hredoMem, ?_, ?_, ?_, ?_⟩
  · intro trans hdo hflow
    exact loopProjection_source_placeToTrans net hdo hflow
  · intro trans hdo hflow
    exact loopProjection_transToPlace_sink net hdo hflow
  · intro trans hredo hflow
    exact loopProjection_source_placeToTrans net hredo hflow
  · intro trans hredo hflow
    exact loopProjection_transToPlace_sink net hredo hflow

theorem loopPattern_projection_boundary_paths
    {Activity : Type w}
    {label : Trans -> TransitionLabel Activity}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : loopPattern label net partition) :
    ∃ doPart redoPart pdo predo,
      doPart ∈ partition.parts ∧
      redoPart ∈ partition.parts ∧
      (∀ trans, doPart trans ->
        net.placeToTrans pdo trans ->
          PetriNet.Path
            (loopProjection net doPart pdo predo)
            (PetriNet.Node.place net.source)
            (PetriNet.Node.trans trans)) ∧
      (∀ trans, doPart trans ->
        net.transToPlace trans predo ->
          PetriNet.Path
            (loopProjection net doPart pdo predo)
            (PetriNet.Node.trans trans)
            (PetriNet.Node.place net.sink)) ∧
      (∀ trans, doPart trans ->
        net.placeToTrans pdo trans ->
        net.transToPlace trans predo ->
          PetriNet.Path
            (loopProjection net doPart pdo predo)
            (PetriNet.Node.place net.source)
            (PetriNet.Node.place net.sink)) ∧
      (∀ trans, redoPart trans ->
        net.placeToTrans predo trans ->
          PetriNet.Path
            (loopProjection net redoPart predo pdo)
            (PetriNet.Node.place net.source)
            (PetriNet.Node.trans trans)) ∧
      (∀ trans, redoPart trans ->
        net.transToPlace trans pdo ->
          PetriNet.Path
            (loopProjection net redoPart predo pdo)
            (PetriNet.Node.trans trans)
            (PetriNet.Node.place net.sink)) ∧
      (∀ trans, redoPart trans ->
        net.placeToTrans predo trans ->
        net.transToPlace trans pdo ->
          PetriNet.Path
            (loopProjection net redoPart predo pdo)
            (PetriNet.Node.place net.source)
            (PetriNet.Node.place net.sink)) := by
  rcases hpattern with
    ⟨doPart, redoPart, _silentPart,
      hdoMem, hredoMem, _hsilentMem,
      pdo, predo, _sourceTrans, _sinkTrans,
      _hne, _hsilentSet, _hsourceSilent, _hsinkSilent,
      _hsourcePost, _hsinkPre, _hsourcePre, _hsourceOut,
      _hsinkIn, _hsinkOut,
      _hdoReach, _hredoReach,
      _hdoNoIn, _hredoNoIn, _hdoNoOut, _hredoNoOut⟩
  refine
    ⟨doPart, redoPart, pdo, predo, hdoMem, hredoMem,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro trans hdo hflow
    exact loopProjection_source_to_transition net hdo hflow
  · intro trans hdo hflow
    exact loopProjection_transition_to_sink net hdo hflow
  · intro trans hdo hstart hend
    exact loopProjection_boundary_path net hdo hstart hend
  · intro trans hredo hflow
    exact loopProjection_source_to_transition net hredo hflow
  · intro trans hredo hflow
    exact loopProjection_transition_to_sink net hredo hflow
  · intro trans hredo hstart hend
    exact loopProjection_boundary_path net hredo hstart hend

theorem loopPattern_projection_restricted_boundary_paths
    {Activity : Type w}
    {label : Trans -> TransitionLabel Activity}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : loopPattern label net partition) :
    ∃ doPart redoPart pdo predo,
      doPart ∈ partition.parts ∧
      redoPart ∈ partition.parts ∧
      (∀ trans, doPart trans ->
        net.placeToTrans pdo trans ->
        net.transToPlace trans predo ->
          PetriNet.Path
            (loopProjectionRestricted net doPart pdo predo)
            (PetriNet.Node.place
              ⟨net.source,
                loopProjectionPlaces_source net doPart pdo predo⟩)
            (PetriNet.Node.place
              ⟨net.sink,
                loopProjectionPlaces_sink net doPart pdo predo⟩)) ∧
      (∀ trans, redoPart trans ->
        net.placeToTrans predo trans ->
        net.transToPlace trans pdo ->
          PetriNet.Path
            (loopProjectionRestricted net redoPart predo pdo)
            (PetriNet.Node.place
              ⟨net.source,
                loopProjectionPlaces_source net redoPart predo pdo⟩)
            (PetriNet.Node.place
              ⟨net.sink,
                loopProjectionPlaces_sink net redoPart predo pdo⟩)) := by
  rcases hpattern with
    ⟨doPart, redoPart, _silentPart,
      hdoMem, hredoMem, _hsilentMem,
      pdo, predo, _sourceTrans, _sinkTrans,
      _hne, _hsilentSet, _hsourceSilent, _hsinkSilent,
      _hsourcePost, _hsinkPre, _hsourcePre, _hsourceOut,
      _hsinkIn, _hsinkOut,
      _hdoReach, _hredoReach,
      _hdoNoIn, _hredoNoIn, _hdoNoOut, _hredoNoOut⟩
  refine ⟨doPart, redoPart, pdo, predo, hdoMem, hredoMem, ?_, ?_⟩
  · intro trans hdo hstart hend
    exact loopProjectionRestricted_boundary_path net hdo hstart hend
  · intro trans hredo hstart hend
    exact loopProjectionRestricted_boundary_path net hredo hstart hend

theorem loopPattern_source_ne_sink
    {Activity : Type w}
    {label : Trans -> TransitionLabel Activity}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : loopPattern label net partition) :
    net.source ≠ net.sink := by
  rcases hpattern with
    ⟨_doPart, _redoPart, _silentPart,
      _hdoMem, _hredoMem, _hsilentMem,
      _pdo, _predo, _sourceTrans, sinkTrans,
      _hne, _hsilentSet, _hsourceSilent, _hsinkSilent,
      _hsourcePost, _hsinkPre, _hsourcePre, _hsourceOut,
      _hsinkIn, hsinkOut,
      _hdoReach, _hredoReach,
      _hdoNoIn, _hredoNoIn, _hdoNoOut, _hredoNoOut⟩
  intro hsame
  have hflow : net.transToPlace sinkTrans net.source := by
    rw [hsame]
    exact (hsinkOut net.sink).mpr rfl
  exact ((net.uniqueSource net.source).2 rfl sinkTrans) hflow

theorem loopPattern_projection_source_no_in
    {Activity : Type w}
    {label : Trans -> TransitionLabel Activity}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : loopPattern label net partition) :
    ∃ doPart redoPart pdo predo,
      doPart ∈ partition.parts ∧
      redoPart ∈ partition.parts ∧
      (∀ trans : {trans : Trans // doPart trans},
        ¬ (loopProjectionRestricted net doPart pdo predo).transToPlace
          trans
          ⟨net.source,
            loopProjectionPlaces_source net doPart pdo predo⟩) ∧
      (∀ trans : {trans : Trans // redoPart trans},
        ¬ (loopProjectionRestricted net redoPart predo pdo).transToPlace
          trans
          ⟨net.source,
            loopProjectionPlaces_source net redoPart predo pdo⟩) := by
  rcases hpattern with
    ⟨doPart, redoPart, _silentPart,
      hdoMem, hredoMem, _hsilentMem,
      pdo, predo, _sourceTrans, sinkTrans,
      _hne, _hsilentSet, _hsourceSilent, _hsinkSilent,
      _hsourcePost, _hsinkPre, _hsourcePre, _hsourceOut,
      _hsinkIn, hsinkOut,
      _hdoReach, _hredoReach,
      _hdoNoIn, _hredoNoIn, _hdoNoOut, _hredoNoOut⟩
  have hsourceSink : net.source ≠ net.sink := by
    intro hsame
    have hflow : net.transToPlace sinkTrans net.source := by
      rw [hsame]
      exact (hsinkOut net.sink).mpr rfl
    exact ((net.uniqueSource net.source).2 rfl sinkTrans) hflow
  refine ⟨doPart, redoPart, pdo, predo, hdoMem, hredoMem, ?_, ?_⟩
  · intro trans
    exact loopProjectionRestricted_source_no_in net hsourceSink trans
  · intro trans
    exact loopProjectionRestricted_source_no_in net hsourceSink trans

theorem loopPattern_projection_sink_no_out
    {Activity : Type w}
    {label : Trans -> TransitionLabel Activity}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : loopPattern label net partition) :
    ∃ doPart redoPart pdo predo,
      doPart ∈ partition.parts ∧
      redoPart ∈ partition.parts ∧
      (∀ trans : {trans : Trans // doPart trans},
        ¬ (loopProjectionRestricted net doPart pdo predo).placeToTrans
          ⟨net.sink,
            loopProjectionPlaces_sink net doPart pdo predo⟩
          trans) ∧
      (∀ trans : {trans : Trans // redoPart trans},
        ¬ (loopProjectionRestricted net redoPart predo pdo).placeToTrans
          ⟨net.sink,
            loopProjectionPlaces_sink net redoPart predo pdo⟩
          trans) := by
  rcases hpattern with
    ⟨doPart, redoPart, _silentPart,
      hdoMem, hredoMem, _hsilentMem,
      pdo, predo, _sourceTrans, sinkTrans,
      _hne, _hsilentSet, _hsourceSilent, _hsinkSilent,
      _hsourcePost, _hsinkPre, _hsourcePre, _hsourceOut,
      _hsinkIn, hsinkOut,
      _hdoReach, _hredoReach,
      _hdoNoIn, _hredoNoIn, _hdoNoOut, _hredoNoOut⟩
  have hsourceSink : net.source ≠ net.sink := by
    intro hsame
    have hflow : net.transToPlace sinkTrans net.source := by
      rw [hsame]
      exact (hsinkOut net.sink).mpr rfl
    exact ((net.uniqueSource net.source).2 rfl sinkTrans) hflow
  refine ⟨doPart, redoPart, pdo, predo, hdoMem, hredoMem, ?_, ?_⟩
  · intro trans
    exact loopProjectionRestricted_sink_no_out net hsourceSink trans
  · intro trans
    exact loopProjectionRestricted_sink_no_out net hsourceSink trans

theorem loopPattern_boundary_places_distinct
    {Activity : Type w}
    {label : Trans -> TransitionLabel Activity}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : loopPattern label net partition) :
    ∃ doPart redoPart pdo predo,
      doPart ∈ partition.parts ∧
      redoPart ∈ partition.parts ∧
      pdo ≠ net.source ∧
      pdo ≠ net.sink ∧
      predo ≠ net.source ∧
      predo ≠ net.sink := by
  rcases hpattern with
    ⟨doPart, redoPart, _silentPart,
      hdoMem, hredoMem, _hsilentMem,
      pdo, predo, sourceTrans, sinkTrans,
      hne, _hsilentSet, _hsourceSilent, _hsinkSilent,
      hsourcePost, hsinkPre, _hsourcePre, hsourceOut,
      hsinkIn, _hsinkOut,
      _hdoReach, _hredoReach,
      _hdoNoIn, _hredoNoIn, _hdoNoOut, _hredoNoOut⟩
  refine ⟨doPart, redoPart, pdo, predo, hdoMem, hredoMem, ?_, ?_, ?_, ?_⟩
  · intro hsame
    have hflow : net.transToPlace sourceTrans net.source := by
      rw [← hsame]
      exact (hsourceOut pdo).mpr rfl
    exact ((net.uniqueSource net.source).2 rfl sourceTrans) hflow
  · intro hsame
    have hflow : net.transToPlace sourceTrans net.sink := by
      rw [← hsame]
      exact (hsourceOut pdo).mpr rfl
    exact hne ((hsinkPre sourceTrans).mp hflow)
  · intro hsame
    have hflow : net.placeToTrans net.source sinkTrans := by
      rw [← hsame]
      exact (hsinkIn predo).mpr rfl
    exact hne ((hsourcePost sinkTrans).mp hflow).symm
  · intro hsame
    have hflow : net.placeToTrans net.sink sinkTrans := by
      rw [← hsame]
      exact (hsinkIn predo).mpr rfl
    exact ((net.uniqueSink net.sink).2 rfl sinkTrans) hflow

theorem loopPattern_part_boundary_exclusion
    {Activity : Type w}
    {label : Trans -> TransitionLabel Activity}
    {net : WorkflowNet Place Trans}
    {partition : Partition Trans}
    (hpattern : loopPattern label net partition) :
    ∃ doPart redoPart pdo predo,
      doPart ∈ partition.parts ∧
      redoPart ∈ partition.parts ∧
      (∀ trans, doPart trans -> ¬ net.transToPlace trans pdo) ∧
      (∀ trans, redoPart trans -> ¬ net.transToPlace trans predo) ∧
      (∀ trans, doPart trans -> ¬ net.placeToTrans predo trans) ∧
      (∀ trans, redoPart trans -> ¬ net.placeToTrans pdo trans) := by
  rcases hpattern with
    ⟨doPart, redoPart, _silentPart,
      hdoMem, hredoMem, _hsilentMem,
      pdo, predo, _sourceTrans, _sinkTrans,
      _hne, _hsilentSet, _hsourceSilent, _hsinkSilent,
      _hsourcePost, _hsinkPre, _hsourcePre, _hsourceOut,
      _hsinkIn, _hsinkOut,
      _hdoReach, _hredoReach,
      hdoNoIn, hredoNoIn, hdoNoOut, hredoNoOut⟩
  exact
    ⟨doPart, redoPart, pdo, predo,
      hdoMem, hredoMem,
      hdoNoIn, hredoNoIn, hdoNoOut, hredoNoOut⟩

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

theorem reachesFromPostset_of_placeToTrans
    (net : WorkflowNet Place Trans)
    {place : Place}
    {trans : Trans}
    (hflow : net.placeToTrans place trans) :
    reachesFromPostset net place trans :=
  ⟨trans, hflow, PetriNet.Path.refl⟩

def executionOrder
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans) : Rel Nat :=
  fun left right =>
    ∃ leftPart rightPart place,
      Powl.listGet? partition.parts left = some leftPart ∧
      Powl.listGet? partition.parts right = some rightPart ∧
      WorkflowNet.exitPoints net leftPart place ∧
      WorkflowNet.entryPoints net rightPart place

theorem executionOrder_of_boundary
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    {left right : Nat}
    {leftPart rightPart : Set Trans}
    {place : Place}
    (hleft : Powl.listGet? partition.parts left = some leftPart)
    (hright : Powl.listGet? partition.parts right = some rightPart)
    (hexit : WorkflowNet.exitPoints net leftPart place)
    (hentry : WorkflowNet.entryPoints net rightPart place) :
    executionOrder net partition left right :=
  ⟨leftPart, rightPart, place, hleft, hright, hexit, hentry⟩

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

theorem partialOrderPattern_no_self_executionOrder
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    (hpattern : partialOrderPattern net partition)
    (index : Nat) :
    ¬ executionOrder net partition index index := by
  intro horder
  exact hpattern.2.2.1 index (TransGen.single horder)

theorem partialOrderPattern_no_executionOrder_cycle
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    (hpattern : partialOrderPattern net partition)
    {left right : Nat}
    (hleftRight : executionOrder net partition left right) :
    ¬ executionOrder net partition right left := by
  intro hrightLeft
  exact
    partialOrderPattern_asymmetric net partition hpattern
      (TransGen.single hleftRight)
      (TransGen.single hrightLeft)

theorem partialOrderPattern_no_same_part_entry_exit
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    (hpattern : partialOrderPattern net partition)
    {index : Nat}
    {part : Set Trans}
    {place : Place}
    (hpart : Powl.listGet? partition.parts index = some part)
    (hexit : WorkflowNet.exitPoints net part place)
    (hentry : WorkflowNet.entryPoints net part place) :
    False :=
  partialOrderPattern_no_self_executionOrder net partition hpattern index
    (executionOrder_of_boundary
      net partition hpart hpart hexit hentry)

theorem partialOrderPattern_samePart_of_reachesFromPostset
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    (hpattern : partialOrderPattern net partition)
    {place : Place}
    {left right : Trans}
    (hleft : reachesFromPostset net place left)
    (hright : reachesFromPostset net place right) :
    partition.samePart left right :=
  hpattern.2.1 place left right hleft hright

theorem partialOrderPattern_part_eq_of_common_postset_reach
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    (hpattern : partialOrderPattern net partition)
    {leftPart rightPart : Set Trans}
    (hleftPartMem : leftPart ∈ partition.parts)
    (hrightPartMem : rightPart ∈ partition.parts)
    {place : Place}
    {left right : Trans}
    (hleftPart : leftPart left)
    (hrightPart : rightPart right)
    (hleftReach : reachesFromPostset net place left)
    (hrightReach : reachesFromPostset net place right) :
    leftPart = rightPart := by
  rcases partialOrderPattern_samePart_of_reachesFromPostset
      net partition hpattern hleftReach hrightReach with
    ⟨samePart, hsameMem, hleftSame, hrightSame⟩
  have hleftEq : leftPart = samePart :=
    partition.disjoint hleftPartMem hsameMem hleftPart hleftSame
  have hrightEq : rightPart = samePart :=
    partition.disjoint hrightPartMem hsameMem hrightPart hrightSame
  exact hleftEq.trans hrightEq.symm

theorem partialOrderPattern_indexed_part_eq_of_common_postset_reach
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    (hpattern : partialOrderPattern net partition)
    {leftIndex rightIndex : Nat}
    {leftPart rightPart : Set Trans}
    (hleftGet : Powl.listGet? partition.parts leftIndex = some leftPart)
    (hrightGet : Powl.listGet? partition.parts rightIndex = some rightPart)
    {place : Place}
    {left right : Trans}
    (hleftPart : leftPart left)
    (hrightPart : rightPart right)
    (hleftReach : reachesFromPostset net place left)
    (hrightReach : reachesFromPostset net place right) :
    leftPart = rightPart :=
  partialOrderPattern_part_eq_of_common_postset_reach
    net partition hpattern
    (Partition.mem_of_listGet? partition hleftGet)
    (Partition.mem_of_listGet? partition hrightGet)
    hleftPart hrightPart hleftReach hrightReach

theorem partialOrderPattern_samePart_of_common_preset
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    (hpattern : partialOrderPattern net partition)
    {place : Place}
    {left right : Trans}
    (hleft : net.placeToTrans place left)
    (hright : net.placeToTrans place right) :
    partition.samePart left right :=
  partialOrderPattern_samePart_of_reachesFromPostset
    net
    partition
    hpattern
    (reachesFromPostset_of_placeToTrans net hleft)
    (reachesFromPostset_of_placeToTrans net hright)

theorem partialOrderPattern_part_eq_of_common_preset
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    (hpattern : partialOrderPattern net partition)
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
  partialOrderPattern_part_eq_of_common_postset_reach
    net
    partition
    hpattern
    hleftPartMem
    hrightPartMem
    hleftPart
    hrightPart
    (reachesFromPostset_of_placeToTrans net hleft)
    (reachesFromPostset_of_placeToTrans net hright)

theorem partialOrderPattern_indexed_part_eq_of_common_preset
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    (hpattern : partialOrderPattern net partition)
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
  partialOrderPattern_part_eq_of_common_preset
    net
    partition
    hpattern
    (Partition.mem_of_listGet? partition hleftGet)
    (Partition.mem_of_listGet? partition hrightGet)
    hleftPart
    hrightPart
    hleft
    hright

theorem partialOrderPattern_entry_placeEquivalent
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    (hpattern : partialOrderPattern net partition)
    {index : Nat}
    {part : Set Trans}
    {leftPlace rightPlace : Place}
    (hpart : Powl.listGet? partition.parts index = some part)
    (hleft : WorkflowNet.entryPoints net part leftPlace)
    (hright : WorkflowNet.entryPoints net part rightPlace) :
    PetriNet.placeEquivalentWrt
      net.toPetriNet part leftPlace rightPlace :=
  hpattern.2.2.2.1 index part leftPlace rightPlace hpart hleft hright

theorem partialOrderPattern_exit_placeEquivalent
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    (hpattern : partialOrderPattern net partition)
    {index : Nat}
    {part : Set Trans}
    {leftPlace rightPlace : Place}
    (hpart : Powl.listGet? partition.parts index = some part)
    (hleft : WorkflowNet.exitPoints net part leftPlace)
    (hright : WorkflowNet.exitPoints net part rightPlace) :
    PetriNet.placeEquivalentWrt
      net.toPetriNet part leftPlace rightPlace :=
  hpattern.2.2.2.2 index part leftPlace rightPlace hpart hleft hright

theorem partialOrderPattern_entry_transToPlace_iff
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    (hpattern : partialOrderPattern net partition)
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
  (partialOrderPattern_entry_placeEquivalent
    net partition hpattern hpart hleft hright).1 trans htrans

theorem partialOrderPattern_entry_placeToTrans_iff
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    (hpattern : partialOrderPattern net partition)
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
  (partialOrderPattern_entry_placeEquivalent
    net partition hpattern hpart hleft hright).2 trans htrans

theorem partialOrderPattern_exit_transToPlace_iff
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    (hpattern : partialOrderPattern net partition)
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
  (partialOrderPattern_exit_placeEquivalent
    net partition hpattern hpart hleft hright).1 trans htrans

theorem partialOrderPattern_exit_placeToTrans_iff
    (net : WorkflowNet Place Trans)
    (partition : Partition Trans)
    (hpattern : partialOrderPattern net partition)
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
  (partialOrderPattern_exit_placeEquivalent
    net partition hpattern hpart hleft hright).2 trans htrans

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

def partialOrderProjectionPlaces
    (net : WorkflowNet Place Trans)
    (part : Set Trans) : Set (BoundaryPlace Place)
  | BoundaryPlace.start => True
  | BoundaryPlace.end_ => True
  | BoundaryPlace.original original =>
      PetriNet.placesTouching net.toPetriNet part original ∧
        ¬ WorkflowNet.entryPoints net part original ∧
        ¬ WorkflowNet.exitPoints net part original

theorem partialOrderProjectionPlaces_start
    (net : WorkflowNet Place Trans)
    (part : Set Trans) :
    partialOrderProjectionPlaces net part BoundaryPlace.start :=
  True.intro

theorem partialOrderProjectionPlaces_end
    (net : WorkflowNet Place Trans)
    (part : Set Trans) :
    partialOrderProjectionPlaces net part BoundaryPlace.end_ :=
  True.intro

theorem partialOrderProjectionPlaces_original
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hnotEntry : ¬ WorkflowNet.entryPoints net part place)
    (hnotExit : ¬ WorkflowNet.exitPoints net part place) :
    partialOrderProjectionPlaces net part (BoundaryPlace.original place) :=
  ⟨htouching, hnotEntry, hnotExit⟩

def partialOrderProjectionRestricted
    (net : WorkflowNet Place Trans)
    (part : Set Trans) :
    PetriNet
      {place : BoundaryPlace Place // partialOrderProjectionPlaces net part place}
      {trans : Trans // part trans} :=
  PetriNet.restrict
    (partialOrderProjection net part)
    (partialOrderProjectionPlaces net part)
    part

theorem partialOrderProjectionRestricted_placeToTrans_iff
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (place :
      {place : BoundaryPlace Place //
        partialOrderProjectionPlaces net part place})
    (trans : {trans : Trans // part trans}) :
    (partialOrderProjectionRestricted net part).placeToTrans place trans ↔
      (partialOrderProjection net part).placeToTrans place.val trans.val :=
  Iff.rfl

theorem partialOrderProjectionRestricted_transToPlace_iff
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (trans : {trans : Trans // part trans})
    (place :
      {place : BoundaryPlace Place //
        partialOrderProjectionPlaces net part place}) :
    (partialOrderProjectionRestricted net part).transToPlace trans place ↔
      (partialOrderProjection net part).transToPlace trans.val place.val :=
  Iff.rfl

theorem partialOrderProjectionRestricted_flow_original
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    {first second :
      PetriNet.Node
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place}
        {trans : Trans // part trans}}
    (hflow :
      PetriNet.flow
        (partialOrderProjectionRestricted net part)
        first second) :
    PetriNet.flow
      (partialOrderProjection net part)
      (PetriNet.restrictedNode first)
      (PetriNet.restrictedNode second) :=
  PetriNet.restrict_flow_original
    (partialOrderProjection net part)
    (partialOrderProjectionPlaces net part)
    part
    hflow

theorem partialOrderProjectionRestricted_flow_of_original
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    {first second : PetriNet.Node (BoundaryPlace Place) Trans}
    (hflow :
      PetriNet.flow
        (partialOrderProjection net part)
        first second)
    (hfirst :
      PetriNet.nodeIn
        (partialOrderProjectionPlaces net part)
        part
        first)
    (hsecond :
      PetriNet.nodeIn
        (partialOrderProjectionPlaces net part)
        part
        second) :
    PetriNet.flow
      (partialOrderProjectionRestricted net part)
      (PetriNet.restrictNode first hfirst)
      (PetriNet.restrictNode second hsecond) :=
  PetriNet.restrict_flow_of_original
    (partialOrderProjection net part)
    (partialOrderProjectionPlaces net part)
    part
    hflow
    hfirst
    hsecond

theorem partialOrderProjectionRestricted_path_original
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    {source target :
      PetriNet.Node
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place}
        {trans : Trans // part trans}}
    (path :
      PetriNet.Path
        (partialOrderProjectionRestricted net part)
        source
        target) :
    PetriNet.Path
      (partialOrderProjection net part)
      (PetriNet.restrictedNode source)
      (PetriNet.restrictedNode target) :=
  PetriNet.restrict_path_original
    (partialOrderProjection net part)
    (partialOrderProjectionPlaces net part)
    part
    path

theorem partialOrderProjectionRestricted_path_of_pathIn
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    {source target : PetriNet.Node (BoundaryPlace Place) Trans}
    (path :
      PetriNet.PathIn
        (partialOrderProjection net part)
        (partialOrderProjectionPlaces net part)
        part
        source
        target) :
    PetriNet.Path
      (partialOrderProjectionRestricted net part)
      (PetriNet.restrictNode source (PetriNet.PathIn.source_mem path))
      (PetriNet.restrictNode target (PetriNet.PathIn.target_mem path)) :=
  PetriNet.PathIn.to_restrict_path path

theorem partialOrderProjectionRestricted_connected_of_pathIn
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (hconnected :
      ∀ node :
          PetriNet.Node (BoundaryPlace Place) Trans,
        PetriNet.nodeIn (partialOrderProjectionPlaces net part) part node ->
          PetriNet.PathIn
              (partialOrderProjection net part)
              (partialOrderProjectionPlaces net part)
              part
              (PetriNet.Node.place BoundaryPlace.start)
              node ∧
            PetriNet.PathIn
              (partialOrderProjection net part)
              (partialOrderProjectionPlaces net part)
              part
              node
              (PetriNet.Node.place BoundaryPlace.end_)) :
    ∀ node :
      PetriNet.Node
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place}
        {trans : Trans // part trans},
      PetriNet.Path
          (partialOrderProjectionRestricted net part)
          (PetriNet.Node.place
            ⟨BoundaryPlace.start, partialOrderProjectionPlaces_start net part⟩)
          node ∧
        PetriNet.Path
          (partialOrderProjectionRestricted net part)
          node
          (PetriNet.Node.place
            ⟨BoundaryPlace.end_,
              partialOrderProjectionPlaces_end net part⟩) := by
  intro node
  let rawNode := PetriNet.restrictedNode node
  have hnode :
      PetriNet.nodeIn
        (partialOrderProjectionPlaces net part)
        part
        rawNode :=
    PetriNet.restrictedNode_nodeIn node
  rcases hconnected rawNode hnode with ⟨hstartPath, hendPath⟩
  have hstart :
      PetriNet.Path
        (partialOrderProjectionRestricted net part)
        (PetriNet.Node.place
          ⟨BoundaryPlace.start, partialOrderProjectionPlaces_start net part⟩)
        node := by
    have hpath :=
      partialOrderProjectionRestricted_path_of_pathIn
        net part hstartPath
    have hsource :
        PetriNet.restrictNode
          (PetriNet.Node.place BoundaryPlace.start)
          (PetriNet.PathIn.source_mem hstartPath) =
            PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩ := by
      rw [PetriNet.restrictNode_irrel
        (PetriNet.Node.place BoundaryPlace.start)
        (PetriNet.PathIn.source_mem hstartPath)
        (partialOrderProjectionPlaces_start net part)]
      rfl
    have htarget :
        PetriNet.restrictNode
          rawNode
          (PetriNet.PathIn.target_mem hstartPath) = node := by
      have hsame :
          PetriNet.restrictNode
            rawNode
            (PetriNet.PathIn.target_mem hstartPath) =
              PetriNet.restrictNode rawNode hnode :=
        PetriNet.restrictNode_irrel
          rawNode
          (PetriNet.PathIn.target_mem hstartPath)
          hnode
      rw [hsame]
      exact PetriNet.restrictNode_restrictedNode node
    simpa [hsource, htarget] using hpath
  have hend :
      PetriNet.Path
        (partialOrderProjectionRestricted net part)
        node
        (PetriNet.Node.place
          ⟨BoundaryPlace.end_,
            partialOrderProjectionPlaces_end net part⟩) := by
    have hpath :=
      partialOrderProjectionRestricted_path_of_pathIn
        net part hendPath
    have hsource :
        PetriNet.restrictNode
          rawNode
          (PetriNet.PathIn.source_mem hendPath) = node := by
      have hsame :
          PetriNet.restrictNode
            rawNode
            (PetriNet.PathIn.source_mem hendPath) =
              PetriNet.restrictNode rawNode hnode :=
        PetriNet.restrictNode_irrel
          rawNode
          (PetriNet.PathIn.source_mem hendPath)
          hnode
      rw [hsame]
      exact PetriNet.restrictNode_restrictedNode node
    have htarget :
        PetriNet.restrictNode
          (PetriNet.Node.place BoundaryPlace.end_)
          (PetriNet.PathIn.target_mem hendPath) =
            PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩ := by
      rw [PetriNet.restrictNode_irrel
        (PetriNet.Node.place BoundaryPlace.end_)
        (PetriNet.PathIn.target_mem hendPath)
        (partialOrderProjectionPlaces_end net part)]
      rfl
    simpa [hsource, htarget] using hpath
  exact ⟨hstart, hend⟩

theorem partialOrderProjection_start_placeToTrans_iff
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (trans : Trans) :
    (partialOrderProjection net part).placeToTrans
      BoundaryPlace.start trans ↔
        part trans ∧
          ∃ original,
            WorkflowNet.entryPoints net part original ∧
            net.placeToTrans original trans :=
  Iff.rfl

theorem partialOrderProjection_end_placeToTrans_iff
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (trans : Trans) :
    (partialOrderProjection net part).placeToTrans
      BoundaryPlace.end_ trans ↔
        part trans ∧
          ∃ original,
            WorkflowNet.exitPoints net part original ∧
            net.placeToTrans original trans :=
  Iff.rfl

theorem partialOrderProjection_original_placeToTrans_iff
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (place : Place)
    (trans : Trans) :
    (partialOrderProjection net part).placeToTrans
      (BoundaryPlace.original place) trans ↔
        part trans ∧
          PetriNet.placesTouching net.toPetriNet part place ∧
          ¬ WorkflowNet.entryPoints net part place ∧
          ¬ WorkflowNet.exitPoints net part place ∧
          net.placeToTrans place trans :=
  Iff.rfl

theorem partialOrderProjection_transToPlace_start_iff
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (trans : Trans) :
    (partialOrderProjection net part).transToPlace
      trans BoundaryPlace.start ↔
        part trans ∧
          ∃ original,
            WorkflowNet.entryPoints net part original ∧
            net.transToPlace trans original :=
  Iff.rfl

theorem partialOrderProjection_transToPlace_end_iff
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (trans : Trans) :
    (partialOrderProjection net part).transToPlace
      trans BoundaryPlace.end_ ↔
        part trans ∧
          ∃ original,
            WorkflowNet.exitPoints net part original ∧
            net.transToPlace trans original :=
  Iff.rfl

theorem partialOrderProjection_transToPlace_original_iff
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (trans : Trans)
    (place : Place) :
    (partialOrderProjection net part).transToPlace
      trans (BoundaryPlace.original place) ↔
        part trans ∧
          PetriNet.placesTouching net.toPetriNet part place ∧
          ¬ WorkflowNet.entryPoints net part place ∧
          ¬ WorkflowNet.exitPoints net part place ∧
          net.transToPlace trans place :=
  Iff.rfl

theorem partialOrderProjection_placeToTrans_place_mem
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : BoundaryPlace Place}
    {trans : Trans}
    (hflow :
      (partialOrderProjection net part).placeToTrans place trans) :
    partialOrderProjectionPlaces net part place := by
  cases place with
  | original original =>
      exact ⟨hflow.2.1, hflow.2.2.1, hflow.2.2.2.1⟩
  | start =>
      exact True.intro
  | end_ =>
      exact True.intro

theorem partialOrderProjection_transToPlace_place_mem
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : BoundaryPlace Place}
    (hflow :
      (partialOrderProjection net part).transToPlace trans place) :
    partialOrderProjectionPlaces net part place := by
  cases place with
  | original original =>
      exact ⟨hflow.2.1, hflow.2.2.1, hflow.2.2.2.1⟩
  | start =>
      exact True.intro
  | end_ =>
      exact True.intro

theorem partialOrderProjection_flow_source_mem
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    {first second : PetriNet.Node (BoundaryPlace Place) Trans}
    (hflow :
      PetriNet.flow (partialOrderProjection net part) first second) :
    PetriNet.nodeIn (partialOrderProjectionPlaces net part) part first := by
  cases first with
  | place place =>
      cases second with
      | place place' =>
          exact False.elim hflow
      | trans trans =>
          exact partialOrderProjection_placeToTrans_place_mem net hflow
  | trans trans =>
      cases second with
      | place place =>
          exact hflow.1
      | trans trans' =>
          exact False.elim hflow

theorem partialOrderProjection_flow_target_mem
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    {first second : PetriNet.Node (BoundaryPlace Place) Trans}
    (hflow :
      PetriNet.flow (partialOrderProjection net part) first second) :
    PetriNet.nodeIn (partialOrderProjectionPlaces net part) part second := by
  cases first with
  | place place =>
      cases second with
      | place place' =>
          exact False.elim hflow
      | trans trans =>
          exact hflow.1
  | trans trans =>
      cases second with
      | place place =>
          exact partialOrderProjection_transToPlace_place_mem net hflow
      | trans trans' =>
          exact False.elim hflow

theorem partialOrderProjection_pathIn_of_path
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    {source target : PetriNet.Node (BoundaryPlace Place) Trans}
    (path :
      PetriNet.Path
        (partialOrderProjection net part)
        source
        target)
    (hsource :
      PetriNet.nodeIn (partialOrderProjectionPlaces net part) part source) :
    PetriNet.PathIn
      (partialOrderProjection net part)
      (partialOrderProjectionPlaces net part)
      part
      source
      target :=
  PetriNet.PathIn.of_path
    path
    hsource
    (fun hflow _ =>
      partialOrderProjection_flow_target_mem net part hflow)

noncomputable def partialOrderProjectionRestrictedMarking
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (marking : Marking Place) :
    Marking
      {place : BoundaryPlace Place //
        partialOrderProjectionPlaces net part place} := by
  classical
  exact fun place =>
    match place.val with
    | BoundaryPlace.original original => marking original
    | BoundaryPlace.start =>
        if ∀ entry, WorkflowNet.entryPoints net part entry ->
            marking entry > 0 then
          1
        else
          0
    | BoundaryPlace.end_ =>
        if ∀ exit, WorkflowNet.exitPoints net part exit ->
            marking exit > 0 then
          1
        else
          0

@[simp] theorem partialOrderProjectionRestrictedMarking_original
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (marking : Marking Place)
    {place : Place}
    (hplace :
      partialOrderProjectionPlaces net part (BoundaryPlace.original place)) :
    partialOrderProjectionRestrictedMarking net part marking
      ⟨BoundaryPlace.original place, hplace⟩ =
        marking place := by
  simp [partialOrderProjectionRestrictedMarking]

theorem partialOrderProjectionRestrictedMarking_start_of_entries_marked
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (marking : Marking Place)
    (hmarked :
      ∀ entry, WorkflowNet.entryPoints net part entry ->
        marking entry > 0) :
  partialOrderProjectionRestrictedMarking net part marking
      ⟨BoundaryPlace.start,
        partialOrderProjectionPlaces_start net part⟩ = 1 := by
  classical
  unfold partialOrderProjectionRestrictedMarking
  dsimp
  exact if_pos hmarked

theorem partialOrderProjectionRestrictedMarking_start_of_not_entries_marked
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (marking : Marking Place)
    (hmarked :
      ¬ ∀ entry, WorkflowNet.entryPoints net part entry ->
        marking entry > 0) :
  partialOrderProjectionRestrictedMarking net part marking
      ⟨BoundaryPlace.start,
        partialOrderProjectionPlaces_start net part⟩ = 0 := by
  classical
  unfold partialOrderProjectionRestrictedMarking
  dsimp
  exact if_neg hmarked

theorem partialOrderProjectionRestrictedMarking_end_of_exits_marked
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (marking : Marking Place)
    (hmarked :
      ∀ exit, WorkflowNet.exitPoints net part exit ->
        marking exit > 0) :
  partialOrderProjectionRestrictedMarking net part marking
      ⟨BoundaryPlace.end_,
        partialOrderProjectionPlaces_end net part⟩ = 1 := by
  classical
  unfold partialOrderProjectionRestrictedMarking
  dsimp
  exact if_pos hmarked

theorem partialOrderProjectionRestrictedMarking_end_of_not_exits_marked
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (marking : Marking Place)
    (hmarked :
      ¬ ∀ exit, WorkflowNet.exitPoints net part exit ->
        marking exit > 0) :
  partialOrderProjectionRestrictedMarking net part marking
      ⟨BoundaryPlace.end_,
        partialOrderProjectionPlaces_end net part⟩ = 0 := by
  classical
  unfold partialOrderProjectionRestrictedMarking
  dsimp
  exact if_neg hmarked

theorem partialOrderProjectionRestrictedMarking_le_one_of_original_le_one
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (marking : Marking Place)
    (hmarking : ∀ place, marking place ≤ 1) :
    ∀ place :
      {place : BoundaryPlace Place //
        partialOrderProjectionPlaces net part place},
      partialOrderProjectionRestrictedMarking net part marking place ≤ 1 := by
  intro place
  rcases place with ⟨place, _hplace⟩
  cases place with
  | original original =>
      simpa [partialOrderProjectionRestrictedMarking] using
        hmarking original
  | start =>
      by_cases hmarked :
          ∀ entry, WorkflowNet.entryPoints net part entry ->
            marking entry > 0
      · unfold partialOrderProjectionRestrictedMarking
        dsimp
        rw [if_pos hmarked]
        exact Nat.le_refl 1
      · unfold partialOrderProjectionRestrictedMarking
        dsimp
        rw [if_neg hmarked]
        exact Nat.zero_le 1
  | end_ =>
      by_cases hmarked :
          ∀ exit, WorkflowNet.exitPoints net part exit ->
            marking exit > 0
      · unfold partialOrderProjectionRestrictedMarking
        dsimp
        rw [if_pos hmarked]
        exact Nat.le_refl 1
      · unfold partialOrderProjectionRestrictedMarking
        dsimp
        rw [if_neg hmarked]
        exact Nat.zero_le 1

noncomputable def partialOrderProjectionNormalizedMarking
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (marking : Marking Place) :
    Marking
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place}) :=
  Marking.normalize
    (partialOrderProjectionRestrictedMarking net part marking)

@[simp] theorem partialOrderProjectionNormalizedMarking_source
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (marking : Marking Place) :
    partialOrderProjectionNormalizedMarking net part marking
      (PetriNet.NormalizedPlace.source :
        PetriNet.NormalizedPlace
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}) = 0 := by
  rw [partialOrderProjectionNormalizedMarking, Marking.normalize_source_apply]

@[simp] theorem partialOrderProjectionNormalizedMarking_sink
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (marking : Marking Place) :
    partialOrderProjectionNormalizedMarking net part marking
      (PetriNet.NormalizedPlace.sink :
        PetriNet.NormalizedPlace
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}) = 0 := by
  rw [partialOrderProjectionNormalizedMarking, Marking.normalize_sink_apply]

@[simp] theorem partialOrderProjectionNormalizedMarking_original
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (marking : Marking Place)
    (place :
      {place : BoundaryPlace Place //
        partialOrderProjectionPlaces net part place}) :
    partialOrderProjectionNormalizedMarking net part marking
      (PetriNet.NormalizedPlace.original place) =
        partialOrderProjectionRestrictedMarking net part marking place := by
  rw [partialOrderProjectionNormalizedMarking, Marking.normalize_original_apply]

theorem partialOrderProjectionNormalizedMarking_original_place
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (marking : Marking Place)
    {place : Place}
    (hplace :
      partialOrderProjectionPlaces net part (BoundaryPlace.original place)) :
    partialOrderProjectionNormalizedMarking net part marking
      (PetriNet.NormalizedPlace.original
        ⟨BoundaryPlace.original place, hplace⟩) =
        marking place := by
  rw [partialOrderProjectionNormalizedMarking, Marking.normalize_original_apply]
  simp [partialOrderProjectionRestrictedMarking]

theorem partialOrderProjectionNormalizedMarking_start_of_entries_marked
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (marking : Marking Place)
    (hmarked :
      ∀ entry, WorkflowNet.entryPoints net part entry ->
        marking entry > 0) :
    partialOrderProjectionNormalizedMarking net part marking
      (PetriNet.NormalizedPlace.original
        ⟨BoundaryPlace.start,
          partialOrderProjectionPlaces_start net part⟩) = 1 := by
  rw [partialOrderProjectionNormalizedMarking, Marking.normalize_original_apply]
  exact
    partialOrderProjectionRestrictedMarking_start_of_entries_marked
      net part marking hmarked

theorem partialOrderProjectionNormalizedMarking_start_of_not_entries_marked
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (marking : Marking Place)
    (hmarked :
      ¬ ∀ entry, WorkflowNet.entryPoints net part entry ->
        marking entry > 0) :
    partialOrderProjectionNormalizedMarking net part marking
      (PetriNet.NormalizedPlace.original
        ⟨BoundaryPlace.start,
          partialOrderProjectionPlaces_start net part⟩) = 0 := by
  rw [partialOrderProjectionNormalizedMarking, Marking.normalize_original_apply]
  exact
    partialOrderProjectionRestrictedMarking_start_of_not_entries_marked
      net part marking hmarked

theorem partialOrderProjectionNormalizedMarking_end_of_exits_marked
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (marking : Marking Place)
    (hmarked :
      ∀ exit, WorkflowNet.exitPoints net part exit ->
        marking exit > 0) :
    partialOrderProjectionNormalizedMarking net part marking
      (PetriNet.NormalizedPlace.original
        ⟨BoundaryPlace.end_,
          partialOrderProjectionPlaces_end net part⟩) = 1 := by
  rw [partialOrderProjectionNormalizedMarking, Marking.normalize_original_apply]
  exact
    partialOrderProjectionRestrictedMarking_end_of_exits_marked
      net part marking hmarked

theorem partialOrderProjectionNormalizedMarking_end_of_not_exits_marked
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (marking : Marking Place)
    (hmarked :
      ¬ ∀ exit, WorkflowNet.exitPoints net part exit ->
        marking exit > 0) :
    partialOrderProjectionNormalizedMarking net part marking
      (PetriNet.NormalizedPlace.original
        ⟨BoundaryPlace.end_,
          partialOrderProjectionPlaces_end net part⟩) = 0 := by
  rw [partialOrderProjectionNormalizedMarking, Marking.normalize_original_apply]
  exact
    partialOrderProjectionRestrictedMarking_end_of_not_exits_marked
      net part marking hmarked

theorem partialOrderProjectionNormalizedMarking_le_one_of_original_le_one
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (marking : Marking Place)
    (hmarking : ∀ place, marking place ≤ 1) :
    ∀ place :
      PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place},
      partialOrderProjectionNormalizedMarking net part marking place ≤ 1 := by
  intro place
  cases place with
  | source =>
      rw [partialOrderProjectionNormalizedMarking_source]
      exact Nat.zero_le 1
  | sink =>
      rw [partialOrderProjectionNormalizedMarking_sink]
      exact Nat.zero_le 1
  | original place =>
      rw [partialOrderProjectionNormalizedMarking_original]
      exact
        partialOrderProjectionRestrictedMarking_le_one_of_original_le_one
          net part marking hmarking place

theorem partialOrderProjectionRestricted_connected_of_path
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (hconnected :
      ∀ node :
          PetriNet.Node (BoundaryPlace Place) Trans,
        PetriNet.nodeIn (partialOrderProjectionPlaces net part) part node ->
          PetriNet.Path
              (partialOrderProjection net part)
              (PetriNet.Node.place BoundaryPlace.start)
              node ∧
            PetriNet.Path
              (partialOrderProjection net part)
              node
              (PetriNet.Node.place BoundaryPlace.end_)) :
    ∀ node :
      PetriNet.Node
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place}
        {trans : Trans // part trans},
      PetriNet.Path
          (partialOrderProjectionRestricted net part)
          (PetriNet.Node.place
            ⟨BoundaryPlace.start, partialOrderProjectionPlaces_start net part⟩)
          node ∧
        PetriNet.Path
          (partialOrderProjectionRestricted net part)
          node
          (PetriNet.Node.place
            ⟨BoundaryPlace.end_,
              partialOrderProjectionPlaces_end net part⟩) :=
  partialOrderProjectionRestricted_connected_of_pathIn
    net part
    (fun node hnode =>
      let paths := hconnected node hnode
      ⟨partialOrderProjection_pathIn_of_path
          net part paths.1
          (by
            exact partialOrderProjectionPlaces_start net part),
        partialOrderProjection_pathIn_of_path
          net part paths.2 hnode⟩)

theorem partialOrderProjectionRestricted_start_placeToTrans_iff'
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (trans : {trans : Trans // part trans}) :
    (partialOrderProjectionRestricted net part).placeToTrans
      ⟨BoundaryPlace.start, partialOrderProjectionPlaces_start net part⟩
      trans ↔
        ∃ original,
          WorkflowNet.entryPoints net part original ∧
          net.placeToTrans original trans.val := by
  constructor
  · intro hflow
    exact hflow.2
  · intro hflow
    exact ⟨trans.property, hflow⟩

theorem partialOrderProjectionRestricted_end_placeToTrans_iff'
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (trans : {trans : Trans // part trans}) :
    (partialOrderProjectionRestricted net part).placeToTrans
      ⟨BoundaryPlace.end_, partialOrderProjectionPlaces_end net part⟩
      trans ↔
        ∃ original,
          WorkflowNet.exitPoints net part original ∧
          net.placeToTrans original trans.val := by
  constructor
  · intro hflow
    exact hflow.2
  · intro hflow
    exact ⟨trans.property, hflow⟩

theorem partialOrderProjectionRestricted_transToPlace_start_iff'
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (trans : {trans : Trans // part trans}) :
    (partialOrderProjectionRestricted net part).transToPlace
      trans
      ⟨BoundaryPlace.start, partialOrderProjectionPlaces_start net part⟩ ↔
        ∃ original,
          WorkflowNet.entryPoints net part original ∧
          net.transToPlace trans.val original := by
  constructor
  · intro hflow
    exact hflow.2
  · intro hflow
    exact ⟨trans.property, hflow⟩

theorem partialOrderProjectionRestricted_transToPlace_end_iff'
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (trans : {trans : Trans // part trans}) :
    (partialOrderProjectionRestricted net part).transToPlace
      trans
      ⟨BoundaryPlace.end_, partialOrderProjectionPlaces_end net part⟩ ↔
        ∃ original,
          WorkflowNet.exitPoints net part original ∧
          net.transToPlace trans.val original := by
  constructor
  · intro hflow
    exact hflow.2
  · intro hflow
    exact ⟨trans.property, hflow⟩

theorem partialOrderProjectionRestricted_original_placeToTrans_iff'
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hplace :
      partialOrderProjectionPlaces net part (BoundaryPlace.original place))
    (trans : {trans : Trans // part trans}) :
    (partialOrderProjectionRestricted net part).placeToTrans
      ⟨BoundaryPlace.original place, hplace⟩
      trans ↔
        net.placeToTrans place trans.val := by
  constructor
  · intro hflow
    exact hflow.2.2.2.2
  · intro hflow
    exact
      ⟨trans.property,
        hplace.1,
        hplace.2.1,
        hplace.2.2,
        hflow⟩

theorem partialOrderProjectionRestricted_transToPlace_original_iff'
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (trans : {trans : Trans // part trans})
    {place : Place}
    (hplace :
      partialOrderProjectionPlaces net part (BoundaryPlace.original place)) :
    (partialOrderProjectionRestricted net part).transToPlace
      trans
      ⟨BoundaryPlace.original place, hplace⟩ ↔
        net.transToPlace trans.val place := by
  constructor
  · intro hflow
    exact hflow.2.2.2.2
  · intro hflow
    exact
      ⟨trans.property,
        hplace.1,
        hplace.2.1,
        hplace.2.2,
        hflow⟩

theorem partialOrderProjection_start_placeToTrans
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part place)
    (hflow : net.placeToTrans place trans) :
    (partialOrderProjection net part).placeToTrans
      BoundaryPlace.start trans :=
  ⟨hpart, place, hentry, hflow⟩

theorem partialOrderProjection_end_placeToTrans
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hexit : WorkflowNet.exitPoints net part place)
    (hflow : net.placeToTrans place trans) :
    (partialOrderProjection net part).placeToTrans
      BoundaryPlace.end_ trans :=
  ⟨hpart, place, hexit, hflow⟩

theorem partialOrderProjection_original_placeToTrans
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hnotEntry : ¬ WorkflowNet.entryPoints net part place)
    (hnotExit : ¬ WorkflowNet.exitPoints net part place)
    (hflow : net.placeToTrans place trans) :
    (partialOrderProjection net part).placeToTrans
      (BoundaryPlace.original place) trans :=
  ⟨hpart, htouching, hnotEntry, hnotExit, hflow⟩

theorem partialOrderProjection_transToPlace_start
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part place)
    (hflow : net.transToPlace trans place) :
    (partialOrderProjection net part).transToPlace
      trans BoundaryPlace.start :=
  ⟨hpart, place, hentry, hflow⟩

theorem partialOrderProjection_transToPlace_end
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (hexit : WorkflowNet.exitPoints net part place)
    (hflow : net.transToPlace trans place) :
    (partialOrderProjection net part).transToPlace
      trans BoundaryPlace.end_ :=
  ⟨hpart, place, hexit, hflow⟩

theorem partialOrderProjection_transToPlace_original
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hnotEntry : ¬ WorkflowNet.entryPoints net part place)
    (hnotExit : ¬ WorkflowNet.exitPoints net part place)
    (hflow : net.transToPlace trans place) :
    (partialOrderProjection net part).transToPlace
      trans (BoundaryPlace.original place) :=
  ⟨hpart, htouching, hnotEntry, hnotExit, hflow⟩

theorem partialOrderProjection_start_to_transition
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part place)
    (hflow : net.placeToTrans place trans) :
    PetriNet.Path
      (partialOrderProjection net part)
      (PetriNet.Node.place BoundaryPlace.start)
      (PetriNet.Node.trans trans) :=
  PetriNet.Path.step
    (by
      simpa [PetriNet.flow] using
        partialOrderProjection_start_placeToTrans
          net hpart hentry hflow)
    PetriNet.Path.refl

theorem partialOrderProjection_transition_to_start
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part place)
    (hflow : net.transToPlace trans place) :
    PetriNet.Path
      (partialOrderProjection net part)
      (PetriNet.Node.trans trans)
      (PetriNet.Node.place BoundaryPlace.start) :=
  PetriNet.Path.step
    (by
      simpa [PetriNet.flow] using
        partialOrderProjection_transToPlace_start
          net hpart hentry hflow)
    PetriNet.Path.refl

theorem partialOrderProjection_end_to_transition
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hexit : WorkflowNet.exitPoints net part place)
    (hflow : net.placeToTrans place trans) :
    PetriNet.Path
      (partialOrderProjection net part)
      (PetriNet.Node.place BoundaryPlace.end_)
      (PetriNet.Node.trans trans) :=
  PetriNet.Path.step
    (by
      simpa [PetriNet.flow] using
        partialOrderProjection_end_placeToTrans
          net hpart hexit hflow)
    PetriNet.Path.refl

theorem partialOrderProjection_transition_to_end
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (hexit : WorkflowNet.exitPoints net part place)
    (hflow : net.transToPlace trans place) :
    PetriNet.Path
      (partialOrderProjection net part)
      (PetriNet.Node.trans trans)
      (PetriNet.Node.place BoundaryPlace.end_) :=
  PetriNet.Path.step
    (by
      simpa [PetriNet.flow] using
        partialOrderProjection_transToPlace_end
          net hpart hexit hflow)
    PetriNet.Path.refl

theorem partialOrderProjection_start_to_end
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
      (partialOrderProjection net part)
      (PetriNet.Node.place BoundaryPlace.start)
      (PetriNet.Node.place BoundaryPlace.end_) :=
  PetriNet.Path.trans
    (partialOrderProjection_start_to_transition net hpart hentry hstart)
    (partialOrderProjection_transition_to_end net hpart hexit hend)

theorem partialOrderProjection_pathIn_start_to_transition
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part place)
    (hflow : net.placeToTrans place trans) :
    PetriNet.PathIn
      (partialOrderProjection net part)
      (partialOrderProjectionPlaces net part)
      part
      (PetriNet.Node.place BoundaryPlace.start)
      (PetriNet.Node.trans trans) := by
  have hstartIn :
      PetriNet.nodeIn
        (partialOrderProjectionPlaces net part)
        part
        (PetriNet.Node.place BoundaryPlace.start) :=
    partialOrderProjectionPlaces_start net part
  have htransIn :
      PetriNet.nodeIn
        (partialOrderProjectionPlaces net part)
        part
        (PetriNet.Node.trans trans) :=
    hpart
  exact
    PetriNet.PathIn.step hstartIn htransIn
      (by
        simpa [PetriNet.flow] using
          partialOrderProjection_start_placeToTrans
            net hpart hentry hflow)
      (PetriNet.PathIn.refl htransIn)

theorem partialOrderProjection_pathIn_transition_to_start
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part place)
    (hflow : net.transToPlace trans place) :
    PetriNet.PathIn
      (partialOrderProjection net part)
      (partialOrderProjectionPlaces net part)
      part
      (PetriNet.Node.trans trans)
      (PetriNet.Node.place BoundaryPlace.start) := by
  have htransIn :
      PetriNet.nodeIn
        (partialOrderProjectionPlaces net part)
        part
        (PetriNet.Node.trans trans) :=
    hpart
  have hstartIn :
      PetriNet.nodeIn
        (partialOrderProjectionPlaces net part)
        part
        (PetriNet.Node.place BoundaryPlace.start) :=
    partialOrderProjectionPlaces_start net part
  exact
    PetriNet.PathIn.step htransIn hstartIn
      (by
        simpa [PetriNet.flow] using
          partialOrderProjection_transToPlace_start
            net hpart hentry hflow)
      (PetriNet.PathIn.refl hstartIn)

theorem partialOrderProjection_pathIn_end_to_transition
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hexit : WorkflowNet.exitPoints net part place)
    (hflow : net.placeToTrans place trans) :
    PetriNet.PathIn
      (partialOrderProjection net part)
      (partialOrderProjectionPlaces net part)
      part
      (PetriNet.Node.place BoundaryPlace.end_)
      (PetriNet.Node.trans trans) := by
  have hendIn :
      PetriNet.nodeIn
        (partialOrderProjectionPlaces net part)
        part
        (PetriNet.Node.place BoundaryPlace.end_) :=
    partialOrderProjectionPlaces_end net part
  have htransIn :
      PetriNet.nodeIn
        (partialOrderProjectionPlaces net part)
        part
        (PetriNet.Node.trans trans) :=
    hpart
  exact
    PetriNet.PathIn.step hendIn htransIn
      (by
        simpa [PetriNet.flow] using
          partialOrderProjection_end_placeToTrans
            net hpart hexit hflow)
      (PetriNet.PathIn.refl htransIn)

theorem partialOrderProjection_pathIn_transition_to_end
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (hexit : WorkflowNet.exitPoints net part place)
    (hflow : net.transToPlace trans place) :
    PetriNet.PathIn
      (partialOrderProjection net part)
      (partialOrderProjectionPlaces net part)
      part
      (PetriNet.Node.trans trans)
      (PetriNet.Node.place BoundaryPlace.end_) := by
  have htransIn :
      PetriNet.nodeIn
        (partialOrderProjectionPlaces net part)
        part
        (PetriNet.Node.trans trans) :=
    hpart
  have hendIn :
      PetriNet.nodeIn
        (partialOrderProjectionPlaces net part)
        part
        (PetriNet.Node.place BoundaryPlace.end_) :=
    partialOrderProjectionPlaces_end net part
  exact
    PetriNet.PathIn.step htransIn hendIn
      (by
        simpa [PetriNet.flow] using
          partialOrderProjection_transToPlace_end
            net hpart hexit hflow)
      (PetriNet.PathIn.refl hendIn)

theorem partialOrderProjection_pathIn_original_to_transition
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hnotEntry : ¬ WorkflowNet.entryPoints net part place)
    (hnotExit : ¬ WorkflowNet.exitPoints net part place)
    (hflow : net.placeToTrans place trans) :
    PetriNet.PathIn
      (partialOrderProjection net part)
      (partialOrderProjectionPlaces net part)
      part
      (PetriNet.Node.place (BoundaryPlace.original place))
      (PetriNet.Node.trans trans) := by
  have horiginalIn :
      PetriNet.nodeIn
        (partialOrderProjectionPlaces net part)
        part
        (PetriNet.Node.place (BoundaryPlace.original place)) :=
    partialOrderProjectionPlaces_original
      net htouching hnotEntry hnotExit
  have htransIn :
      PetriNet.nodeIn
        (partialOrderProjectionPlaces net part)
        part
        (PetriNet.Node.trans trans) :=
    hpart
  exact
    PetriNet.PathIn.step horiginalIn htransIn
      (by
        simpa [PetriNet.flow] using
          partialOrderProjection_original_placeToTrans
            net hpart htouching hnotEntry hnotExit hflow)
      (PetriNet.PathIn.refl htransIn)

theorem partialOrderProjection_pathIn_transition_to_original
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hnotEntry : ¬ WorkflowNet.entryPoints net part place)
    (hnotExit : ¬ WorkflowNet.exitPoints net part place)
    (hflow : net.transToPlace trans place) :
    PetriNet.PathIn
      (partialOrderProjection net part)
      (partialOrderProjectionPlaces net part)
      part
      (PetriNet.Node.trans trans)
      (PetriNet.Node.place (BoundaryPlace.original place)) := by
  have htransIn :
      PetriNet.nodeIn
        (partialOrderProjectionPlaces net part)
        part
        (PetriNet.Node.trans trans) :=
    hpart
  have horiginalIn :
      PetriNet.nodeIn
        (partialOrderProjectionPlaces net part)
        part
        (PetriNet.Node.place (BoundaryPlace.original place)) :=
    partialOrderProjectionPlaces_original
      net htouching hnotEntry hnotExit
  exact
    PetriNet.PathIn.step htransIn horiginalIn
      (by
        simpa [PetriNet.flow] using
          partialOrderProjection_transToPlace_original
            net hpart htouching hnotEntry hnotExit hflow)
      (PetriNet.PathIn.refl horiginalIn)

theorem partialOrderProjection_pathIn_start_to_end
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {entry exit : Place}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part entry)
    (hexit : WorkflowNet.exitPoints net part exit)
    (hstart : net.placeToTrans entry trans)
    (hend : net.transToPlace trans exit) :
    PetriNet.PathIn
      (partialOrderProjection net part)
      (partialOrderProjectionPlaces net part)
      part
      (PetriNet.Node.place BoundaryPlace.start)
      (PetriNet.Node.place BoundaryPlace.end_) :=
  PetriNet.PathIn.trans
    (partialOrderProjection_pathIn_start_to_transition
      net hpart hentry hstart)
    (partialOrderProjection_pathIn_transition_to_end
      net hpart hexit hend)

theorem partialOrderProjectionRestricted_start_placeToTrans
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part place)
    (hflow : net.placeToTrans place trans) :
    (partialOrderProjectionRestricted net part).placeToTrans
      ⟨BoundaryPlace.start, partialOrderProjectionPlaces_start net part⟩
      ⟨trans, hpart⟩ := by
  simpa [partialOrderProjectionRestricted, PetriNet.restrict] using
    partialOrderProjection_start_placeToTrans net hpart hentry hflow

theorem partialOrderProjectionRestricted_end_placeToTrans
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hexit : WorkflowNet.exitPoints net part place)
    (hflow : net.placeToTrans place trans) :
    (partialOrderProjectionRestricted net part).placeToTrans
      ⟨BoundaryPlace.end_, partialOrderProjectionPlaces_end net part⟩
      ⟨trans, hpart⟩ := by
  simpa [partialOrderProjectionRestricted, PetriNet.restrict] using
    partialOrderProjection_end_placeToTrans net hpart hexit hflow

theorem partialOrderProjectionRestricted_transToPlace_start
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part place)
    (hflow : net.transToPlace trans place) :
    (partialOrderProjectionRestricted net part).transToPlace
      ⟨trans, hpart⟩
      ⟨BoundaryPlace.start, partialOrderProjectionPlaces_start net part⟩ := by
  simpa [partialOrderProjectionRestricted, PetriNet.restrict] using
    partialOrderProjection_transToPlace_start net hpart hentry hflow

theorem partialOrderProjectionRestricted_transToPlace_end
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (hexit : WorkflowNet.exitPoints net part place)
    (hflow : net.transToPlace trans place) :
    (partialOrderProjectionRestricted net part).transToPlace
      ⟨trans, hpart⟩
      ⟨BoundaryPlace.end_, partialOrderProjectionPlaces_end net part⟩ := by
  simpa [partialOrderProjectionRestricted, PetriNet.restrict] using
    partialOrderProjection_transToPlace_end net hpart hexit hflow

theorem partialOrderProjectionRestricted_original_placeToTrans
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hnotEntry : ¬ WorkflowNet.entryPoints net part place)
    (hnotExit : ¬ WorkflowNet.exitPoints net part place)
    (hflow : net.placeToTrans place trans) :
    (partialOrderProjectionRestricted net part).placeToTrans
      ⟨BoundaryPlace.original place,
        partialOrderProjectionPlaces_original
          net htouching hnotEntry hnotExit⟩
      ⟨trans, hpart⟩ := by
  simpa [partialOrderProjectionRestricted, PetriNet.restrict] using
    partialOrderProjection_original_placeToTrans
      net hpart htouching hnotEntry hnotExit hflow

theorem partialOrderProjectionRestricted_transToPlace_original
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (htouching : PetriNet.placesTouching net.toPetriNet part place)
    (hnotEntry : ¬ WorkflowNet.entryPoints net part place)
    (hnotExit : ¬ WorkflowNet.exitPoints net part place)
    (hflow : net.transToPlace trans place) :
    (partialOrderProjectionRestricted net part).transToPlace
      ⟨trans, hpart⟩
      ⟨BoundaryPlace.original place,
        partialOrderProjectionPlaces_original
          net htouching hnotEntry hnotExit⟩ := by
  simpa [partialOrderProjectionRestricted, PetriNet.restrict] using
    partialOrderProjection_transToPlace_original
      net hpart htouching hnotEntry hnotExit hflow

theorem partialOrderProjectionRestricted_original_to_transition
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
      (partialOrderProjectionRestricted net part)
      (PetriNet.Node.place
        ⟨BoundaryPlace.original place,
          partialOrderProjectionPlaces_original
            net htouching hnotEntry hnotExit⟩)
      (PetriNet.Node.trans ⟨trans, hpart⟩) :=
  PetriNet.Path.step
    (by
      simpa [PetriNet.flow] using
        partialOrderProjectionRestricted_original_placeToTrans
          net hpart htouching hnotEntry hnotExit hflow)
    PetriNet.Path.refl

theorem partialOrderProjectionRestricted_transition_to_original
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
      (partialOrderProjectionRestricted net part)
      (PetriNet.Node.trans ⟨trans, hpart⟩)
      (PetriNet.Node.place
        ⟨BoundaryPlace.original place,
          partialOrderProjectionPlaces_original
            net htouching hnotEntry hnotExit⟩) :=
  PetriNet.Path.step
    (by
      simpa [PetriNet.flow] using
        partialOrderProjectionRestricted_transToPlace_original
          net hpart htouching hnotEntry hnotExit hflow)
    PetriNet.Path.refl

theorem partialOrderProjectionRestricted_start_to_transition
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part place)
    (hflow : net.placeToTrans place trans) :
    PetriNet.Path
      (partialOrderProjectionRestricted net part)
      (PetriNet.Node.place
        ⟨BoundaryPlace.start, partialOrderProjectionPlaces_start net part⟩)
      (PetriNet.Node.trans ⟨trans, hpart⟩) :=
  PetriNet.Path.step
    (by
      simpa [PetriNet.flow] using
        partialOrderProjectionRestricted_start_placeToTrans
          net hpart hentry hflow)
    PetriNet.Path.refl

theorem partialOrderProjectionRestricted_transition_to_start
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (hentry : WorkflowNet.entryPoints net part place)
    (hflow : net.transToPlace trans place) :
    PetriNet.Path
      (partialOrderProjectionRestricted net part)
      (PetriNet.Node.trans ⟨trans, hpart⟩)
      (PetriNet.Node.place
        ⟨BoundaryPlace.start, partialOrderProjectionPlaces_start net part⟩) :=
  PetriNet.Path.step
    (by
      simpa [PetriNet.flow] using
        partialOrderProjectionRestricted_transToPlace_start
          net hpart hentry hflow)
    PetriNet.Path.refl

theorem partialOrderProjectionRestricted_end_to_transition
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    {trans : Trans}
    (hpart : part trans)
    (hexit : WorkflowNet.exitPoints net part place)
    (hflow : net.placeToTrans place trans) :
    PetriNet.Path
      (partialOrderProjectionRestricted net part)
      (PetriNet.Node.place
        ⟨BoundaryPlace.end_, partialOrderProjectionPlaces_end net part⟩)
      (PetriNet.Node.trans ⟨trans, hpart⟩) :=
  PetriNet.Path.step
    (by
      simpa [PetriNet.flow] using
        partialOrderProjectionRestricted_end_placeToTrans
          net hpart hexit hflow)
    PetriNet.Path.refl

theorem partialOrderProjectionRestricted_transition_to_end
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {trans : Trans}
    {place : Place}
    (hpart : part trans)
    (hexit : WorkflowNet.exitPoints net part place)
    (hflow : net.transToPlace trans place) :
    PetriNet.Path
      (partialOrderProjectionRestricted net part)
      (PetriNet.Node.trans ⟨trans, hpart⟩)
      (PetriNet.Node.place
        ⟨BoundaryPlace.end_, partialOrderProjectionPlaces_end net part⟩) :=
  PetriNet.Path.step
    (by
      simpa [PetriNet.flow] using
        partialOrderProjectionRestricted_transToPlace_end
          net hpart hexit hflow)
    PetriNet.Path.refl

theorem partialOrderProjectionRestricted_start_to_end
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
      (partialOrderProjectionRestricted net part)
      (PetriNet.Node.place
        ⟨BoundaryPlace.start, partialOrderProjectionPlaces_start net part⟩)
      (PetriNet.Node.place
        ⟨BoundaryPlace.end_, partialOrderProjectionPlaces_end net part⟩) :=
  PetriNet.Path.trans
    (partialOrderProjectionRestricted_start_to_transition
      net hpart hentry hstart)
    (partialOrderProjectionRestricted_transition_to_end
      net hpart hexit hend)

theorem partialOrderProjectionRestricted_transition_connected_of_entry_exit
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
        (partialOrderProjectionRestricted net part)
        (PetriNet.Node.place
          ⟨BoundaryPlace.start, partialOrderProjectionPlaces_start net part⟩)
        (PetriNet.Node.trans trans) ∧
      PetriNet.Path
        (partialOrderProjectionRestricted net part)
        (PetriNet.Node.trans trans)
        (PetriNet.Node.place
          ⟨BoundaryPlace.end_, partialOrderProjectionPlaces_end net part⟩) := by
  rcases hentry with ⟨entry, hentryPoint, hentryFlow⟩
  rcases hexit with ⟨exit, hexitPoint, hexitFlow⟩
  exact
    ⟨partialOrderProjectionRestricted_start_to_transition
        net trans.property hentryPoint hentryFlow,
      partialOrderProjectionRestricted_transition_to_end
        net trans.property hexitPoint hexitFlow⟩

theorem partialOrderProjectionRestricted_original_connected_of_incident_transitions
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    {place : Place}
    (hplace :
      partialOrderProjectionPlaces net part (BoundaryPlace.original place))
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
        (partialOrderProjectionRestricted net part)
        (PetriNet.Node.place
          ⟨BoundaryPlace.start, partialOrderProjectionPlaces_start net part⟩)
        (PetriNet.Node.place
          ⟨BoundaryPlace.original place, hplace⟩) ∧
      PetriNet.Path
        (partialOrderProjectionRestricted net part)
        (PetriNet.Node.place
          ⟨BoundaryPlace.original place, hplace⟩)
        (PetriNet.Node.place
          ⟨BoundaryPlace.end_, partialOrderProjectionPlaces_end net part⟩) := by
  rcases hplace with ⟨htouching, hnotEntry, hnotExit⟩
  rcases hincoming with
    ⟨inTrans, hinPart, hinFlow, entry, hentryPoint, hentryFlow⟩
  rcases houtgoing with
    ⟨outTrans, houtPart, houtFlow, exit, hexitPoint, hexitFlow⟩
  constructor
  · exact
      PetriNet.Path.trans
        (partialOrderProjectionRestricted_start_to_transition
          net hinPart hentryPoint hentryFlow)
        (partialOrderProjectionRestricted_transition_to_original
          net hinPart htouching hnotEntry hnotExit hinFlow)
  · exact
      PetriNet.Path.trans
        (partialOrderProjectionRestricted_original_to_transition
          net houtPart htouching hnotEntry hnotExit houtFlow)
        (partialOrderProjectionRestricted_transition_to_end
          net houtPart hexitPoint hexitFlow)

theorem partialOrderProjectionRestricted_connected_of_entry_exit_incidence
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
        partialOrderProjectionPlaces net part (BoundaryPlace.original place) ->
          ∃ trans,
            part trans ∧
              net.transToPlace trans place ∧
              ∃ entry,
                WorkflowNet.entryPoints net part entry ∧
                  net.placeToTrans entry trans)
    (houtgoing :
      ∀ {place : Place},
        partialOrderProjectionPlaces net part (BoundaryPlace.original place) ->
          ∃ trans,
            part trans ∧
              net.placeToTrans place trans ∧
              ∃ exit,
                WorkflowNet.exitPoints net part exit ∧
                  net.transToPlace trans exit) :
    ∀ node :
      PetriNet.Node
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place}
        {trans : Trans // part trans},
      PetriNet.Path
          (partialOrderProjectionRestricted net part)
          (PetriNet.Node.place
            ⟨BoundaryPlace.start, partialOrderProjectionPlaces_start net part⟩)
          node ∧
        PetriNet.Path
          (partialOrderProjectionRestricted net part)
          node
          (PetriNet.Node.place
            ⟨BoundaryPlace.end_,
              partialOrderProjectionPlaces_end net part⟩) := by
  have hstartToEnd :
      PetriNet.Path
        (partialOrderProjectionRestricted net part)
        (PetriNet.Node.place
          ⟨BoundaryPlace.start, partialOrderProjectionPlaces_start net part⟩)
        (PetriNet.Node.place
          ⟨BoundaryPlace.end_, partialOrderProjectionPlaces_end net part⟩) := by
    rcases hnonempty with ⟨trans, hpart⟩
    rcases hentry trans hpart with ⟨entry, hentryPoint, hentryFlow⟩
    rcases hexit trans hpart with ⟨exit, hexitPoint, hexitFlow⟩
    exact
      partialOrderProjectionRestricted_start_to_end
        net hpart hentryPoint hexitPoint hentryFlow hexitFlow
  intro node
  cases node with
  | place place =>
      rcases place with ⟨place, hplace⟩
      cases place with
      | start =>
          exact ⟨PetriNet.Path.refl, hstartToEnd⟩
      | end_ =>
          exact ⟨hstartToEnd, PetriNet.Path.refl⟩
      | original place =>
          exact
            partialOrderProjectionRestricted_original_connected_of_incident_transitions
              net hplace (hincoming hplace) (houtgoing hplace)
  | trans trans =>
      exact
        partialOrderProjectionRestricted_transition_connected_of_entry_exit
          net trans (hentry trans.val trans.property)
          (hexit trans.val trans.property)

def partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩)) :
    WorkflowNet
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})
      (PetriNet.NormalizedTrans {trans : Trans // part trans}) :=
  WorkflowNet.normalized
    (partialOrderProjectionRestricted net part)
    ⟨BoundaryPlace.start, partialOrderProjectionPlaces_start net part⟩
    ⟨BoundaryPlace.end_, partialOrderProjectionPlaces_end net part⟩
    hconnected

theorem partialOrderProjectionRestrictedNormalized_original_enabled_of_original_enabled
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    (marking : Marking Place)
    {trans : Trans}
    (hpart : part trans)
    (henabled : WorkflowNet.enabled net marking trans)
    (hentriesMarked :
      ∀ entry, WorkflowNet.entryPoints net part entry ->
        marking entry > 0)
    (hexitsMarked :
      ∀ exit, WorkflowNet.exitPoints net part exit ->
        marking exit > 0) :
    WorkflowNet.enabled
      (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
        net part hconnected)
      (partialOrderProjectionNormalizedMarking net part marking)
      (PetriNet.NormalizedTrans.original ⟨trans, hpart⟩) := by
  intro place hflow
  cases place with
  | source =>
      simp [
        partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected,
        WorkflowNet.normalized, PetriNet.normalize] at hflow
  | sink =>
      simp [
        partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected,
        WorkflowNet.normalized, PetriNet.normalize] at hflow
  | original place =>
      have hrestricted :
          (partialOrderProjectionRestricted net part).placeToTrans
            place
            ⟨trans, hpart⟩ := by
        simpa [
          partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected,
          WorkflowNet.normalized, PetriNet.normalize] using hflow
      rcases place with ⟨place, hplace⟩
      cases place with
      | original original =>
          rw [partialOrderProjectionNormalizedMarking_original]
          simpa [partialOrderProjectionRestrictedMarking] using
            henabled original
              ((partialOrderProjectionRestricted_original_placeToTrans_iff'
                net hplace ⟨trans, hpart⟩).mp hrestricted)
      | start =>
          rw [partialOrderProjectionNormalizedMarking_original]
          unfold partialOrderProjectionRestrictedMarking
          dsimp
          rw [if_pos hentriesMarked]
          exact Nat.zero_lt_succ 0
      | end_ =>
          rw [partialOrderProjectionNormalizedMarking_original]
          unfold partialOrderProjectionRestrictedMarking
          dsimp
          rw [if_pos hexitsMarked]
          exact Nat.zero_lt_succ 0

theorem partialOrderProjectionRestrictedNormalized_original_fires_to_fire_of_original_enabled
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    (marking : Marking Place)
    {trans : Trans}
    (hpart : part trans)
    (henabled : WorkflowNet.enabled net marking trans)
    (hentriesMarked :
      ∀ entry, WorkflowNet.entryPoints net part entry ->
        marking entry > 0)
    (hexitsMarked :
      ∀ exit, WorkflowNet.exitPoints net part exit ->
        marking exit > 0) :
    WorkflowNet.fires
      (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
        net part hconnected)
      (partialOrderProjectionNormalizedMarking net part marking)
      (PetriNet.NormalizedTrans.original ⟨trans, hpart⟩)
      (WorkflowNet.fire
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected)
        (partialOrderProjectionNormalizedMarking net part marking)
        (PetriNet.NormalizedTrans.original ⟨trans, hpart⟩)) :=
  ⟨partialOrderProjectionRestrictedNormalized_original_enabled_of_original_enabled
      net hconnected marking hpart henabled hentriesMarked hexitsMarked,
    rfl⟩

theorem partialOrderProjectionRestrictedNormalized_original_firing_witness_of_original_enabled
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    (marking : Marking Place)
    {trans : Trans}
    (hpart : part trans)
    (henabled : WorkflowNet.enabled net marking trans)
    (hentriesMarked :
      ∀ entry, WorkflowNet.entryPoints net part entry ->
        marking entry > 0)
    (hexitsMarked :
      ∀ exit, WorkflowNet.exitPoints net part exit ->
        marking exit > 0) :
    ∃ after,
      WorkflowNet.fires
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected)
        (partialOrderProjectionNormalizedMarking net part marking)
        (PetriNet.NormalizedTrans.original ⟨trans, hpart⟩)
        after :=
  ⟨WorkflowNet.fire
      (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
        net part hconnected)
      (partialOrderProjectionNormalizedMarking net part marking)
      (PetriNet.NormalizedTrans.original ⟨trans, hpart⟩),
    partialOrderProjectionRestrictedNormalized_original_fires_to_fire_of_original_enabled
      net hconnected marking hpart henabled hentriesMarked hexitsMarked⟩

theorem partialOrderProjectionRestrictedNormalized_original_singleton_firingSequence_of_original_enabled
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    (marking : Marking Place)
    {trans : Trans}
    (hpart : part trans)
    (henabled : WorkflowNet.enabled net marking trans)
    (hentriesMarked :
      ∀ entry, WorkflowNet.entryPoints net part entry ->
        marking entry > 0)
    (hexitsMarked :
      ∀ exit, WorkflowNet.exitPoints net part exit ->
        marking exit > 0) :
    WorkflowNet.FiringSequence
      (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
        net part hconnected)
      (partialOrderProjectionNormalizedMarking net part marking)
      [PetriNet.NormalizedTrans.original ⟨trans, hpart⟩]
      (WorkflowNet.fire
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected)
        (partialOrderProjectionNormalizedMarking net part marking)
        (PetriNet.NormalizedTrans.original ⟨trans, hpart⟩)) :=
  WorkflowNet.firingSequence_singleton
    (partialOrderProjectionRestrictedNormalized_original_fires_to_fire_of_original_enabled
      net hconnected marking hpart henabled hentriesMarked hexitsMarked)

theorem partialOrderProjectionRestrictedNormalized_original_reachable_fire_of_original_enabled
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    (marking : Marking Place)
    {trans : Trans}
    (hpart : part trans)
    (henabled : WorkflowNet.enabled net marking trans)
    (hentriesMarked :
      ∀ entry, WorkflowNet.entryPoints net part entry ->
        marking entry > 0)
    (hexitsMarked :
      ∀ exit, WorkflowNet.exitPoints net part exit ->
        marking exit > 0) :
    WorkflowNet.reachable
      (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
        net part hconnected)
      (partialOrderProjectionNormalizedMarking net part marking)
      (WorkflowNet.fire
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected)
        (partialOrderProjectionNormalizedMarking net part marking)
        (PetriNet.NormalizedTrans.original ⟨trans, hpart⟩)) :=
  WorkflowNet.reachable_of_fires
    (partialOrderProjectionRestrictedNormalized_original_fires_to_fire_of_original_enabled
      net hconnected marking hpart henabled hentriesMarked hexitsMarked)

theorem partialOrderProjectionRestrictedNormalized_original_noDeadTransition_witness_of_original_enabled
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    (marking : Marking Place)
    {trans : Trans}
    (hpart : part trans)
    (hreachable :
      WorkflowNet.reachable
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected)
        (WorkflowNet.initial
          (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
            net part hconnected))
        (partialOrderProjectionNormalizedMarking net part marking))
    (henabled : WorkflowNet.enabled net marking trans)
    (hentriesMarked :
      ∀ entry, WorkflowNet.entryPoints net part entry ->
        marking entry > 0)
    (hexitsMarked :
      ∀ exit, WorkflowNet.exitPoints net part exit ->
        marking exit > 0) :
    ∃ projectedMarking,
      WorkflowNet.reachable
          (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
            net part hconnected)
          (WorkflowNet.initial
            (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
              net part hconnected))
          projectedMarking ∧
        WorkflowNet.enabled
          (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
            net part hconnected)
          projectedMarking
          (PetriNet.NormalizedTrans.original ⟨trans, hpart⟩) :=
  ⟨partialOrderProjectionNormalizedMarking net part marking,
    hreachable,
    partialOrderProjectionRestrictedNormalized_original_enabled_of_original_enabled
      net hconnected marking hpart henabled hentriesMarked hexitsMarked⟩

theorem partialOrderProjectionRestrictedNormalized_original_noDeadTransition_witnesses_of_original_enabled
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    (hwitness :
      ∀ trans : {trans : Trans // part trans},
        ∃ marking,
          WorkflowNet.reachable
              (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                net part hconnected)
              (WorkflowNet.initial
                (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                  net part hconnected))
              (partialOrderProjectionNormalizedMarking net part marking) ∧
            WorkflowNet.enabled net marking trans.val ∧
            (∀ entry, WorkflowNet.entryPoints net part entry ->
              marking entry > 0) ∧
            (∀ exit, WorkflowNet.exitPoints net part exit ->
              marking exit > 0)) :
    ∀ trans : {trans : Trans // part trans},
      ∃ projectedMarking,
        WorkflowNet.reachable
            (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
              net part hconnected)
            (WorkflowNet.initial
              (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                net part hconnected))
            projectedMarking ∧
          WorkflowNet.enabled
            (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
              net part hconnected)
            projectedMarking
            (PetriNet.NormalizedTrans.original trans) := by
  intro trans
  rcases hwitness trans with
    ⟨marking, hreachable, henabled, hentriesMarked, hexitsMarked⟩
  exact
    partialOrderProjectionRestrictedNormalized_original_noDeadTransition_witness_of_original_enabled
      net hconnected marking trans.property hreachable
      henabled hentriesMarked hexitsMarked

theorem partialOrderProjectionRestrictedNormalized_enter_enabled_initial
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩)) :
    WorkflowNet.enabled
      (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
        net part hconnected)
      (WorkflowNet.initial
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected))
      PetriNet.NormalizedTrans.enter := by
  intro place hflow
  cases place with
  | source =>
      simp [
        partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected,
        WorkflowNet.normalized, WorkflowNet.initial, Marking.single]
  | original place =>
      simp [
        partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected,
        WorkflowNet.normalized, PetriNet.normalize] at hflow
  | sink =>
      simp [
        partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected,
        WorkflowNet.normalized, PetriNet.normalize] at hflow

theorem partialOrderProjectionRestrictedNormalized_enter_noDeadTransition_witness
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩)) :
    ∃ projectedMarking,
      WorkflowNet.reachable
          (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
            net part hconnected)
          (WorkflowNet.initial
            (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
              net part hconnected))
          projectedMarking ∧
        WorkflowNet.enabled
          (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
            net part hconnected)
          projectedMarking
          PetriNet.NormalizedTrans.enter :=
  ⟨WorkflowNet.initial
      (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
        net part hconnected),
    ⟨[], WorkflowNet.FiringSequence.nil⟩,
    partialOrderProjectionRestrictedNormalized_enter_enabled_initial
      net hconnected⟩

theorem partialOrderProjectionRestrictedNormalized_exit_enabled_of_exits_marked
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    (marking : Marking Place)
    (hexitsMarked :
      ∀ exit, WorkflowNet.exitPoints net part exit ->
        marking exit > 0) :
    WorkflowNet.enabled
      (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
        net part hconnected)
      (partialOrderProjectionNormalizedMarking net part marking)
      PetriNet.NormalizedTrans.exit := by
  intro place hflow
  cases place with
  | source =>
      simp [
        partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected,
        WorkflowNet.normalized, PetriNet.normalize] at hflow
  | original place =>
      have hplace :
          place =
            ⟨BoundaryPlace.end_,
              partialOrderProjectionPlaces_end net part⟩ := by
        simpa [
          partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected,
          WorkflowNet.normalized, PetriNet.normalize] using hflow
      subst hplace
      rw [
        partialOrderProjectionNormalizedMarking_end_of_exits_marked
          net part marking hexitsMarked]
      exact Nat.zero_lt_succ 0
  | sink =>
      simp [
        partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected,
        WorkflowNet.normalized, PetriNet.normalize] at hflow

theorem partialOrderProjectionRestrictedNormalized_exit_noDeadTransition_witness
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    (marking : Marking Place)
    (hreachable :
      WorkflowNet.reachable
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected)
        (WorkflowNet.initial
          (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
            net part hconnected))
        (partialOrderProjectionNormalizedMarking net part marking))
    (hexitsMarked :
      ∀ exit, WorkflowNet.exitPoints net part exit ->
        marking exit > 0) :
    ∃ projectedMarking,
      WorkflowNet.reachable
          (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
            net part hconnected)
          (WorkflowNet.initial
            (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
              net part hconnected))
          projectedMarking ∧
        WorkflowNet.enabled
          (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
            net part hconnected)
          projectedMarking
          PetriNet.NormalizedTrans.exit :=
  ⟨partialOrderProjectionNormalizedMarking net part marking,
    hreachable,
    partialOrderProjectionRestrictedNormalized_exit_enabled_of_exits_marked
      net hconnected marking hexitsMarked⟩

theorem partialOrderProjectionRestrictedNormalized_noDeadTransitions_of_witnesses
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    (horiginal :
      ∀ trans : {trans : Trans // part trans},
        ∃ marking,
          WorkflowNet.reachable
              (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                net part hconnected)
              (WorkflowNet.initial
                (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                  net part hconnected))
              (partialOrderProjectionNormalizedMarking net part marking) ∧
            WorkflowNet.enabled net marking trans.val ∧
            (∀ entry, WorkflowNet.entryPoints net part entry ->
              marking entry > 0) ∧
            (∀ exit, WorkflowNet.exitPoints net part exit ->
              marking exit > 0))
    (hexit :
      ∃ marking,
        WorkflowNet.reachable
            (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
              net part hconnected)
            (WorkflowNet.initial
              (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                net part hconnected))
            (partialOrderProjectionNormalizedMarking net part marking) ∧
          (∀ exit, WorkflowNet.exitPoints net part exit ->
            marking exit > 0)) :
    WorkflowNet.noDeadTransitions
      (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
        net part hconnected) := by
  intro trans
  cases trans with
  | enter =>
      exact
        partialOrderProjectionRestrictedNormalized_enter_noDeadTransition_witness
          net hconnected
  | original trans =>
      exact
        partialOrderProjectionRestrictedNormalized_original_noDeadTransition_witnesses_of_original_enabled
          net hconnected horiginal trans
  | exit =>
      rcases hexit with ⟨marking, hreachable, hexitsMarked⟩
      exact
        partialOrderProjectionRestrictedNormalized_exit_noDeadTransition_witness
          net hconnected marking hreachable hexitsMarked

theorem partialOrderProjectionRestrictedNormalized_sound_of_witnesses
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    (horiginal :
      ∀ trans : {trans : Trans // part trans},
        ∃ marking,
          WorkflowNet.reachable
              (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                net part hconnected)
              (WorkflowNet.initial
                (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                  net part hconnected))
              (partialOrderProjectionNormalizedMarking net part marking) ∧
            WorkflowNet.enabled net marking trans.val ∧
            (∀ entry, WorkflowNet.entryPoints net part entry ->
              marking entry > 0) ∧
            (∀ exit, WorkflowNet.exitPoints net part exit ->
              marking exit > 0))
    (hexit :
      ∃ marking,
        WorkflowNet.reachable
            (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
              net part hconnected)
            (WorkflowNet.initial
              (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                net part hconnected))
            (partialOrderProjectionNormalizedMarking net part marking) ∧
          (∀ exit, WorkflowNet.exitPoints net part exit ->
            marking exit > 0))
    (hcomplete :
      WorkflowNet.optionToComplete
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected))
    (hproper :
      WorkflowNet.properCompletion
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected)) :
    WorkflowNet.sound
      (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
        net part hconnected) :=
  ⟨partialOrderProjectionRestrictedNormalized_noDeadTransitions_of_witnesses
      net hconnected horiginal hexit,
    hcomplete,
    hproper⟩

theorem partialOrderProjectionRestrictedNormalized_safeAndSound_of_witnesses
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    (horiginal :
      ∀ trans : {trans : Trans // part trans},
        ∃ marking,
          WorkflowNet.reachable
              (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                net part hconnected)
              (WorkflowNet.initial
                (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                  net part hconnected))
              (partialOrderProjectionNormalizedMarking net part marking) ∧
            WorkflowNet.enabled net marking trans.val ∧
            (∀ entry, WorkflowNet.entryPoints net part entry ->
              marking entry > 0) ∧
            (∀ exit, WorkflowNet.exitPoints net part exit ->
              marking exit > 0))
    (hexit :
      ∃ marking,
        WorkflowNet.reachable
            (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
              net part hconnected)
            (WorkflowNet.initial
              (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                net part hconnected))
            (partialOrderProjectionNormalizedMarking net part marking) ∧
          (∀ exit, WorkflowNet.exitPoints net part exit ->
            marking exit > 0))
    (hsafe :
      WorkflowNet.safe
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected))
    (hcomplete :
      WorkflowNet.optionToComplete
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected))
    (hproper :
      WorkflowNet.properCompletion
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected)) :
    WorkflowNet.safeAndSound
      (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
        net part hconnected) :=
  ⟨hsafe,
    partialOrderProjectionRestrictedNormalized_sound_of_witnesses
      net hconnected horiginal hexit hcomplete hproper⟩

theorem partialOrderProjectionRestrictedNormalized_safe_of_original_reachable_shape
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    (horiginalSafe : WorkflowNet.safe net)
    (hshape :
      ∀ projected,
        WorkflowNet.reachable
            (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
              net part hconnected)
            (WorkflowNet.initial
              (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                net part hconnected))
            projected ->
          ∃ original,
            WorkflowNet.reachable net (WorkflowNet.initial net) original ∧
              projected =
                partialOrderProjectionNormalizedMarking
                  net part original) :
    WorkflowNet.safe
      (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
        net part hconnected) := by
  intro projected hreachable place
  rcases hshape projected hreachable with
    ⟨original, horiginalReachable, hprojected⟩
  subst hprojected
  exact
    partialOrderProjectionNormalizedMarking_le_one_of_original_le_one
      net part original
      (fun place => horiginalSafe original horiginalReachable place)
      place

theorem partialOrderProjectionRestrictedNormalized_safeAndSound_of_original_reachable_shape
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    (horiginal :
      ∀ trans : {trans : Trans // part trans},
        ∃ marking,
          WorkflowNet.reachable
              (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                net part hconnected)
              (WorkflowNet.initial
                (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                  net part hconnected))
              (partialOrderProjectionNormalizedMarking net part marking) ∧
            WorkflowNet.enabled net marking trans.val ∧
            (∀ entry, WorkflowNet.entryPoints net part entry ->
              marking entry > 0) ∧
            (∀ exit, WorkflowNet.exitPoints net part exit ->
              marking exit > 0))
    (hexit :
      ∃ marking,
        WorkflowNet.reachable
            (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
              net part hconnected)
            (WorkflowNet.initial
              (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                net part hconnected))
            (partialOrderProjectionNormalizedMarking net part marking) ∧
          (∀ exit, WorkflowNet.exitPoints net part exit ->
            marking exit > 0))
    (horiginalSafe : WorkflowNet.safe net)
    (hshape :
      ∀ projected,
        WorkflowNet.reachable
            (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
              net part hconnected)
            (WorkflowNet.initial
              (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                net part hconnected))
            projected ->
          ∃ original,
            WorkflowNet.reachable net (WorkflowNet.initial net) original ∧
              projected =
                partialOrderProjectionNormalizedMarking
                  net part original)
    (hcomplete :
      WorkflowNet.optionToComplete
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected))
    (hproper :
      WorkflowNet.properCompletion
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected)) :
    WorkflowNet.safeAndSound
      (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
        net part hconnected) :=
  partialOrderProjectionRestrictedNormalized_safeAndSound_of_witnesses
    net hconnected horiginal hexit
    (partialOrderProjectionRestrictedNormalized_safe_of_original_reachable_shape
      net hconnected horiginalSafe hshape)
    hcomplete
    hproper

def partialOrderProjectionRestrictedNormalizedReachableShape
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    (marking :
      Marking
        (PetriNet.NormalizedPlace
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place})) : Prop :=
  marking =
      WorkflowNet.initial
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected) ∨
    (∃ original,
      WorkflowNet.reachable net (WorkflowNet.initial net) original ∧
        marking =
          partialOrderProjectionNormalizedMarking
            net part original) ∨
    marking =
      WorkflowNet.final
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected)

theorem partialOrderProjectionRestrictedNormalizedReachableShape_initial
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩)) :
    partialOrderProjectionRestrictedNormalizedReachableShape
      net part hconnected
      (WorkflowNet.initial
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected)) :=
  Or.inl rfl

theorem partialOrderProjectionRestrictedNormalizedReachableShape_projected
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    {original : Marking Place}
    (hreachable :
      WorkflowNet.reachable net (WorkflowNet.initial net) original) :
    partialOrderProjectionRestrictedNormalizedReachableShape
      net part hconnected
      (partialOrderProjectionNormalizedMarking net part original) :=
  Or.inr (Or.inl ⟨original, hreachable, rfl⟩)

theorem partialOrderProjectionRestrictedNormalizedReachableShape_final
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩)) :
    partialOrderProjectionRestrictedNormalizedReachableShape
      net part hconnected
      (WorkflowNet.final
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected)) :=
  Or.inr (Or.inr rfl)

theorem partialOrderProjectionRestrictedNormalizedReachableShape_cases
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    {marking :
      Marking
        (PetriNet.NormalizedPlace
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place})}
    {motive : Prop}
    (hshape :
      partialOrderProjectionRestrictedNormalizedReachableShape
        net part hconnected marking)
    (hinitial :
      marking =
          WorkflowNet.initial
            (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
              net part hconnected) ->
        motive)
    (hprojected :
      (∃ original,
        WorkflowNet.reachable net (WorkflowNet.initial net) original ∧
          marking =
            partialOrderProjectionNormalizedMarking
              net part original) ->
        motive)
    (hfinal :
      marking =
          WorkflowNet.final
            (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
              net part hconnected) ->
        motive) :
    motive := by
  rcases hshape with hinitialShape | hrest
  · exact hinitial hinitialShape
  · rcases hrest with hprojectedShape | hfinalShape
    · exact hprojected hprojectedShape
    · exact hfinal hfinalShape

theorem partialOrderProjectionRestrictedNormalized_initial_le_one
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩)) :
    ∀ place,
      WorkflowNet.initial
          (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
            net part hconnected)
          place ≤ 1 := by
  intro place
  unfold WorkflowNet.initial Marking.single
  by_cases hplace :
      place =
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected).source
  · simp [hplace]
  · simp [hplace]

theorem partialOrderProjectionRestrictedNormalized_final_le_one
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩)) :
    ∀ place,
      WorkflowNet.final
          (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
            net part hconnected)
          place ≤ 1 := by
  intro place
  unfold WorkflowNet.final Marking.single
  by_cases hplace :
      place =
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected).sink
  · simp [hplace]
  · simp [hplace]

theorem partialOrderProjectionRestrictedNormalizedReachableShape_le_one_of_original_safe
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    (horiginalSafe : WorkflowNet.safe net)
    {marking :
      Marking
        (PetriNet.NormalizedPlace
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place})}
    (hshape :
      partialOrderProjectionRestrictedNormalizedReachableShape
        net part hconnected marking) :
    ∀ place, marking place ≤ 1 := by
  intro place
  exact
    partialOrderProjectionRestrictedNormalizedReachableShape_cases
      net hconnected hshape
      (fun hinitial => by
        subst hinitial
        exact
          partialOrderProjectionRestrictedNormalized_initial_le_one
            net hconnected place)
      (fun hprojected => by
        rcases hprojected with
          ⟨original, horiginalReachable, hprojected⟩
        subst hprojected
        exact
          partialOrderProjectionNormalizedMarking_le_one_of_original_le_one
            net part original
            (fun place => horiginalSafe original horiginalReachable place)
            place)
      (fun hfinal => by
        subst hfinal
        exact
          partialOrderProjectionRestrictedNormalized_final_le_one
            net hconnected place)

theorem partialOrderProjectionRestrictedNormalized_safe_of_original_three_way_reachable_shape
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    (horiginalSafe : WorkflowNet.safe net)
    (hshape :
      ∀ projected,
        WorkflowNet.reachable
            (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
              net part hconnected)
            (WorkflowNet.initial
              (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                net part hconnected))
            projected ->
          partialOrderProjectionRestrictedNormalizedReachableShape
            net part hconnected projected) :
    WorkflowNet.safe
      (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
        net part hconnected) := by
  intro projected hreachable place
  exact
    partialOrderProjectionRestrictedNormalizedReachableShape_le_one_of_original_safe
      net hconnected horiginalSafe (hshape projected hreachable) place

theorem partialOrderProjectionRestrictedNormalized_safeAndSound_of_original_three_way_reachable_shape
    [DecidableEq Place]
    (net : WorkflowNet Place Trans)
    {part : Set Trans}
    [DecidableEq
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})]
    (hconnected :
      ∀ node :
        PetriNet.Node
          {place : BoundaryPlace Place //
            partialOrderProjectionPlaces net part place}
          {trans : Trans // part trans},
        PetriNet.Path
            (partialOrderProjectionRestricted net part)
            (PetriNet.Node.place
              ⟨BoundaryPlace.start,
                partialOrderProjectionPlaces_start net part⟩)
            node ∧
          PetriNet.Path
            (partialOrderProjectionRestricted net part)
            node
            (PetriNet.Node.place
              ⟨BoundaryPlace.end_,
                partialOrderProjectionPlaces_end net part⟩))
    (horiginal :
      ∀ trans : {trans : Trans // part trans},
        ∃ marking,
          WorkflowNet.reachable
              (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                net part hconnected)
              (WorkflowNet.initial
                (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                  net part hconnected))
              (partialOrderProjectionNormalizedMarking net part marking) ∧
            WorkflowNet.enabled net marking trans.val ∧
            (∀ entry, WorkflowNet.entryPoints net part entry ->
              marking entry > 0) ∧
            (∀ exit, WorkflowNet.exitPoints net part exit ->
              marking exit > 0))
    (hexit :
      ∃ marking,
        WorkflowNet.reachable
            (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
              net part hconnected)
            (WorkflowNet.initial
              (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                net part hconnected))
            (partialOrderProjectionNormalizedMarking net part marking) ∧
          (∀ exit, WorkflowNet.exitPoints net part exit ->
            marking exit > 0))
    (horiginalSafe : WorkflowNet.safe net)
    (hshape :
      ∀ projected,
        WorkflowNet.reachable
            (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
              net part hconnected)
            (WorkflowNet.initial
              (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
                net part hconnected))
            projected ->
          partialOrderProjectionRestrictedNormalizedReachableShape
            net part hconnected projected)
    (hcomplete :
      WorkflowNet.optionToComplete
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected))
    (hproper :
      WorkflowNet.properCompletion
        (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
          net part hconnected)) :
    WorkflowNet.safeAndSound
      (partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
        net part hconnected) :=
  partialOrderProjectionRestrictedNormalized_safeAndSound_of_witnesses
    net hconnected horiginal hexit
    (partialOrderProjectionRestrictedNormalized_safe_of_original_three_way_reachable_shape
      net hconnected horiginalSafe hshape)
    hcomplete
    hproper

def partialOrderProjectionRestrictedNormalizedWorkflowNetOfPathIn
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (hconnected :
      ∀ node :
          PetriNet.Node (BoundaryPlace Place) Trans,
        PetriNet.nodeIn (partialOrderProjectionPlaces net part) part node ->
          PetriNet.PathIn
              (partialOrderProjection net part)
              (partialOrderProjectionPlaces net part)
              part
              (PetriNet.Node.place BoundaryPlace.start)
              node ∧
            PetriNet.PathIn
              (partialOrderProjection net part)
              (partialOrderProjectionPlaces net part)
              part
              node
              (PetriNet.Node.place BoundaryPlace.end_)) :
    WorkflowNet
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})
      (PetriNet.NormalizedTrans {trans : Trans // part trans}) :=
  partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
    net part
    (partialOrderProjectionRestricted_connected_of_pathIn
      net part hconnected)

def partialOrderProjectionRestrictedNormalizedWorkflowNetOfPath
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (hconnected :
      ∀ node :
          PetriNet.Node (BoundaryPlace Place) Trans,
        PetriNet.nodeIn (partialOrderProjectionPlaces net part) part node ->
          PetriNet.Path
              (partialOrderProjection net part)
              (PetriNet.Node.place BoundaryPlace.start)
              node ∧
            PetriNet.Path
              (partialOrderProjection net part)
              node
              (PetriNet.Node.place BoundaryPlace.end_)) :
    WorkflowNet
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})
      (PetriNet.NormalizedTrans {trans : Trans // part trans}) :=
  partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
    net part
    (partialOrderProjectionRestricted_connected_of_path
      net part hconnected)

def partialOrderProjectionRestrictedNormalizedWorkflowNetOfIncidence
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
        partialOrderProjectionPlaces net part (BoundaryPlace.original place) ->
          ∃ trans,
            part trans ∧
              net.transToPlace trans place ∧
              ∃ entry,
                WorkflowNet.entryPoints net part entry ∧
                  net.placeToTrans entry trans)
    (houtgoing :
      ∀ {place : Place},
        partialOrderProjectionPlaces net part (BoundaryPlace.original place) ->
          ∃ trans,
            part trans ∧
              net.placeToTrans place trans ∧
              ∃ exit,
                WorkflowNet.exitPoints net part exit ∧
                  net.transToPlace trans exit) :
    WorkflowNet
      (PetriNet.NormalizedPlace
        {place : BoundaryPlace Place //
          partialOrderProjectionPlaces net part place})
      (PetriNet.NormalizedTrans {trans : Trans // part trans}) :=
  partialOrderProjectionRestrictedNormalizedWorkflowNetOfConnected
    net part
    (partialOrderProjectionRestricted_connected_of_entry_exit_incidence
      net hnonempty hentry hexit hincoming houtgoing)

def partialOrderProjectionNormalizedWorkflowNetOfConnected
    (net : WorkflowNet Place Trans)
    (part : Set Trans)
    (hconnected :
      ∀ node : PetriNet.Node (BoundaryPlace Place) Trans,
        PetriNet.Path
            (partialOrderProjection net part)
            (PetriNet.Node.place BoundaryPlace.start)
            node ∧
          PetriNet.Path
            (partialOrderProjection net part)
            node
            (PetriNet.Node.place BoundaryPlace.end_)) :
    WorkflowNet
      (PetriNet.NormalizedPlace (BoundaryPlace Place))
      (PetriNet.NormalizedTrans Trans) :=
  WorkflowNet.normalized
    (partialOrderProjection net part)
    BoundaryPlace.start
    BoundaryPlace.end_
    hconnected

end Patterns

end KouraniWfnetPowl
