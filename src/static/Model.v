From Coq Require Import List Arith ListSet String.

From compcert.lib Require Import Maps.

Import ListNotations.

Inductive PortId := | mkPortId: nat -> PortId.

(*
Definition port1 := mkPortId 1.
*)


Lemma PortId_eq: forall (x y: PortId), {x=y} + {x<>y}.
Proof.
  decide equality.
  decide equality.
Defined.

Definition PortIds := ListSet.set PortId.

Inductive CompId := | mkCompId: nat -> CompId.

Lemma CompId_eq: forall (x y: CompId), {x=y} + {x<>y}.
Proof.
  decide equality.
  decide equality.
Defined.

Definition CompIds := ListSet.set CompId.

Inductive Var := | mkVar: string -> Var.

Lemma Var_eq: forall (x y: Var), {x=y} + {x<>y}.
Proof.
  decide equality.
  apply string_dec.
Defined.

Definition Vars := ListSet.set Var.

Inductive PortDirection := In | Out.

Inductive PortKind := Event | Data | EventData.
(*|
\pd_name-用于报告和调试目的的端口的可打印名称，
\pd_id-端口的唯一标识符，由HAMR代码生成器生成，
\pd_compId-此端口所属组件的唯一标识符，
\pd_direction-端口的方向（输入或输出）
\pd_kind-端口的AADL端口类别（事件、数据或事件数据），
\pd_size-与端口相关联的缓冲区的大小，
|*)
Record PortDescr := {
  pd_name      : string;
  pd_id        : PortId;
  pd_compId    : CompId;
  pd_direction : PortDirection;
  pd_kind      : PortKind;
  pd_size      : nat;
  pd_urgency   : nat;
}.

Definition wf_PortDescr (pd: PortDescr): Prop :=
  (pd_size pd > 0) /\
  (pd_kind pd = Data -> pd_size pd = 1).

Definition mkPortDescr (n:string) (i:PortId) (ci: CompId) (d: PortDirection)
  (k: PortKind) (s u: nat): PortDescr := {|
  pd_name      := n;
  pd_id        := i;
  pd_compId    := ci;
  pd_direction := d;
  pd_kind      := k;
  pd_size      := s;
  pd_urgency   := u;
|}.
(*Example*)
Definition port1 := mkPortId 1.
Definition comp1 := mkCompId 1.
Definition myPortDescr := mkPortDescr "example" port1 comp1 In Data 10 5.

(*|以下帮助函数查询端口描述符中捕获的端口属性。|*)
Definition isInPD (pd: PortDescr) : bool :=
  match pd_direction pd with
  | In => true
  | _ => false
  end.

Definition isOutPD (pd: PortDescr) : bool :=
  match pd_direction pd with
  | Out => true
  | _ => false
  end.

Definition isDataPD (pd: PortDescr) : bool :=
  match pd_kind pd with 
  | Data => true
  | _ => false
  end.

Definition isEventPD (pd: PortDescr) : bool :=
  match pd_kind pd with 
  | Event => true
  | _ => false
  end.

Definition isEventDataPD (pd: PortDescr) : bool :=
  match pd_kind pd with
  | EventData => true
  | _ => false
  end.

Definition isEventLikePD (pd: PortDescr) : bool :=
  match pd_kind pd with
  | Event => true
  | EventData => true
  | _ => false
  end.

Inductive DispatchProtocol :=
  Periodic | Sporadic.
(*与端口描述符类似，组件描述符组合来自AADL实例模型的信息片段
转换为提供组件属性的单个结构。在当前的形式化中，只表示线程组件。
因此，组件描述符中包含的属性属于AADL线程组件。*)

(*\cd_name—用于报告和调试目的的组件的可打印名称，
\cd_id-组件的唯一标识符，
\cd_portIds-接口上声明的端口的唯一标识符集(该端口所属的组件)
\cd_dispatchProtocol-此（线程）组件的AADL属性Dispatch\Protocol的值，
\cd_dispatchTriggers-可以充当调度的类似事件的输入端口的标识符集
\cd_compVars-对行为有贡献的变量的标识符集*)
Record CompDescr := {
  cd_name              : string;
  cd_id                : CompId;
  cd_portIds           : PortIds;
  cd_dispatchProtocol  : DispatchProtocol;
  cd_dispatchTriggers  : PortIds;
  cd_compVars          : Vars;
}.

Definition mkCompDescr (n: string) (i: CompId) (pis: PortIds) (dp: DispatchProtocol)
  (dts: PortIds) (v: Vars): CompDescr := {|
  cd_name              := n;
  cd_id                := i;
  cd_portIds           := pis;
  cd_dispatchProtocol  := dp;
  cd_dispatchTriggers  := dts;
  cd_compVars          := v;
|}.

Definition isPeriodicCD (cd: CompDescr) :=
 cd_dispatchProtocol cd = Periodic.

Definition isSporadicCD (cd: CompDescr) :=
 cd_dispatchProtocol cd = Sporadic.

Module PortEq.
  Definition t := PortId.
  Definition eq := PortId_eq.
End PortEq.

Module Portmap := EMap(PortEq).

Definition Conns := Portmap.t (option PortIds).

Module CompEq.
  Definition t := CompId.
  Definition eq := CompId_eq.
End CompEq.

Module Compmap := EMap(CompEq).

Record Model := {
  modelCompDescrs : Compmap.t (option CompDescr);
  modelPortDescrs : Portmap.t (option PortDescr);
  modelConns      : Conns;
}.
Definition mkModel (compdescrs: Compmap.t (option CompDescr))
  (portdescrs: Portmap.t (option PortDescr)) (conns: Conns) := {|
  modelCompDescrs := compdescrs;
  modelPortDescrs := portdescrs;
  modelConns      := conns;
|}.

(*================ H e l p e r     F u n c t i o n s ===================*)
(*Does model m include a component (id) c?*)
Definition inModelCID (m: Model) (c: CompId): bool :=
  match Compmap.get c (modelCompDescrs m) with
  | None => false
  | Some _ => true
  end.

(*Does model m include a port (id) p?*)
Definition inModelPID (m: Model) (p: PortId): bool :=
  match Portmap.get p (modelPortDescrs m) with
  | None => false
  | Some _ => true
  end.
(*Does model m include a input port (id) p*)
Definition isInPID (m: Model) (p: PortId): bool :=
  match Portmap.get p (modelPortDescrs m) with
  |None => false
  |Some x => match pd_direction x with 
              |In => true
              |_ => false
            end
  end.
(*Does model m include an output port (id) p?*)
Definition isOutPID (m: Model) (p: PortId): bool :=
  match Portmap.get p (modelPortDescrs m) with
  |None => false
  |Some x => match pd_direction x with 
              |Out => true
              |_ => false
            end
  end.
(*Does model m include a port (id) p with queue size n*)
Definition isSizePID (m: Model) (p: PortId) (n: nat): bool :=
  match Portmap.get p (modelPortDescrs m) with
  |None => false
  |Some x => Nat.eqb (pd_size x) n
  end.
(*Return the queue size of port (id) p in model m.*)
Definition sizePID (m: Model) (p: PortId): option nat :=
  match Portmap.get p (modelPortDescrs m) with
  |None => None
  |Some x => Some (pd_size x)
  end.
(*Return the kind (data, event, event data) of port (id) p in model m.*)

Definition kindPID (m: Model) (p: PortId): option PortKind :=
  match Portmap.get p (modelPortDescrs m) with
  |None => None
  |Some x => Some (pd_kind x)
  end.

(*Does model m include a data port (id) p?*)
Definition isDataPID (m: Model) (p: PortId): bool :=
  match kindPID m p with
  | Some Data => true
  | _ => false
  end. 
(*Does model m include a event port (id) p?*)
Definition isEventPID (m: Model) (p: PortId): bool :=
  match kindPID m p with
  | Some Event => true
  | _ => false
  end.
(*Does model m include a event data port (id) p?*)
Definition isEventDataPID (m: Model) (p: PortId): bool :=
  match kindPID m p with
  | Some EventData => true
  | _ => false
  end.
(*Does model m include a event-like port (id) p?*)
Definition isEventLikePID (m: Model) (p: PortId): bool :=
  match kindPID m p with
  | Some Event => true
  | Some EventData => true
  | _ => false
  end.
(*Return the urgency of port (id) p in model m.*)

Definition urgencyPID (m: Model) (p: PortId): option nat :=
  match Portmap.get p (modelPortDescrs m) with
  | None => None 
  | Some x => Some (pd_urgency x)
  end.

(*In model m, does component (id) c have a data port (id) p?*)
Definition isPortOfCIDPID (m: Model) (c: CompId) (p: PortId): bool :=
  match Compmap.get c (modelCompDescrs m) with
  | None => false
  | Some x => ListSet.set_mem PortId_eq p (cd_portIds x)
  end.
(*In model m, does component (descriptor) cd have a var (id) v?*)
Definition isVarOfCD (m: Model) (cd: CompDescr) (v: Var): bool :=
  ListSet.set_mem Var_eq v (cd_compVars cd).
(*In model m, does component (id) c have a var (id) v?*)
Definition isVarOfCID (m: Model) (c: CompId) (v: Var): bool :=
  match Compmap.get c (modelCompDescrs m) with
  | None => false
  | Some x => isVarOfCD m x v
  end.
(*In model m, does component (descriptor) cd have an input port (id) p?*)
Definition isInCDPID (m: Model) (cd: CompDescr) (p: PortId): bool :=
  if ListSet.set_mem PortId_eq p (cd_portIds cd) then
    match Portmap.get p (modelPortDescrs m) with
              | None => false
              | Some x => isInPD x
              end
    else false.
(*In model m, does component (id) c have an input port (id) p?*)
Definition isInCIDPID (m: Model) (c: CompId) (p: PortId): bool :=
  match Compmap.get c (modelCompDescrs m) with
  | None => false
  | Some x => isInCDPID m x p
  end.

(*In model m, does component (descriptor) cd have an output port (id) p?*)
Definition isOutCDPID (m: Model) (cd: CompDescr) (p: PortId): bool :=
  if ListSet.set_mem PortId_eq p (cd_portIds cd) then
    match Portmap.get p (modelPortDescrs m) with
              | None => false
              | Some x => isOutPD x
              end
    else false.
(*In model m, does component (id) c have an output port (id) p?*)
Definition isOutCIDPID (m: Model) (c: CompId) (p: PortId): bool :=
  match Compmap.get c (modelCompDescrs m) with
  | None => false
  | Some x => isOutCDPID m x p
  end.

(*In model m, does component (descriptor) cd have a data port (id) p?*)
Definition isDataCDPID (m: Model) (cd: CompDescr) (p: PortId): bool :=
  if ListSet.set_mem PortId_eq p (cd_portIds cd) then
    match Portmap.get p (modelPortDescrs m) with
              | None => false
              | Some x => isDataPD x
              end
    else false.
(*In model m, does component (id) c have a data port (id) p?*)
Definition isDataCIDPID (m: Model) (c: CompId) (p: PortId): bool :=
  match Compmap.get c (modelCompDescrs m) with
  | None => false
  | Some x => isDataCDPID m x p
  end.

(*In model m, does component (descriptor) cd have an event port (id) p?*)
Definition isEventCDPID (m: Model) (cd: CompDescr) (p: PortId): bool :=
  if ListSet.set_mem PortId_eq p (cd_portIds cd) then
    match Portmap.get p (modelPortDescrs m) with
              | None => false
              | Some x => isEventPD x
              end
    else false.
(*In model m, does component (id) c have an event port (id) p?*)
Definition isEventCIDPID (m: Model) (c: CompId) (p: PortId): bool :=
  match Compmap.get c (modelCompDescrs m) with
  | None => false
  | Some x => isEventCDPID m x p
  end.

(*In model m, does component (descriptor) cd have an event-like port (id) p?*)
Definition isEventLikeCDPID (m: Model) (cd: CompDescr) (p: PortId): bool :=
  if ListSet.set_mem PortId_eq p (cd_portIds cd) then
    match Portmap.get p (modelPortDescrs m) with
              | None => false
              | Some x => isEventLikePD x
              end
    else false.
(*In model m, does component (id) c have an event-like port (id) p?*)
Definition isEventLikeCIDPID (m: Model) (c: CompId) (p: PortId): bool :=
  match Compmap.get c (modelCompDescrs m) with
  | None => false
  | Some x => isEventLikeCDPID m x p
  end.

(*In model m, does component (descriptor) cd have a input data port (id) p?*)
Definition isInDataCDPID (m: Model) (cd: CompDescr) (p: PortId): bool :=
  if ListSet.set_mem PortId_eq p (cd_portIds cd) then
    match Portmap.get p (modelPortDescrs m) with
    | None => false
    | Some x => (isInPD x) && (isDataPD x)
    end
  else false.
(*In model m, does component (id) c have a input data port (id) p?*)
Definition isInDataCIDPID (m: Model) (c: CompId) (p: PortId): bool :=
  match Compmap.get c (modelCompDescrs m) with
  | None => false
  | Some x => isInDataCDPID m x p
  end.

(*In model m, does component (descriptor) cd have an input event-like port (id) p?*)
Definition isInEventLikeCDPID (m: Model) (cd: CompDescr) (p: PortId): bool :=
  if ListSet.set_mem PortId_eq p (cd_portIds cd) then
    match Portmap.get p (modelPortDescrs m) with
    | None => false
    | Some x => (isInPD x) && (isEventLikePD x)
    end
  else false.
(*In model m, does component (id) c have an event-like port (id) p?*)
Definition isInEventLikeCIDPID (m: Model) (c: CompId) (p: PortId): bool :=
  match Compmap.get c (modelCompDescrs m) with
  | None => false
  | Some x => isInEventLikeCDPID m x p
  end.

(*Return the ports belonging to component (id) c in model m.*)
Definition portsOfCID (m: Model) (c: CompId) : option PortIds :=
  match Compmap.get c (modelCompDescrs m) with
  | None => None
  | Some x => Some (cd_portIds x)
  end.
(*Return the input ports belonging to component (id) c in model m.*)
(*--------------------use two function----------------*)
Fixpoint inPortsOfPortIds (m: Model) (c: CompId) (portIds: PortIds) : PortIds :=
  match portIds with
  | [] => []
  | portId :: rest =>
      if isInCIDPID m c portId then
        portId :: (inPortsOfPortIds m c rest)
      else
        inPortsOfPortIds m c rest
  end.
Definition inPortsOfCID (m: Model) (c: CompId) : PortIds :=
  match portsOfCID m c with 
  | None => []
  | Some x => inPortsOfPortIds m c x
  end.

(*Return the input data ports belonging to component (id) c in model m.*)
(*--------------------use two function----------------*)
Fixpoint inDataPortsOfPortIds (m: Model) (c: CompId) (portIds: PortIds) : PortIds :=
  match portIds with
  | [] => []
  | portId :: rest =>
      if isInDataCIDPID m c portId then
        portId :: (inDataPortsOfPortIds m c rest)
      else
        inDataPortsOfPortIds m c rest
  end.
Definition inDataPortsOfCID (m: Model) (c: CompId) : PortIds :=
  match portsOfCID m c with
  | None => []
  | Some x => inDataPortsOfPortIds m c x
  end.

(*Return the input event-like ports belonging to component (id) c in model m.*)
(*--------------------use two function----------------*)
Fixpoint inEventLikePortsOfPortIds (m: Model) (c: CompId) (portIds: PortIds) : PortIds :=
  match portIds with
  | [] => []
  | portId :: rest =>
      if isEventLikeCIDPID m c portId then
        portId :: (inEventLikePortsOfPortIds m c rest)
      else
        inEventLikePortsOfPortIds m c rest
  end.
Definition inEventLikePortsOfCID (m: Model) (c: CompId) : PortIds :=
  match portsOfCID m c with
  | None => []
  | Some x => inEventLikePortsOfPortIds m c x
  end.
(*Return the dispatch triggers (port ids)belonging to component (id) c in model m.*)
Definition dispatchTriggersOfCID (m: Model) (c: CompId): PortIds :=
  match Compmap.get c (modelCompDescrs m) with
  |None => []
  |Some x => cd_dispatchTriggers x
  end.
(*========= M o d e l   W e l l f o r m e d n e s s   P r o p e r t i e s  ===========*)
(*Each port descriptor in the modelPortDescrs map is well-formed.*)
Definition wf_Model_PortDescr (m: Model) : Prop :=
  forall p portDescr,
    Portmap.get p (modelPortDescrs m) = Some portDescr ->
    wf_PortDescr portDescr.

(*For each entry (p:: PortId, pd:: PortDescr) in the port descriptors map, 
   the port id in the descriptor pd matches p.*)
Definition wf_Model_PortDescrsIds (m: Model) : Prop :=
  forall p portDescr,
    Portmap.get p (modelPortDescrs m) = Some portDescr ->
    (pd_id portDescr) = p.

(*For each entry (c:: CompId, cd:: CompDescr) in the component 
  descriptors map, the comp id in the descriptor cd matches c.*)
Definition wf_Model_CompDescrsIds (m: Model) : Prop :=
  forall c compDescr,
    Compmap.get c (modelCompDescrs m) = Some compDescr ->
    (cd_id compDescr) = c.

(*For each entry (p:: PortId, pd:: PortDescr) in the port descriptors map, 
   the comp id indicating the enclosing component for the port is in the
   domain of the component descriptors map.*)
Definition wf_Model_PortDescrsCompId (m: Model) : Prop :=
  forall p portDescr,
    Portmap.get p (modelPortDescrs m) = Some portDescr ->
    exists c, Compmap.get (pd_compId portDescr) (modelCompDescrs m) = Some c.

(*For each entry (c:: CompId, cd:: CompDescr) in the component descriptors map, 
   the port ids of component's contained ports are contained in the domain of the 
   port descriptor map.*)
Fixpoint cdPortIdsIsOfComp (m: Model) (portIds: PortIds) : bool :=
  match portIds with
  | [] => true
  | portId :: rest => match Portmap.get portId (modelPortDescrs m) with
                      | None => false
                      | Some _ => cdPortIdsIsOfComp m rest 
                      end
  end.
Definition wf_Model_CompDescrsContainedPortIds (m: Model) : Prop :=
  forall c compDescr,
    Compmap.get c (modelCompDescrs m) = Some compDescr ->
    (cdPortIdsIsOfComp m (cd_portIds compDescr)) = true.

(*For each pair of component ids c, d in the model,
      the sets of ids of ports belonging to those components are disjoint.*)
(*---------------cjQ-------maybe error----------------------*)

Fixpoint cdPortIds1_Disjoint_cdPortIds2 (portIds1: PortIds) (portIds2: PortIds) : bool :=
  match portIds1 with
  | [] => true
  | portId :: rest => if ListSet.set_mem PortId_eq portId portIds2 then
                          false
                      else
                          cdPortIds1_Disjoint_cdPortIds2 rest portIds2
  end.
Definition wf_Model_DisjointPortIds (m: Model) : Prop :=
  forall c d compDescr1 compDescr2,
    (Compmap.get c (modelCompDescrs m) = Some compDescr1 /\
    Compmap.get d (modelCompDescrs m) = Some compDescr2) ->
    c <> d ->
    (cdPortIds1_Disjoint_cdPortIds2 (cd_portIds compDescr1) (cd_portIds compDescr2))=true.

(*For each entry (p:: PortId, s:: PortId set) in the connections map,  
   the port id p and the port ids s = {p1, ..., pn} are in the domain of the 
   port descriptor map.*)
Definition wf_Model_ConnsPortIds (m: Model) : Prop :=
  forall p portIds,
      Portmap.get p (modelConns m) = Some portIds ->
      match Portmap.get p (modelPortDescrs m) with
      | Some _ => (cdPortIdsIsOfComp m portIds) = true
      | None => False
      end.

(*For each entry (p:: PortId, s:: PortId set) in the connections map,  
   the port id p and the port ids s = {p1, ..., pn} are in the domain of the 
   port descriptor map.*)
Definition wf_Model_ConnsPortCategories (m: Model) : Prop :=
  forall p p' portIds,
      Portmap.get p (modelConns m) = Some portIds /\
      (isOutPID m p = true) /\
      ((ListSet.set_mem PortId_eq p' portIds)= true) /\
      (isInPID m p' = true) ->
      kindPID m p = kindPID m p'.
     
(*For each entry (p:: PortId, pd:: PortDescr) in the port map,  
      if p is an in data port, then it has a size of at most one.*)
Definition wf_Model_InDataPorts (m: Model) : Prop :=
  forall p portDescr,
    Portmap.get p (modelPortDescrs m) = Some portDescr /\
    (isInPID m p = true) /\
    (isDataPD portDescr = true) ->
    match (sizePID m p) with 
    | Some size => size <=1
    | None => False
    end.

Definition wf_Model_SporadicComp (m: Model) : Prop :=
  forall c compDescr,
    Compmap.get c (modelCompDescrs m) = Some compDescr /\
    isSporadicCD compDescr ->
    cd_dispatchTriggers compDescr <> [].

(*The following top-level definition for well-formed models
is the conjunction of the properties above.*)
Definition wf_Model (m: Model) :Prop :=
  wf_Model_PortDescr m /\
  wf_Model_PortDescrsIds m /\
  wf_Model_CompDescrsIds m /\
  wf_Model_PortDescrsCompId m /\
  wf_Model_CompDescrsContainedPortIds m /\
  wf_Model_DisjointPortIds m /\
  wf_Model_ConnsPortIds m /\
  wf_Model_ConnsPortCategories m /\
  wf_Model_InDataPorts m /\
  wf_Model_SporadicComp m.

(* 2024-03-12 17:06 chengjian*)