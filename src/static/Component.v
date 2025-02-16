From Coq Require Import List Arith ListSet String.

From compcert.lib Require Import Maps.

Import ListNotations.

From aadlcoq.src.static Require Import Model.

Inductive ProcessId := | mkProcessId: nat -> ProcessId.

Lemma ProcessId_eq: forall (x y: ProcessId), {x=y} + {x<>y}.
Proof.
  decide equality.
  decide equality.
Defined.

Definition ProcessIds := ListSet.set ProcessId.

Record ProcessDescr := {
  pcd_name              : string;              (* 进程名称 *)
  pcd_id                : ProcessId;           (* 进程唯一标识符 *)
  pcd_portIds           : PortIds;             (* 进程端口集合 *)
  pcd_containedThreads  : list CompId;         (* 包含的线程ID列表 *)
  pcd_compVars          : Vars;                (* 进程级变量 *)
  pcd_connectionBindings: Conns;               (* 内部连接绑定 *)
}.

Definition mkProcessDescr (n: string) (i: ProcessId) (pis: PortIds) 
  (cts: list CompId) (v: Vars) (conns: Conns): ProcessDescr := {|
  pcd_name              := n;
  pcd_id                := i;
  pcd_portIds           := pis;
  pcd_containedThreads  := cts;
  pcd_compVars          := v;
  pcd_connectionBindings:= conns;
|}.

(*Definition processA := mkProcessDescr "ProcessA" 
        pid1 portSet [tid1, tid2] vars connBindings.
*)
Inductive ThreadGroupId := | mkThreadGroupId: nat -> ThreadGroupId.

Lemma ThreadGroupId_eq: forall (x y: ThreadGroupId), {x=y} + {x<>y}.
Proof.
  decide equality.
  decide equality.
Defined.

Definition ThreadGroupIds := ListSet.set ThreadGroupId.

Record ThreadGroupDescr := {
  tg_name              : string;              (* 线程组名称 *)
  tg_id                : ThreadGroupId;       (* 线程组唯一标识符 *)
  tg_portIds           : PortIds;             (* 线程组端口集合 *)
  tg_containedThreads  : CompIds;             (* 包含的线程ID列表 *)
  tg_containedGroups   : ThreadGroupIds;      (* 包含的线程组ID列表 *)
  tg_compVars          : Vars;                (* 线程组级变量 *)
  tg_connectionBindings: Conns;               (* 内部连接绑定 *)
}.

(* 定义线程组描述的构造函数 *)
Definition mkThreadGroupDescr (n: string) (i: ThreadGroupId) (pis: PortIds)
  (cts: CompIds) (cgs: ThreadGroupIds) (v: Vars) (conns: Conns) : ThreadGroupDescr := 
  {| 
    tg_name := n;
    tg_id := i;
    tg_portIds := pis;
    tg_containedThreads := cts;
    tg_containedGroups := cgs;
    tg_compVars := v;
    tg_connectionBindings := conns;
  |}.
(*-------------------------------*)
Inductive SubprogramId := | mkSubprogramId: nat -> SubprogramId.

Lemma SubprogramId_eq: forall (x y: SubprogramId), {x=y} + {x<>y}.
Proof.
  decide equality.
  decide equality.
Defined.
Definition SubprogramIds := ListSet.set SubprogramId.

Record SubprogramDescr := {
  sp_name              : string;              (* 子程序名称 *)
  sp_id                : SubprogramId;        (* 子程序唯一标识符 *)
  sp_portIds           : PortIds;             (* 子程序端口集合 *)
  sp_compVars          : Vars;                (* 子程序级变量 *)
  sp_callSequence      : SubprogramIds;       (* 调用序列 *)
}.
(* 定义子程序描述的构造函数 *)
Definition mkSubprogramDescr (n: string) (i: SubprogramId) (pis: PortIds)
  (v: Vars) (callSeq: SubprogramIds) : SubprogramDescr :=
  {|
    sp_name := n;
    sp_id := i;
    sp_portIds := pis;
    sp_compVars := v;
    sp_callSequence := callSeq;
  |}.

(*--------------------------------------*)
Inductive SubprogramGroupId := | mkSubprogramGroupId: nat -> SubprogramGroupId.

Lemma SubprogramGroupId_eq: forall (x y: SubprogramGroupId), {x=y} + {x<>y}.
Proof.
  decide equality.
  decide equality.
Defined.
Definition SubprogramGroupIds := ListSet.set SubprogramGroupId.
Record SubprogramGroupDescr := {
  sg_name              : string;              (* 子程序组名称 *)
  sg_id                : SubprogramGroupId;   (* 子程序组唯一标识符 *)
  sg_portIds           : PortIds;             (* 子程序组端口集合 *)
  sg_containedSubprogs : SubprogramIds;       (* 包含的子程序ID列表 *)
  sg_compVars          : Vars;                (* 子程序组级变量 *)
  sg_connectionBindings: Conns;               (* 内部连接绑定 *)
}.
(* 定义子程序组描述的构造函数 *)
Definition mkSubprogramGroupDescr (n: string) (i: SubprogramGroupId) (pis: PortIds)
  (sps: SubprogramIds) (v: Vars) (conns: Conns) : SubprogramGroupDescr :=
  {|
    sg_name := n;
    sg_id := i;
    sg_portIds := pis;
    sg_containedSubprogs := sps;
    sg_compVars := v;
    sg_connectionBindings := conns;
  |}.

(*-------------------------------------------*)
Inductive SystemId := | mkSystemId: nat -> SystemId.

Lemma SystemId_eq: forall (x y: SystemId), {x=y} + {x<>y}.
Proof.
  decide equality.
  decide equality.
Defined.

Module ProcessEq.
  Definition t := ProcessId.
  Definition eq:= ProcessId_eq.
End ProcessEq.

Module Processmap := EMap(ProcessEq).

Module ThreadGroupEq.
  Definition t := ThreadGroupId.
  Definition eq:= ThreadGroupId_eq.
End ThreadGroupEq.

Module ThreadGroupmap := EMap(ThreadGroupEq).

Module SubprogramGroupEq.
  Definition t := SubprogramGroupId.
  Definition eq:= SubprogramGroupId_eq.
End SubprogramGroupEq.

Module SubprogramGroupmap := EMap(SubprogramGroupEq).

Record SystemDescr := {
  sys_name              : string;              (* 系统名称 *)
  sys_id                : SystemId;            (* 系统唯一标识符 *)
  sys_portIds           : Portmap.t (option PortDescr); (* 端口映射 *)
  sys_containedProcesses: Processmap.t (option ProcessDescr); (* 进程映射 *)
  sys_containedThreadGroups: ThreadGroupmap.t (option ThreadGroupDescr); (* 线程组映射 *)
  sys_containedSubprogramGroups: SubprogramGroupmap.t (option SubprogramGroupDescr); (* 子程序组映射 *)
  sys_compVars          : Vars;                (* 变量list *)
  sys_connectionBindings: Conns;               (* 内部连接绑定 *)
}.

Definition mkSystemDescr (n: string) (i: SystemId) (pis: Portmap.t (option PortDescr))
  (cps: Processmap.t (option ProcessDescr)) (ctgs: ThreadGroupmap.t (option ThreadGroupDescr)) 
  (csgs: SubprogramGroupmap.t (option SubprogramGroupDescr)) (v: Vars) (conns: Conns): SystemDescr := {|
  sys_name              := n;
  sys_id                := i;
  sys_portIds           := pis;
  sys_containedProcesses:= cps;
  sys_containedThreadGroups:= ctgs;
  sys_containedSubprogramGroups:= csgs;
  sys_compVars          := v;
  sys_connectionBindings:= conns;
|}.

(*-------------------------------Example System-------------------------------------*)
Definition comp0 := mkCompId 0.
Definition portid0 := mkPortId 0.
Definition portid1 := mkPortId 1.

Definition comp1 := mkCompId 1.
Definition portid2 := mkPortId 2.
Definition portid3 := mkPortId 3.
Definition portid4 := mkPortId 4.
Definition portid5 := mkPortId 5.

Definition comp2 := mkCompId 2.
Definition portid6 := mkPortId 6.
Definition portid7 := mkPortId 7.

Definition processid1 := mkProcessId 1.
Definition threadgroupid1 := mkThreadGroupId 1.
Definition subprogramgroupid1 := mkSubprogramGroupId 1.
Definition systemid1 := mkSystemId 1.

Definition var1 := mkVar "myvar1".
Definition var2 := mkVar "myvar2".

Definition vars : Vars :=
  ListSet.set_add Var_eq var1 (ListSet.set_add Var_eq var2 []).

(*------------------------PortDescr---------------------------*)
Definition Port1 : PortDescr :=
  mkPortDescr "SensorCurrentTempPort" portid0 comp0 Out Data 1 0.

Definition Port2 : PortDescr :=
  mkPortDescr "SensorTempChangePort" portid1 comp0 Out Event 5 1.

Definition Port3 : PortDescr :=
  mkPortDescr "ControlCurrentTempPort" portid2 comp1 In Data 1 0.

Definition Conns_empty : Portmap.t (option PortIds) := fun _ => None.
Definition process1 : ProcessDescr := mkProcessDescr
  "Process1" processid1 
  [portid1]  (* 假设 portid1 是端口 ID *)
  []  (* 假设没有包含的线程 *)
  []  (* 假设没有进程级变量 *)
  Conns_empty  (* 假设没有连接绑定 *)
.

Definition threadgroup1 : ThreadGroupDescr := mkThreadGroupDescr
  "ThreadGroup1"
  threadgroupid1
  [portid2]  (* 假设 portid2 是端口 ID *)
  []  (* 假设没有包含的线程 *)
  []  (* 假设没有包含的线程组 *)
  vars  (* 假设没有线程组级变量 *)
  Conns_empty  (* 假设没有连接绑定 *)
.

Definition subprogramgroup1 : SubprogramGroupDescr := mkSubprogramGroupDescr
  "SubprogramGroup1"
  subprogramgroupid1
  [portid3]  (* 假设 portid3 是端口 ID *)
  []  (* 假设没有包含的子程序 *)
  []  (* 假设没有子程序组级变量 *)
  Conns_empty  (* 假设没有连接绑定 *)
.

Definition port_map :=
  Portmap.set portid1 (Some Port1) (
    Portmap.set portid2 (Some Port2) (
      Portmap.set portid3 (Some Port3) (Portmap.init None)
    )
  ).

Definition process_map :=
  Processmap.set processid1 (Some process1) (Processmap.init None).

Definition threadgroup_map :=
  ThreadGroupmap.set threadgroupid1 (Some threadgroup1) (ThreadGroupmap.init None).

Definition subprogramgroup_map :=
  SubprogramGroupmap.set subprogramgroupid1 (Some subprogramgroup1) (SubprogramGroupmap.init None).

Definition mySystem := {|
  sys_name := "MySystem";
  sys_id := mkSystemId 1;  (* 假设系统 ID 为 1 *)
  sys_portIds := port_map;
  sys_containedProcesses := process_map;
  sys_containedThreadGroups := threadgroup_map;
  sys_containedSubprogramGroups := subprogramgroup_map;
  sys_compVars := vars;
  sys_connectionBindings := Conns_empty;  (* 假设没有连接绑定 *)
|}.
(*----------------------------------------------------------------------*)
(*每个构造子将具体的 ID 类型（如 ProcessId、ThreadGroupId 等）
包装为 ComponentId 类型.*)
Inductive ComponentId :=
  | CProcessId : ProcessId -> ComponentId
  | CThreadGroupId : ThreadGroupId -> ComponentId
  | CSubprogramId : SubprogramId -> ComponentId
  | CSubprogramGroupId : SubprogramGroupId -> ComponentId
  | CSystemId : SystemId -> ComponentId
  | CThreadId : CompId -> ComponentId.

Definition get_id_name (id: ComponentId) : string :=
  match id with
  | CProcessId _ => "Process"
  | CThreadGroupId _ => "ThreadGroup"
  | CSubprogramId _ => "Subprogram"
  | CSubprogramGroupId _ => "SubprogramGroup"
  | CSystemId _ => "System"
  | CThreadId _ => "Thread"
  end.
Definition get_process_id (id: ComponentId) : option ProcessId :=
  match id with
  | CProcessId pid => Some pid
  | _ => None
  end.

Definition get_thread_id (id: ComponentId) : option CompId :=
  match id with
  | CThreadId tid => Some tid
  | _ => None
  end.

Lemma ComponentId_eq: forall (x y: ComponentId), {x=y} + {x<>y}.
Proof.
  repeat decide equality.
Defined.

Definition pid : ProcessId := mkProcessId 1.  (* 某个进程 ID *)
Definition tgid : ThreadGroupId := mkThreadGroupId 2.  (* 某个线程组 ID *)
Definition tid : CompId := mkCompId 3.  (* 某个线程 ID *)

Definition component1 : ComponentId := CProcessId pid.
Definition component2 : ComponentId := CThreadGroupId tgid.
Definition component3 : ComponentId := CThreadId tid.

(* 测试 *)
Compute get_id_name component1.  (* 输出: "Process" *)
Compute get_id_name component2.  (* 输出: "ThreadGroup" *)
Compute get_id_name component3.  (* 输出: "Thread" *)

(*-----------------------------Mode Transition------------------------------*)
(*
正常模式
紧急模式
维护模式
*)
Inductive Mode :=
  | NormalMode
  | EmergencyMode
  | MaintenanceMode.

(*模式变换的触发条件通常与以下内容相关：
事件：例如接收到特定消息、检测到故障等。
时间：例如定时器超时。
数据值：例如某个变量的值达到阈值。
*)
Inductive triggerEvent :=
  | FailureDetected
  | RecoveryComplete
  | CalibrationComplete.

Record Transition := {
  trans_source : Mode;               (* 源模式 *)
  trans_target : Mode;               (* 目标模式 *)
  trans_trigger: triggerEvent;       (* 触发条件 *)
}.
(*example*)
Definition transition1 := {|
  trans_source := NormalMode;
  trans_target := EmergencyMode;
  trans_trigger := FailureDetected;
|}.

Definition transition2 := {|
  trans_source := EmergencyMode;
  trans_target := MaintenanceMode;
  trans_trigger := RecoveryComplete;
|}.

Definition transition3 := {|
  trans_source := MaintenanceMode;
  trans_target := NormalMode;
  trans_trigger := CalibrationComplete;
|}.

Module TransitionEq.
  Definition t := ComponentId.
  Definition eq := ComponentId_eq.
End TransitionEq.

Module Transitionmap := EMap(TransitionEq).

(*定义组件到模式变换的映射*)
Definition ComponentTransitions := Transitionmap.t (option (list Transition)).

(*================ H e l p e r     F u n c t i o n s ===================*)
(*----定义一个函数来检查某个组件是否在系统中---*)
Definition inSystemCID (sys: SystemDescr) (c: ComponentId): bool :=
  match c with
  | CProcessId pid => match Processmap.get pid (sys_containedProcesses sys) with
                      | None => false
                      | Some _ => true
                      end
  | CThreadGroupId tgid => match ThreadGroupmap.get tgid (sys_containedThreadGroups sys) with
                           | None => false
                           | Some _ => true
                           end
  | CSubprogramGroupId sgid => match SubprogramGroupmap.get sgid (sys_containedSubprogramGroups sys) with
                               | None => false
                               | Some _ => true
                               end
  | _ => false  (* 其他类型的组件不在系统中 *)
  end.

Definition inSystemPID (sys: SystemDescr) (p: PortId): bool :=
  match Portmap.get p (sys_portIds sys) with
  | None => false
  | Some _ => true
  end.

Definition isInSysPID (sys: SystemDescr) (p: PortId): bool :=
  match Portmap.get p (sys_portIds sys) with
  | None => false
  | Some x => match pd_direction x with
              | In => true
              | _  => false
              end
  end.
Definition isOutSysPID (sys: SystemDescr) (p: PortId): bool :=
  match Portmap.get p (sys_portIds sys) with
  | None => false
  | Some x => match pd_direction x with
              | Out => true
              | _  => false
              end
  end.
Definition inSizeSysPID (sys: SystemDescr) (p: PortId) (n: nat): bool :=
  match Portmap.get p (sys_portIds sys) with
  | None => false
  | Some x => Nat.eqb (pd_size x) n
  end.
Definition SizeSysPID (sys: SystemDescr) (p: PortId): option nat :=
  match Portmap.get p (sys_portIds sys) with
  | None => None
  | Some x => Some (pd_size x)
  end.
(*Return the kind (data, event, event data) of port (id) p in model m.*)
Definition syskindPID (sys: SystemDescr) (p: PortId): option PortKind :=
  match Portmap.get p (sys_portIds sys) with
  |None => None
  |Some x => Some (pd_kind x)
  end.
(*检查某个端口是否为数据端口*)
Definition isDataSysPID (sys: SystemDescr) (p: PortId): bool :=
  match syskindPID sys p with
  | Some Data => true
  | _ => false
  end.
Definition isEventSysPID (sys: SystemDescr) (p: PortId): bool :=
  match syskindPID sys p with
  | Some Event => true
  | _ => false
  end.
Definition isEventDataSysPID (sys: SystemDescr) (p: PortId): bool :=
  match syskindPID sys p with
  | Some EventData => true
  | _ => false
  end.
Definition isEventLikeSysPID (sys: SystemDescr) (p: PortId): bool :=
  match syskindPID sys p with
  | Some Event => true
  | Some EventData => true
  | _ => false
  end.
(*判断组件是否存在，并检查端口是否属于该组件。*)
Definition isPortOfSysCIDPID (sys: SystemDescr) (c: ComponentId) (p: PortId): bool :=
  match c with
  | CProcessId pid =>
      match Processmap.get pid (sys_containedProcesses sys) with
      | Some process => ListSet.set_mem PortId_eq p (pcd_portIds process)
      | None => false
      end
  | CThreadGroupId tgid =>
      match ThreadGroupmap.get tgid (sys_containedThreadGroups sys) with
      | Some threadgroup => ListSet.set_mem PortId_eq p (tg_portIds threadgroup)
      | None => false
      end
  | CSubprogramGroupId sgid =>
      match SubprogramGroupmap.get sgid (sys_containedSubprogramGroups sys) with
      | Some subprogramgroup => ListSet.set_mem PortId_eq p (sg_portIds subprogramgroup)
      | None => false
      end
  | _ => false  (* 其他类型的组件不支持端口 *)
  end.

Definition isVarOfSys (sys: SystemDescr) (c: ComponentId) (v: Var): bool :=
  match c with
  | CSystemId sid =>
      ListSet.set_mem Var_eq v (sys_compVars sys)
  | CProcessId pid =>
      match Processmap.get pid (sys_containedProcesses sys) with
      | Some process => ListSet.set_mem Var_eq v (pcd_compVars process)
      | None => false
      end
  | CThreadGroupId tgid =>
      match ThreadGroupmap.get tgid (sys_containedThreadGroups sys) with
      | Some threadgroup => ListSet.set_mem Var_eq v (tg_compVars threadgroup)
      | None => false
      end
  | CSubprogramGroupId sgid =>
      match SubprogramGroupmap.get sgid (sys_containedSubprogramGroups sys) with
      | Some subprogramgroup => ListSet.set_mem Var_eq v (sg_compVars subprogramgroup)
      | None => false
      end
  | _ => false  (* 其他类型的组件不支持端口 *)
  end.
(*---------------------------Use Helper Function-----------------------------*)
Definition processid2 := mkProcessId 2.
Definition threadgroupid2 := mkThreadGroupId 2.
Definition subprogramgroupid2 := mkSubprogramGroupId 2.
(* 检查组件是否存在 *)
Compute inSystemCID mySystem (CProcessId processid1). (*true*)
Compute inSystemCID mySystem (CProcessId processid2). (*false*)
Compute inSystemCID mySystem (CThreadGroupId threadgroupid1). (*true*)
Compute inSystemCID mySystem (CThreadGroupId threadgroupid2). (*false*)
Compute inSystemCID mySystem (CSubprogramGroupId subprogramgroupid1). (*true*)
Compute inSystemCID mySystem (CSubprogramGroupId subprogramgroupid2). (*false*)

(* 检查端口是否为数据端口 *)
Compute isDataSysPID mySystem portid1. (*true*)
Compute isDataSysPID mySystem portid2. (*false*)
Compute isDataSysPID mySystem portid3. (*true*)

(* 检查端口是否属于某个组件 *)
Compute isPortOfSysCIDPID mySystem (CProcessId processid1) portid1. (*true*)
Compute isPortOfSysCIDPID mySystem (CProcessId processid1) portid2. (*false*)
Compute isPortOfSysCIDPID mySystem (CProcessId processid1) portid3. (*false*)
Compute isPortOfSysCIDPID mySystem (CThreadGroupId threadgroupid1) portid1. (*false*)
Compute isPortOfSysCIDPID mySystem (CThreadGroupId threadgroupid1) portid2. (*true*)
Compute isPortOfSysCIDPID mySystem (CThreadGroupId threadgroupid1) portid3. (*false*)

(* 检查变量是否属于系统或某个组件 *)
Compute isVarOfSys mySystem (CSystemId systemid1) var1. (*true*)
Compute isVarOfSys mySystem (CSystemId systemid1) var2. (*true*)
Compute isVarOfSys mySystem (CProcessId processid1) var2. (*false*)
Compute isVarOfSys mySystem (CProcessId processid1) var1. (*false*)
Compute isVarOfSys mySystem (CProcessId processid1) var2. (*false*)
Compute isVarOfSys mySystem (CThreadGroupId threadgroupid1) var1. (*true*)
Compute isVarOfSys mySystem (CThreadGroupId threadgroupid1) var2. (*true*)

(*========= M o d e l   W e l l f o r m e d n e s s   P r o p e r t i e s  ===========*)
(*每个端口描述符是良构的*)
Definition wf_System_PortDescr (sys: SystemDescr) : Prop :=
  forall p portDescr,
    Portmap.get p sys.(sys_portIds) = Some portDescr ->
    wf_PortDescr portDescr.

(*端口描述符中的端口 ID 与映射键匹配*)
Definition wf_System_PortDescrsIds (sys: SystemDescr) : Prop :=
  forall p portDescr,
    Portmap.get p (sys_portIds sys) = Some portDescr ->
    (pd_id portDescr) = p.

(*组件描述符中的组件 ID 与映射键匹配*)
Definition wf_System_CompDescrsIds (sys: SystemDescr) : Prop :=
  forall c ProcessDescr ThreadGroupDescr SubprogramGroupDescr,
    match c with
     | CProcessId pid => Processmap.get pid (sys_containedProcesses sys)
                         = Some ProcessDescr -> 
                            pcd_id ProcessDescr = pid
     | CThreadGroupId tgid => ThreadGroupmap.get tgid (sys_containedThreadGroups sys)
                              = Some ThreadGroupDescr ->
                                tg_id ThreadGroupDescr = tgid
     | CSubprogramGroupId sgid => SubprogramGroupmap.get sgid (sys_containedSubprogramGroups sys)
                                  = Some SubprogramGroupDescr ->
                                    sg_id SubprogramGroupDescr = sgid
     | _ => False
     end.

(*端口描述符中的组件 ID 在组件描述符映射中存在*)
Definition wf_System_PortDescrsCompId (sys: SystemDescr) : Prop :=
  forall p portDescr,
    Portmap.get p (sys_portIds sys) = Some portDescr ->
    exists c, (match c with
               | CProcessId pid => 
                      Processmap.get pid (sys_containedProcesses sys) <> None
               | CThreadGroupId tgid => 
                      ThreadGroupmap.get tgid (sys_containedThreadGroups sys) <> None
               | CSubprogramGroupId sgid => 
                      SubprogramGroupmap.get sgid (sys_containedSubprogramGroups sys) <> None
               | _ => False
               end).

(*组件描述符中的端口 ID 在端口描述符映射中存在*)
Fixpoint cdPortIdsIsOfSystem (sys: SystemDescr) (portIds: PortIds) : bool :=
  match portIds with
  | [] => true
  | portId :: rest => match Portmap.get portId sys.(sys_portIds) with
                      | None => false
                      | Some _ => cdPortIdsIsOfSystem sys rest
                      end
  end.

Definition wf_System_CompDescrsContainedPortIds (sys: SystemDescr) : Prop :=
  forall c ProcessDescr ThreadGroupDescr SubprogramGroupDescr,
    match c with
     | CProcessId pid => Processmap.get pid (sys_containedProcesses sys)
                         = Some ProcessDescr -> 
                            cdPortIdsIsOfSystem sys (pcd_portIds ProcessDescr) = true
     | CThreadGroupId tgid => ThreadGroupmap.get tgid (sys_containedThreadGroups sys)
                              = Some ThreadGroupDescr ->
                                cdPortIdsIsOfSystem sys (tg_portIds ThreadGroupDescr) = true
     | CSubprogramGroupId sgid => SubprogramGroupmap.get sgid (sys_containedSubprogramGroups sys)
                                  = Some SubprogramGroupDescr ->
                                    cdPortIdsIsOfSystem sys (sg_portIds SubprogramGroupDescr) = true
     | _ => False
     end.

(*不同组件的端口 ID 集合是互斥的*)
Fixpoint cdPortIds1_Disjoint_cdPortIds2 (portIds1: PortIds) (portIds2: PortIds) : bool :=
  match portIds1 with
  | [] => true
  | portId :: rest => if ListSet.set_mem PortId_eq portId portIds2 then
                          false
                      else
                          cdPortIds1_Disjoint_cdPortIds2 rest portIds2
  end.

Definition wf_System_DisjointPortIds (sys: SystemDescr) : Prop :=
  forall c d ProcessDescr1 ThreadGroupDescr1 SubprogramGroupDescr1
                                   ProcessDescr2 ThreadGroupDescr2 SubprogramGroupDescr2,
    (match c with
     | CProcessId pid => Processmap.get pid (sys_containedProcesses sys)
                         = Some ProcessDescr1
     | CThreadGroupId tgid => ThreadGroupmap.get tgid (sys_containedThreadGroups sys)
                         = Some ThreadGroupDescr1
     | CSubprogramGroupId sgid => SubprogramGroupmap.get sgid (sys_containedSubprogramGroups sys)
                         = Some SubprogramGroupDescr1
     | _ => False
     end) /\
    (match c with
     | CProcessId pid => Processmap.get pid (sys_containedProcesses sys)
                         = Some ProcessDescr2
     | CThreadGroupId tgid => ThreadGroupmap.get tgid (sys_containedThreadGroups sys)
                         = Some ThreadGroupDescr2
     | CSubprogramGroupId sgid => SubprogramGroupmap.get sgid (sys_containedSubprogramGroups sys)
                         = Some SubprogramGroupDescr2
     | _ => False
     end) /\
    c <> d ->
    (match (c, d) with
     | (CProcessId _, CProcessId _) => 
          cdPortIds1_Disjoint_cdPortIds2 (pcd_portIds ProcessDescr1) (pcd_portIds ProcessDescr2)
     | (CThreadGroupId _, CThreadGroupId _) => 
          cdPortIds1_Disjoint_cdPortIds2 (tg_portIds ThreadGroupDescr1) (tg_portIds ThreadGroupDescr2)
     | (CSubprogramGroupId _, CSubprogramGroupId _) => 
          cdPortIds1_Disjoint_cdPortIds2 (sg_portIds SubprogramGroupDescr2) (sg_portIds SubprogramGroupDescr2)
     | _ => true
     end) = true.

(*连接中的端口 ID 在端口描述符映射中存在*)
Definition wf_System_ConnsPortIds (sys: SystemDescr) : Prop :=
  forall p portIds,
      Portmap.get p (sys_connectionBindings sys) = Some portIds ->
      (match Portmap.get p sys.(sys_portIds) with
      | Some _ => cdPortIdsIsOfSystem sys portIds
      | None => false
      end) = true.

(*连接中的端口类别匹配*)
Definition wf_System_ConnsPortCategories (sys: SystemDescr) : Prop :=
  forall p p' portIds,
      Portmap.get p sys.(sys_connectionBindings) = Some portIds /\
      (isOutSysPID sys p = true) /\
      ((ListSet.set_mem PortId_eq p' portIds)= true) /\
      (isInSysPID sys p' = true) ->
      syskindPID sys p = syskindPID sys p'.

(*输入数据端口的大小最多为 1*)
Definition wf_System_InDataPorts (sys: SystemDescr) : Prop :=
  forall p portDescr,
    Portmap.get p sys.(sys_portIds) = Some portDescr /\
    (isInSysPID sys p = true) /\
    (isDataSysPID sys p = true) ->
    match (SizeSysPID sys p) with 
    | Some size => size <=1
    | None => False
    end.

(*系统良构性定义,涵盖了端口、组件、连接的各种约束条件*)
Definition wf_System (sys: SystemDescr) : Prop :=
  wf_System_PortDescr sys /\
  wf_System_PortDescrsIds sys /\
  wf_System_CompDescrsIds sys /\
  wf_System_PortDescrsCompId sys /\
  wf_System_CompDescrsContainedPortIds sys /\
  wf_System_DisjointPortIds sys /\
  wf_System_ConnsPortIds sys /\
  wf_System_ConnsPortCategories sys /\
  wf_System_InDataPorts sys.