From Coq Require Import List Arith ListSet String.
From compcert.common Require Import Values.
From compcert.lib Require Import Maps.

Import ListNotations.

From aadlcoq.src Require Import Model ThreadState PortState.

Inductive EnabledStatus : Type :=
  | Periodic : EnabledStatus
  | Sporadic : PortId -> EnabledStatus.
Lemma EnabledStatus_eq: forall (x y: EnabledStatus), {x=y} + {x<>y}.
Proof.
  decide equality.
  decide equality.
  decide equality.
Defined.

Definition EnabledStatusSet := ListSet.set EnabledStatus.
(*如果模型声明的线程周期(将记录在CompDesc中)
与当前时间(当前省略)适当相关，则启用周期线程*)
(*这个方法是一个占位符。它的当前实现只是返回一
个值，表示它已启用*)
(* ToDo: we currently assume periodic components are always enabled. *)
Definition periodicIsEnabled (cd: CompDescr): bool:=
  true.
(* ToDo: we currently assume periodic components are always enabled. *)
Definition periodicEnabledStatus (cd: CompDescr): EnabledStatusSet:=
  [Periodic].

(*如果满足以下两种条件，则启用偶发线程:
1. Timing:自线程最后一次调度以来的时间间隔超过了模型声明
的线程“period”(“period”属性的命名有些错误，实际上反映了
最小分离时间)。在目前的形式化状态下，时间被省略，这个条件
被认为是平凡的。
2. 事件到达:至少有一个消息/值已经到达模型中作为分派触发器
声明的端口。默认情况下(如果模型中没有显式声明事件触发器)，
所有事件和事件数据端口(参见第5.4(6)节)
*)
(*占位符，用于检查是否达到了偶发线程的最小分离时间。*)
Definition minSeparationAchieved (m: Model)(c: CompId): bool:=
  true.

(*----cjQ----maybe error---*)
Definition selectMaximumUrgencyPorts (m: Model)(c: CompId)(candidateDispatchPorts: PortIds)(pids: PortIds): Prop:=
  forall p,
    exists x, portsOfCID m c = Some x /\ 
      ListSet.set_In p x  /\
        ~exists p' n1 n2,
          ListSet.set_In p' candidateDispatchPorts /\
            urgencyPID m p = Some n1 /\ urgencyPID m p' = Some n2 /\
              n1 < n2 <->
  ListSet.set_mem PortId_eq p pids = true.

(*---cjQ----using getdataAvailableTriggers maybe error*)
Definition getdataAvailableTriggers (pids: PortIds)(ps: PortState)(s: PortIds): Prop:=
  forall p,
    dataAvailablePID ps p = true /\ ListSet.set_mem PortId_eq p pids = true <->
  ListSet.set_mem PortId_eq p s = true.
Definition getSporadicDispatchablePorts (m: Model)(c: CompId)(cd: CompDescr)(ps: PortState)(pids: PortIds): Prop:=
  let declaredDispatchTriggers := cd_dispatchTriggers cd 
  in exists dataAvailableTriggers, getdataAvailableTriggers declaredDispatchTriggers ps dataAvailableTriggers /\
  selectMaximumUrgencyPorts m c dataAvailableTriggers pids.

(*返回一组 {EnabledStatus} 值，指示哪些端口触发了非周期性调度。*)
Definition sporadicEnabledStatus (m: Model)(c: CompId)(cd: CompDescr)(c_infi: PortState)(ess: EnabledStatusSet): Prop:=
  exists dispatchablePorts,
    (getSporadicDispatchablePorts m c cd c_infi dispatchablePorts) /\
    (minSeparationAchieved m c = true) /\
  forall es p, ListSet.set_In p dispatchablePorts /\ es = (Sporadic p) <->
  ListSet.set_mem EnabledStatus_eq es ess = true.

(*{computeEnabledStatus} 返回一组 {EnabledStatus} 值，指示线程是否可分派。*)
Definition computeEnabledStatus (m: Model)(c: CompId)(ps: PortState)(ess: EnabledStatusSet): Prop:=
  match Compmap.get c (modelCompDescrs m) with
  | None => False
  | Some compDescr => 
          match (cd_dispatchProtocol compDescr) with
          | Model.Periodic => (periodicEnabledStatus compDescr = ess)
          | Model.Sporadic => sporadicEnabledStatus m c compDescr ps ess
          end
  end.

(*---------Determining Ports to Freeze-------------*)
(*一旦确定线程可分派（启用），我们还可以确定在调度操作中应冻结哪些端口，
因为用于确定冻结端口的信息与用于确定调度的信息耦合在一起。*)
(*section8.3.2.......*)
(*周期性线程——调度触发器的概念与周期性线程无关(调度仅由超时触
发，而不是事件到达)。因此，所有的输入端口被冻结*)
Definition getPeriodicPortsToFreeze (m: Model)(c: CompId): PortIds:=
  inPortsOfCID m c.

Definition getNonTriggeringEventLikePorts (m: Model)(c: CompId): PortIds:=
  ListSet.set_diff PortId_eq (inEventLikePortsOfCID m c) (dispatchTriggersOfCID m c).

Definition getSporadicAlwaysFreezePorts (m: Model)(c: CompId): PortIds:=
  ListSet.set_union PortId_eq (inDataPortsOfCID m c) (getNonTriggeringEventLikePorts m c).

Definition getSporadicPortsToFreeze (m: Model)(c: CompId)(triggeringPort: PortId): PortIds:=
  ListSet.set_union PortId_eq (getSporadicAlwaysFreezePorts m c) (triggeringPort::nil).

(*-------------Computing Dispatch Status-----------------*)

(*----later put DispatchStatusSet in ThreadState.v-------*)
Definition DispatchStatusSet := ListSet.set DispatchStatus.
Lemma DispatchStatus_eq: forall (x y: DispatchStatus), {x=y} + {x<>y}.
Proof.
  repeat decide equality.
Defined.


(*cjQ-------x :: nil right?------*)
Definition computePeriodicDispatchStatus (m: Model)(c: CompId)(cd: CompDescr): DispatchStatusSet:=
  if periodicIsEnabled cd then
    let portsToFreeze := (getPeriodicPortsToFreeze m c)
    in ThreadState.Periodic portsToFreeze::nil
  else
    ThreadState.NotEnabled::nil.

(*当触发事件到达时，去获得触发事件端口，并冻结它和数据端口（默认冻结）*)
Definition computeSporadicDispatchStatus (m: Model)(c: CompId)(cd: CompDescr)(c_infi: PortState)(dss: DispatchStatusSet): Prop:=
  exists dispatchablePorts, 
    getSporadicDispatchablePorts m c cd c_infi dispatchablePorts /\
  forall p,
    ListSet.set_In p dispatchablePorts <->
  ListSet.set_mem DispatchStatus_eq (ThreadState.Sporadic p (getSporadicPortsToFreeze m c p)) dss = true.

Definition computeDispatchStatus (m: Model)(c: CompId)(c_infi: PortState)(dss: DispatchStatusSet): Prop:=
  match Compmap.get c (modelCompDescrs m) with
  | Some compDescr => 
          match (cd_dispatchProtocol compDescr) with
          | Model.Periodic => computePeriodicDispatchStatus m c compDescr = dss
          | Model.Sporadic => computeSporadicDispatchStatus m c compDescr c_infi dss
          end
  | None => False
  end.

(*------2024-04-02 19:48 Cheng Jian--------*)