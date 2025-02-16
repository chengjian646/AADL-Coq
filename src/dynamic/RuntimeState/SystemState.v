From Coq Require Import List Arith ListSet String.
From compcert.common Require Import Values.
From compcert.lib Require Import Maps.
Require Import Coq.Sets.Ensembles.

Import ListNotations.
From aadlcoq.src.static Require Import Model.
From aadlcoq.src.dynamic.RuntimeState Require Import ThreadState PortState.

Inductive Phase := Initializing | Computing.

(*从调度器的角度来看，每个线程
  •暂停等待调度
  •调度并准备调度
  •运行。
*)
(*
这是对AADL线程调度状态的简化，反映在标准的第5.4.1节“Thread States and Actions”
和5.4.2节“Thread Dispatching”以及图5和图6中。特别是，我们不考虑与模式、激活、停
用或由于资源获取或子程序调用而暂停相关的状态。*)
Inductive ScheduleState := Waiting | Ready | Running.
Lemma ScheduleState_eq: forall (x y: ScheduleState), {x=y} + {x<>y}.
Proof.
  decide equality.
Defined.

Module ScheduleStateEq.
  Definition t := ScheduleState.
  Definition eq := ScheduleState_eq.
End ScheduleStateEq.

Module ScheduleStatemap := EMap(ScheduleStateEq).

Definition Threadschedule := ScheduleStatemap.t ScheduleState.

Inductive Exec := 
  | Initialize (cids: list CompId)
  | Compute (c: CompId).

Record SystemSchedule := {
  ssc_scheduleInit  : list CompId;
  ssc_scheduleFirst : CompIds;
  ssc_scheduleComp  : Compmap.t (option CompIds)
}.

Parameter u : Type.
(*系统状态包括以下元素：
•从CompId到线程状态的映射
•通信基底状态的（抽象）表示
•从CompId到每个线程的调度状态的映射
•系统的当前阶段；
•接下来要执行的线程。
*)
Record SystemState :={
  sst_systemThread : Compmap.t (option ThreadState);
  sst_systemComms  : option u;
  sst_systemState  : Compmap.t (option ScheduleState);(*Waiting\Ready\Running*)
  sst_systemPhase  : Phase;
  sst_systemExec   : Exec;
}.

(*需要遍历所有的key*)
Lemma ThreadState_eq: forall (x y: ThreadState), {x=y} + {x<>y}.
Proof.
  Admitted.
Definition systemThreadStates (s: SystemState) (ts: ListSet.set ThreadState): Prop:=
  forall c t,
    Compmap.get c (sst_systemThread s) = Some t <->
      ListSet.set_mem ThreadState_eq t ts = true.

(*-------------Well-formedness Definitions--------*)
Definition wf_SystemSchedule (md: Model) (sch: SystemSchedule): Prop:=
  (forall c x,
     Compmap.get c (modelCompDescrs md) = Some x <->(*cjQ--对应两条良定义*)
       List.In c (ssc_scheduleInit sch) ) /\
  (List.length (ssc_scheduleFirst sch) <> 0) /\
  (forall c x,
     List.In c (ssc_scheduleFirst sch) ->
       Compmap.get c (modelCompDescrs md) = Some x) /\
  (forall c x cs,
     Compmap.get c (modelCompDescrs md) = Some x <->
       Compmap.get c (ssc_scheduleComp sch) = Some cs ).

(*可以使用以下助手谓词来确定系统的当前阶段。*)
Definition isInitializing (s: SystemState): Prop:=
  (sst_systemPhase s) = Initializing /\
  exists cs, (sst_systemExec s) = Initialize cs.

Definition isComputing (s: SystemState): Prop:=
  (sst_systemPhase s) = Computing /\
  exists c, (sst_systemExec s) = Compute c.

(*-------cjQ--------------Communication---------------------*)

Record Communication :={
  comPush : u -> PortState -> Conns ->  ListSet.set(u * PortState);
  comPull : u -> PortState -> Conns ->  ListSet.set(u * PortState);
}.










