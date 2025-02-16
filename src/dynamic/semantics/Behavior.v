From Coq Require Import List Arith ListSet String.
From compcert.common Require Import Values.
From compcert.lib Require Import Maps.

Import ListNotations.
From aadlcoq.src.static Require Import Model.
From aadlcoq.src.dynamic.RuntimeState Require Import ThreadState PortState VarState SystemState Queue.
From aadlcoq.src.dynamic.semantics Require Import App.
From aadlcoq.src.dynamic.scheduling Require Import DispatchLogic.


(*-------------------Initialize Entry Point------------------------*)
(*本节中的规则反映了如何通过执行线程入口点的应用程序逻辑来转换线程的状态。 每个入口点的状态转换由
从 App.thy 中定义的入口点合约派生的传递函数（关系）决定。 应用程序逻辑传输关系是在应用程序代码可
见的线程状态部分上定义的：应用程序输入端口状态@{term appi}、应用程序输出端口状态@{term appo}和
线程变量@{term tvar}。 本节中的规则将传输关系从状态的应用程序代码可见部分“提升”到整个线程状态。 
此外，对于计算入口点执行，规则包括调用 AADL 运行时服务来管理端口队列的入队和出队。*)
Inductive stepInit: App -> ThreadState -> ThreadState -> Prop :=
  | sInit_initialize: forall a vs ps t0 t1,
    appInit a vs ps = true ->
    tstate vs (ts_infi t0) (ts_appi t0) ps (ts_info t0) (ts_disp t0) = t1 ->
    stepInit a t0 t1.

Lemma stepInit_releinv: forall a t t',
    stepInit a t t' -> 
      appInit a (ts_tvar t') (ts_appo t') = true.
Proof.
  intros a t t' H_Init.
  inversion H_Init.
  subst.
  simpl.
  apply H.
Qed.

Definition receiveInputSrc (pki: PortId -> PortKind)(ps: PortIds)(src: PortState)(dst: PortState)(p: PortId): option Queue:=
  if (ListSet.set_mem PortId_eq p ps) then
    match pki p with
    | Data => match Portmap.get p src with
              | None => None
              | Some x => Some (clear x)
              end
    | Event => match Portmap.get p src with
              | None => None
              | Some x => Some (tail x)
              end
    | EventData => match Portmap.get p src with
                   | None => None
                   | Some x => Some (clear x)
                   end
    end
  else
    None.

Definition receiveInputDst (pki: PortId -> PortKind)(ps: PortIds)(src: PortState)(dst: PortState)(p: PortId): option Queue:=
  if (ListSet.set_mem PortId_eq p ps) then
    match pki p with
    | Data => Portmap.get p src
    | Event => match Portmap.get p dst with
              | None => None
              | Some dstx => match Portmap.get p src with
                          | None => None
                          | Some srcx => match head srcx with
                                         | None => Some (setBuffer dstx nil) (**r TODO: why not return None? how does AADL standard say it? *)
                                         | Some xval => Some (setBuffer dstx [xval])
                                         end
                          end
              end
    | EventData => Portmap.get p dst(*AADL-HSM maybe error*) (**r TODO: why? *)
    end
  else
    None.

Inductive receiveInput:(PortId->PortKind) -> PortIds -> PortState -> PortState 
              -> PortState -> PortState -> Prop:=
  | ri_default: forall pki ps src dst ps1 ps2,
    (receiveInputSrc pki ps src dst) = ps1 -> (**r we only care Some case *)
    (receiveInputDst pki ps src dst) = ps2 ->
      receiveInput pki ps src dst ps1 ps2.

Definition domPortState (ps: PortState) (s: PortIds): Prop :=
  forall p x,
    Portmap.get p ps = Some x <->
      ListSet.set_mem PortId_eq p s = true.

Inductive sendOutput: PortState -> PortState -> PortState -> PortState -> Prop:=
  | so_default: forall src dst s empty_q,
    domPortState src s ->
    clearAll s src = Some empty_q ->
      sendOutput src dst empty_q src.

Definition option_res {A B: Type} (f: A -> B): A -> option B :=
  fun a: A => Some (f a).

Inductive stepThread: (PortState -> DispatchStatusSet -> Prop) -> (PortId-> option PortKind) 
              -> (option App) -> ((option ScheduleState) * ScheduleState) -> 
              (option ThreadState) -> ThreadState -> Prop:=
  | dispatch: forall cds pki app cat dsp t infi' appi' t1 dss,
              cat = (Some Waiting,Ready) /\
              cds (ts_infi t) dss /\
              ListSet.set_mem DispatchStatus_eq dsp dss = true /\
              dsp <>  ThreadState.NotEnabled /\
              receiveInput pki (dispatchInputPorts dsp) (ts_infi t) (ts_appi t) infi' appi' ->
              tstate (ts_tvar t) infi' appi' (ts_appo t) (ts_info t) dsp = t1 ->
              stepThread cds (option_res pki) app cat (Some t) t1
  | compute : forall cds pki app cat t ws qs s empty_q t1,
              cat = (Some Ready,Running) /\
              (appCompute app) (ts_tvar t) (ts_appi t) (ts_disp t) ws qs = true ->
              domPortState (ts_appi t) s ->
              clearAll s (ts_appi t) = Some empty_q ->
              tstate ws (ts_infi t) empty_q qs (ts_info t) (ts_disp t) = t1 ->
              stepThread cds pki (Some app) cat (Some t) t1
  | complete: forall cds pki app cat t info' appo' t1,
              cat = (Some Running,Waiting) /\
              sendOutput (ts_appo t) (ts_info t) appo' info' ->
              tstate (ts_tvar t) (ts_infi t) (ts_appi t) appo' info' ThreadState.NotEnabled = t1 ->
              stepThread cds pki app cat (Some t) t1.

Definition empty_u : option u := None.
Definition initSys (m: Model) (s: SystemState) :=
  (isInitializing s) /\
  (forall c ts,
     inModelCID m c = true /\
     sst_systemThread s c = Some ts ->
     initial_ThreadState m c ts) /\
  (forall c x,
     sst_systemState s c = Some x -> x = Waiting) /\
  (sst_systemComms s = empty_u).


Definition sState (st: Compmap.t (option ThreadState))(sc: option u)
      (ss: Compmap.t (option ScheduleState))(sp: Phase)(se: Exec): SystemState:={|
  sst_systemThread := st;
  sst_systemComms  := sc;
  sst_systemState  := ss;
  sst_systemPhase  := sp;
  sst_systemExec   := se;
|}.
Lemma PortState_eq: forall (x y: PortState), {x=y} + {x<>y}.
Proof.
  Admitted.
Lemma U_eq: forall (x y: u), {x=y} + {x<>y}.
Proof.
  Admitted.
Lemma uPortState_eq: forall (x y: (u * PortState)), {x=y} + {x<>y}.
Proof.
  decide equality.
  - apply PortState_eq.
  - apply U_eq.
Qed.

Inductive stepSys: AppModel -> Communication -> SystemSchedule 
                  -> SystemState -> SystemState -> Prop:=
  | sSys_initialize: forall s c cs appvalue threadstate t am cm sc s1,
                isInitializing s /\
                sst_systemExec s = Initialize (c::cs) /\
                Compmap.get c (appModelApp am) = Some appvalue /\
                Compmap.get c (sst_systemThread s) = Some threadstate /\
                stepInit appvalue threadstate t ->
                sState (Compmap.set c (Some t) (sst_systemThread s))
                       (sst_systemComms s)
                       (sst_systemState s)
                       (sst_systemPhase s)
                       (Initialize cs) = s1 ->
                stepSys am cm sc s s1
  | switch :forall s c sc am cm s1,
            isInitializing s /\
            sst_systemExec s = Initialize nil /\
            ListSet.set_mem CompId_eq c (ssc_scheduleFirst sc) = true ->
            sState (sst_systemThread s)
                   (sst_systemComms s)
                   (sst_systemState s)
                   (Computing)
                   (Compute c) = s1 ->
            stepSys am cm sc s s1
  | push :  forall s c t s' sb it cm am sc t1 s1,
            isComputing s /\
            Compmap.get c (sst_systemThread s) = Some t /\
            sst_systemComms s = Some s'/\
            ListSet.set_mem uPortState_eq (sb,it) 
            (comPush cm s' (ts_info t) (appModelConns am)) = true->
            tstate (ts_tvar t) (ts_infi t) (ts_appi t) (ts_appo t) it (ts_disp t) = t1 ->
            sState (Compmap.set c (Some t1) (sst_systemThread s))
                   (Some sb)
                   (sst_systemState s)
                   (sst_systemPhase s)
                   (sst_systemExec s) = s1 ->
            stepSys am cm sc s s1
  | pull :  forall s c t s' sb it cm am sc t1 s1,
            isComputing s /\
            Compmap.get c (sst_systemThread s) = Some t /\
            sst_systemComms s = Some s'/\
            ListSet.set_mem uPortState_eq (sb,it) 
            (comPull cm s' (ts_infi t) (appModelConns am)) = true->
            tstate (ts_tvar t) it (ts_appi t) (ts_appo t) (ts_info t) (ts_disp t) = t1 ->
            sState (Compmap.set c (Some t1) (sst_systemThread s))
                   (Some sb)
                   (sst_systemState s)
                   (sst_systemPhase s)
                   (sst_systemExec s) = s1 ->
            stepSys am cm sc s s1
  | execute : forall s c cs c' am p dss cm a t sc s1,
              isComputing s /\
              sst_systemExec s = Compute c /\
              Compmap.get c (ssc_scheduleComp sc) = Some cs /\
              ListSet.set_mem CompId_eq c' cs = true /\
              stepThread (computeDispatchStatus (appModel am) c)
                         (appModelPortKind am)
                         (Compmap.get c (appModelApp am))
                         (Compmap.get c (sst_systemState s),a)
                         (Compmap.get c (sst_systemThread s)) t ->
              sState (Compmap.set c (Some t) (sst_systemThread s))
                   (sst_systemComms s)
                   (Compmap.set c (Some a) (sst_systemState s))
                   (sst_systemPhase s)
                    (Compute c') = s1 ->
              stepSys am cm sc s s1.

(*从系统的角度->从单个线程的角度*)
Lemma stepSysInit_ruleinv:
  forall s x xs am cm sc s',
  isInitializing s /\
  SystemState.sst_systemExec s = Initialize (x::xs) /\
  stepSys am cm sc s s' ->
  (forall xapp xts xts',
  Compmap.get x (appModelApp am) = Some xapp /\
  Compmap.get x (sst_systemThread s) = Some xts /\
  Compmap.get x (sst_systemThread s') = Some xts' /\
  stepInit xapp xts xts').
Proof.
  Admitted.

Lemma stepSysInit_redsch_ruleinv:
  forall s x xs am cm sc s',
  isInitializing s /\
  SystemState.sst_systemExec s = Initialize (x::xs) /\
  stepSys am cm sc s s' ->
  sst_systemExec s' = Initialize xs.
Proof.
  Admitted.

Lemma stepSysInit_initInv_ruleinv:
  forall s x xs am cm sc s',
  isInitializing s /\
  SystemState.sst_systemExec s = Initialize (x::xs) /\
  stepSys am cm sc s s' ->
  isInitializing s'.
Proof.
  Admitted.











