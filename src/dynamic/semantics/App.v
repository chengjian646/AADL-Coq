From Coq Require Import List Arith ListSet String.
From compcert.common Require Import Values.
From compcert.lib Require Import Maps.

Import ListNotations.
From aadlcoq.src.static Require Import Model.
From aadlcoq.src.dynamic.RuntimeState Require Import ThreadState PortState VarState Queue.

Record App :={
  appInit    : VarState -> PortState -> bool;
  appCompute : VarState -> PortState -> DispatchStatus 
                -> VarState -> PortState -> bool;
}.

(*每个线程都通过从compid到app的映射与它的应用程序逻辑行为相关联。*)
Definition CIDApp := Compmap.t (option App).

Record AppModel :={
  appModel    : Model;
  appModelApp : CIDApp;
}.

(*定义了以下帮助函数来访问AppModel的元素。*)
Definition appModelCompDescrs (am: AppModel): Compmap.t (option CompDescr):=
  modelCompDescrs(appModel am).

Definition appModelPortDescrs (am: AppModel): Portmap.t (option PortDescr):=
  modelPortDescrs(appModel am).

Definition appModelPortKind (am: AppModel)(p: PortId): option PortKind:=
  match Portmap.get p (appModelPortDescrs am) with
  | None => None
  | Some x => Some (pd_kind x)
  end.

Definition appModelConns (am: AppModel): Conns:=
  modelConns(appModel am).

Definition appModelCIDs (am: AppModel)(cids: CompIds): Prop:=
  forall c x,
    Compmap.get c (appModelCompDescrs am) = Some x <->
      ListSet.set_mem CompId_eq c cids = true.

Definition appModelPIDs (am: AppModel)(pids: PortIds): Prop:=
  forall p x,
    Portmap.get p (appModelPortDescrs am) = Some x <->
      ListSet.set_mem PortId_eq p pids = true.

(*cjQ----返回值太长？*)
Definition appModelInit (am: AppModel)(c: CompId): option (VarState -> PortState -> bool):=
  match Compmap.get c (appModelApp am) with
  | None => None
  | Some x => Some (appInit x)
  end.

Definition appModelCompute (am: AppModel)(c: CompId): option (VarState -> PortState -> DispatchStatus -> VarState -> PortState -> bool):=
  match Compmap.get c (appModelApp am) with
  | None => None
  | Some x => Some (appCompute x)
  end.

(*
第一个属性陈述了应用逻辑谓词的基本约束，这些约束与一般模型有关，
但不考虑与应用逻辑相关的模型线程规范。这是一种较弱的属性，在需要
时可以通过下面的其他属性来加强。约束条件是:
•由appInit约束的端口状态属于输出端口
•appCompute将输入端口状态与输出端口状态关联起来
•来自模型的所有数据端口都被appCompute约束为具有非空值。
*)
Definition wf_App (m: Model)(a: App): Prop:=
  (exists ws qs, 
    (appInit a) ws qs = true) /\
  (forall ws qs,
    (appInit a) ws qs = true -> 
      forall p x,
        Portmap.get p qs = Some x /\ isOutPID m p = true) /\
  (forall vs ps d ws qs,
    (appCompute a) vs ps d ws qs = true ->
      (forall p x,
        Portmap.get p ps = Some x /\ isInPID m p = true)/\
      (forall p x,
        Portmap.get p qs = Some x /\ isOutPID m p = true)) /\
  (forall vs ps d ws qs,
    (appCompute a) vs ps d ws qs = true ->
      (forall q x,
        Portmap.get q (modelPortDescrs m) = Some x /\ isDataPD x = true ->
          exists queue, 
            Portmap.get q qs = Some queue /\ isEmpty queue = false)).
(*
下面的属性进一步将应用逻辑谓词限制为特定线程c的特征:
•变量状态满足appInit,则必须只包含线程中的id变量
•端口状态满足appInit，则必须只包含线程中的端口id
•变量状态满足appCompute,则必须只包含线程c中的id变量
•端口状态满足appCompute，则必须只包含线程c中的端口ids
•端口状态满足appCompute输出端口状态,则必须只包含线程c中的输出端口id。
*)
Definition wf_CIDAppCIDAPP (m: Model)(c: CompId)(a: App): Prop:=
  (wf_App m a) /\
  (forall ws qs,
    (appInit a) ws qs = true ->
      (forall v x,
        Varmap.get v ws = Some x -> 
          isVarOfCID m c v = true) /\
      (forall p x,
        Portmap.get p qs = Some x ->
          isPortOfCIDPID m c p = true)) /\
  (forall vs ps d ws qs,
    (appCompute a) vs ps d ws qs = true ->
      (forall v x1 x2,
        Varmap.get v vs = Some x1 \/
        Varmap.get v ws = Some x2 -> 
          isVarOfCID m c v = true) /\
      (forall p x1 x2,
        Portmap.get p ps = Some x1 \/
        Portmap.get p qs = Some x2 ->
          isPortOfCIDPID m c p = true) /\
      (forall q x,
        Portmap.get q qs = Some x <->
          isPortOfCIDPID m c q = true /\ isOutPID m q = true)).

(*如果每个单独线程的应用逻辑都是格式良好的，那么模型的线程应用
逻辑就是格式良好的。*)
Definition wf_CIDApp (m: Model)(ca: CIDApp): Prop:=
  forall c x,
    Compmap.get c ca = Some x ->
      wf_CIDAppCIDAPP m c x.

(*如果模型是格式良好的，并且应用程序逻辑相对于模型是格式良好的，
那么与应用程序逻辑集成的模型就是格式良好的。*)
Definition wf_AppModel (am: AppModel): Prop:=
  wf_Model (appModel am) /\
  wf_CIDApp (appModel am)(appModelApp am).

(*------2024-04-09 17:00 Cheng Jian--------*)