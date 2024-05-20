From Coq Require Import List Arith ListSet String.
From compcert.common Require Import Values.
From compcert.lib Require Import Maps.

Import ListNotations.

From aadlcoq.src Require Import Model VarState PortState.

Inductive DispatchStatus :=
  | NotEnabled  (* 线程未启用 *)
  | Periodic (ports : PortIds)  (* 周期性线程启用，具有要冻结的输入端口集合 *)
  | Sporadic (trigger : PortId) (ports : PortIds).  (* 非周期性线程通过触发器启用，具有要冻结的输入端口集合 *)

(*给定一个调度状态值，下面的helper函数返回值被冻结的输入端口。*)
Definition dispatchInputPorts (dispatch_status: DispatchStatus) : PortIds:=
  match dispatch_status with
  | NotEnabled => nil
  | Periodic ps => ps
  | Sporadic _ ps => ps
  end.

Definition disp_elem (dispatch_status: DispatchStatus) (p: PortId) : bool:=
  match dispatch_status with
  | NotEnabled => false
  | Periodic portset => ListSet.set_mem PortId_eq p portset
  | Sporadic p' portset => match PortId_eq p' p with
                           | left _ => true
                           | right _ => ListSet.set_mem PortId_eq p portset
                           end
  end.

(*线程的运行时状态由以下元素组成*)
(*
tvar-线程的局部变量的状态
iin-基础结构输入端口状态（表示输入端口的基础结构视图）
ain-应用程序输入端口状态（表示线程应用程序逻辑的输入端口视图）
aout-应用程序输出端口状态（表示线程应用程序逻辑的输出端口视图）
iout-基础结构输出端口状态（表示基础结构的输出端口视图）
disp-线程的当前调度状态
*)
Record ThreadState := {
  ts_tvar : VarState;
  ts_infi : PortState;
  ts_appi : PortState;
  ts_appo : PortState;
  ts_info : PortState;
  ts_disp : DispatchStatus;
}.

Definition tstate (tv:VarState)(ii:PortState)(ai:PortState)(ao:PortState)
  (io:PortState)(ds:DispatchStatus): ThreadState:={|
  ts_tvar := tv;
  ts_infi := ii;
  ts_appi := ai;
  ts_appo := ao;
  ts_info := io;
  ts_disp := ds;
|}.


(*-------------Well-formedness Definitions--------*)
Fixpoint VarsisVarOfCID (m: Model)(c: CompId)(varlist: Vars): Vars:=
  match varlist with
  | [] => []
  | v::t => if isVarOfCID m c v then
                v::(VarsisVarOfCID m c t)
              else
                VarsisVarOfCID m c t
  end.
Definition wf_ThreadState_tvar (m: Model)(c: CompId)(vs: VarState): Prop:=
  match Compmap.get c (modelCompDescrs m) with
  | None => False
  | Some x => wf_VarState vs (VarsisVarOfCID m c (cd_compVars x) )
  end.

Fixpoint PortisInCIDPID (m: Model)(c: CompId)(portlist: PortIds): PortIds:=
  match portlist with
  | [] => []
  | p::t => if isInCIDPID m c p then
                p::(PortisInCIDPID m c t)
              else
                PortisInCIDPID m c t
  end.
Definition wf_ThreadState_infi (m: Model)(c: CompId)(ps: PortState): Prop:=
  match Compmap.get c (modelCompDescrs m) with
  | None => False
  | Some x => wf_PortState ps (PortisInCIDPID m c (cd_portIds x) )
  end.
Definition wf_ThreadState_appi (m: Model)(c: CompId)(ps: PortState): Prop:=
  match Compmap.get c (modelCompDescrs m) with
  | None => False
  | Some x => wf_PortState ps (PortisInCIDPID m c (cd_portIds x) )
  end.

Fixpoint PortisOutCIDPID (m: Model)(c: CompId)(portlist: PortIds): PortIds:=
  match portlist with
  | [] => []
  | p::t => if isOutCIDPID m c p then
                p::(PortisOutCIDPID m c t)
              else
                PortisOutCIDPID m c t
  end.
Definition wf_ThreadState_appo (m: Model)(c: CompId)(ps: PortState): Prop:=
  match Compmap.get c (modelCompDescrs m) with
  | None => False
  | Some x => wf_PortState ps (PortisOutCIDPID m c (cd_portIds x) )
  end.
Definition wf_ThreadState_info (m: Model)(c: CompId)(ps: PortState): Prop:=
  match Compmap.get c (modelCompDescrs m) with
  | None => False
  | Some x => wf_PortState ps (PortisOutCIDPID m c (cd_portIds x) )
  end.

Definition wf_ThreadState_disp (m: Model)(c: CompId)(ds: DispatchStatus): Prop:=
  forall p,
    (disp_elem ds p = true)-> 
  (isInCIDPID m c p) = true.

Definition wf_ThreadState (m: Model)(c: CompId)(ts: ThreadState): Prop:=
  wf_ThreadState_tvar m c (ts_tvar ts) /\
  wf_ThreadState_infi m c (ts_infi ts) /\
  wf_ThreadState_appi m c (ts_appi ts) /\
  wf_ThreadState_appo m c (ts_appo ts) /\
  wf_ThreadState_info m c (ts_info ts) /\
  wf_ThreadState_disp m c (ts_disp ts).

(*------------------Initial Thread States---------------------*)
(*目前，我们将通用数据类型实例化为{int}，并且使用｛0｝作为默认变量值。*)
Definition default_value : val := Vzero.

Definition initial_ThreadState_tvar (m: Model)(c: CompId)(ts: ThreadState) : Prop:=
  wf_ThreadState_tvar m c (ts_tvar ts) /\
  forall v x,
    Varmap.get v (ts_tvar ts) = Some x ->
  x = default_value.

Definition initial_ThreadState_infi (m: Model)(c: CompId)(ts: ThreadState) : Prop:=
  wf_ThreadState_infi m c (ts_infi ts) /\
  dataUnavailable (ts_infi ts).

Definition initial_ThreadState_appi (m: Model)(c: CompId)(ts: ThreadState) : Prop:=
  wf_ThreadState_appi m c (ts_appi ts) /\
  dataUnavailable (ts_appi ts).

Definition initial_ThreadState_appo (m: Model)(c: CompId)(ts: ThreadState) : Prop:=
  wf_ThreadState_appo m c (ts_appo ts) /\
  dataUnavailable (ts_appo ts).

Definition initial_ThreadState_info (m: Model)(c: CompId)(ts: ThreadState) : Prop:=
  wf_ThreadState_info m c (ts_info ts) /\
  dataUnavailable (ts_info ts).

Definition initial_ThreadState_disp (m: Model)(c: CompId)(ts: ThreadState) : Prop:=
  wf_ThreadState_disp m c (ts_disp ts) /\
  ts_disp ts = NotEnabled.

Definition initial_ThreadState (m: Model)(c: CompId)(ts: ThreadState) : Prop:=
  initial_ThreadState_tvar m c ts /\
  initial_ThreadState_infi m c ts /\
  initial_ThreadState_appi m c ts /\
  initial_ThreadState_appo m c ts /\
  initial_ThreadState_info m c ts /\
  initial_ThreadState_disp m c ts.

Lemma initial_implies_wf :forall (m: Model)(c: CompId)(ts: ThreadState),
  initial_ThreadState m c ts ->
  wf_ThreadState m c ts.
Proof.
  intros m c ts.
  unfold initial_ThreadState.
  unfold initial_ThreadState_tvar;
  unfold initial_ThreadState_infi;
  unfold initial_ThreadState_appi;
  unfold initial_ThreadState_appo;
  unfold initial_ThreadState_info;
  unfold initial_ThreadState_disp.
  intros.
  unfold wf_ThreadState.
  destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  destruct H1 as [H1_1 H1_2];
  destruct H2 as [H2_1 H2_2];
  destruct H3 as [H3_1 H3_2];
  destruct H4 as [H4_1 H4_2];
  destruct H5 as [H5_1 H5_2];
  destruct H6 as [H6_1 H6_2].
  repeat split.
  - apply H1_1.
  - apply H2_1.
  - apply H3_1.
  - apply H4_1.
  - apply H5_1.
  - apply H6_1.
Qed.

(*------2024-03-19 21:42 Cheng Jian--------*)