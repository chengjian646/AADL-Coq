From Coq Require Import List Arith ListSet String Lia Logic.FunctionalExtensionality.
From compcert.common Require Import Values.
From compcert.lib Require Import Maps.

From aadlcoq.src Require Import Model Queue.

(*引入类型PortState——从PortId到Queue的映射，
  以实现每个队列的关联*)
Definition PortState := Portmap.t (option Queue). (**r why option Queue? *)

(*-------------Well-formedness Definitions--------*)
Definition wf_PortState_dom (ps: PortState) (pids: PortIds): Prop:=
  forall k v,
    Portmap.get k ps = Some v <->
    ListSet.set_In k pids.

Definition wf_PortState_queues (ps: PortState) : Prop:=
  forall p v,
    Portmap.get p ps = Some v -> wf_Queue v.

Definition wf_PortState(ps: PortState) (pids: PortIds): Prop:=
  (wf_PortState_dom ps pids) /\ (wf_PortState_queues ps).

(*-------------------------Operations-------------------------*)
Definition portDefinedPID (ps: PortState) (p: PortId): bool:=
  match Portmap.get p ps with
  | None => false
  | Some _ => true
  end.

(*检查端口状态中是否存在一个非空队列与给定的端口标识符相关联*)
Definition dataAvailablePID (ps: PortState) (p: PortId): bool:=
  match Portmap.get p ps with
  | None => false
  | Some q => negb(isEmpty q)
  end.

(*给定端口状态ps，返回一组存在可用数据端口ID*)
Definition dataAvailablePorts (ps: PortState) (s: PortIds): Prop :=
  forall p,
    dataAvailablePID ps p = true <->
      ListSet.set_mem PortId_eq p s = true.

(*端口状态ps是否有任何具有可用数据的队列？*)
Definition dataUnavailable (ps: PortState) : Prop:=
  ~exists p q,
    Portmap.get p ps = Some q /\ (isEmpty q = false).

(*端口状态ps是否在集合pid中的所有端口上都有可用的数据？*)
Fixpoint readyPIDs (ps: PortState) (pids: PortIds): bool:=
  match pids with
  | nil => true
  | portId :: rest => (dataAvailablePID ps portId) && 
                      (readyPIDs ps rest)
  end.

  
(*从属于集合pids中的每个端口的队列中取出一个值来更新端口状态ps*)
Fixpoint portDequeuePIDs(ps: PortState) (pids: PortIds): option PortState:=
  match pids with
  | nil => Some ps
  | p :: rest => match Portmap.get p ps with
                      | None => portDequeuePIDs ps rest
                      | Some q => portDequeuePIDs (Portmap.set p (Some (tail q)) ps) rest
                      end
  end.

(*通过从端口p中取出一个值来转换端口状态ps*)
Definition portDequeuePID (ps: PortState) (p: PortId): PortState:=
  match Portmap.get p ps with
  | None => ps
  | Some x => (Portmap.set p (Some (tail x)) ps)
  end.

(*返回端口状态ps内p的队列中的第一个值。*)
Definition portHeadPID (ps: PortState) (p: PortId): option val:=
  match Portmap.get p ps with
  | None => None
  | Some x => head x
  end.

(*返回端口状态为ps的p队列的整个缓冲区*)
Definition portBufferPID (ps: PortState) (p: PortId): vals:=
  match Portmap.get p ps with
  | None => nil
  | Some x => q_buffer x
  end.

Definition portEnqueuePID (ps: PortState) (p: PortId) (v: val): PortState:=
  match Portmap.get p ps with
  | None => ps
  | Some x => (Portmap.set p (Some (push x v)) ps)
  end.

Definition portReplacePID (ps: PortState) (p: PortId) (q: Queue): PortState:=
  match Portmap.get p ps with
  | None => ps
  | Some _ => (Portmap.set p (Some q) ps)
  end.

Fixpoint clearAll (pids: PortIds) (ps: PortState): option PortState:=
  match pids with
  | nil => Some ps
  | p :: rest => match Portmap.get p ps with
                      | None => clearAll rest ps (**r TODO: why not None? *)
                      | Some q => clearAll rest (Portmap.set p (Some (clear q)) ps)
                      end
  end.

Lemma PortMap_setset: forall {A:Type} (p: PortId) (v1:A) v2 ps,
    Portmap.set p v1 (Portmap.set p v2 ps) = Portmap.set p v1 ps.
Proof.
  intros.
  unfold Portmap.set.
  extensionality y.
  destruct PortEq.eq; reflexivity.
Qed.

Lemma Empty_is_Zero:forall (q: Queue),
  (isEmpty q = true) -> List.length (q_buffer q) = 0.
Proof.
  intros.
  unfold isEmpty in H.
  destruct (q_buffer q) eqn:H2.
  - simpl.
    reflexivity.
  - discriminate.
Qed.

Lemma Tail_Push_Same: forall q a,
    (q_capacity q > 0) /\ (isEmpty q = true) -> tail (push q a) = q.
Proof.
  intros q a H.
  destruct H as [H_capa H_isEmp].
  unfold push.
  destruct (Datatypes.length (q_buffer q) <? q_capacity q) eqn:H1.
  - unfold isEmpty in H_isEmp.
    destruct (q_buffer q) eqn:H_bufferq.
    + simpl.
      unfold tail.
      simpl.
      destruct q.
      simpl in *.
      rewrite H_bufferq.
      destruct q_strategy eqn:H_eqn.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
   + discriminate.
  - apply Empty_is_Zero in H_isEmp.
    rewrite H_isEmp in H1.
    apply Nat.ltb_lt in H_capa.
    rewrite H_capa in H1.
    discriminate.
Qed.

Lemma PortMap_setget_same: forall {A:Type} (p:PortId) (ps : Portmap.t A),
    Portmap.set p (Portmap.get p ps) ps = ps.
Proof.
  intros.
  unfold Portmap.set, Portmap.get.
  extensionality y.
  destruct PortEq.eq as [He | Hn] eqn: Heq; [subst y| ]; f_equal.
Qed.


Lemma portEnqueueDequeue_empty:forall (ps: PortState) (p: PortId) (x: val),
  (portDefinedPID ps p = true) /\
  (exists q,Portmap.get p ps = Some q /\ (q_capacity q > 0) /\ (isEmpty q = true)) ->
  portDequeuePID (portEnqueuePID ps p x) p = ps.
Proof.
  intros ps p x.
  intros.
  destruct H as [H_def [q H_capa_isEmp]].
  unfold portEnqueuePID.
  destruct H_capa_isEmp as [H1 [H2 H3]].
  rewrite H1.
  unfold portDequeuePID.
  unfold Portmap.get.
  rewrite Portmap.gss.
  rewrite PortMap_setset.
  rewrite Tail_Push_Same.
  - rewrite <- H1.
    apply PortMap_setget_same.
  - split.
    + apply H2.
    + apply H3.
Qed.

(*-----------Operation Properties-----------------*)
Lemma portReplacePID_preserves_wf_PortState_dom: forall ps dom_pids p q,
  wf_PortState_dom ps dom_pids /\
  ListSet.set_In p dom_pids ->
  wf_PortState_dom (portReplacePID ps p q) dom_pids.
Proof.
  intros.
  destruct H as [H_wf H_In].
  unfold portReplacePID.
  destruct (Portmap.get p ps) eqn:H_p.
  - unfold wf_PortState_dom in *.
    intros.
    split.
    + unfold Portmap.set.
    Admitted.

Lemma pset_preserves_wf_PortState: forall ps dom_pids p q,
  wf_PortState ps dom_pids /\
  ListSet.set_In p dom_pids /\
  wf_Queue q ->
  wf_PortState (portReplacePID ps p q) dom_pids.
Proof.
  Admitted.
Lemma pdeq_preserves_wf_PortState_dom: forall ps dom_pids p,
  wf_PortState_dom ps dom_pids /\
  ListSet.set_In p dom_pids ->
  wf_PortState_dom (portDequeuePID ps p) dom_pids.
Proof.
  Admitted.

Lemma pdeq_preserves_wf_PortState: forall ps dom_pids p,
  wf_PortState ps dom_pids /\
  ListSet.set_In p dom_pids ->
  wf_PortState (portDequeuePID ps p) dom_pids.
Proof.
  Admitted.

(*2024-03-28 Cheng Jian*)





