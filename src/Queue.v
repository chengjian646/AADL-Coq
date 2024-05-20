From Coq Require Import List Arith ListSet String.
From compcert.common Require Import Values.
Require Import Coq.Arith.Arith Lia.

Import ListNotations.

(*定义一个数据类型来表示AADL的端口 Overflow\_Handling\
_Protocol（OHP）属性的三个选项。添加一个额外的Unbounded
选项，以便在对语义的各个方面进行原型设计时使用。*)
Inductive Strategy := DropEarliest | DropLatest | Error | Unbounded.

Definition vals := ListSet.set val.

(*定义一种记录类型以使用以下字段表示队列值：
error—当OHP设置为error时，此字段用于指示队列处于错误状态。
buffer——队列存储的表示
capacity——[static]缓冲区的最大元素数（队列）可以容纳。此字段的值应等于
      AADL模型中的队列大小端口属性（默认值为1.如果OHP是无界，则忽略此值。
strategy——[static]队列的OHP。此字段的值应等于AADL模型中的OHP端口属性
*)
Record Queue :={
  q_error : bool;
  q_buffer : vals;
  q_capacity : nat;
  q_strategy : Strategy;
}.
(*Create a queue initialised with given buffer, capacity and strategy*)
Definition mk_queue (b: vals) (c: nat) (s: Strategy): Queue :={|
  q_error := false;
  q_buffer := b;
  q_capacity := c;
  q_strategy := s;
|}.
(*Create a queue initialised with an empty buffer, capacity and strategy*)
Definition mk_empty_queue (c: nat) (s: Strategy): Queue :={|
  q_error := false;
  q_buffer := [];
  q_capacity := c;
  q_strategy := s;
|}.

Definition less_eq_list (x y: vals) :=
  Val.lessdef_list x y.

Definition less_list (x y: vals):=
  (Val.lessdef_list x y) /\ x <> y.

Definition wf_Queue (q: Queue): Prop :=
  q_strategy q <> Unbounded -> List.length(q_buffer q) <= (q_capacity q).
(*================ O P E R A T I O N S ===================*)

(*Check if the queue is empty.*)
Definition isEmpty (q: Queue) : bool :=
  match q_buffer q with
  | [] => true
  | x :: rest => false
  end.

(*Check if the queue has exactly one element.*)
Definition isOneElement (q: Queue) : bool :=
  List.length(q_buffer q) =? 1.

(*Return the head (first value) from the queue.*)
Definition head (q: Queue) : option val :=
  match (q_buffer q) with
  | [] => None
  | hd :: _ => Some hd
  end.

(*Take the tail of a queue.*)
Definition tail (q: Queue) : Queue :={|
  q_error := q_error q;
  q_buffer := match (q_buffer q) with
              | nil => nil
              | _ :: tl => tl
              end;
  q_capacity := q_capacity q;
  q_strategy := q_strategy q;
|}.

(*Enqueue a single value.*)
Definition push (q: Queue) (a: val) : Queue :={|
  q_error := match q_strategy q with
             | Error => if List.length(q_buffer q) <? (q_capacity q) then
                            q_error q
                        else
                            true
             | _ => q_error q
             end;
  q_buffer := if List.length(q_buffer q) <? (q_capacity q) then
                  ListSet.set_add Val.eq a (q_buffer q)
              else
                  match (q_strategy q) with
                  | DropEarliest =>
                      ListSet.set_add Val.eq a (q_buffer(tail q))
                  | DropLatest =>
                      q_buffer q
                  | Error =>
                      []
                  | Unbounded => 
                      ListSet.set_add Val.eq a (q_buffer q)
                  end;
  q_capacity := q_capacity q;
  q_strategy := q_strategy q;
|}.


(*Enqueue a list of values.*)
Definition pushQueue (q: Queue) (q':vals) : Queue :={|
  q_error := match q_strategy q with
             | Error => if (List.length(q_buffer q) + List.length q') <=? (q_capacity q) then
                            q_error q
                        else
                            true
             | _ => q_error q
             end;
  q_buffer := match (q_strategy q) with
                  | DropEarliest =>
                      List.skipn (List.length(q_buffer q) + List.length q' - (q_capacity q)) (ListSet.set_union Val.eq (q_buffer q) q')
                  | DropLatest =>
                      List.firstn (q_capacity q) (ListSet.set_union Val.eq (q_buffer q) q')
                  | Error =>
                      if (List.length(q_buffer q) + List.length q') <=? (q_capacity q) then
                          ListSet.set_union Val.eq (q_buffer q) q'
                      else
                          []
                  | Unbounded => 
                      ListSet.set_union Val.eq (q_buffer q) q'
                  end;
  q_capacity := q_capacity q;
  q_strategy := q_strategy q;
|}.

(*Drop the first (head-side) n values from the queue.*)
Definition drop (n: nat) (q: Queue) : Queue :={|
  q_error := q_error q;
  q_buffer := List.skipn n (q_buffer q);
  q_capacity := q_capacity q;
  q_strategy := q_strategy q;
|}.

(*Remove all values from the queue.*)
Definition clear (q: Queue) : Queue :={|
  q_error := q_error q;
  q_buffer := [];
  q_capacity := q_capacity q;
  q_strategy := q_strategy q;
|}.

(*Set the queue buffer to a specific list of values (head corresponding to the
first item in the list.*)
Definition setBuffer (q: Queue) (b: vals): Queue :={|
  q_error := q_error q;
  q_buffer := b;
  q_capacity := q_capacity q;
  q_strategy := q_strategy q;
|}.
(*=======O p e r a t i o n  P r o p e r t i e s=========*)
(*judge two lists are equal*)
(*Fixpoint JudgeListsEqual (l1: vals) (l2: vals): bool :=
  match l1 , l2 with
  | nil , nil => true
  | l1_hd::l1_r ,l2_hd::l2_r =>
                match Val.eq l1_hd  l2_hd with
                | left _ => JudgeListsEqual l1_r l2_r
                | right _ => false
                end
  | _ , _ => false
  end.
Theorem judge_lists_equal_refl : forall (l1 : vals), JudgeListsEqual l1 l1 = true.
Proof.
  intros l1.
  induction l1 as [| hd tl IHl1].
  - (* Case: l1 = nil *)
    reflexivity.
  - (* Case: l1 = hd :: tl *)
    simpl.
    destruct Val.eq as [Heq | Hneq].
    + assumption.
    + exfalso. apply Hneq. reflexivity.
Qed.*)

(*head Properties*)
Lemma single_queue_head : forall (q:Queue) a,
  q_buffer q = [a] -> head q = Some a.
Proof.
  intros q a H_s.
  unfold head.
  rewrite H_s.
  reflexivity.
Qed.

(*tail Properties*)
(*tail | doesn't change*)
Lemma tail_frame_error :forall (q: Queue),
  q_error (tail q) = q_error q.
Proof.
  reflexivity.
Qed.

Lemma tail_frame_capacity :forall (q: Queue),
  q_capacity (tail q) = q_capacity q.
Proof.
  reflexivity.
Qed.

Lemma tail_frame_strategy :forall (q: Queue),
  q_strategy(tail q) = q_strategy q.
Proof.
  reflexivity.
Qed.

(*tail | preserves well-formedness.*)
Lemma tail_wf : forall (q:Queue),
  wf_Queue q -> wf_Queue(tail q).
Proof.
  unfold wf_Queue.
  intros.
  simpl in H0.
  apply H in H0.
  simpl.
  destruct (q_buffer q) eqn:H_buffer.
  - apply H0.
  - simpl in H0.
    lia.
Qed.

Lemma single_queue_tail : forall (q:Queue),
  List.length(q_buffer q) = 1 -> List.length(q_buffer (tail q)) = 0.
Proof.
  intros.
  unfold tail.
  destruct (q_buffer q) eqn:H_1.
  - simpl.
    reflexivity.
  - simpl.
    simpl in H.
    lia.
Qed.

(*push | Properties*)
(*push | doesn't change*)
Lemma push_frame_capacity : forall (q: Queue) (a: val),
  q_capacity (push q a) = q_capacity q.
Proof.
  intros.
  unfold push.
  simpl.
  reflexivity.
Qed.

Lemma push_frame_strategy : forall (q: Queue) (a: val),
  q_strategy (push q a) = q_strategy q.
Proof.
  intros.
  unfold push.
  simpl.
  reflexivity.
Qed.

Lemma push_within_capacity : forall (q: Queue) (a: val),
  List.length (q_buffer q) < q_capacity q ->
     (q_buffer(push q a)) = (ListSet.set_add Val.eq a (q_buffer q)).
Proof.
  intros q a H_lt.
  unfold push.
  simpl.
  apply Nat.ltb_lt in H_lt.
  rewrite H_lt.
  f_equal.
Qed.

Lemma push_no_error : forall (q: Queue) (a: val),
  List.length (q_buffer q) < q_capacity q ->
    q_error(push q a) = q_error(q).
Proof.
  intros.
  unfold push.
  simpl.
  destruct (q_strategy q) eqn:H_str.
  - reflexivity.
  - reflexivity.
  - destruct (Datatypes.length(q_buffer q) <? q_capacity q) eqn:H_1.
    + reflexivity.
    + assert (H_false: (Datatypes.length (q_buffer q) <? q_capacity q) = true).
      { apply Nat.ltb_lt. apply H. }
      rewrite H_1 in H_false.
      discriminate.
  - reflexivity.
Qed.

(*drop | Properties*)
(*drop | doesn't change*)
Lemma drop_frame_error : forall (n: nat) (q: Queue),
  q_error(drop n q) = q_error q.
Proof.
  intros.
  unfold drop.
  simpl.
  reflexivity.
Qed.

Lemma drop_frame_capacity : forall (n: nat) (q: Queue),
  q_capacity(drop n q) = q_capacity q.
Proof.
  intros.
  unfold drop.
  simpl.
  reflexivity.
Qed.

Lemma drop_frame_strategy : forall (n: nat) (q: Queue),
  q_strategy(drop n q) = q_strategy q.
Proof.
  intros.
  unfold drop.
  simpl.
  reflexivity.
Qed.

Lemma drop_wf : forall (n: nat) (q: Queue),
  wf_Queue q -> wf_Queue (drop n q).
Proof.
  intros.
  unfold drop.
  unfold wf_Queue.
  simpl.
  unfold wf_Queue in H.
  intros.
  apply H in H0.
  rewrite skipn_length.
  lia.
Qed.


(*clear | Properties*)
(*clear | doesn't change*)
Lemma clear_frame_error : forall (q: Queue),
  q_error(clear q) = q_error q.
Proof.
  intros.
  unfold clear.
  simpl.
  reflexivity.
Qed.

Lemma clear_frame_capacity : forall (q: Queue),
  q_capacity(clear q) = q_capacity q.
Proof.
  intros.
  unfold clear.
  simpl.
  reflexivity.
Qed.

Lemma clear_frame_strategy : forall (q: Queue),
  q_strategy(clear q) = q_strategy q.
Proof.
  intros.
  unfold clear.
  simpl.
  reflexivity.
Qed.
(*----maybe some error in AADL-HSM---*)
Lemma clear_wf : forall (q: Queue),
  wf_Queue(q) -> wf_Queue (clear q).
Proof.
  unfold wf_Queue.
  unfold clear.
  intros.
  simpl.
  simpl in H0.
  apply H in H0.
  lia.
Qed.

(*setBuffer | Properties*)
(*setBuffer | doesn't change*)
Lemma setBuffer_frame_error : forall (q: Queue) (b: vals),
  q_error(setBuffer q b) = q_error q.
Proof.
  intros.
  unfold setBuffer.
  simpl.
  reflexivity.
Qed.

Lemma setBuffer_frame_capacity : forall (q: Queue) (b: vals),
  q_capacity(setBuffer q b) = q_capacity q.
Proof.
  intros.
  unfold setBuffer.
  simpl.
  reflexivity.
Qed.

Lemma setBuffer_frame_strategy : forall (q: Queue) (b: vals),
  q_strategy(setBuffer q b) = q_strategy q.
Proof.
  intros.
  unfold setBuffer.
  simpl.
  reflexivity.
Qed.

Lemma setBuffer_wf : forall (q: Queue) (b: vals),
  List.length(b) <= q_capacity q ->
    wf_Queue(setBuffer q b).
Proof.
  intros.
  unfold setBuffer.
  unfold wf_Queue.
  simpl.
  intros.
  apply H.
Qed.

(* 2024-03-16 10:24 Cheng Jian*)