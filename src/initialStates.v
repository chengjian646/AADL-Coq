From Coq Require Import List Arith ListSet String.
From compcert.common Require Import Values.
From compcert.lib Require Import Maps.

Import ListNotations.

From aadlcoq.src Require Import Queue Model ThreadState PortState SystemState.

Definition empty_queue_size1 : Queue :=
  mk_empty_queue 1 DropEarliest.

Definition empty_queue_size5 : Queue :=
  mk_empty_queue 5 DropEarliest.





















