From Coq Require Import List Arith ListSet String.
From compcert.common Require Import Values.
From compcert.lib Require Import Maps.

Import ListNotations.

From aadlcoq.src.static Require Import Model.
From aadlcoq.src.dynamic.RuntimeState Require Import ThreadState PortState.


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

(*-----------------------Sensor----------------------------*)
Definition SensorCurrentTempPort : PortDescr :=
  mkPortDescr "SensorCurrentTempPort" portid0 comp0 Out Data 1 0.

Definition SensorTempChangePort : PortDescr :=
  mkPortDescr "SensorTempChangePort" portid1 comp0 Out Event 5 1.


Definition Sensor_Component : CompDescr :=
  mkCompDescr "Sensor_Component" comp0
              [portid0 ; portid1]
              Model.Periodic
              []
              [].
(*--------------------------Control------------------------*)
Definition ControlCurrentTempPort : PortDescr :=
  mkPortDescr "ControlCurrentTempPort" portid2 comp1 In Data 1 0.

Definition ControlTempChangePort : PortDescr :=
  mkPortDescr "ControlTempChangePort" portid3 comp1 In Event 5 1.

Definition ControlStoveCmdPort : PortDescr :=
  mkPortDescr "ControlStoveCmdPort" portid4 comp1 Out Event 5 1.

Definition ControlStoveAckPort : PortDescr :=
  mkPortDescr "ControlStoveAckPort" portid5 comp1 In Event 5 1.

Definition var_low := mkVar "lowtemp".
Definition var_high := mkVar "hightemp".

Definition Control_Component : CompDescr :=
  mkCompDescr "Control_Component" comp1
              [portid2 ; portid3 ; portid4 ; portid5]
              Model.Sporadic
              [portid3 ; portid5]
              [var_low ; var_high].

(*-----------------------Stove---------------------------*)
Definition StoveCmdPort : PortDescr :=
  mkPortDescr "StoveCmdPort" portid6 comp2 In Event 5 1.

Definition StoveAckPort : PortDescr :=
  mkPortDescr "StoveAckPort" portid7 comp2 Out Event 5 1.


Definition Stove_Component : CompDescr :=
  mkCompDescr "Stove_Component" comp2
              [portid6 ; portid7]
              Model.Sporadic
              [portid6]
              [].

(*-------------------------------------------------------*)
Definition test_set2 : PortIds := ListSet.set_add PortId_eq portid2 [].

Definition Portmap_empty : Portmap.t (option PortIds) := fun _ => None.

(**Portmap.t (option PortIds) *)
Definition conn02 := Portmap.set portid0 (Some (test_set2)) Portmap_empty. 




