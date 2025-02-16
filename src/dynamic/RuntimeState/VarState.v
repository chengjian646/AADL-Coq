From compcert.common Require Import Values.
From compcert.lib Require Import Maps.

From aadlcoq.src.static Require Import Model.
(*
Variable A : Type. *)

Module VarEq.
  Definition t := Var.
  Definition eq := Var_eq.
End VarEq.

Module Varmap := EMap(VarEq).
(*应用程序变量类型和值的概念在这一点上还没有完全
发展，所以我们将表示通用值类型的类型a的VarState
参数化。*)
Definition VarState := Varmap.t (option val).
(*Definition VarState (A: Type) := Varmap.t (option A).*)

(*目前，我们没有任何条件为VarState做好准备。
之后，我们将需要添加条件，例如，指示存储的值
与变量的类型匹配。因此，为格式良好留下一个占位符。*) (*
Print Vars. *)
(*检查vars列表中的所有元素是否在映射的key中*)

Definition wf_VarState_dom (vs: VarState) (vars: Vars) : Prop:=
  forall k v,
    Varmap.get k vs = Some v <->
    ListSet.set_In k vars.

Definition wf_VarState (vs: VarState) (vars: Vars) : Prop:=
  wf_VarState_dom vs vars.