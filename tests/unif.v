From Ltac2 Require Import Ltac2.
From Ltac2Judgement Require Import Judge.
From Ltac2Judgement Require Unsafe.

Ltac2 pretype_in_ctx flags ctx c :=
  let j := pretype_judge flags ctx c in
  judge_constr j.

(* XXX "preterm" is at level 8 but we want to accept top level *)
Ltac2 Notation "open_constr_in_ctx:(" ctx(tactic) "|-" x(preterm) ")" :=
  pretype_in_ctx Constr.Pretype.Flags.open_constr_flags_no_tc ctx x.

Ltac2 conv_in ctx c1 c2 := Unsafe.conv_in_ctx Unification.CONV TransparentState.full ctx c1 c2.

Ltac2 unify_in ctx c1 c2 :=
  match Control.case (fun () => Unsafe.unify_in_ctx Unification.CONV TransparentState.full ctx c1 c2) with
  | Val _ => true
  | Err _ => false
  end.

Ltac2 mkVar x := Constr.Unsafe.make (Constr.Unsafe.Var x).

Ltac2 Eval
  let ctx := global_ctx() in
  let a := mkVar @A in
  let mk t r :=
    let ctx := Unsafe.push_named_assum ctx @A t Constr.Binder.Relevant in
    let ctx := Unsafe.push_named_assum ctx @x a r in
    let ctx := Unsafe.push_named_assum ctx @y a r in
    ctx
  in
  let ctx1 := mk 'Prop Constr.Binder.Relevant in
  let ctx2 := mk 'SProp Constr.Binder.Irrelevant in
  Control.assert_false (conv_in ctx1 (mkVar @x) (mkVar @y));
  Control.assert_true  (conv_in ctx2 (mkVar @x) (mkVar @y));
  Control.assert_false (unify_in ctx1 (mkVar @x) (mkVar @y));
  Control.assert_true  (unify_in ctx2 (mkVar @x) (mkVar @y));
  ().

Ltac2 Eval
  let ctx := global_ctx() in
  let ctx := push_named_def @x (pretype_judge Constr.Pretype.Flags.open_constr_flags_no_tc ctx preterm:(3)) in
  Control.assert_true (conv_in ctx (mkVar @x) '3);
  Control.assert_false (conv_in ctx (mkVar @x) '4);
  Control.assert_true  (unify_in ctx (mkVar @x) '3);
  Control.assert_false (unify_in ctx (mkVar @x) '4);
  Control.assert_false (conv_in ctx (mkVar @x) '(S _));
  Control.assert_true  (unify_in ctx (mkVar @x) '(S _));
  ().
