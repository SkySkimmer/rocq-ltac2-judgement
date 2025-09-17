From Ltac2 Require Import Ltac2.
From Ltac2Judgement Require Import Judge.

Ltac2 mkProd (id:ident) (dom : typej) (codom : termj -> typej) :=
  let codom_ctx := push_named_assum id dom in
  let codomj := codom (hypj id codom_ctx) in
  (* XXX should assert that codomj has compatible context with dom to be safe *)
  let codom := unsafe_subst_vars [id] (judge_constr codomj) in
  let r := relevance_of_sort (sort_of_typej dom) in
  let bnd := Constr.Binder.unsafe_make (Some id) r (judge_constr dom) in
  let c := Constr.Unsafe.make (Constr.Unsafe.Prod bnd codom) in
  unsafe_typej (judge_ctx dom) c (sort_of_product (sort_of_typej dom) (sort_of_typej codomj)).

#[warnings="-ltac2-notation-for-abbreviation"]
Ltac2 Notation oflags := Constr.Pretype.Flags.open_constr_flags_no_tc.

(* forall (A:Set) (x:A) (e:x = x), e = eq_refl
   (term construction with a relatively high amout of dependency on introduced variables) *)
Ltac2 Eval
  let ctx := global_ctx() in
  let c : _ judge :=
  mkProd @A (pretype_type_judge oflags ctx preterm:(Set)) (fun a =>
   mkProd @x (termj_is_typej a) (fun x =>
    let xc := judge_constr x in
    let refl_typ := pretype_type_judge oflags (judge_ctx x) preterm:($xc = $xc) in
    mkProd @e refl_typ (fun e =>
      (* NB: because we are using named and not rel, refl_typ is still valid in the extended ctx *)
      let ec := judge_constr e in
      let refl_typc := judge_constr refl_typ in
      pretype_type_judge oflags (judge_ctx e) preterm:(@eq $refl_typc $ec eq_refl))))
  in
  c.
