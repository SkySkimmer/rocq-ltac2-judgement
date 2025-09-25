From Ltac2 Require Import Ltac2.
From Ltac2Judgement Require Import Judge.
From Ltac2Judgement Require Unsafe.

Ltac2 mkProdj (id:ident) (dom : typej) (codom : termj -> typej) :=
  let codom_ctx := push_named_assum id dom in
  let codomj := codom (hypj id codom_ctx) in
  (* XXX should assert that codomj has compatible context with dom to be safe *)
  let codom := Unsafe.subst_vars [id] (judge_constr codomj) in
  let r := relevance_of_sort (sort_of_typej dom) in
  let bnd := Constr.Binder.unsafe_make (Some id) r (judge_constr dom) in
  let c := Constr.Unsafe.make (Constr.Unsafe.Prod bnd codom) in
  Unsafe.typej (judge_ctx dom) c (sort_of_product (sort_of_typej dom) (sort_of_typej codomj)).

#[warnings="-ltac2-notation-for-abbreviation"]
Ltac2 Notation oflags := Constr.Pretype.Flags.open_constr_flags_no_tc.

(* forall (A:Set) (x:A) (e:x = x), e = eq_refl
   (term construction with a relatively high amout of dependency on introduced variables) *)
Ltac2 Eval
  let ctx := global_ctx() in
  let c : _ judge :=
  mkProdj @A (pretype_type_judge oflags ctx preterm:(Set)) (fun a =>
   mkProdj @x (termj_is_typej a) (fun x =>
    let xc := judge_constr x in
    let refl_typ := pretype_type_judge oflags (judge_ctx x) preterm:($xc = $xc) in
    mkProdj @e refl_typ (fun e =>
      (* NB: because we are using named and not rel, refl_typ is still valid in the extended ctx *)
      let ec := judge_constr e in
      let refl_typc := judge_constr refl_typ in
      pretype_type_judge oflags (judge_ctx e) preterm:(@eq $refl_typc $ec eq_refl))))
  in
  c.

(** unsafe HOAS (manual ctx manipulation) *)
Ltac2 mkProd (ctx : ctx) (id:ident) (dom : constr) (codom : ctx -> constr -> constr) :=
  let domr := Unsafe.relevance_of_type_in_ctx ctx dom in
  let codom_ctx := Unsafe.push_named_assum ctx id dom domr in
  let codom := codom codom_ctx (Constr.Unsafe.make (Constr.Unsafe.Var id)) in
  let codom := Unsafe.subst_vars [id] codom in
  Constr.Unsafe.make (Constr.Unsafe.Prod (Constr.Binder.unsafe_make (Some id) domr dom) codom).

Ltac2 pretype_in_ctx flags ctx c :=
  let j := pretype_judge flags ctx c in
  judge_constr j.

(* XXX "preterm" is at level 8 but we want to accept top level *)
Ltac2 Notation "open_constr_in_ctx:(" ctx(tactic) "|-" x(preterm) ")" :=
  pretype_in_ctx Constr.Pretype.Flags.open_constr_flags_no_tc ctx x.

(* forall (A:Set) (x:A) (e:x = x), e = eq_refl
   (term construction with a relatively high amout of dependency on introduced variables) *)
Ltac2 Eval
  let env := global_ctx() in
  let c :=
  mkProd env @A 'Set (fun env a =>
   mkProd env @x a (fun env x =>
    let refl_typ := open_constr_in_ctx:(env |- ($x = $x)) in
    mkProd env @e refl_typ (fun env e =>
      (* NB: because we are using named and not rel, refl_typ is still valid in the extended env *)
      open_constr_in_ctx:(env |- (@eq $refl_typ $e eq_refl)))))
  in
  Control.assert_true (Constr.equal c '(forall (A:Set) (x:A) (e:x = x), e = eq_refl));
  let _ := Constr.type c in
  ().

(* forall x:nat, (x = x) = (x = x)
   demonstrates how the locally bound variable can be referred to in terms *)
Ltac2 Eval
  let env := global_ctx() in
  let c :=
  mkProd env @x 'nat (fun env x =>
   (* we can refer to x as any of [x], [&x] and [$x]
      (not sure how reliable bare [x] is) *)
   let c1 := open_constr_in_ctx:(env |- (&x = x)) in
   let c2 := open_constr_in_ctx:(env |- (&x = $x)) in
   open_constr_in_ctx:(env |- ($c1 = $c2)))
  in
  Control.assert_true (Constr.equal c '(forall x:nat, (x = x) = (x = x))).

(* forall x:nat, 2 + x = S (S x)
   with the RHS constructed by reducing the LHS in the extended context *)
Ltac2 Eval
  let env := global_ctx() in
  let c :=
  mkProd env @x 'nat (fun env x =>
    let y := open_constr_in_ctx:(env |- (2 + $x)) in
    let y_reduced := Unsafe.eval_in_ctx env (Std.Red.simpl RedFlags.all None) y in
    (* 'eq is '(@eq _) which produces a type evar with empty context *)
    open_constr_in_ctx:(env |- ($y = $y_reduced)))
  in
  Control.assert_true (Constr.equal c '(forall x, 2 + x = S (S x)));
  let _ := Constr.type c in
  ().

Ltac2 mkLetIn (ctx : ctx) (id:ident) (value : constr) (typ : constr) (body : ctx -> constr -> constr) :=
  let r := Unsafe.relevance_of_term_in_ctx ctx value in
  let body_ctx := Unsafe.push_named_def ctx id value typ r in
  let body := body body_ctx (Constr.Unsafe.make (Constr.Unsafe.Var id)) in
  let body := Unsafe.subst_vars [id] body in
  Constr.Unsafe.make (Constr.Unsafe.LetIn (Constr.Binder.unsafe_make (Some id) r typ) value body).

Ltac2 Eval
  let env := global_ctx() in
  let c :=
  mkLetIn env @x '3 'nat (fun env x =>
    open_constr_in_ctx:(env |- (eq_refl : $x = 3)))
  in
  Control.assert_true (Constr.equal c '(let x := 3 in eq_refl : x = 3));
  let _ := Constr.type c in
  ().
