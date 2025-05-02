open Names
open Ltac2_plugin
open Tac2externals
open Tac2ffi
open Proofview.Notations
open EConstr

let return = Proofview.tclUNIT

let plugin_name = "rocq-ltac2-judgement.plugin"

let pname s = { Tac2expr.mltac_plugin = plugin_name; mltac_tactic = s }

let define s = define (pname s)

let core_prefix path n = KerName.make path (Label.of_id (Id.of_string_soft n))

let rocq_core n = core_prefix Tac2env.rocq_prefix n

let err_notfocussed =
  Tac2interp.LtacError (rocq_core "Not_focussed", [||])

let err_invalid_arg msg =
  Tac2interp.LtacError (rocq_core "Invalid_argument", [|of_option of_pp msg|])

(* XXX add a rel context? but we may want to have some "dummy" entries
   to handle lifts, not sure how to do that yet. *)
type ctx = Environ.named_context_val

let reset_ctx env (named : ctx) =
  let env = Environ.reset_with_named_context named env in
  env

let pf_apply_in ?(catch_exceptions=false) ctx f =
  Proofview.tclEVARMAP >>= fun sigma ->
  Proofview.tclENV >>= fun genv ->
  let env = reset_ctx genv ctx in
  Tac2core.wrap_exceptions ~passthrough:(not catch_exceptions) (fun () -> f env sigma)

type 'a judge = {
  ctx : ctx;
  term : EConstr.t;
  typ : 'a;
}

type _ judge_kind =
  | TermJudge : (EConstr.types * EConstr.ESorts.t) judge_kind
  | TypeJudge : EConstr.ESorts.t judge_kind

type any_judge = AnyJ : 'k judge_kind * 'k judge -> any_judge

type termj = (EConstr.types * EConstr.ESorts.t) judge
type typej = EConstr.ESorts.t judge

let val_ctx : ctx Tac2dyn.Val.tag = Tac2dyn.Val.create "judge-ctx"
let val_judge : any_judge Tac2dyn.Val.tag = Tac2dyn.Val.create "judge"

let ctx = Tac2ffi.repr_ext val_ctx
let judge = Tac2ffi.repr_ext val_judge

let of_termj j = Tac2ffi.of_ext val_judge (AnyJ (TermJudge, j))
let of_typej j = Tac2ffi.of_ext val_judge (AnyJ (TypeJudge, j))
let to_termj j : termj = match Tac2ffi.to_ext val_judge j with
  | AnyJ (TermJudge, j) -> j
  | AnyJ (TypeJudge, _) -> assert false
let to_typej j : typej = match Tac2ffi.to_ext val_judge j with
  | AnyJ (TypeJudge, j) -> j
  | AnyJ (TermJudge, _) -> assert false
let termj = Tac2ffi.make_repr of_termj to_termj
let typej = Tac2ffi.make_repr of_typej to_typej

let () = define "judge_ctx" (judge @-> ret ctx) @@ fun (AnyJ (_, t)) -> t.ctx

let () = define "judge_constr" (judge @-> ret constr) @@ fun (AnyJ (_, t)) -> t.term

let () = define "unsafe_typej" (ctx @-> constr @-> sort @-> ret typej) @@ fun ctx t s ->
  { ctx; term=t; typ=s }

let () = define "unsafe_termj" (constr @-> typej @-> ret termj) @@ fun c j ->
  { ctx = j.ctx; term=c; typ=(j.term, j.typ) }

let () = define "infer_termj" (ctx @-> constr @-> tac termj) @@ fun ctx c ->
  pf_apply_in ~catch_exceptions:true ctx @@ fun env sigma ->
  let sigma, t = Typing.type_of env sigma c in
  let s = Retyping.get_sort_of env sigma t in
  Proofview.Unsafe.tclEVARS sigma <*>
  return { ctx; term = c; typ = (t, s) }

let () = define "termj_is_typej" (termj @-> tac typej) @@ fun { ctx; term; typ=(ty,_) } ->
  pf_apply_in ~catch_exceptions:true ctx @@ fun env sigma ->
  let sigma, tj = Typing.type_judgment env sigma (Environ.make_judge term ty) in
  Proofview.Unsafe.tclEVARS sigma <*>
  return { ctx; term = tj.utj_val; typ = tj.utj_type }

let ctx_of_env env : ctx = Environ.named_context_val env

let () = define "global_ctx" (unit @-> eret ctx) @@ fun () env _ ->
  (* rel context is always empty but getting the empty context this way is fine *)
  ctx_of_env env

let () = define "goal_ctx" (unit @-> tac ctx) @@ fun () ->
  Proofview.Goal.goals >>= function
  | [gl] ->
    gl >>= fun gl ->
    return (ctx_of_env (Proofview.Goal.env gl))
  | [] | _ :: _ :: _ ->
    Tac2core.throw err_notfocussed

let () = define "current_ctx" (unit @-> tac ctx) @@ fun () ->
  Tac2core.pf_apply @@ fun env _ -> return (ctx_of_env env)

let () = define "typej_of_termj" (termj @-> ret typej) @@ fun j ->
  { ctx = j.ctx; term = fst j.typ; typ = snd j.typ }

let () = define "sort_of_typej" (typej @-> ret sort) @@ fun j -> j.typ

(* NB if we add a rel context to [ctx], we must check that no rels appear in the type. *)
let () = define "push_named_assum" (ident @-> typej @-> tac ctx) @@ fun id j ->
  let named = j.ctx in
  if Id.Map.mem id named.env_named_map then
    Tac2core.throw
      (err_invalid_arg
         (Some Pp.(str "Ltac2 judgement push_named_assum: " ++ Id.print id ++ str " not free.")))
  else
    let idr = Context.make_annot id (ESorts.relevance_of_sort j.typ) in
    let named = EConstr.push_named_context_val (LocalAssum (idr,j.term)) named in
    return named

let () = define "pretype_in" (pretype_flags @-> ctx @-> preterm @-> tac termj) @@ fun flags ctx c ->
  pf_apply_in ~catch_exceptions:true ctx @@ fun env sigma ->
  let sigma, t, ty =
    Pretyping.understand_uconstr_ty ~flags ~expected_type:WithoutTypeConstraint env sigma c
  in
  let s = Retyping.get_sort_of env sigma ty in
  let res = { ctx; term = t; typ = (ty, s) } in
  Proofview.Unsafe.tclEVARS sigma <*>
  return res

let () = define "pretype_type_in" (pretype_flags @-> ctx @-> preterm @-> tac typej) @@ fun flags ctx c ->
  pf_apply_in ~catch_exceptions:true ctx @@ fun env sigma ->
  let sigma, t, ty =
    Pretyping.understand_uconstr_ty ~flags ~expected_type:IsType env sigma c
  in
  let s = destSort sigma ty in
  let res = { ctx; term = t; typ = s } in
  Proofview.Unsafe.tclEVARS sigma <*>
  return res

let () = define "pretype_in_expecting" (pretype_flags @-> preterm @-> typej @-> tac termj) @@ fun flags c { ctx; term=ty; typ=s } ->
  pf_apply_in ~catch_exceptions:true ctx @@ fun env sigma ->
  let sigma, t, ty =
    Pretyping.understand_uconstr_ty ~flags ~expected_type:(OfType ty) env sigma c
  in
  let res = { ctx; term = t; typ = (ty, s) } in
  Proofview.Unsafe.tclEVARS sigma <*>
  return res
