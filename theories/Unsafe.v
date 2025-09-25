From Ltac2 Require Import Init.
From Ltac2 Require Constr Std Unification.

From Ltac2Judgement Require Import Judge.

(** From arguments [Γ] [t] and [s] return [Γ ⊢ t : s] without checking anything. *)
Ltac2 @external typej : ctx -> constr -> sort -> typej
  := "rocq-ltac2-judgement.plugin" "unsafe_typej".

(** From arguments [Γ] [c] and [t] return [Γ ⊢ c : t] without checking anything. *)
Ltac2 @external termj : constr -> typej -> termj
  := "rocq-ltac2-judgement.plugin" "unsafe_termj".

(** [subst_vars [id1;...;idn] t] substitutes [Var idj] by [Rel j] in [t]. *)
Ltac2 @external subst_vars : ident list -> constr -> constr
  := "rocq-ltac2-judgement.plugin" "subst_vars".
(* XXX upstream this? *)

(** From arguments [Γ] and [c], if [c] is a valid term in [Γ] return its relevance as a term
    (faster than retyping but not quite constant time).
    Does not check that [c] is a valid term in [Γ]. *)
Ltac2 @external relevance_of_term_in_ctx : ctx -> constr -> Constr.Binder.relevance
  := "rocq-ltac2-judgement.plugin" "relevance_of_term_in_ctx".

(** From arguments [Γ] and [c], if [c] is a valid type in [Γ] return its relevance as a type
    (by retyping).
    Does not check that [c] is a valid type in [Γ]. *)
Ltac2 @external relevance_of_type_in_ctx : ctx -> constr -> Constr.Binder.relevance
  := "rocq-ltac2-judgement.plugin" "relevance_of_type_in_ctx".

(** From arguments [Γ] [id] [t] and [r], produces [Γ, id : t] assuming [t] has relevance [r].
    Throws if [id] is already bound in [Γ].
    Does not check that [t] is valid or has relevance [r] in [Γ]. *)
Ltac2 @external push_named_assum : ctx -> ident -> constr -> Constr.Binder.relevance -> ctx
  := "rocq-ltac2-judgement.plugin" "unsafe_push_named_assum".

(** From arguments [Γ] [id] [c] [t] and [r], produces [Γ, id := c : t] assuming [t] has relevance [r].
    Throws if [id] is already bound in [Γ].
    Does not check anything else. *)
Ltac2 @external push_named_def : ctx -> ident -> constr -> constr -> Constr.Binder.relevance -> ctx
  := "rocq-ltac2-judgement.plugin" "unsafe_push_named_def".

Module Binder.

  (** Produces the [binder] corresponding to a type judgement and a name.

      Safe to call, but [binder] does not retain context information
      so using the resulting value with safe APIs
      (eg [Std.eval_hnf (Constr.Binder.type (of_typej ...))])
      is not safe. *)
  Ltac2 of_typej (na : ident option) (j : typej) : binder :=
    Constr.Binder.unsafe_make na (relevance_of_sort (sort_of_typej j)) (judge_constr j).

  (** From arguments [Γ] [na] [t] produces the binder for [na : t],
      retyping [t] in [Γ] to get its relevance. *)
  Ltac2 make_in_ctx (ctx : ctx) (na : ident option) (t : constr) : binder :=
    let r := relevance_of_type_in_ctx ctx t in
    Constr.Binder.unsafe_make na r t.

End Binder.

(** [eval_in_ctx Γ red c] reduces [c] according to [red] in context [Γ].
    Does not check that [c] or [red] are valid in [Γ]. *)
Ltac2 @external eval_in_ctx : ctx -> Std.Red.t -> constr -> constr
  := "rocq-ltac2-judgement.plugin" "eval_in_ctx".
(* XXX judgement version (but red can contain constr!) *)

(** Print the given term in the given context (does not print the context). *)
Ltac2 @external message_of_constr_in_ctx : ctx -> constr -> message
  := "rocq-ltac2-judgement.plugin" "message_of_constr_in_ctx".
(* XXX also add kfprintf_in_ctx for more convenient printing *)

(** [conv_in_ctx] returns true if both terms are convertible, in which case it updates the
    environment with the universes constraints required for the terms to be convertible.
    It returns false if the terms are not convertible.
    It fails if there is more than one goal under focus.

    [conv_in_ctx] is parametrised by:
    - Unification.conv_flag which controls if conversion is done up to cumulativity or not
    - TransparentState.t which controls which constants get unfolded during conversion
*)
Ltac2 @external conv_in_ctx : Unification.conv_flag -> TransparentState.t -> ctx -> constr -> constr -> bool
  := "rocq-ltac2-judgement.plugin" "conv_in_ctx".

(** [unify pb ts ctx c1 c2] unifies [c1] and [c2] in [ctx] (using Evarconv unification), which
    may have the effect of instantiating evars. If the [c1] and [c2] cannot be
    unified, an [Internal] exception is raised. *)
Ltac2 @external unify_in_ctx : Unification.conv_flag -> TransparentState.t -> ctx -> constr -> constr -> unit
  := "rocq-ltac2-judgement.plugin" "unify_in_ctx".
