From Ltac2 Require Import Init.
From Ltac2 Require Constr.

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
