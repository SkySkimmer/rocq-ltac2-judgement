From Ltac2 Require Import Init.
From Ltac2 Require Constr.

Declare ML Module "rocq-ltac2-judgement.plugin".

(** A context [Γ]. *)
Ltac2 Type ctx.

(** Term judgements [Γ ⊢ c : t : s] and type judgements [Γ ⊢ c : s]
    are both instances of this type. When the phantom type is unknown
    we see a generalized judgement [Γ ⊢ c : *]. *)
Ltac2 Type 'phantom judge.

Ltac2 Type term_phantom.
Ltac2 Type type_phantom.

(** A judgement [Γ ⊢ c : t : s] ([s] is a sort).
    Note that this is parenthesized as [Γ ⊢ c : (t : s)]. *)
Ltac2 Type termj := term_phantom judge.

(** A judgement [Γ ⊢ t : s] ([s] is a sort). *)
Ltac2 Type typej := type_phantom judge.

(** From argument [Γ ⊢ c : *] return [Γ]. *)
Ltac2 @external judge_ctx : 'a judge -> ctx
  := "rocq-ltac2-judgement.plugin" "judge_ctx".

(** From argument [Γ ⊢ c : *] return [c]. *)
Ltac2 @external judge_constr : 'a judge -> constr
  := "rocq-ltac2-judgement.plugin" "judge_constr".

(** From arguments [Γ] [t] and [s] return [Γ ⊢ t : s] without checking anything. *)
Ltac2 @external unsafe_typej : ctx -> constr -> sort -> typej
  := "rocq-ltac2-judgement.plugin" "unsafe_typej".

(** From arguments [Γ] [c] [t] and [s] return [Γ ⊢ c : t : s] without checking anything. *)
Ltac2 @external unsafe_termj : constr -> typej -> termj
  := "rocq-ltac2-judgement.plugin" "unsafe_termj".

(** From arguments [Γ] and [c], check that [c] is well typed in [Γ]
    with type [t] whose sort is [s] and return [Γ ⊢ c : t : s]. *)
Ltac2 @external infer_termj : ctx -> constr -> termj
  := "rocq-ltac2-judgement.plugin" "infer_termj".

(** If the given judgement is [Γ ⊢ t : s : _] where [s] is a sort (or evar
    which can be defined to a fresh sort), return type judgement [Γ ⊢ t : s].
    Not to be confused with [typej_of_termj]. *)
Ltac2 @external termj_is_typej : termj -> typej
  := "rocq-ltac2-judgement.plugin" "termj_is_typej".

(** Return the global context (containing section variables and no
    goal hypotheses). *)
Ltac2 @external global_ctx : unit -> ctx
  := "rocq-ltac2-judgement.plugin" "global_ctx".

(** If 1 goal is focused, return the goal context (containing goal
    hypotheses, and any section variables which haven't been cleard).
    Otherwise throw [Not_focussed]. *)
Ltac2 @external goal_ctx : unit -> ctx
  := "rocq-ltac2-judgement.plugin" "goal_ctx".

(** If no goals are focused, [global_ctx]. If 1 goal is focused,
    [goal_ctx]. Otherwise throw [Not_focussed]. *)
Ltac2 @external current_ctx : unit -> ctx
  := "rocq-ltac2-judgement.plugin" "current_ctx".

(** From argument [Γ ⊢ c : t : s], return [Γ ⊢ t : s] *)
Ltac2 @external typej_of_termj : termj -> typej
  := "rocq-ltac2-judgement.plugin" "typej_of_termj".

(** From argument [Γ ⊢ t : s], return [s] *)
Ltac2 @external sort_of_typej : typej -> sort
  := "rocq-ltac2-judgement.plugin" "sort_of_typej".

(** From argument [Γ ⊢ c : t : s], return [s] *)
Ltac2 sort_of_termj (j : termj) : sort := sort_of_typej (typej_of_termj j).

(** From arguments [id] and [Γ ⊢ t : s], produce [Γ, id : t].
    [id] must be fresh in [Γ]. *)
Ltac2 @external push_named_assum : ident -> typej -> ctx
  := "rocq-ltac2-judgement.plugin" "push_named_assum".

(** Infer a term judgement from a preterm in a given context. *)
Ltac2 @external pretype_in : Constr.Pretype.Flags.t -> ctx -> preterm -> termj
  := "rocq-ltac2-judgement.plugin" "pretype_in".

(** Infer a type judgement from a preterm in a given context. *)
Ltac2 @external pretype_type_in : Constr.Pretype.Flags.t -> ctx -> preterm -> typej
  := "rocq-ltac2-judgement.plugin" "pretype_type_in".

(** Infer a term judgement from a preterm at a given expected type
    (the judgement for the expected type contains the context). *)
Ltac2 @external pretype_in_expecting : Constr.Pretype.Flags.t -> preterm -> typej -> termj
  := "rocq-ltac2-judgement.plugin" "pretype_in_expecting".
