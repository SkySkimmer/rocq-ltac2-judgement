From Ltac2 Require Import Init.
From Ltac2 Require Constr.

Declare ML Module "rocq-ltac2-judgement.plugin".

(** NB: "retype" means re-inferring the type of a term with minimal checking.
    For instance if the term "Nad.add true true" is constructed (through unsafe means),
    retyping it succeeds producing type "nat". *)

(** A context [Γ]. *)
Ltac2 Type ctx.

(** Term judgements [Γ ⊢ c : t] and type judgements [Γ ⊢ c : s] are both instances of this type.
    When the phantom type is unknown we see a generalized judgement [Γ ⊢ c : *]. *)
Ltac2 Type 'phantom judge.

Ltac2 Type term_phantom.
Ltac2 Type type_phantom.

(** A judgement [Γ ⊢ c : t]. *)
Ltac2 Type termj := term_phantom judge.

(** A type judgement [Γ ⊢ t : s] ([s] is s sort). *)
Ltac2 Type typej := type_phantom judge.

(** From argument [Γ ⊢ c : *] return [Γ]. *)
Ltac2 @external judge_ctx : 'a judge -> ctx
  := "rocq-ltac2-judgement.plugin" "judge_ctx".

(** From argument [Γ ⊢ c : *] return [c]. *)
Ltac2 @external judge_constr : 'a judge -> constr
  := "rocq-ltac2-judgement.plugin" "judge_constr".

(** From [id] and [Γ], if [id ∈ Γ] return [Γ ⊢ id : t] for apppropriate [t]. *)
Ltac2 @external hypj : ident -> ctx -> termj
  := "rocq-ltac2-judgement.plugin" "hypj".

(** From arguments [Γ] and [c],
    check that [c] is well typed in [Γ] with type [t]
    and return [Γ ⊢ c : t]. *)
Ltac2 @external infer_termj : ctx -> constr -> termj
  := "rocq-ltac2-judgement.plugin" "infer_termj".

(** If the given judgement is [Γ ⊢ t : s] where [s] is a sort
    (or evar which can be defined to a fresh sort),
    return type judgement [Γ ⊢ t : s].
    Not to be confused with [typej_of_termj]. *)
Ltac2 @external termj_is_typej : termj -> typej
  := "rocq-ltac2-judgement.plugin" "termj_is_typej".

(** From type judgement [Γ ⊢ t : s] return term judgement [Γ ⊢ t : s]. *)
Ltac2 @external typej_is_termj : typej -> termj
  := "rocq-ltac2-judgement.plugin" "typej_is_termj".

(** Return the global context (containing section variables and no goal hypotheses). *)
Ltac2 @external global_ctx : unit -> ctx
  := "rocq-ltac2-judgement.plugin" "global_ctx".

(** If 1 goal is focused, return the goal context
    (containing goal hypotheses, and any section variables which haven't been cleared).
    Otherwise throw [Not_focussed]. *)
Ltac2 @external goal_ctx : unit -> ctx
  := "rocq-ltac2-judgement.plugin" "goal_ctx".

(** If no goals are focused, [global_ctx].
    If 1 goal is focused, [goal_ctx].
    Otherwise throw [Not_focussed]. *)
Ltac2 @external current_ctx : unit -> ctx
  := "rocq-ltac2-judgement.plugin" "current_ctx".

(** From argument [Γ ⊢ c : t], return [Γ ⊢ t : s].
    Must retype [t] to get its sort [s]. *)
Ltac2 @external typej_of_termj : termj -> typej
  := "rocq-ltac2-judgement.plugin" "typej_of_termj".

(** From argument [Γ ⊢ t : s], return [s] *)
Ltac2 @external sort_of_typej : typej -> sort
  := "rocq-ltac2-judgement.plugin" "sort_of_typej".

(** Produce the relevance of the given sort (SProp -> Irrelevant, etc). *)
Ltac2 @external relevance_of_sort : sort -> Constr.Binder.relevance
  := "rocq-ltac2-judgement.plugin" "relevance_of_sort".
(* XXX upstream this *)

(** From [Γ] and [s] produce [Γ ⊢ s : s+1]. *)
Ltac2 @external typej_of_sort : ctx -> sort -> typej
  := "rocq-ltac2-judgement.plugin" "typej_of_sort".

(** From arguments [id] and [Γ ⊢ t : s], produce [Γ, id : t].
    [id] must be fresh in [Γ]. *)
Ltac2 @external push_named_assum : ident -> typej -> ctx
  := "rocq-ltac2-judgement.plugin" "push_named_assum".

(** Infer a term judgement from a preterm in a given context. *)
Ltac2 @external pretype_judge : Constr.Pretype.Flags.t -> ctx -> preterm -> termj
  := "rocq-ltac2-judgement.plugin" "pretype_judge".

(** Infer a type judgement from a preterm in a given context. *)
Ltac2 @external pretype_type_judge : Constr.Pretype.Flags.t -> ctx -> preterm -> typej
  := "rocq-ltac2-judgement.plugin" "pretype_type_judge".

(** Infer a term judgement from a preterm at a given expected type
    (the judgement for the expected type contains the context). *)
Ltac2 @external pretype_in_expecting : Constr.Pretype.Flags.t -> preterm -> typej -> termj
  := "rocq-ltac2-judgement.plugin" "pretype_in_expecting".

(** From [s] and [s'] produce [s''] such that if [A : s] and [B : s'] then [A -> B : s'']. *)
Ltac2 @external sort_of_product : sort -> sort -> sort
  := "rocq-ltac2-judgement.plugin" "sort_of_product".
(* XXX upstream this *)
