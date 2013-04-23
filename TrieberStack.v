Require Import RGref.DSL.DSL.
Require Import RGref.DSL.Concurrency.

(** Trieber Stack
    A lock-free stack implementation. *)
(** Luckily, we can escape the induction-recursion encoding since
    nodes are constant. *)
Inductive Node : Set :=
  | mkNode : nat -> option (ref{Node|any}[local_imm,local_imm]) -> Node.

(** We'll follow roughly S11.2 of The Art of Multiprocessor Programming:
    a basic Trieber stack, with no backoff or elimination. *)
Inductive deltaTS : hrel (option (ref{Node|any}[local_imm,local_imm])) :=
  | ts_nop : forall n h h', deltaTS n n h h'
  | ts_push : forall n hd hd' h h', h'[hd']=(mkNode n hd) ->
                                    deltaTS hd (Some hd') h h'
  | ts_pop : forall n hd hd' h h', h[hd]=(mkNode n hd') ->
                                   deltaTS (Some hd) hd' h h'.

Lemma precise_deltaTS : precise_rel deltaTS.
Proof.
  red. intros. induction H1.
  constructor.
  eapply ts_push. rewrite <- H0; eauto. constructor. red. unfold reach_option. constructor.
      red. red. reflexivity.
  eapply ts_pop. rewrite <- H; eauto. constructor. constructor. red. red. reflexivity.
Qed.
Hint Resolve precise_deltaTS.

                                                       
Definition ts := ref{option (ref{Node|any}[local_imm,local_imm])|any}[deltaTS,deltaTS].

Program Definition alloc_ts {Γ} (u:unit) : rgref Γ ts Γ :=
  Alloc None.

(* TODO: push, pop implementations *)