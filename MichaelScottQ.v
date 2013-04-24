Require Import RGref.DSL.DSL.
Require Import RGref.DSL.Concurrency.

(** A Tail-less Michael-Scott Queue *)

(** Unless we introduce lots of indirections through references to options,
    we're stuck adapting Capretta's impredicative induction-recursion
    encoding to support mutual inductive types indexing each other. *)
Inductive Node : Set :=
  | mkNode : forall (TAIL:Set) (TP:hpred TAIL) (TRel:hrel TAIL),
               nat -> option (ref{TAIL|TP}[TRel,TRel]) -> Node.
Inductive validNode : hpred (Node) :=
  | nil_next : forall (TAIL:Set) (TP:hpred TAIL) (TRel:hrel TAIL) n h,
                 validNode (mkNode TAIL TP TRel n None) h
  | nil_reach : forall (TP:hpred Node) (TRel:hrel Node) n h tl,
                  validNode (h[tl]) h ->
                  validNode (mkNode Node TP TRel n (Some tl)) h.
Inductive deltaNode : hrel Node :=
  | node_refl : forall n h,
                  deltaNode n n h h
  | node_append : forall n n' R tl h h',
                    h[tl]=(mkNode Node validNode R n' None) ->
                    h'[tl]=(mkNode Node validNode R n' None) ->
                    deltaNode (mkNode Node validNode R n None)
                              (mkNode Node validNode R n (Some tl))
                              h h'.
Print ImmediateReachability.
Global Instance nd_reach : ImmediateReachability Node := {
  imm_reachable_from_in :=
  (fun T P R G r nd =>
     match nd with
     | mkNode TL TP TR n tl => imm_reachable_from_in r tl
     end)
}.

Definition noderef := ref{Node|validNode}[deltaNode,deltaNode].

Lemma msq_stability : stable validNode deltaNode.
Proof.
  compute. intros.
  induction H0; eauto.
  constructor. rewrite H1. constructor.
Qed.
Hint Resolve msq_stability.

(** We're following The Art of Multiprocessor Programming, S10.5, but
    temporarily skipping the tail.
    Enqueue appends a single node at the end.
    Dequeue moves the head pointer froma sentinel to sentinel.next, which
    becomes the new sentinel.
*)
Inductive MSQ : Set := mkMSQ : noderef -> MSQ.
Definition vMSQ : hpred MSQ := any. (* More interesting with tail pointer *)
Inductive δmsq : hrel MSQ :=
  (* h and h' here are important.  This allows arbitrary changes as long as the
     head pointer remains unchanged.  It relies on the noderef to enforce
     further properties. *)
  | msq_nop : forall n h h', δmsq n n h h'
  | msq_dequeue : forall n hd h h' rest,
                    h[hd]=(mkNode Node validNode deltaNode n (Some rest)) ->
                    δmsq (mkMSQ hd) (mkMSQ rest) h h'.
Definition msq := ref{MSQ|vMSQ}[δmsq,δmsq].

Lemma MSQ_stability : stable vMSQ δmsq.
Proof.
  compute; intros; eauto.
Qed.
Hint Resolve MSQ_stability.

Definition alloc_msq {Γ} (_:unit) : rgref Γ msq Γ :=
  sentinel <- Alloc (mkNode Node validNode deltaNode 0 None);
  Alloc (mkMSQ sentinel).