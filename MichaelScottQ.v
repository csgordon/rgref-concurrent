Require Import RGref.DSL.DSL.
Require Import RGref.DSL.Concurrency.

(** * A Tail-less Michael-Scott Queue *)

(** ** An attempt at axiomatizing an inductive-inductive definition with an induction principle. *)
Section IndIndAxiomaticHack.
Axiom Node : Set.
Axiom validNode : hpred Node.
Axiom deltaNode : hrel Node.
Axiom mkNode : nat -> option (ref{Node|validNode}[deltaNode,deltaNode]) -> Node.
Axiom Node_rect : forall (P:Node->Type), (forall n o, P (mkNode n o)) -> forall nd, P nd. 
Inductive validNode' : hpred Node :=
  | nil_next : forall n h, validNode' (mkNode n None) h
  | nil_reach : forall n h tl, validNode' (h[tl]) h ->
                               validNode' (mkNode n (Some tl)) h
with deltaNode' : hrel Node :=
  | node_nil_refl : forall n h h',
                  deltaNode' (mkNode n None) (mkNode n None) h h'
  | node_tl_refl : forall n h h' tl,
                   deltaNode' (h[tl]) (h'[tl]) h h' ->
                   deltaNode' (mkNode n (Some tl)) (mkNode n (Some tl)) h h'
  | node_append : forall n n' tl h h',
                    (* Do I need this? h[tl]=(mkNode Node validNode R n' None) -> *)
                    h'[tl]=(mkNode n' None) ->
                    deltaNode' (mkNode n None)
                              (mkNode n (Some tl))
                              h h'.
Axiom validity : validNode ≡p validNode'.
Axiom delta_eq : deltaNode ⊆⊇ deltaNode'.
Inductive msq_reach : forall {T:Set}{P R G} (p:ref{T|P}[R,G]) (a:Node), Prop :=
  | msq_reach_tail : forall p n, msq_reach p (mkNode n (Some p)).
(* This instance must be defined this way rather than as a naive match on the node
   to avoid eliminating a large data type (the inductive-inductive-hacked Node)
   into Type *)
Global Instance nd_reach : ImmediateReachability Node := {
  imm_reachable_from_in := fun T P R G p a => msq_reach p a}.

(** Still need one injectivity axiom to work around the impredicative set stuff... but this axiomatization
    actually should make the -impredicative-set flag unnecessary.  Might be worth converting the whole framework, though. *)
Axiom node_inj : forall n n' t t', mkNode n t = mkNode n' t' -> n=n' /\ t=t'.
Lemma stable_node' : stable validNode' deltaNode'.
  compute; intros.
  induction H0; eauto; try constructor.
      apply IHdeltaNode'. inversion H; subst. assert (Htmp := node_inj _ _ _ _ H2). destruct Htmp. inversion H3.
                                              assert (Htmp := node_inj _ _ _ _ H1). destruct Htmp. inversion H4; subst. assumption.
      rewrite H0. constructor.
Qed.
Hint Resolve stable_node'.

Definition clean_node_ptr : ref{Node|validNode}[deltaNode,deltaNode] -> ref{Node|validNode'}[deltaNode',deltaNode'].
  intros.
  assert (H1 := validity). assert (H2 := delta_eq).
  compute in *. destruct H2.
  eapply convert; eauto. intros; firstorder.
Defined.
Definition noderef := ref{Node|validNode}[deltaNode,deltaNode].
  
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
                    h[hd]=(mkNode n (Some rest)) ->
                    δmsq (mkMSQ hd) (mkMSQ rest) h h'.
Definition msq := ref{MSQ|vMSQ}[δmsq,δmsq].
Inductive q_reachability : forall {T:Set}{P R G} (p:ref{T|P}[R,G]) (q:MSQ), Prop :=
  | q_r : forall n, q_reachability n (mkMSQ n).
Instance q_reach : ImmediateReachability MSQ :=
  { imm_reachable_from_in := @q_reachability }.

Lemma MSQ_stability : stable vMSQ δmsq.
Proof.
  compute; intros; eauto.
Qed.
Hint Resolve MSQ_stability.
Check @contains.
Inductive nd_contains : hrel Node -> Prop :=
  | nd_cont : forall RR n tl,
                @contains noderef _ (fun c c' h h' => RR (mkNode n (Some tl))
                                              (mkNode n (Some tl))
                                              h h') ->
              nd_contains RR.
Instance nd_containment : Containment Node := { contains := nd_contains }.
Inductive msq_contains : hrel MSQ -> Prop :=
  | msq_cont : forall RR tl,
                contains (fun c c' h h' => RR (mkMSQ tl) (mkMSQ tl) h h') ->
              msq_contains RR.
Instance msq_containment : Containment MSQ := { contains := msq_contains }.
Instance nd_fold : rel_fold Node.
  (* TODO: Again, need a workaround for the ind-ind hack + constructor typing args. *)
Print rel_fold.
  eapply Build_rel_fold. intros. exact H.
Defined.
Instance msq_fold : rel_fold MSQ.
  (* TODO: Again, need a workaround for the ind-ind hack + constructor typing args. *)
  eapply Build_rel_fold. intros. exact H.
Defined.

Lemma precise_valid_node : precise_pred validNode'.
  compute. intros; intuition; eauto. induction H; constructor.
  rewrite <- H0; try solve[repeat constructor]. 
  eapply IHvalidNode'. intros.
  Require Import Coq.Program.Equality.
  dependent induction H1.
    (* This case is a messy contradiction, induction tried to use the reflexively reachable case for things w/ wrong types *) admit.
    eapply H0. eapply trans_reachable with (i := tl). constructor. eapply directly_reachable. assumption.
    eapply H0. clear IHreachable_from_in. eapply trans_reachable with (i := tl). constructor. eapply trans_reachable with (i := i); eauto.
Qed.
Hint Resolve precise_valid_node.

Lemma precise_delta_node : precise_rel deltaNode'.
  compute; intros; intuition; eauto. induction H1; try constructor.

  rewrite <- H. rewrite <- H0. apply IHdeltaNode'.
  intros. apply H. eapply trans_reachable with (i := tl). constructor. assumption.
  intros. apply H0. eapply trans_reachable with (i := tl). constructor. assumption.
  constructor. constructor. constructor. constructor.

  eapply node_append.
  rewrite <- H0. eauto.
  constructor. constructor.
Qed.
Hint Resolve precise_delta_node.
Lemma precise_valid_node2 : precise_pred validNode.
Proof. compute. assert (Htmp := validity). compute in Htmp.
       assert (forall x h, validNode x h -> validNode' x h). intros; edestruct Htmp; eauto.
       assert (forall x h, validNode' x h -> validNode x h). intros; edestruct Htmp; eauto.
       intros.
       apply H0. eapply precise_valid_node; eauto.
Qed.
Lemma precise_delta_node2 : precise_rel deltaNode.
Proof. compute. assert (Htmp := delta_eq). destruct Htmp. compute in *.
       intros. apply H0. eapply precise_delta_node; eauto.
Qed.
Hint Resolve precise_valid_node2 precise_delta_node2.
Lemma delta_refl : hreflexive deltaNode.
Proof. compute. intros. destruct delta_eq. apply H0.
       (* TODO: This may actually be false at the moment; need to fix this *)
Admitted.
Hint Resolve delta_refl.

Lemma precise_δmsq : precise_rel δmsq.
  compute; intros. induction H1; eauto; try constructor.
  eapply msq_dequeue. rewrite <- H. apply H1. constructor. constructor.
Qed.
Lemma precise_vMSQ : precise_pred vMSQ.
  compute; intros. auto.
Qed.
Hint Resolve precise_δmsq precise_vMSQ.
Local Obligation Tactic := intros; intuition; eauto; try repeat constructor.

Lemma stability : stable validNode deltaNode.
Proof. red. intros. destruct (validity x' h'). destruct delta_eq; compute in *.
       apply H2.
       eapply stable_node'; eauto.
       destruct (validity x h). firstorder.
Qed.
Hint Resolve stability.

Program Definition alloc_msq {Γ} (_:unit) : rgref Γ msq Γ :=
  sentinel <- Alloc (mkNode 0 None);
  Alloc (mkMSQ sentinel).
Next Obligation. destruct (validity (mkNode 0 None) h). apply H1; constructor. Qed.

Program Definition dq_msq {Γ} (q:msq) : rgref Γ (option nat) Γ :=
  RGFix _ _ (fun rec q =>
    match !q with
    | mkMSQ sent =>
      Node_rect (fun _ => _) (fun x o => match o return (!sent=mkNode x o) -> rgref Γ (option nat) Γ with
                                         | None => fun _ => rgret None
                                         | Some hd => fun _ =>
                                               Node_rect (fun _ => _) (fun n tl => success <- CAS(q,mkMSQ sent,mkMSQ hd);
                                                                                   if success then rgret (Some n) else rec q) (!hd)
                                         end eq_refl) (!sent)
    end) q.
Next Obligation. (* δmsq guarantee proof *)
  apply msq_dequeue with (n := x). (* TODO: Follows from appropriate !x=h[x] assumption... *) admit.
Qed.
Next Obligation. subst. (* TODO: Need to fix up induction principle for this to work right. *) admit.
Qed.
(* TODO: PROBLEM: folding the δmsq restriction through the list when finding the tail to enqueue means δmsq must account for enqueues.
   Currently it doesn't. *)


End IndIndAxiomaticHack.

(** Unless we introduce lots of indirections through references to options,
    we're stuck adapting Capretta's impredicative induction-recursion
    encoding to support mutual inductive types indexing each other. *)
Inductive Node : Set :=
  | mkNode : forall (TAIL:Set) (TP:hpred TAIL) (TRel:hrel TAIL),
               nat -> option (ref{TAIL|TP}[TRel,TRel]) -> Node.
(* Workarounds for the elimination consequences of the impredicative encoding of induction-induction.
   Technically unsound. *)
Axiom nd_inj1 : forall C D P P' R R' n n' tl tl', mkNode C P R n tl = mkNode D P' R' n' tl' -> C = D.
Axiom nd_inj2 : forall C P P' R R' n n' tl tl', mkNode C P R n tl = mkNode C P' R' n' tl' -> P = P' /\ R = R'.
Axiom nd_inj3 : forall C P R n n' tl tl', mkNode C P R n tl = mkNode C P R n' tl' -> n = n' /\ tl = tl'.

Inductive validNode : hpred (Node) :=
  | nil_next : forall (TAIL:Set) (TP:hpred TAIL) (TRel:hrel TAIL) n h,
                 validNode (mkNode TAIL TP TRel n None) h
  | nil_reach : forall (TP:hpred Node) (TRel:hrel Node) n h tl,
                  validNode (h[tl]) h ->
                  validNode (mkNode Node TP TRel n (Some tl)) h.
Inductive deltaNode : hrel Node :=
  | node_nil_refl : forall n R h h',
                  deltaNode (mkNode Node validNode R n None) (mkNode Node validNode R n None) h h'
  | node_tl_refl : forall n R h h' tl,
                   deltaNode (h[tl]) (h'[tl]) h h' ->
                   deltaNode (mkNode Node validNode R n (Some tl)) (mkNode Node validNode R n (Some tl)) h h'
  | node_append : forall n n' R tl h h',
                    (* Do I need this? h[tl]=(mkNode Node validNode R n' None) -> *)
                    h'[tl]=(mkNode Node validNode R n' None) ->
                    deltaNode (mkNode Node validNode R n None)
                              (mkNode Node validNode R n (Some tl))
                              h h'.
Print ImmediateReachability.
Inductive msq_reach : forall {T:Set}{P R G} (p:ref{T|P}[R,G]) (a:Node), Prop :=
  | msq_reach_tail : forall T P R p n, msq_reach p (mkNode T P R n (Some p)).
(* This instance must be defined this way rather than as a naive match on the node
   to avoid eliminating a large data type (the inductive-inductive-hacked Node)
   into Type *)
Global Instance nd_reach : ImmediateReachability Node := {
  imm_reachable_from_in := fun T P R G p a => msq_reach p a}.

Definition noderef := ref{Node|validNode}[deltaNode,deltaNode].

Lemma msq_stability : stable validNode deltaNode.
Proof.
  compute. intros.

  induction H0; eauto; try constructor.
  apply IHdeltaNode. inversion H; subst.
  (* [sigh] impossible case not discharged b/c of impred-set... these assumptions come from the case where next is None,
     but we already know it's Some... *) admit.
      assert (Htmp := nd_inj2 _ _ _ _ _ _ _ _ _ H2). destruct Htmp. subst.
      assert (Htmp := nd_inj3 Node validNode R _ _ _ _ H2). destruct Htmp. subst. inversion H4; subst. assumption.
  rewrite H0. constructor.
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
Inductive q_reachability : forall {T:Set}{P R G} (p:ref{T|P}[R,G]) (q:MSQ), Prop :=
  | q_r : forall n, q_reachability n (mkMSQ n).
Instance q_reach : ImmediateReachability MSQ :=
  { imm_reachable_from_in := @q_reachability }.

Lemma MSQ_stability : stable vMSQ δmsq.
Proof.
  compute; intros; eauto.
Qed.
Hint Resolve MSQ_stability.

Inductive nd_contains : hrel Node -> Prop :=
  | nd_cont : forall RR (C:Set){CC:Containment C} P R n tl,
                contains (fun c c' h h' => RR (mkNode C P R n (Some tl))
                                              (mkNode C P R n (Some tl))
                                              h h') ->
              nd_contains RR.
Instance nd_containment : Containment Node := { contains := nd_contains }.
Inductive msq_contains : hrel MSQ -> Prop :=
  | msq_cont : forall RR tl,
                contains (fun c c' h h' => RR (mkMSQ tl) (mkMSQ tl) h h') ->
              msq_contains RR.
Instance msq_containment : Containment MSQ := { contains := msq_contains }.
Instance nd_fold : rel_fold Node.
  (* TODO: Again, need a workaround for the ind-ind hack + constructor typing args. *)
Print rel_fold.
  eapply Build_rel_fold. intros. exact H.
Defined.
Instance msq_fold : rel_fold MSQ.
  (* TODO: Again, need a workaround for the ind-ind hack + constructor typing args. *)
  eapply Build_rel_fold. intros. exact H.
Defined.


Lemma precise_valid_node : precise_pred validNode.
  compute. intros; intuition; eauto. induction H; constructor.
  rewrite <- H0; try solve[repeat constructor]. 
  eapply IHvalidNode. intros.
  Require Import Coq.Program.Equality.
  dependent induction H1.
    (* This case is a messy contradiction, induction tried to use the reflexively reachable case for things w/ wrong types *) admit.
    eapply H0. Print reachable_from_in. eapply trans_reachable with (i := tl). constructor. eapply directly_reachable. assumption.
    eapply H0. clear IHreachable_from_in. eapply trans_reachable with (i := tl). constructor. eapply trans_reachable with (i := i); eauto.
Qed.
Hint Resolve precise_valid_node.

Lemma precise_delta_node : precise_rel deltaNode.
  compute; intros; intuition; eauto. induction H1; try constructor.

  rewrite <- H. rewrite <- H0. apply IHdeltaNode.
  intros. apply H. eapply trans_reachable with (i := tl). constructor. assumption.
  intros. apply H0. eapply trans_reachable with (i := tl). constructor. assumption.
  constructor. constructor. constructor. constructor.

  eapply node_append.
  rewrite <- H0. eauto.
  constructor. constructor.
Qed.
Hint Resolve precise_delta_node.

Lemma precise_δmsq : precise_rel δmsq.
  compute; intros. induction H1; eauto; try constructor.
  eapply msq_dequeue. rewrite <- H. apply H1. constructor. constructor.
Qed.
Lemma precise_vMSQ : precise_pred vMSQ.
  compute; intros. auto.
Qed.
Hint Resolve precise_δmsq precise_vMSQ.

Local Obligation Tactic := intros; intuition; eauto; try repeat constructor.

Program Definition alloc_msq {Γ} (_:unit) : rgref Γ msq Γ :=
  sentinel <- Alloc (mkNode Node validNode deltaNode 0 None);
  (*sentinel <- alloc _ _ _  (mkNode Node validNode deltaNode 0 None) _ _ _ _ _;*)
  Alloc (mkMSQ sentinel).

(* The CAS is going to hit large elimination issues.... 
Program Definition dq_msq {Γ} (q:msq) : rgref Γ (option nat) Γ :=
  RGFix _ _ (fun rec q =>
    match !q with
    | mkMSQ q =>
    match !q with
    | mkNode _ _ _ _ None => rgret None
    | mkNode _ _ _ _ (Some hd) =>
                 match !hd with
                 | mkNode _ _ _ n tl => success <- CAS(q,mkMSQ hd,tl);
                                        if success then rgret (Some n) else rec q
                 end
    end
    end).
*)
