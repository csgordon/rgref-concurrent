Require Import RGref.DSL.DSL.
Require Import RGref.DSL.Concurrency.

(** * A Tail-less Michael-Scott Queue *)

(** ** Axiomatized inductive-inductive definition with an induction principle. *)
Axiom Node : Set.
Axiom validNode : hpred Node.
Axiom deltaNode : hrel Node.
Axiom mkNode : nat -> option (ref{Node|validNode}[deltaNode,deltaNode]) -> Node.
Axiom Node_rect : forall (P:Node->Type), (forall n o, P (mkNode n o)) -> forall nd, P nd. 
Definition Node_rec {T:Set} := Node_rect (fun _ => T).
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
Axiom destruct_node : forall nd, exists n, exists tl, nd = mkNode n tl. (* destruction principle *)
Axiom compute_node_rect : forall T B x tl, Node_rect T B (mkNode x tl) = B x tl. (* fake computation *)


(** ** General properties of node definitions *)
Inductive msq_reach : forall {T:Set}{P R G} (p:ref{T|P}[R,G]) (a:Node), Prop :=
  | msq_reach_tail : forall p n, msq_reach p (mkNode n (Some p)).
(* This instance must be defined this way rather than as a naive match on the node
   to avoid eliminating a large data type (the inductive-inductive-hacked Node)
   into Type
  TODO: Simplify now that we're not using -impredicative-set *)
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

(*Definition clean_node_ptr : ref{Node|validNode}[deltaNode,deltaNode] -> ref{Node|validNode'}[deltaNode',deltaNode'].
  intros.
  assert (H1 := validity). assert (H2 := delta_eq).
  compute in *. destruct H2.
  eapply convert; eauto. intros; firstorder.
Defined.*)
Definition noderef := ref{Node|validNode}[deltaNode,deltaNode].
  
(** ** A queue base, for head (and eventually tail) pointer(s).
    We're following The Art of Multiprocessor Programming, S10.5, but
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
      Node_rect (fun _ => _)
                (fun x o => match o return (!sent=mkNode x o) -> rgref Γ (option nat) Γ with
                           | None => fun _ => rgret None
                           | Some hd => fun _ =>
                                 Node_rect (fun _ => _)
                                           (fun n tl => success <- CAS(q,mkMSQ sent,mkMSQ hd);
                                                       if success then rgret (Some n) else rec q) (!hd)
                           end _) (!sent)
    end) q.
Next Obligation. (* δmsq guarantee proof *)
  apply msq_dequeue with (n := x). (* TODO: Follows from appropriate !x=h[x] assumption... *) admit.
Qed.
Next Obligation. subst. (* TODO: Need to fix up induction principle for this to work right. *) admit.
Qed.
(* TODO: PROBLEM: folding the δmsq restriction through the list when finding the tail to enqueue means δmsq must account for enqueues.
   Currently it doesn't. *)

Require Import RGref.DSL.Fields.

Inductive NFields : Set := val | next.
Instance nfields : FieldTyping Node NFields.
Instance nfield_val : FieldType Node NFields val nat := {
    (*getF := fun v => match v with (mkNode x tl) => x end;*)
    getF := Node_rec (fun x tl => x);
    (*setF := fun v fv => match v with (mkNode x tl) => mkNode fv tl end*)
    setF := fun n v => Node_rec (fun x tl => mkNode v tl) n
}.
Instance nfield_next : FieldType Node NFields next (option (ref{Node|validNode}[deltaNode,deltaNode])) := {
    getF := Node_rec (fun x tl => tl);
    setF := fun v fv => Node_rec (fun x tl => mkNode x fv) v
}.

(* TODO: fCAS and CAS need to enforce Safe on the expressions *)
Local Obligation Tactic := intros; eauto with typeclass_instances; repeat constructor; compute; eauto.
Program Definition nq_msq {Γ} (q:msq) (n:nat) : rgref Γ unit Γ :=
  RGFix _ unit (fun loop tl =>
                  best_tl <- (RGFix _ _ (fun chase tl => match (tl ~> next) with None => rgret tl | Some tl' => chase tl' end) tl) ;
                  _ <- (LinAlloc[VZero] (mkNode n None) ) ;
                  (* Really need a refining fCAS, which returns either a success indicator or
                     a refinement of the r:ref{A|P}[R,G] with refinement P' such that
                     P∧<CAS failed>⇒ P' and stable P' R. *)
                  (*success <- fCAS( best_tl → next , None, Some _ ) ;*)
                  success <- share_field_CAS( best_tl → next , None, (fun tl => Some tl) , VZero , TFirst VZero _ _) ;
                  (* If the CAS failed, next is not None, but there isn't a great way to extract the Some arg *)
                  if success then rgret tt else loop (best_tl ~> next)
               )
        (match !q with mkMSQ sentinel => sentinel end).
Next Obligation. intros; subst. destruct H0. subst. destruct (validity (mkNode n None) h). apply H2. constructor. Qed.
Next Obligation. intros; exfalso; assumption. Qed.
Next Obligation. (* deltaNode *)
  intros. destruct delta_eq. apply H4.
  destruct (destruct_node v) as [n' [tl' H']]. rewrite H' in *. clear H'.
  simpl in H1. compute in H1.
  rewrite compute_node_rect in *.
  subst tl'.
  destruct H2.
  eapply node_append.
  (* TODO: Need to prove the null-ness is preserved... which is only true if ¬(s≡best_tl)... 
     Could add some assumptions to share_field_CAS guarantee obligation that transfer 
     non-pointer-equivalence based on incompatible rely/guarantee to the result, e.g.:
         ∀ P R G (x:ref{aT|P}[R,G]), ¬(G⊆aR)∨¬(aG⊆R) → ¬(s≡x)
     since if a reference could not have aliased the linear value, it cannot alias the (equivalent)
     weakened conversion result.
  *)
  assert (forall P R G (x:ref{Node|P}[R,G]), not (G⊆empty) \/ (not (havoc⊆R)) -> not (s≡x)) by admit.
  assert (~ (s ≡ best_tl)). apply H5. left. compute. intros. apply (H6 (mkNode 3 None) (mkNode 3 None) h h). 
  apply H4. constructor.
  rewrite non_ptr_eq_based_nonaliasing; eauto.
Qed.  
Next Obligation. (* a Set.... probably from field read folding... *) 
  exact (rgfold deltaNode deltaNode). Defined.
