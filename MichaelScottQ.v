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
Definition Node_ind (T:Node->Prop) := Node_rect T.
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

(* TODO: Figure out how to justify this with general principles.  It's sound here b/c we know
   it's acyclic, but there should be an underlying general principle... Could just say it's true for
   any recursive option member, for any T, works for [option ref{T...}]... No, that doesn't
   prohibit cycles in the heap... This is actually reliant on a well-founded reachability
   through the heap, which we know is true in this case.  *)
Axiom Node_heap_rect : forall h (P:Node->Type), (forall n, P (mkNode n None)) ->
                                                     (forall n r, P (h[r]) -> P (mkNode n (Some r))) ->
                                                     forall n, P n.
(** ** Field map for the M&S Queue *)
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

(** Folding is identity for both, since all inner pointers are already at least
    as restrictive as outer pointers *)
Instance nd_fold : readable_at Node deltaNode deltaNode := id_fold.
Instance msq_fold : readable_at MSQ δmsq δmsq := id_fold.

Lemma precise_valid_node : precise_pred validNode'.
  compute. intros; intuition; eauto. induction H; constructor.
  rewrite <- H0; try solve[repeat constructor]. 
  eapply IHvalidNode'. intros.
  Require Import Coq.Program.Equality.
  dependent induction H1.
    (** Messy contradiction; dep. induction tried to use the reflexive reachability
        for things w/ wrong types.  I suspect this would be a non-issue if
        I could properly define Node with its predicates and relations as an
        inductive-inductive datatype, as dependent induction doesn't typically
        generate these kinds of obligations. *)
    assert (ref{T|P'}[R',G'] = Node -> False) by admit. (*OK*) exfalso. firstorder.
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
Proof. compute. intros. destruct delta_eq. apply H0. clear H; clear H0.
       eapply (Node_heap_rect h (fun x => deltaNode' x x h h)); constructor; auto.
Qed.
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

(** *** Allocation *)
Program Definition alloc_msq {Γ} (_:unit) : rgref Γ msq Γ :=
  sentinel <- Alloc (mkNode 0 None);
  Alloc (mkMSQ sentinel).
Next Obligation. destruct (validity (mkNode 0 None) h). apply H1; constructor. Qed.

(** *** Dequeue operation *)
Program Definition dq_msq {Γ} (q:msq) : rgref Γ (option nat) Γ :=
  RGFix _ _ (fun rec q =>
    match !q with
    | mkMSQ sent =>
      observe-field sent --> val as x, pf in (fun a h => @eq nat (getF a) x);
      observe-field sent --> next as o, pf' 
          in (fun a h => match o with
                         | None => True 
                         | Some hd => @eq (option _) (getF a) (Some hd) end);
      match o with
      | None => rgret None
      | Some hd => 
            n <- rgret (hd ~> val);
            success <- CAS(q,mkMSQ sent,mkMSQ hd);
            if success then rgret (Some n) else rec q
      end
    end) q.
Next Obligation. (** stable refinement *)
  simpl. red. intuition. subst.
  destruct delta_eq. assert (H' := H _ _ _ _ H0).
  induction H'; eauto. unfold Node_rec. repeat rewrite compute_node_rect.
  reflexivity.
Qed.
Next Obligation. (* tail refinement true *)
  unfold dq_msq_obligation_6 in *. 
  subst program_branch_0.
  subst program_branch_1.
  Check @getF.
  assert (opt_ind : forall T (o:option T), {o = None} + {exists t, o = Some t}).
      intros. induction o; intuition. right. eexists; eauto.

  induction (opt_ind _ (getF (T:=Node) (@asB Node _ _ Node nd_fold eq_refl (@dofold _ _ _ nd_fold b)))).
  Set Printing Implicit. idtac.
  unfold res in *. unfold nd_fold at 2 in a. unfold id_fold in *.
  rewrite a.
  Unset Printing Implicit. idtac.
  tauto.
  destruct b0. 
  Set Printing Implicit. idtac.
  unfold res in *. unfold nd_fold at 2 in H. unfold id_fold in *.
  rewrite H.
  compute in *. rewrite H. reflexivity.
Qed.
Next Obligation. (* tail obs stability *)
  red. intros.
  destruct delta_eq.
  assert ( Htp := H1 _ _ _ _ H0).
  induction t; auto.
  induction Htp; eauto.
  simpl in H. compute in H. rewrite compute_node_rect in *.
  inversion H.
Qed.
Next Obligation. (** δmsq guarantee proof *)
  apply msq_dequeue with (n := x). subst o.
  assert (node_inj : forall nd, nd = mkNode (getF nd) (getF nd)).
      intros. simpl. unfold Node_rec. 
      assert (H' := destruct_node nd). 
      destruct H'. destruct H0. rewrite H0.
      repeat rewrite compute_node_rect.
      reflexivity.
  rewrite (node_inj (h[sent])).
  rewrite pf. rewrite pf'.
  reflexivity.
Qed.

(** ** M&S Queue Operations *)
(** TODO: fCAS and CAS need to enforce Safe on the expressions *)
Local Obligation Tactic := intros; eauto with typeclass_instances; repeat constructor; compute; eauto.
(** *** Enqueue operation *)
Program Definition nq_msq {Γ} (q:msq) (n:nat) : rgref Γ unit Γ :=
  RGFix _ unit (fun loop tl =>
                  best_tl <- (RGFix _ _ (fun chase tl => match (tl ~> next) with None => rgret tl | Some tl' => chase tl' end) tl) ;
                  _ <- (LinAlloc[VZero] (mkNode n None) ) ;
                  (* Really need a refining fCAS, which returns either a success indicator or
                     a refinement of the r:ref{A|P}[R,G] with refinement P' such that
                     P∧<CAS failed>⇒ P' and stable P' R. *)
                  (*success <- fCAS( best_tl → next , None, Some _ ) ;*)
                  success <- share_field_CAS'( best_tl → next , None, (fun tl => Some tl) , VZero , TFirst VZero _ _ , best_tl) ;
                  (* If the CAS failed, next is not None, but there isn't a great way to extract the Some arg *)
                  if success then rgret tt else loop (best_tl ~> next)
               )
        (match !q with mkMSQ sentinel => sentinel end).
Next Obligation.  intros; congruence. Qed.
Next Obligation. intros; subst. destruct H0. subst. destruct (validity (mkNode n None) h). apply H2. constructor. Qed.
Next Obligation. 
  (* This goal comes from the lin_convert use, trying to prove local_imm ⊆ deltaNode,
     but this isn't quite true.  Readable from refimmut would do the trick, though,
     except readable doesn't contain the recursive pointers of a full option field.
     Really, we're in a case where given the refinement (x=e) the implication is
     true. *)
  destruct H0. subst a. compute in H1. subst a'. 
  destruct delta_eq.
  apply H1. constructor.
Qed.
Next Obligation. (* deltaNode *)
  intros. destruct delta_eq. apply H5.
  destruct (destruct_node v) as [n' [tl' H']]. rewrite H' in *. clear H'.
  simpl in H1. compute in H1.
  rewrite compute_node_rect in *.
  subst tl'.
  destruct H2.
  eapply node_append.
  (**  Need to prove the null-ness is preserved... which is only true if ¬(s≡best_tl). *)
  assert (~ (s ≡ best_tl)). apply H3. left. compute. intros. 
      assert (mkNode 3 None = mkNode 3 (Some s)).
          eapply H6. apply H5. eapply node_append; eauto.
      assert (Hbad := node_inj _ _ _ _ H7).
      destruct Hbad. inversion H9.
  rewrite non_ptr_eq_based_nonaliasing; eauto.
  Grab Existential Variables.
  exact h.
Qed.  
Next Obligation. (* a Set.... probably from field read folding... *) 
  exact (res (T := Node)).
Defined.
