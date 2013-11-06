Require Import RGref.DSL.DSL.
Require Import RGref.DSL.Concurrency.
Require Import RGref.DSL.Fields.
Require Import FinResults.
Require Import Utf8.

(** * Lock-Free Linearizable Union-Find
    We're following Anderson and Woll's STOC'91 paper 
    "Wait-free Parallel Algorithms for the Union Find Problem."
*)
(** ** Basic structures, field maps *)
Inductive cell (n:nat) : Set :=
  | mkCell : nat -> Fin.t n -> cell n.
Instance ir_cell {n:nat} : ImmediateReachability (cell n) :=
  { imm_reachable_from_in := fun T P R G r x => False }.
Instance foldcell {n:nat} : rel_fold (cell n) :=
  { rgfold := fun _ _ => cell n;
    fold := fun _ _ x => x }.
Instance containcell {n:nat} : Containment (cell n) :=
  { contains := fun _ => True }.
Definition uf (n:nat) := Array n (ref{cell n|any}[local_imm,local_imm]).
Inductive F : Set := rank | parent.
Instance fielding {n:nat} : FieldTyping (cell n) F.
Instance cell_rank {n:nat} : FieldType (cell n) F rank nat :=
  { getF := fun x => match x with mkCell r p => r end;
    setF := fun x v => match x with mkCell r p => mkCell _ v p end }.
Instance cell_parent {n:nat} : FieldType (cell n) F parent (Fin.t n) :=
  { getF := fun x => match x with mkCell r p => p end;
    setF := fun x v => match x with mkCell r p => mkCell _ r v end }.
  
(** ** Useful predicates and properties of the union-find array structure *)
Inductive terminating_ascent (n:nat) (x:uf n) (h:heap) (i:Fin.t n) : Prop :=
  | self_ascent : (getF (h[x <| i |>])) = i ->
                  terminating_ascent n x h i
  | trans_ascent : forall t,
                     t = (getF (h[x <| i |>])) ->
                     (getF (h[x <| i |>])) ≤ (getF (h[x <| t |>])) ->
                     terminating_ascent n x h t ->
                     terminating_ascent n x h i.

Inductive chase (n:nat) (x:uf n) (h:heap) (i : Fin.t n) : Fin.t n -> Prop :=
  | self_chase : (*(getF (h[x<|i|>])) = i ->*)
                 chase n x h i i
  | trans_chase : forall t f,
                    chase n x h t f ->
                    (getF (h[x<|i|>])) = t ->
                    chase n x h i f
.

Inductive φ (n:nat) : hpred (uf n) :=
  pfφ : forall x h,
          (forall i, terminating_ascent n x h i) ->
          φ n x h.

(** ** Change relations and meta properties. *)
Inductive δ (n:nat) : hrel (uf n) :=
  | path_compression : forall x f c h h' (rt:Fin.t n),
                         φ n x h ->
                         (*root n x h f rt ->
                         root n x h (getF (h[c])) rt ->*)
                         (* The chase assumption means we're not permuting reachability,
                            which means we're not introducing a cycle. It also implies the
                            increasing rank. *)
                         @eq nat (getF (h[x <| f |>])) (getF (h[c])) -> (* preserve rank *)
                         chase n x h f (getF (h[c])) ->
                         δ n x (array_write x f c) h h'
  (** Union sets the parent and rank of a self-parent *)
  | path_union : forall A x xr c h h' y xr' yr,
                   h[(array_read A x)] = mkCell n xr x ->
                   h[c] = mkCell n xr' y ->
                   xr ≤ xr' ->
                   (*h[(array_read A y)] = mkCell n yr y -> ; TOO STRONG: y may not be root by the time we hit the CAS *)
                   getF (h[(array_read A y)]) = yr ->
                   (* Update according to paper's x ≺ y ; point lower-rank to higher rank, or break tie with index order *)
                   xr' < yr \/ (xr'=yr /\ (proj1_sig (to_nat x) < proj1_sig (to_nat y))) ->
                   δ n A (array_write A x c) h h'
  (** Sometimes union just attempts to bump the rank of a root node; using ≤ also gives easy reflexivity. *)
  | bump_rank : forall A x xr xr' h h' c,
                  h[array_read A x] = mkCell n xr x ->
                  xr ≤ xr' ->
                  h[c] = mkCell n xr' x ->
                  δ n A (array_write A x c) h h'
.

Lemma chase_rank' : forall n h x i j t,
                      terminating_ascent n x h i ->
                      getF (h[x<|i|>]) = t ->
                      chase n x h t j ->
                      getF (h[x <| i |>]) ≤ getF (h[x <| j |>]).
Proof.
  intros.
  Require Import Coq.Program.Equality.
  
  generalize dependent i.
  dependent induction H1; intros.
      dependent induction H. rewrite H in H0. subst i0. auto.
                             unfold fin in *.
                             assert (t=i) by congruence. rewrite <- H3 in *. assumption.
      dependent induction H0. 
          assert (i=i0) by congruence. subst i0.
          assert (i=t) by congruence. subst t. rewrite H0 in H1.
          apply IHchase; eauto. apply self_ascent; eauto.
          unfold fin in *.
          assert (i=t0) by congruence. rewrite <- H5 in *.
      etransitivity; try eassumption.
      apply IHchase; eauto.
Qed.

Lemma trans_chase' : forall n x h f i j, j=getF(h[x<|i|>]) -> chase n x h f i -> chase n x h f j.
Proof.
  intros.
  induction H0. eapply trans_chase; eauto. rewrite <- H. constructor.
  eapply trans_chase. apply IHchase. assumption. assumption.
Qed.

Lemma Hself_ref : forall n x h,
                  (forall i, terminating_ascent n x h i) ->
                  forall i0 i1, getF (h [x <| i0 |>]) = i1 -> getF (h [x <| i1 |>]) = i0 ->
                      i1 = i0.
  intros n x h H.
    intros A.
    induction (H A).
        intros. unfold fin in *. congruence.
        intros. unfold fin in *.
          assert (i1=t) by congruence. rewrite H4 in *.
          symmetry. apply IHt; eauto.
Qed.
Lemma Hdouble : forall n x h,
                  (forall i, terminating_ascent n x h i) ->
                  forall X Z, chase n x h X Z -> chase n x h Z X -> X = Z.
Proof.
  intros n x h H.
  intro X. induction (H X); intros.
               induction H1; induction H2; auto.
               assert (f=t) by congruence. rewrite <- H5 in *. clear dependent t.
               apply IHchase; eauto. eapply trans_chase. eassumption. assumption.
           assert (chase n x h Z t).
               induction H3. eapply trans_chase. constructor. intuition.
                 eapply trans_chase'. eassumption. eapply trans_chase. eassumption. assumption.
           induction H2. reflexivity. 
             unfold fin in *. assert (t = t1) by congruence. rewrite H6 in *. clear dependent t.
             assert (Htmp := IHt _ H2 H4). rewrite Htmp in *.
             symmetry. apply IHt; try eassumption. eapply trans_chase. constructor. assumption.
Qed.
Lemma chase_update_preserves_term_ascent :
  forall h h' n x f i mid c,
    @eq nat (getF (h[x <| f |>])) (getF (h[c])) ->
    (forall i, terminating_ascent n x h i) ->
    chase n x h f mid ->
    getF (h [c]) = mid ->
    terminating_ascent n (array_write x f c) h' i.
Proof.
  intros h h' n x f i mid c Hrank H.
  intros Hc Hf.
  induction (H i).
  (* self *)
  induction (fin_dec _ f i).
      subst i.
      (*Check chase_ind.
      eapply (chase_ind n x)
      with (h := h)
      (P := fun base targ => 
                   terminating_ascent n (array_write x f c) h' f).*)
      inversion Hc.
          apply self_ascent. rewrite read_updated_cell. erewrite immutable_vals; eassumption.
          subst f0. 
              induction (H mid).
                induction (fin_dec _ f i). subst f. apply self_ascent. rewrite read_updated_cell. erewrite immutable_vals; eassumption.
                    apply trans_ascent with (t:=i);
                      try rewrite read_updated_cell;
                      try rewrite read_past_updated_cell; eauto;
                      try rewrite immutable_vals with (h':=h') in *.
                    symmetry; auto.

                    rewrite immutable_vals with (h':=h). rewrite <- Hrank.
                    etransitivity. rewrite immutable_vals with (h':=h). reflexivity.
                    rewrite <- immutable_vals with (h:=h)(h':=h').
                    eapply chase_rank'; eauto.
                    rewrite immutable_vals with (h:=h)(h':=h').
                    rewrite H2. assumption.

                    apply self_ascent. rewrite read_past_updated_cell.
                    erewrite immutable_vals; eassumption. assumption.
                assert (f = i). clear IHt0 t1 H4 H1.
                    induction Hc. auto.
                    assert (i = t). congruence. subst t.
                    assert (i = t1). congruence. subst t1.
                    rewrite H2. apply IHHc; eauto.
                    rewrite <- H2. symmetry; auto.
                    rewrite <- H2. symmetry; auto.
                    rewrite <- H2. symmetry; auto.
                subst f.
                assert (i = t) by congruence. subst t.
                assert (t0 = i). subst t0. rewrite <- H0 at 2. reflexivity. subst t0.
                apply self_ascent. rewrite read_updated_cell. erewrite immutable_vals; eassumption.

      apply self_ascent. rewrite read_past_updated_cell; auto. erewrite immutable_vals; eassumption; auto.
  (* trans *)
  induction (fin_dec _ f i). subst i.
  apply trans_ascent with (t:=mid). rewrite read_updated_cell. 
                                    rewrite immutable_vals with (h':=h).
                                    rewrite <- Hf. reflexivity.
                                    rewrite read_updated_cell.
                                    induction (fin_dec _ f mid).
                                      rewrite <- a. rewrite read_updated_cell. reflexivity.
                                      rewrite read_past_updated_cell; auto.
                                      
                                      repeat rewrite <- immutable_vals with (h:=h)(h':=h').
                                      rewrite <- Hrank.
                                      assert (chase n x h t mid).
                                          clear H1. clear IHt. clear t0.
                                          inversion Hc. contradiction b. 
                                          unfold fin in *. 
                                          subst f0. 
                                          assert (t=t0) by congruence. subst t.
                                          rewrite H2. assumption.
                                      eapply chase_rank'; auto.
                                      rewrite H0 in H2. assumption.


                                    induction (fin_dec _ f mid).
                                      rewrite <- a in *. apply self_ascent. rewrite read_updated_cell. erewrite immutable_vals; eassumption.
                                      assert (chase n x h t mid).
                                          induction Hc. contradiction b. reflexivity.
                                              unfold fin in *. assert (t1=t) by congruence.
                                              rewrite H3 in *.
                                              assumption.
                                      symmetry in H0.
                                      assert (Htp := chase_rank' n h x f mid t (H f) H0 H2).
                                      clear Hf.
                                      induction (H mid). apply self_ascent. rewrite read_past_updated_cell. erewrite immutable_vals; eassumption. assumption.

                                      induction (fin_dec _ f t1).
                                        rewrite <- a in *. clear dependent t1.
                                        (* i->f->t in x, but i->f->(via c)->i in x', which doesn't preserve terminating_ascent,
                                           so there *should* be a contradiction here somewhere!. *)
                                        (* In x, we have:
                                             - H2: chase n x h t i         --- t->...->i
                                             - H3: getF (h[x<|i|>]) = f    --- i->f
                                             - H0: getF (h[x<|f|>]) = t    --- f->t
                                             - H0 w/ H3                    --- i->f->t
                                           so we have t->...->i and i->...->t, both in x, where all indices
                                           have terminating ascents.  The only way for this to be consistent
                                           is for t=f=i... *)
                                        assert (forall i0 i1, getF (h [x <| i0 |>]) = i1 -> getF (h [x <| i1 |>]) = i0 ->
                                                              i1 = i0).
                                            eauto using Hself_ref.
                                        
                                        assert (t=i). eapply Hdouble; eauto.
                                            eapply trans_chase; eauto. unfold fin in *. rewrite <- H3.
                                            eapply trans_chase; eauto. constructor. 
                                        rewrite H6 in *.
                                        assumption.
                                        
                                      apply trans_ascent with (t := t1).
                                        rewrite read_past_updated_cell; auto; erewrite immutable_vals; eassumption.
                                        rewrite read_past_updated_cell; auto.
                                        rewrite immutable_vals with (h' := h).
                                        rewrite read_past_updated_cell; auto.
                                        etransitivity; try eassumption.
                                        erewrite immutable_vals; reflexivity.
                                        apply IHt1; try eassumption.
                                        eapply trans_chase'; eauto.
                                        eapply trans_chase'. apply H3. assumption.
                                        etransitivity; eassumption.
    induction (fin_dec _ f t). 
        apply trans_ascent with (t:=t); try rewrite read_past_updated_cell; auto.
        erewrite immutable_vals. eassumption.
        subst f. rewrite read_updated_cell. 
        
        repeat rewrite <- immutable_vals with (h:=h)(h':=h').
        rewrite <- Hrank. assumption.

    apply trans_ascent with (t:=t); try rewrite read_past_updated_cell; auto.
        erewrite immutable_vals. eassumption.
        rewrite read_past_updated_cell; auto.
        rewrite immutable_vals with (h':=h') in *.
        etransitivity. eassumption.
        rewrite immutable_vals with (h':=h'). reflexivity.
Qed.

Definition imm_vals' : forall h h' T P r, h[r]=h'[r] :=
  fun h h' T P => immutable_vals T P h h'.
Ltac swap h h' := repeat rewrite (imm_vals' h h') in *.
Ltac arrays h h' :=
  swap h h';
  repeat (unfold fin in *;
           match goal with 
           | [ |- context[ array_read (array_write ?A ?x ?y) ?x ] ] =>
               rewrite read_updated_cell
           | [ H : ?x ≠ ?z |- context[ array_read (array_write ?A ?x ?y) ?z ]] =>
               rewrite read_past_updated_cell; auto
           | [ H : ?z ≠ ?x |- context[ array_read (array_write ?A ?x ?y) ?z ]] =>
               rewrite read_past_updated_cell; auto
               end).

Lemma ascend_new_heap : forall n x h h', (forall i, terminating_ascent n x h i) ->
                                         forall i, terminating_ascent n x h' i.
Proof.
  intros.
  induction (H i); arrays h h'.
      apply self_ascent; eauto.
      eapply trans_ascent; eauto.
Qed.


Lemma union_identity : forall n x h f y (c:ref{cell n|any}[local_imm,local_imm]),
                         f≠y -> getF(h[c])=y -> 
                         terminating_ascent n x h y ->
                         forall y', chase n x h y y' -> f≠y' ->
                                    terminating_ascent n (array_write x f c) h y'.
Proof.
  intros n x h f y c. intro. intro. intro.
  
  revert H0.
  induction H1.
  (* self *) intros. induction H2. apply self_ascent; arrays h h'; eauto.
             assert (i = t) by congruence. rewrite H5 in *. firstorder.
  (* trans *)
  intros. 
  induction H4.
Admitted.

Require Import Coq.Arith.Lt.
Lemma stable_φ_δ : forall n, stable (φ n) (δ n).
Proof.
  intros. red. intros.
  induction H0.
  (* Compression *)
      destruct H. constructor. intros.
      eapply chase_update_preserves_term_ascent; eauto.
  (* Union *)
      destruct H. constructor.
      
      cut ( (* Omitting n, x0, H, x *)
                h[x0<|x|>] = mkCell n xr x ->
                h[c]=mkCell n xr' y ->
                xr ≤ xr' ->
                getF (h[x0<|y|>]) = yr ->
                xr ≤ yr ->
                forall i, terminating_ascent n (array_write x0 x c) h' i).
      intros Hgeneralized.
      apply Hgeneralized; eauto.
      etransitivity; eauto. induction H4. eauto with arith. destruct H4. subst xr'. reflexivity.

      intros. 

      (* TODO: It may be worth proving a separate lemma that ascent is preserved for anything reachable from y in the original *)

      induction (H i).
      (* originally self-ascent *)
          induction (fin_dec _ x i).
            subst x. (* remapping the updated cell itself *)
            apply trans_ascent with (t:=y); arrays h h'; try rewrite H6; eauto.
              induction (fin_dec _ y i). subst y; arrays h h'. rewrite H1. reflexivity.
                                         arrays h h'. rewrite H8. simpl.
                                         induction H4. eauto with arith.
                                         destruct H4. subst xr'. reflexivity.
              induction (fin_dec _ y i). subst y; arrays h h'. 
                                         apply self_ascent; arrays h h'. rewrite H6; auto.
                        induction (H y). apply self_ascent; arrays h h'.
                            induction (fin_dec _ i t).
                                         subst i. 
                                         (* i = t should be a contradiction:
                                            i0 -> t, t -> t, and we just made
                                            x0<|t↦c|><|t|> = mkCell xr' i0, tying a cycle. *)
                                         arrays h h'.
                                         rewrite H5 in H12. rewrite H8 in H12. simpl in H12.
                                         induction H4. 
                                         assert (xr < yr). eauto with arith.
                                         assert (xr ≤ yr). eauto with arith.
                                         Require Import Coq.Arith.Le.
                                         assert (xr = yr). eauto using le_antisym.
                                         subst xr. exfalso. eapply lt_irrefl. eassumption.
                                         destruct H4. subst yr.
                                         rewrite <- H4 in H12.
                                         assert (xr = xr'). eauto using le_antisym. subst xr.
                                     apply trans_ascent with (t:=t); arrays h h'.
                                       rewrite H1. rewrite <- H4. reflexivity.
                                     admit.
                             apply trans_ascent with (t:=t); arrays h h'.
                               assert (getF (h'[c]) = i0). rewrite H1. reflexivity.
                               eapply union_identity; try apply H13; eauto.
                               eapply ascend_new_heap; eauto.
                               eapply trans_chase. constructor. subst t. reflexivity.
                               apply self_ascent; arrays h h'; eauto.
    (* originally trans *)
    induction (fin_dec _ x i).
        subst x.
        induction (fin_dec _ y i). subst y.
          apply self_ascent; arrays h h'. rewrite H1. reflexivity.
        
        apply trans_ascent with (t:=y); arrays h h'; eauto. rewrite H1. reflexivity.
        rewrite H1. rewrite H8. simpl. 
        induction H4. eauto with arith. destruct H4; subst xr'; reflexivity.
        eapply union_identity. Focus 2. rewrite H1. reflexivity.
          intuition. simpl. eapply ascend_new_heap; eauto.
          simpl. constructor. intuition.

    apply trans_ascent with (t:=t); arrays h h'; eauto.
        induction (fin_dec _ x t); try subst x; arrays h h'.
        rewrite H1. rewrite H5 in H11. etransitivity; eauto.
(*
      rewrite immutable_vals with (h' := h') in H1.
      
      intros.
      induction (fin_dec n x i). subst x.
      generalize dependent i.
          induction (H y); intros.
              apply trans_ascent with (t := i);
                try rewrite read_updated_cell; eauto;
                try rewrite H1; eauto.
              rewrite read_past_updated_cell. rewrite immutable_vals with (h':= h') in H3.
                rewrite H3. simpl. induction H5. eauto with arith. destruct H5. subst xr'. reflexivity.
          intros Hbad. subst i. (*rewrite H2 in H0.*)
          assert (Hcontra := lt_irrefl). unfold not in Hcontra.
          assert (Hcontra' := le_not_lt). unfold not in Hcontra'.
          rewrite H4 in *. simpl in *. subst yr.
          induction H5. firstorder. destruct H3. firstorder.
              apply self_ascent.
              rewrite read_past_updated_cell. rewrite <- immutable_vals with (h:=h). auto.
          intros Hbad. subst i. (*rewrite H2 in H0.*)
          assert (Hcontra := lt_irrefl). unfold not in Hcontra.
          assert (Hcontra' := le_not_lt). unfold not in Hcontra'.
          rewrite H4 in *. simpl in *. subst yr.
          induction H5. firstorder. destruct H3. firstorder.
*)
      
  (* Rank bump *)
  constructor. intros. destruct H.
  induction (fin_dec n x i).
      subst. apply self_ascent. rewrite read_updated_cell; eauto.
             rewrite <- immutable_vals with (h := h); eauto. rewrite H2. simpl. auto.
  induction (H i).
      apply self_ascent. rewrite read_past_updated_cell; eauto.
                         rewrite <- immutable_vals with (h := h); eauto.
      induction (fin_dec n x t).
          subst x. 
      apply trans_ascent with (t := t);
          try rewrite read_past_updated_cell with (f1 := t) (f2 := i); eauto.
      rewrite <- immutable_vals with (h := h); eauto.
      rewrite read_updated_cell; eauto.
      rewrite <- immutable_vals with (h := h); eauto.
      rewrite H0 in *. rewrite immutable_vals with (h' := h') in H2. rewrite H2.
      unfold getF at 2. unfold cell_rank.
      unfold getF at 2 in H4. unfold cell_rank in H4.
      etransitivity. eassumption. eauto.
      apply self_ascent. rewrite read_updated_cell; eauto. 
          rewrite immutable_vals with (h' := h') in H2.
          rewrite H2. reflexivity.

      apply trans_ascent with (t := t);
          try rewrite read_past_updated_cell with (f1 := x) (f2 := i); eauto.
      rewrite <- immutable_vals with (h := h); eauto.

      rewrite <- immutable_vals with (h := h); eauto.
      rewrite read_past_updated_cell; eauto.
      etransitivity. eassumption. rewrite immutable_vals with (h' := h').
      reflexivity.
Qed.
Hint Resolve stable_φ_δ.

Lemma precise_φ : forall n, precise_pred (φ n).
Proof.
  intros; red; intros.
  induction H; constructor; intros.
  induction (H i).
  constructor. rewrite <- H0; eauto. constructor.
  red in x. compute. eexists; reflexivity.
  eapply trans_ascent. rewrite <- H0; eauto.
  constructor. compute. eexists; reflexivity.
  rewrite <- immutable_vals with (h:=h). etransitivity. eassumption.
  rewrite immutable_vals with (h':=h'). reflexivity. assumption.
Qed.
Lemma precise_chase : forall n i j, precise_pred (fun x h => chase n x h i j).
Proof.  
  intros. red; intros.
  induction H. 
      constructor; intros. (*rewrite immutable_fields with (h' := h). auto.*)
      eapply trans_chase. eassumption.
      rewrite immutable_fields with (h' := h).
      auto.
Qed.
Lemma precise_δ : forall n, precise_rel (δ n).
  intros. red. intros.
  induction H1.
    assert (H' := precise_chase). red in H'.
    assert (Htmp := precise_φ n). red in Htmp.
    eapply path_compression; eauto.
    
    Focus 2. eapply H'. rewrite immutable_vals with (h' := h). eassumption.
    eauto.
    repeat rewrite immutable_vals with (h:=h2) (h' := h). eassumption.

    rewrite H in H1. rewrite (immutable_vals _ _ h h2) in H2. rewrite H in H4.
    eapply path_union; eauto. 
    constructor. repeat red. exists y. compute; reflexivity.
    constructor. repeat red. exists x. compute; reflexivity.
    
    rewrite (immutable_vals  _ _ h h2) in H1.
    rewrite (immutable_vals  _ _ h h2) in H3.
    eapply bump_rank; eauto.
Qed.
    
Hint Resolve precise_φ precise_δ.

(** TODO: δ seems to only be reflexive when applied to arrays satisfying
    φ.  This is intuitively reasonable; if reads of a ref{T|P}[R,G] occur
    where P "implies" G reflexive, then it's fine, as with any P' where
    P' => P.  Maybe readable_at should take a P predicate as well,
    any maybe the reflexivity requirements should be moved to
    readable_at.  Then,
        Class ConditionallyReflexive {T:Set}(P:hpred T)(G:hrel T) :=
        { irefl : forall t h, P t h -> G t t h h }.
        Class Reflexive {T:Set}(G:hrel T) := { r : hreflexive G }.
        Instance RIR {T}{P}`{Reflexive G} : ConditionallyReflexive P G :=
        { irefl := fun t h Pth => r t h }.
        Class readable_at T P R G `{ConditionallyReflexive P G} := <as before>
    And then we'd pretty much require a readable_at wherever a proof
    of hreflexive was required before (pretty much already true).
*)
Lemma refl_δ : forall n, hreflexive (δ (S n)).
Proof.
  (*intros; red; intros.
  rewrite <- (array_id_update x (@F1 _)) at 2 .
  (* TODO: This seems to require knowledge that x is wf *) assert (φ _ x h) by admit.
  inversion H; subst. specialize (H0 (@F1 _)).
  assert (Htmp := ascent_root _ _ _ _ H0). destruct Htmp.
  eapply path_compression; try eassumption.
  induction H1.
  rewrite H1. eapply self_root; eauto.
  rewrite H2. assumption.
  
  eapply trans_chase.
  Focus 2. reflexivity.
  apply self_chase. 
*)
  intros. red. intros.
  rewrite <- (array_id_update x (@F1 _)) at 2.
  Check bump_rank.
  eapply bump_rank with (xr := getF (h[x<|F1|>])) (xr' := getF (h[x<|F1|>])).
  (** TODO: Need a lemma that there exists a root.... but then we need to assume φ again... *)
Admitted. (* refl_δ *)
Hint Resolve refl_δ.
Instance read_uf {n:nat} : readable_at (uf n) (δ n) (δ n) := id_fold.

(** ** Union-Find Operations *)

(** *** Helper property *)
Definition init_cell {n:nat} (i:nat) (pf:i<n) : hpred (cell n) :=
  (fun x h => x = mkCell n 0 (of_nat_lt pf)).
Lemma prec_init : forall n i pf, precise_pred (@init_cell n i pf).
Proof. intros; red; intros. inversion H. constructor. Qed.
Hint Resolve prec_init.
Lemma stable_init : forall n i pf, stable (@init_cell n i pf) local_imm.
Proof. intros. red; intros. inversion H0; subst. auto. Qed.
Hint Resolve stable_init.

(** *** Allocation of a union-find structure *)
Program Definition alloc_uf {Γ} (n:nat) : rgref Γ (ref{uf (S n)|φ _}[δ _, δ _]) Γ :=
  indep_array_conv_alloc n (fun i pf => alloc (init_cell i pf) local_imm local_imm 
                                              (mkCell (S n) 0 (of_nat_lt pf)) _ _ _ _ _ _
                           ) _ _.
Next Obligation. constructor. Qed.
Next Obligation. eapply convert; eauto. Defined.
Next Obligation.
  (* Prove φ of the initial array.  Need the array allocation to expose some summary of the
     initialization process, something like making the result of the allocation function
     depend on the index, together with a conversion that weakens that result (like loosening
     a refinement that the parent pointer is the cell number initially) and some way to
     stitch those together for an array-wide refinement... *)
  unfold alloc_uf_obligation_7 in *.
  constructor. intros.
  constructor.
  assert (exists i0, exists (pf:i0 < S n), i = of_nat_lt pf).
      exists (proj1_sig (to_nat i)). exists (proj2_sig (to_nat i)).
      clear H. clear A. induction i. compute; auto. 
          unfold to_nat; fold (@to_nat (n0)).
          destruct (to_nat i).
          unfold proj2_sig. simpl.
          f_equal. rewrite IHi. f_equal. simpl.
          apply ProofIrrelevance.proof_irrelevance.
  destruct H0 as [i0 [pf H0]].
  specialize (H i0 pf). destruct H as [f0 Hconv].
  rewrite H0. assert (Htmp := heap_lookup2 h f0). simpl in Htmp.
  rewrite Hconv.
  rewrite <- (convert_equiv f0). rewrite Htmp. simpl. auto.
Qed.

(* This will show up with any array read. *)
Lemma uf_folding : forall n, 
    res (T := uf n) (R := δ n) (G := δ n) = Array n (ref{cell n|any}[local_imm,local_imm]).
  intros. simpl. unfold uf. reflexivity.
(*  f_equal. 
  (* Need to use this axiom for prove the equality, but I need this term
     (uf_folding n) to be definitionally equal to eq_refl later for some rewriting...*)
  eapply rgref_exchange; try solve [compute; eauto].
  split; red; intros.
      destruct H; auto.
      split; auto. intros. inversion H; subst a'; subst a.
      (* Need to destruct an application of ascent_root... *)
      eapply path_compression; try  rewrite array_id_update.
.*)
Defined. (* need to unfold later *)
Hint Resolve uf_folding.
Hint Extern 4 (rgfold _ _ = Array _ _) => apply uf_folding.
Hint Extern 4 (Array _ _ = Array _ _) => apply uf_folding.

(** *** UpdateRoot *)
Require Import Coq.Arith.Arith.
Program Definition UpdateRoot {Γ n} (A:ref{uf (S n)|φ _}[δ _, δ _]) (x:Fin.t (S n)) (oldrank:nat) (y:Fin.t (S n)) (newrank:nat) 
  (pf : {x=y/\newrank>oldrank}+{fin_lt x y=true/\oldrank=newrank}): rgref Γ bool Γ :=
  (*let old := (A ~> x) in*)
  old <- rgret (A ~> x) ;
  (*
  if (orb (negb (fin_beq (@field_read _ _ _ _ _ _ _ _ _ _ old parent _ _) (*old ~> parent*) x))
          (negb (beq_nat (@field_read _ _ _ _ _ _ _ _ _ _ old rank _ (@cell_rank n)) (*old~>rank*) oldrank)))
*)
  (* TODO: Should match-refine the old ref before this. *)
  match (orb (negb (fin_beq (@field_read _ _ _ _ _ _ _ _ _ _ old parent _ _) (*old ~> parent*) x))
          (negb (beq_nat (@field_read _ _ _ _ _ _ _ _ _ _ old rank _ (@cell_rank (S n))) (*old~>rank*) oldrank)))
  with
  (*then*) |true => rgret false
  (*else*)|false=> (
      new <- alloc' any local_imm local_imm (mkCell (S n) newrank y) _ _ _ _ _ _; (*Alloc (mkCell n newrank y);*)
      (*fCAS( A → x , old, convert new _ _ _ _ _ _ _ _)*)
      (@field_cas_core _ _ _ _ _ _ _ _ A x _ _ old (convert new _ _ _ _ _ _ _ _) _)
  )
  end
.
Next Obligation.
  
  unfold UpdateRoot_obligation_13.
  unfold UpdateRoot_obligation_14.
  unfold UpdateRoot_obligation_15.
  unfold UpdateRoot_obligation_16.
  unfold UpdateRoot_obligation_17.
  unfold UpdateRoot_obligation_18.
  unfold UpdateRoot_obligation_19.
  unfold UpdateRoot_obligation_20.
  assert (H := heap_lookup2 h new).
  destruct H.
  
  assert (forall (A B:bool), false = (A || B)%bool -> false = A /\ false = B).
      intros. induction A0. inversion H1. induction B. inversion H1. auto.
  assert (Htmp := H1 _ _ Heq_anonymous). clear H1.
  destruct Htmp.
  assert (forall (B:bool), false = negb B -> true = B).
      intros. induction B; inversion H1; eauto.

  assert (H' := H3 _ H1). symmetry in H'. rewrite fin_beq_eq in H'.
  Locate beq_nat.
  assert (H'' := H3 _ H2). assert (H''' := beq_nat_eq _ _ H'').
  clear H3. clear H''.

  induction pf.
  (* bump rank *)
  destruct a. subst y.
  apply bump_rank with (xr := oldrank) (xr' := newrank); eauto with arith;
    try rewrite <- convert_equiv.
  erewrite <- field_projection_commutes' with (h:=h) in *; eauto.
  Axiom cell_ctor_complete : forall n (c:cell n), c = mkCell _ (getF c) (getF c).
  rewrite (cell_ctor_complete _ (h[h[A]<|x|>])). f_equal; eauto.
  assert (Htmp := heap_lookup2 h new). destruct Htmp. firstorder.

  (* path union *)
  eapply path_union.
  
  cut (h[ h[A]<|x|>] = mkCell _ oldrank x).
  intro t; apply t.
  Check field_projection_commutes'.

  (** Is there a granularity / atomicity issue w/ the fields of old?
      Shouldn't be; old is local_imm, and the ptr is only read once, with
      equivalence with h[A]<|x|> introduced by the CAS *)

  erewrite <- field_projection_commutes with (h:=h) in H'.
  erewrite <- field_projection_commutes with (h:=h) in H'''.
  unfold UpdateRoot_obligation_5 in *.
  unfold UpdateRoot_obligation_3 in *.
  simpl eq_rec in *.
  rewrite (cell_ctor_complete _ (h[ _ ])).
  f_equal; eauto.

  rewrite <- convert_equiv. apply H0. firstorder.
  
  (* TODO: We don't need the fin_lt x y (and at call sites, we can't provide it!
     information that y's rank is greater than x's should come from elsewhere;
     ideally from a Program match, but the paper doesn't have one.  It seems to
     be /stable/ contextual information about y that its rank is >= oldrank,
     so it should be provided at the call site.  Need to fix the pf arg. *)
  destruct b. subst oldrank; reflexivity.
  reflexivity.
  assert (forall h, newrank < getF (f:=rank)(FT:=nat) (h[h[A]<|y|>]) \/ 
                    (newrank = getF (f:=rank)(FT:=nat) (h[h[A]<|y|>]) /\ fin_lt x y = true)) by admit.
  induction (H3 h); intuition. 
  right. intuition. rewrite fin_lt_nat in H6. assumption.

Qed. (* UpdateRoot guarantee (δ n) *)

(** *** Find operation *)
Program Definition Find {Γ n} (r:ref{uf (S n)|φ _}[δ _, δ _]) (f:Fin.t (S n)) : rgref Γ (Fin.t (S n)) Γ :=
  RGFix _ _ (fun find_rec f =>
               let c : (ref{cell _|any}[local_imm,local_imm]) := (r ~> f) in
               let p := c ~> parent in
               if (fin_beq p f)
               then rgret f
               else (
                   c' <- Alloc! (mkCell _ (let _ := @cell_rank (S n) in c ~> rank) 
                                         ((@field_read _ _ _ _ _ _ _ _ (uf_folding (S n)) _ r p _ _) ~> parent ) ) ;
                   (*_ <- fCAS( r → f, c, convert_P _ _ _ c');*)
                   _ <- @field_cas_core _ _ _ _ _ _ _ _ r f _ _ c (convert_P _ _ _ c') _;
                   find_rec p
               )
            ) f
  .
Next Obligation. exact any. Defined.
Next Obligation. unfold Find_obligation_5. eauto. Qed.
Next Obligation. intuition. Qed.
Next Obligation. unfold Find_obligation_5. eauto. Qed.

Lemma cellres : forall n, @res (cell n) local_imm local_imm _ = cell n.
intros. simpl. reflexivity.
Defined.
      
Next Obligation. (* δ *)
  unfold Find_obligation_5 in *.
  assert (Htmp := heap_lookup2 h r). inversion Htmp; subst.

  eapply path_compression. eauto. (* stray dead rt arg *)
  assumption.
  rewrite conversion_P_refeq.
  assert (Htmp' := heap_lookup2 h c'). destruct Htmp'. rewrite H2; eauto.
  simpl @getF at 2.

      unfold Find_obligation_8 in *. unfold Find_obligation_9 in *.
      unfold Find_obligation_10 in *. unfold Find_obligation_3 in *.
      unfold Find_obligation_4 in *. unfold Find_obligation_1 in *.
      unfold Find_obligation_2 in *.
      
  rewrite <- H0.
  erewrite <- field_projection_commutes' with (h := h) (f := rank); auto.

  assert (Htmp' := heap_lookup2 h c'). destruct Htmp'. 
  rewrite conversion_P_refeq.
  rewrite H2; eauto. simpl @getF.

(*  inversion H1.
      subst f0.*)
(*
      assert (
                @field_read _ _ _ _ _ _ _ _ (cellres _) (@local_imm_refl _) 
                 (@field_read _ _ _ _ _ _ _ _ (uf_folding _) (refl_δ _) r f0 _ (@array_field_index _ _ f0))
               parent _ (@cell_parent _) = f0).
          intros. rewrite <- field_projection_commutes' with (h := h) (f := parent).
                  rewrite <- field_projection_commutes' with (h := h) (f := f0).
                  apply H4.
                  simpl. auto.
                  auto.
      unfold cellres in *. unfold uf_folding in *.
      rewrite H5. rewrite H5. apply self_root. assumption.

      subst r0.
      assert (
                @field_read _ _ _ _ _ _ _ _ ((cellres _)) (@local_imm_refl _) 
                 (@field_read _ _ _ _ _ _ _ _ (uf_folding _) (refl_δ _) r f0 _ (@array_field_index _ _ f0))
               parent _ (@cell_parent _) = t).
          intros. rewrite <- field_projection_commutes' with (h:=h) (f:=parent).
          rewrite <- H5. f_equal. f_equal. symmetry. assumption.
          simpl. reflexivity.
      unfold cellres in *. unfold uf_folding in *.

      rewrite H6. 

      inversion H4.
          subst t.
          assert (
                    @field_read _ _ _ _ _ _ _ _ ((cellres _)) (@local_imm_refl _) 
                     (@field_read _ _ _ _ _ _ _ _ (uf_folding _) (refl_δ _) r x _ (@array_field_index _ _ x))
                   parent _ (@cell_parent _) = x).
              rewrite <- field_projection_commutes' with (h:=h)(f:=parent); eauto.
              rewrite <- field_projection_commutes' with (h:=h); eauto.
      unfold cellres in *. unfold uf_folding in *.
          rewrite H5. constructor. assumption.
          subst r0.
          assert (
                    @field_read _ _ _ _ _ _ _ _ ((cellres _)) (@local_imm_refl _) 
                     (@field_read _ _ _ _ _ _ _ _ (uf_folding _) (refl_δ _) r t _ (@array_field_index _ _ t))
                   parent _ (@cell_parent _) = t0).
          intros. rewrite <- field_projection_commutes' with (h:=h) (f:=parent); eauto.
          rewrite <- H8. f_equal. f_equal. 
          rewrite <- field_projection_commutes' with (h:=h).
          simpl. reflexivity. simpl. reflexivity.
              
      unfold cellres in *. unfold uf_folding in *.
          rewrite H9. assumption.
          

    rewrite conversion_P_refeq.
    destruct (heap_lookup2 h c').
    rewrite H3; try firstorder. simpl.
      *)
      unfold Find_obligation_8 in *. unfold Find_obligation_9 in *.
      unfold Find_obligation_10 in *. unfold Find_obligation_3 in *.
      unfold Find_obligation_4 in *. unfold Find_obligation_1 in *.
      unfold Find_obligation_2 in *.
    Check trans_chase.
    Unset Printing Notations. idtac.
    Set Printing Implicit. idtac.
    eapply (trans_chase _ (h[r]) h f0 
(@field_read (cell _) (cell _) F 
                        (t _) (@any (cell _)) (@local_imm (cell _))
                        (@local_imm (cell _)) (weak_read (cell _))
                        (@eq_refl Set (cell _)) (local_imm_refl (cell _))
                        (@field_read (uf _)
                           (Array _
                              (ref (cell _) (@any (cell _))
                                 (@local_imm (cell _)) 
                                 (@local_imm (cell _)))) 
                           (t _)
                           (ref (cell _) (@any (cell _))
                              (@local_imm (cell _)) 
                              (@local_imm (cell _))) 
                           (φ _) (δ _) (δ _) (@read_uf _)
                           (@eq_refl Set
                              (Array _
                                 (ref (cell _) (@any (cell _))
                                    (@local_imm (cell _))
                                    (@local_imm (cell _))))) 
                           (refl_δ _) r f0
                           (@array_fields _
                              (ref (cell _) (@any (cell _))
                                 (@local_imm (cell _)) 
                                 (@local_imm (cell _))))
                           (@array_field_index _
                              (ref (cell _) (@any (cell _))
                                 (@local_imm (cell _)) 
                                 (@local_imm (cell _))) f0)) parent
                        (@fielding _) (@cell_parent _))). 
    Unset Printing Implicit. idtac.

    Check @getF.
    Check @field_read.
    Print field_read.
    assert (Hparenting :
              (*eq (getF (heap_deref h (array_read (heap_deref h r) f0)))*)
              eq (@getF _ _ _ parent _ cell_parent (heap_deref h (array_read (heap_deref h r) f0)))
                 (@field_read _ _ _ _ any local_imm local_imm _ eq_refl (local_imm_refl _) 
                              (field_read (H0:=eq_refl)(hreflexive0:=refl_δ _) r f0) parent _ _)).
    rewrite H0. erewrite field_projection_commutes' with (h:=h). reflexivity.
    simpl; eauto.
    
    erewrite <- field_projection_commutes' with (h:=h)(f:=parent); eauto.

    Focus 2.
    rewrite H0. erewrite field_projection_commutes' with (h:=h). reflexivity.
    simpl; eauto.
    Set Printing Notations. idtac.
    
    rewrite H0 in Hparenting.
    repeat rewrite Hparenting.

    eapply trans_chase. apply self_chase.

    erewrite field_projection_commutes' with (h:=h); eauto.
    f_equal.
    Focus 2. auto.
    Definition uf_fielding : forall n f, FieldType (uf n) (t n) f (ref{cell n|any}[local_imm,local_imm]).
      unfold uf. intros. apply @array_field_index.
    Defined.
    assert (Helper := fun f pf => field_projection_commutes' h (Fin.t _) (uf _) (φ _) (δ _) (δ _) _ r f _ (uf_folding _) pf (refl_δ _) array_fields (uf_fielding _ f)).
    unfold getF in Helper. unfold uf_fielding in Helper. unfold array_field_index in *.
    rewrite Helper.
    reflexivity.
    compute; eauto.
    
Qed.

Require Import Coq.Arith.Bool_nat.
Definition gt x y := nat_lt_ge_bool y x.

Definition ignore {Γ Γ' T} (C:rgref Γ T Γ') : rgref Γ unit Γ' :=
  _ <- C;
  rgret tt.
(** *** Union operation *)
Check @getF.
(** Coq is bad at automatically unfolding uf to an Array, so we give it a hint *)
Global Instance uf_fields {n:nat} : FieldTyping (uf n) (fin _) := array_fields.
Global Instance uf_field_index {n:nat}{T:Set}{f:fin _} : FieldType (uf n) (fin _) f (ref{_|_}[_,_]) :=
  array_field_index.
Check @field_read_refine.
Check fielding.
Lemma uf_cell_increasing_rank :
   ∀ n x0,
   ∀ t : ref{cell (S n) | any }[ local_imm, local_imm],
            stable
              (λ (A : uf (S n)) (h : heap),
               getF (h [A <| x0 |>]) ≥ getF (h [t])) 
              (δ (S n)).
Proof.
  compute; intuition; eauto.
  induction H0;
  match goal with
  | [ |- context[array_read (array_write ?x ?f ?c) ?x0] ] => induction (fin_dec _ f x0)
  end; try subst x0; arrays h h'; eauto.
  compute in H1; rewrite <- H1; eauto.
  assert (getF (h'[A<|x|>]) ≤ getF (h'[c])).
     rewrite H1. rewrite H0. compute. eauto.
  unfold getF in H5. unfold cell_rank in H5.
  etransitivity; eauto.
  assert (getF (h'[A<|x|>]) ≤ getF (h'[c])).
     rewrite H2. rewrite H0. compute. eauto.
  unfold getF in H3. unfold cell_rank in H3.
  etransitivity; eauto.
Qed.
Hint Resolve uf_cell_increasing_rank.

Program Definition union {Γ n} (r:ref{uf (S n)|φ _}[δ _, δ _]) (x y:Fin.t (S n)) : rgref Γ unit Γ :=
  RGFix _ _ (fun TryAgain _ =>
               x <- Find r x;
               y <- Find r y;
               if (fin_beq x y)
               then rgret tt
               else (
                   observe-field r --> x as oldx, pfx in (λ A h, getF (h[(array_read A x)]) ≥ getF (h[oldx]));
                   observe-field r --> y as oldy, pfy in (λ A h, getF (h[(A<|y|>)]) ≥ getF (h[oldy]));
                   observe-field-explicit (@cell_rank (S n)) for oldx --> rank as rankx, pf in (λ (c:cell _) h, getF (FieldType:=cell_rank) c ≥ rankx);
                   observe-field-explicit (@cell_rank (S n)) for oldy --> rank as ranky, pf in (λ (c:cell _) h, getF (FieldType:=cell_rank) c ≥ ranky);
                   (** TODO: revisit for non-atomic multiple reads, sequencing *)
                   (** TODO: Should be be reading from x' and y' here instead of x and y??? *)
                   xr <- rgret (@field_read _ _ _ _ _ _ _ _ _ _
                                          (@field_read _ _ _ _ _ _ _ _ (uf_folding (S n)) _ r x (@array_fields (S n) _) (@array_field_index (S n) _ x))
                                          rank _ (@cell_rank (S n)));
                   (** TODO: Should break this up and refine r such that (forall h, h[r<|y|>].rank >= old_y_ptr.rank), which provides
                       an assumption UpdateRoot needs *)
                   yr <- rgret (@field_read _ _ _ _ _ _ _ _ _ _
                                          (@field_read _ _ _ _ _ _ _ _ (uf_folding (S n)) _ r y (@array_fields (S n) _) (@array_field_index (S n) _ y))
                                          rank _ (@cell_rank (S n)));
                   (*_ <-
                   (if (orb (gt xr yr)
                           (andb (beq_nat xr yr)
                                 (gt (to_nat x) (to_nat y))))
                   then _ (** TODO: Swap(x,y); Swap(xr,yr); <-- Is this updating imperative variables? *)
                   else rgret tt) ; *)
                   ret <-
                   (match (orb (gt xr yr)
                           (andb (beq_nat xr yr)
                                 (gt (to_nat x) (to_nat y)))) with
                   | true => UpdateRoot r y yr x yr _ 
                   | false => UpdateRoot r x xr y xr _ 
                   end);
                   (*ret <- UpdateRoot r x xr y yr _;*)
                   if ret
                   then TryAgain tt
                   else if (beq_nat xr yr)
                        then ignore (UpdateRoot r y yr y (yr + 1) _)
                        else rgret tt
                   
               )
            )
        tt.
(** Proof obligations for UpdateRoot calls *)
  (*assert (forall h, newrank < getF (f:=rank)(FT:=nat) (h[h[A]<|y|>]) \/ 
                    (newrank = getF (f:=rank)(FT:=nat) (h[h[A]<|y|>]) /\ fin_lt x y = true)).*)
Next Obligation.  eapply uf_cell_increasing_rank. Qed.
Next Obligation.  eapply uf_cell_increasing_rank. Qed.
Next Obligation. compute; intuition; subst; eauto. Qed.
Next Obligation. compute; intuition; subst; eauto. Qed.
Next Obligation. 
    Set Printing Notations. idtac.
    Require Import Coq.Bool.Bool.
    symmetry in Heq_anonymous.
    right. intuition.
    (* TODO: trying to make y < x seems wrong; we know the ranks are ordered correctly.  A refine-match on the to-be-parent that its rank is >= a val, and the to-be-child's rank is <= that val, ensures ordering... so this shouldn't be req'd. *) admit.
Qed.
Next Obligation. 
  right. intuition. (* Ditto. *) admit.
Qed.
Next Obligation. left. intuition. eauto with arith. Qed.
  
(** *** Sameset test *)
Program Definition Sameset {Γ n} (A:ref{uf (S n)|φ _}[δ _,δ _]) (x y:Fin.t (S n)) :=
  RGFix _ _ (fun TryAgain _ =>
               x <- Find A x;
               y <- Find A y;
               if (fin_beq x y)
               then rgret true
               else (if fin_beq ((@field_read _ _ _ _ _ _ _ _ (@uf_folding _) _ A x _ (@array_field_index _ _ x)) ~> parent) x
                     then @rgret Γ _ false
                     else TryAgain tt)
            ) tt.
