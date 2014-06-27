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
                     (@eq nat (getF (h[x <| i |>])) (getF (h[x <| t |>])) -> 
                         proj1_sig (to_nat i) < proj1_sig (to_nat t)) ->
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
                         (* This old chase theory is too strong.  consider reading the grandparent for a CAS, then the parent is looked up and completely bumped (so the links now skip the was-grandparent).  Then the CAS on the original cell would succeed, but actually extend the path at the moment of the write (subsequently it would be compressed again by the parent-lookup process, but... *)
                         (*chase n x h f (getF (h[c])) -> *)
                         (* Instead, we need to
                            1) prevent cycles (i.e. not h[c].parent-->f)
                            2) at least perform an update within the same set (common ancestor for h[c].parent and f)
                            Since not h[c].parent-->f, h[c].parent's path to the root is not affected by updating f,
                            f's new path is f-->h[c].parent-->...->root, and anything reaching f is <whatever>-->f->...
                            Thus terminating_ascent is preserved.
                            We require (2) to ensure we don't spuriously munge sets...
                            Note that this permits /extending/ the path to the root!  This is true of the original paper as well.
                            We may do all of the reads for the compression CAS on an element i, and just before the CAS, several other
                            threads perform lookups on the parent, and each completes /the parent's/ *first* compression.  This moves the parent
                            several links closer to the root, without affecting the (original) grandparent-of-i's distance from the root.
                            Then the CAS in the original lookup of i succeeds, swapping i's parent from the original parent (now much closer to the root)
                            to the original grandparent, which is (momentarily) further from the root than the original parent!
                         *)
                         (exists Y, ~chase n x h (getF (h[c])) f /\
                                     chase n x h (getF (h[c])) Y /\
                                     chase n x h f Y
                         ) ->
    getF (h[c]) ≤ getF (h[x<|(getF (h[c]))|>]) ->
    (@eq nat (getF (h[c])) (getF (h[x<|(getF (h[c]))|>])) ->
         proj1_sig (to_nat f) < proj1_sig (to_nat (getF (h[c])))) ->
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
  | uf_id : forall A h h', δ n A A h h'
.

Ltac fcong i j :=
  unfold fin in *; 
  let H := fresh in
  assert (H : i = j) by congruence;
  rewrite H in *;
  clear dependent i.

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
                             fcong t i. rewrite H3 in *. assumption.
      dependent induction H0. 
          fcong i0 i. fcong t i.
          apply IHchase; eauto. apply self_ascent; eauto.
          fcong i t0.
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
        intros. fcong i1 i; eauto.
        intros. fcong t i1.
          symmetry. apply IHt; eauto.
Qed.
Lemma Hdouble : forall n x h,
                  (forall i, terminating_ascent n x h i) ->
                  forall X Z, chase n x h X Z -> chase n x h Z X -> X = Z.
Proof.
  intros n x h H.
  intro X. induction (H X); intros.
               induction H1; induction H2; auto.
               fcong t f.
               apply IHchase; eauto. eapply trans_chase. eassumption. assumption.
           assert (chase n x h Z t).
               induction H4. eapply trans_chase. constructor. intuition.
                 eapply trans_chase'. eassumption. eapply trans_chase. eassumption. assumption.
           induction H3. reflexivity. 
             fcong t t1.
             assert (Htmp := IHt _ H3 H5). rewrite Htmp in *.
             symmetry. apply IHt; try eassumption. eapply trans_chase. constructor. assumption.
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

Lemma self_loop_chase : forall n x h i j,
                          chase n x h i j ->
                          getF (h[x<|i|>]) = i ->
                          i = j.
Proof. intros. induction H; eauto. fcong t i. firstorder. Qed.
Lemma ascend_new_heap : forall n x h h', (forall i, terminating_ascent n x h i) ->
                                         forall i, terminating_ascent n x h' i.
Proof.
  intros.
  induction (H i); arrays h h'.
      apply self_ascent; eauto.
      eapply trans_ascent; eauto.
Qed.
Lemma ascend_new_heap' : forall n x h h' i, terminating_ascent n x h i ->
                                         terminating_ascent n x h' i.
Proof.
  intros. induction H; arrays h h'. apply self_ascent; eauto. eapply trans_ascent; eauto.
Qed.
Lemma chase_new_heap : forall n x h h' i j, chase n x h i j -> chase n x h' i j.
Proof.
  intros. induction H; try constructor.
  arrays h h'. eapply trans_chase; eauto.
Qed.
Lemma chase_step : forall n x h a b c,
                     chase n x h a c -> a ≠ c -> getF(h[x<|a|>])=b -> chase n x h b c.
Proof. intros.
       generalize dependent b.
       induction H. exfalso; eauto.
       intros. fcong t b. clear H2.
       induction (fin_dec _ b f). subst f. constructor.
       firstorder.
Qed.
Lemma no_chase_step : forall n x h a b c,
                        ~chase n x h a c -> a≠c -> getF(h[x<|a|>])=b -> ~chase n x h b c.
Proof. intros. intro Hbad. apply H. eapply trans_chase; eauto. Qed.

Lemma sort_equiv_rank : forall n x h,
                          (forall i, terminating_ascent n x h i) ->
                          forall a b,
                            chase n x h a b ->
                            a ≠ b ->
                            @eq nat (getF(h[x<|a|>])) (getF(h[x<|b|>])) ->
                            proj1_sig (to_nat a) < proj1_sig (to_nat b).
Proof.
  intros n x h H a.
  induction (H a); intros.
      exfalso. apply H2. eapply self_loop_chase; eauto.
      assert ((getF(h[x<|b|>])) ≤ (getF(h[x<|t|>]))).
          rewrite <- H5. assumption.
      assert (chase n x h t b). eapply chase_step; eauto.
      assert ((getF(h[x<|t|>])) ≤ (getF(h[x<|b|>]))).
          clear H5 H6 H3 IHt. clear H0 H2. induction H7. reflexivity.
          etransitivity; try apply IHchase; eauto.
          induction (H i0). fcong i0 t. reflexivity.
              fcong t1 t. firstorder.
          induction (H i0). fcong t i0. assumption.
              fcong t1 t. etransitivity; eauto.
      assert (@eq nat (getF(h[x<|t|>])) (getF(h[x<|b|>]))).
          apply Le.le_antisym; eauto.
      rewrite H9 in *. rewrite H5 in *.
      induction (fin_dec _ t b). rewrite a in *. firstorder.
      etransitivity; eauto.
Qed.
Lemma chase_rank : forall n x h,
                     (forall i, terminating_ascent n x h i) ->
                     forall a b, chase n x h a b ->
                                 (getF(h[x<|a|>])) ≤ (getF(h[x<|b|>])).
Proof. intros. induction H0. reflexivity.
       induction (H i). fcong t i. assumption.
                        fcong t0 t. etransitivity; eauto.
Qed.
Lemma chase_rank_strict : forall n x h,
                            (forall i, terminating_ascent n x h i) ->
                            forall a b, a ≠ b -> chase n x h a b ->
                                 @eq nat (getF(h[x<|a|>])) (getF(h[x<|b|>])) ->
                                 proj1_sig (to_nat a) < proj1_sig (to_nat b).
Proof.
  intros. induction H1. contradiction H0; eauto.
   induction (fin_dec _ t f). subst f. 
       induction (H i). fcong t i. contradiction H0; eauto.
           fcong t0 t. firstorder.
  assert (@eq nat (getF(h[x<|i|>])) (getF(h[x<|t|>]))).
    induction (H i). fcong t i. auto.
         fcong t0 t. 
         assert ((getF(h[x<|t|>])) ≤ (getF(h[x<|f|>]))).
             apply chase_rank; eauto. eapply Le.le_antisym; eauto. rewrite H2; eauto.
  induction (fin_dec _ i t).
      rewrite <- a in *. clear dependent t. firstorder.
      induction (H i). fcong t i. contradiction b0; eauto.
      fcong t0 t.
  etransitivity; try apply IHchase; eauto. rewrite <- H4. assumption.
Qed.

Lemma chase_dec : forall n x h i j, i≠j -> φ n x h -> chase n x h i j \/ ~chase n x h i j.
Proof.
  intros. generalize dependent j.
  rename H0 into H.
  intros j Hne.
  induction H. intros.
  induction (H i).
  induction (fin_dec _ i j). subst j. left. constructor.
                             right. intros Hbad. induction Hbad. contradiction b. auto.
                             assert (i = t) by congruence. rewrite H2 in *. firstorder.
  clear H1.
  induction (fin_dec _ t j). subst j. 
      left. eapply trans_chase; try constructor. symmetry; assumption.
  induction (IHt b).
  left. eapply trans_chase; eauto.
  right.
  intro Hbad. apply H1. 
  clear IHt H1.
  inversion Hbad. subst j. contradiction Hne; eauto.
  subst j. unfold fin in *.
  fcong t1 t. assumption.
Qed.
Lemma no_chase_irrefl : forall n x h i j, ~chase n x h i j -> i ≠ j.
Proof. intros. intro Hbad. subst. apply H. constructor. Qed.
Lemma no_chase_irrefl' : forall n x h i j, ~chase n x h i j -> j ≠ i.
Proof. intros. intro Hbad. subst. apply H. constructor. Qed.

(* When chase_dec deduces a certain index doesn't chase a path to the updated
   array index, we simply recycle the old ascent proof *)
Lemma unaffected_update : forall n x h f c,
                            φ n x h ->
                            @eq nat (getF (h[x<|f|>])) (getF (h[c])) ->
                            forall b,
                              ~ chase n x h b f ->
                              terminating_ascent n (array_write x f c) h b.
Proof.
  intros n x h f c H Hrank.
  destruct H.
  intros b; induction (H b).
     intros Hbad. apply self_ascent. rewrite read_past_updated_cell; eauto. eapply no_chase_irrefl'; eauto.
     intros Hbad. assert (Htmp := no_chase_irrefl' _ _ _ _ _ Hbad).
         assert (Hch : ~chase n x h t f).  eauto using no_chase_step.
         assert (Htmp' := no_chase_irrefl' _ _ _ _ _ Hch).
         apply trans_ascent with (t:=t); arrays h h'.
         apply IHt; eauto.
Qed.
Lemma unaffected_update_le : forall n x h f c,
                            φ n x h ->
                            (getF (h[x<|f|>])) ≤ (getF (h[c])) ->
                            forall b,
                              ~ chase n x h b f ->
                              terminating_ascent n (array_write x f c) h b.
Proof.
  intros n x h f c H Hrank.
  destruct H.
  intros b; induction (H b).
     intros Hbad. apply self_ascent. rewrite read_past_updated_cell; eauto. eapply no_chase_irrefl'; eauto.
     intros Hbad. assert (Htmp := no_chase_irrefl' _ _ _ _ _ Hbad).
         assert (Hch : ~chase n x h t f).  eauto using no_chase_step.
         assert (Htmp' := no_chase_irrefl' _ _ _ _ _ Hch).
         apply trans_ascent with (t:=t); arrays h h'.
         apply IHt; eauto.
Qed.
Lemma update_ascent : forall n x h f c jmp,
                        φ n x h ->
                        @eq nat (getF (h[x<|f|>])) (getF (h[c])) ->
                        getF (h[c]) ≤ getF (h[x<|jmp|>]) ->
                        (@eq nat (getF (h[c])) (getF (h[x<|jmp|>])) ->
                         proj1_sig (to_nat f) < proj1_sig (to_nat jmp)) ->
                        getF(h[c]) = jmp ->
                        ~chase n x h jmp f ->
                        terminating_ascent n (array_write x f c) h f.
Proof.
  intros.
  assert (Htmp := no_chase_irrefl' _ _ _ _ _ H4).
  apply trans_ascent with (t:=jmp); arrays h h'.
  congruence.
  eauto using unaffected_update.
Qed.
Lemma update_ascent_le : forall n x h f c jmp,
                        φ n x h ->
                        (getF (h[x<|f|>])) ≤ (getF (h[c])) ->
                        getF (h[c]) ≤ getF (h[x<|jmp|>]) ->
                        (@eq nat (getF (h[c])) (getF (h[x<|jmp|>])) ->
                         proj1_sig (to_nat f) < proj1_sig (to_nat jmp)) ->
                        getF(h[c]) = jmp ->
                        ~chase n x h jmp f ->
                        terminating_ascent n (array_write x f c) h f.
Proof.
  intros.
  assert (Htmp := no_chase_irrefl' _ _ _ _ _ H4).
  apply trans_ascent with (t:=jmp); arrays h h'.
  congruence.
  eapply unaffected_update_le; eauto.
Qed.

Lemma affected_update : forall n x h f c,
                          φ n x h ->
                          @eq nat (getF (h[x<|f|>])) (getF (h[c])) ->
                          terminating_ascent n (array_write x f c) h f ->
                          forall b,
                            chase n x h b f ->
                            terminating_ascent n (array_write x f c) h b.
Proof.
  intros n x h f c H Hrank. intros.  destruct H.
  induction (H b).
      induction H1; eauto.
      induction H1; eauto. fcong i0 i. eauto. fcong i0 i. fcong t i. firstorder.
      (* trans *)
      induction H1; eauto. 
      induction (fin_dec _ i f).
          rewrite a in *. assumption.
      fcong t1 t.
      induction (fin_dec _ t f). rewrite a in *. clear dependent t.
        eapply trans_ascent with (t:=f); arrays h h'; eauto.
            rewrite <- Hrank in *. firstorder.
            rewrite <- Hrank in *. firstorder.
        eapply trans_ascent with (t:=t); arrays h h'; eauto.
Qed.
Lemma affected_update_le : forall n x h f c,
                          φ n x h ->
                          (getF (h[x<|f|>])) ≤ (getF (h[c])) ->
                          terminating_ascent n (array_write x f c) h f ->
                          forall b,
                            chase n x h b f ->
                            terminating_ascent n (array_write x f c) h b.
Proof.
  intros n x h f c H Hrank. intros.  destruct H.
  induction (H b).
      induction H1; eauto.
      induction H1; eauto. fcong i0 i. eauto. fcong i0 i. fcong t i. firstorder.
      (* trans *)
      induction H1; eauto. 
      induction (fin_dec _ i f).
          rewrite a in *. assumption.
      fcong t1 t.
      induction (fin_dec _ t f). rewrite a in *. clear dependent t.
        eapply trans_ascent with (t:=f); arrays h h'; eauto.
            rewrite <- Hrank in *. firstorder.
            intro Heq. arrays h h'. rewrite <- Heq in Hrank.
            assert (Heq' : @eq nat (getF (h[x<|i|>])) (getF (h[x<|f|>]))).
                eapply Le.le_antisym; eauto.
            firstorder.
        eapply trans_ascent with (t:=t); arrays h h'; eauto.
Qed.
(* TODO: Now, some of these lemmas should be provable by inducting on the use of
   chase_dec, then in the affected cases, inducting on whether or not the affected index is the updated cell or not, then applying one of the previous 3 lemmas.
*)

Lemma sameset_acyclic_update_preserves_term_ascent :
  forall h h' n x f c newparent i,
    @eq nat (getF (h[x <| f |>])) (getF (h[c])) ->
    (forall i, terminating_ascent n x h i) ->
    getF (h[c]) = newparent ->
    (exists Y, ~chase n x h (getF (h[c])) f /\
                chase n x h (getF (h[c])) Y /\
                chase n x h f Y) ->
    getF (h[c]) ≤ getF (h[x<|newparent|>]) ->
    (@eq nat (getF (h[c])) (getF (h[x<|newparent|>])) ->
         proj1_sig (to_nat f) < proj1_sig (to_nat newparent)) ->
    terminating_ascent n (array_write x f c) h' i.
Proof.
  intros h h' n x f c newparent i Hrank H.
  intros Hparent.
  intros [Y [Hnocycle [HcY HfY]]].
  intros Hparent_rank Hparent_sort.
  fold fin in *. (* some of the lemmas are stated w.r.t. Fin.t... *)
  
  Check chase_dec.

  induction (fin_dec _ i f).
  + subst f. rewrite Hparent in *.
    assert (newparent <> i). eapply no_chase_irrefl; eauto. auto.
    eapply trans_ascent with (t:=newparent).
    rewrite read_updated_cell. arrays h h'. auto.
    rewrite read_updated_cell.
    rewrite read_past_updated_cell; auto. arrays h h'; auto.
    rewrite read_updated_cell. rewrite read_past_updated_cell; try solve[auto].
    arrays h h'. intro Heq. specialize (Hparent_sort Heq).
    auto.
    eapply unaffected_update. constructor. intros. eapply ascend_new_heap'. eauto. arrays h h'. assumption.
    intro Hbad. assert (chase n x h newparent i).
    eapply chase_new_heap. eassumption. auto.
  + 
  induction (chase_dec n x h i f); try solve[constructor; eauto]; eauto.
  - apply (affected_update n x h' f c); eauto.
        constructor; eauto using ascend_new_heap.
        arrays h h'; eassumption.
        rewrite Hparent in *.
        assert (newparent <> f). eapply no_chase_irrefl; eauto. auto.
        eapply trans_ascent with (t:=newparent).
        rewrite read_updated_cell. arrays h h'; auto.
        rewrite read_updated_cell. rewrite read_past_updated_cell.
        repeat rewrite (imm_vals' h h') in *. tauto.
        solve[auto].
        rewrite read_updated_cell. rewrite read_past_updated_cell; auto.
        repeat rewrite (imm_vals' h h') in *.
        intro Heq; specialize (Hparent_sort Heq). tauto.
        (* newparent is "unaffected" *)
        eapply unaffected_update.
            constructor. eauto using ascend_new_heap.
            arrays h h'; eassumption.
            intro Hbad. apply Hnocycle.
            eauto using chase_new_heap.
            eauto using chase_new_heap.
    - (* unaffected: i is "above" f or in another set *)
    assert (sol := unaffected_update n x h f c (pfφ _ _ h H) Hrank i H0).
    Check ascend_new_heap.
    apply (ascend_new_heap' n _ h h'). eauto.
Qed.    
       (* Notes: Once an index is non-root, it remains non-root.
                  Non-root ranks are fixed forever.
                  --> If we observe a path x-->y for x<>y,
                      then forever onwards, x.rank <= y.rank.
                  In locations where we read out a parent link,
                  we can generate this.  Then again for the grandparent, using transitivity of <=.
         *)
    
    

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
      (* f = i *)
      subst i.
      inversion Hc.
          apply self_ascent. rewrite read_updated_cell. erewrite immutable_vals; eassumption.
          subst f0.
              fcong t f. clear H1 H2.
              induction (H mid).
                (* self *)
                induction (fin_dec _ f i). subst f. apply self_ascent. rewrite read_updated_cell. erewrite immutable_vals; eassumption.
                
                    exfalso. apply b. clear Hf Hrank.
                    induction Hc; eauto.
                    fcong t i. firstorder.
                
                (* trans *)
                assert (f = i). eapply self_loop_chase; eauto.
                rewrite H4 in *.
                apply self_ascent; arrays h h'; eauto.
      (* f ≠ i *)
      apply self_ascent. rewrite read_past_updated_cell; auto. erewrite immutable_vals; eassumption; auto.

  (* trans *)
  induction (fin_dec _ f i). subst i.
  
  induction (fin_dec _ f mid). rewrite <- a in *. clear dependent mid.
      apply self_ascent; arrays h h'; eauto.

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
                                          fcong t t0. assumption.
                                      eapply chase_rank'; auto.
                                      rewrite H0 in H3. assumption.
                                    
                                    (* New case for rank= -> < *)
                                    intro H'. arrays h h'.
                                    rewrite read_updated_cell in H'; eauto.
                                    rewrite read_past_updated_cell in H'; eauto.
                                    rewrite <- Hrank in H'. 
                                    eapply chase_rank_strict; arrays h h'; eauto.
                                    
                                    eapply unaffected_update.
                                      constructor; eauto using ascend_new_heap.
                                      arrays h h'. eauto.
                                      intro Hbad. apply b. eapply Hdouble; eauto using chase_new_heap.
                                      
                                    induction (fin_dec _ f t).
                                      rewrite a in *. clear dependent f.
                                      apply trans_ascent with (t:= t); arrays h h'.
                                          rewrite <- Hrank; eauto.
                                          intro H'. apply H2. rewrite <- Hrank in *. assumption.
                                          assumption.
                                      apply trans_ascent with (t:=t); arrays h h'.
                                      assumption.
Qed.

Lemma no_chase_extend : forall n x h s m,
                          chase n x h s m ->
                          forall f, ~ chase n x h s f ->
                          ~ chase n x h m f.
Proof.
  intros n x h s m H.
  induction H. tauto.
  intros.
  apply IHchase. intro.
  apply H1. eapply trans_chase. eassumption. eauto.
Qed.

Lemma union_identity : forall n x h f y (c:ref{cell n|any}[local_imm,local_imm]),
                         f≠y -> 
                         (*getF(h[c])=y -> *)
                         terminating_ascent n x h y ->
                         ~chase n x h y f ->
                         getF(h[x<|f|>]) = f ->
                         forall y', chase n x h y y' -> f≠y' ->
                                    terminating_ascent n (array_write x f c) h y'.
Proof.
  intros n x h f y c. intro.
  intro.
  intros Hchase.
  intros Hupdate_root.
  
  induction H0.
  (* self *) intros. induction H1. apply self_ascent; arrays h h'; eauto.
             assert (i = t) by congruence. rewrite H4 in *. firstorder.
  (* trans *)
  intros. 
  (* back patch *) rename H2 into Hcond. rename H3 into H2. rename H4 into H3. rename H5 into H4.
  induction H3.
    induction (fin_dec _ f t). rewrite a in *.
    exfalso. apply Hchase. eapply trans_chase; try constructor; eauto.
    apply trans_ascent with (t:=t); arrays h h'.
    apply IHterminating_ascent; eauto.
    eapply no_chase_extend; eauto. eapply trans_chase; try solve[symmetry;eassumption]. constructor.
  constructor.
  unfold fin in *. assert (t = t0) by congruence. rewrite H6 in *. clear dependent t.
  assert (f ≠ t0). intro Hbad. rewrite Hbad in *. exfalso. apply Hchase. eapply trans_chase. constructor. symmetry; eauto.
  apply IHterminating_ascent; eauto.
  eapply no_chase_extend; try eassumption. eapply trans_chase; try solve[symmetry;eassumption]. constructor.
Qed.


Require Import Coq.Arith.Lt.
Lemma stable_φ_δ : forall n, stable (φ n) (δ n).
Proof.
  intros. red. intros.
  induction H0.
  (* Compression *)
      destruct H. constructor. intros.
      (*eapply chase_update_preserves_term_ascent; eauto.*)
      eapply sameset_acyclic_update_preserves_term_ascent; eauto.
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
      induction (fin_dec _  i x). 
          rewrite a in *. clear dependent i.
          induction (fin_dec _ x y). subst y.
            apply self_ascent; arrays h h'; eauto. rewrite H1. reflexivity.
            apply trans_ascent with (t:=y); arrays h h'; eauto.
                rewrite H1. reflexivity.
                rewrite H1. rewrite H3. simpl.
                induction H4. eauto with arith. destruct H4. subst xr'. reflexivity.
                (* new cond case *)
                rewrite H1. rewrite H8. simpl. intro Hcond. rewrite Hcond in *; clear dependent xr'.
                induction H4. exfalso. eapply Lt.lt_irrefl; eauto.
                destruct H4. assumption.
              (* Now we're pointing to y, which doesn't chase back to x in x0 *)
              eapply union_identity; eauto.
                eapply ascend_new_heap; eauto.
                (* BETTER be provable that ~ chase y x *)
                    Require Import Coq.Arith.Le.
                    Require Import Coq.Arith.Lt.
                    intro X. induction H4.
                    (* xr' < yr *) 
                    induction X. apply b; reflexivity.
                    assert (Hch' := chase_new_heap n x0 h' h _ _ X).
                    arrays h' h.
                    assert (Htmp := chase_rank' n h x0 _ _ _ (H i) H10 Hch').
                    arrays h h'. rewrite H3 in Htmp. rewrite H0 in Htmp. simpl in Htmp.
                    assert (yr ≤ xr'). etransitivity; eauto.
                    assert (h'' := le_not_lt _ _ H11). apply h''. assumption.
                    
                    (* xr'=yr, x < y *)
                    destruct H4. subst xr'.
                    induction X. apply b; reflexivity.
                    assert (Hch' := chase_new_heap n x0 h' h _ _ X).
                    arrays h' h.
                    assert (Htmp := chase_rank' n h x0 _ _ _ (H i) H4 Hch').
                    rewrite H0 in Htmp. rewrite H8 in Htmp. simpl in Htmp.
                    assert (heq := le_antisym _ _ Htmp H9). subst xr.
                    (* now the ranks must be == from i->t->...->f. and f < i.
                       but by inducting on term_ascent i, which reaches f, if
                       the ranks are equal then i < f, which is a contradiction. *)
                    induction (H i). 
                      (* self *) assert (t=i) by congruence. rewrite H12 in *.
                                 clear H6 H5 H2 H7 H9 Htmp H11 H12 t IHX H8.
                                 assert (i = f). induction X; try reflexivity.
                                 arrays h h'. assert (i=t) by congruence. rewrite <- H5 in *. clear H5. clear t.
                                 firstorder.
                                 subst f. eapply lt_irrefl; eauto.
                      (* trans *) fcong t0 t. 
                                 assert (getF (h[x0<|t|>]) ≤ getF (h[x0<|f|>])).
                                     induction (fin_dec _ t f). subst f. reflexivity.
                                     eapply chase_rank'; eauto.
                                     induction Hch'. exfalso; intuition.
                                       clear IHHch'.
                                     rewrite H14. assumption.
                                 assert (getF (h[x0<|t|>]) = yr).
                                     rewrite H3 in H12.
                                     rewrite H0 in H14. unfold getF at 2 in H14. unfold cell_rank in *.
                                     eapply le_antisym; eauto.
                                 (* Looks like I need to add a hyp to the inductive
                                    term_ascent ctor... if the ranks are = then child < parent  *)
                                 rewrite H15 in *.
                                 assert (Htmp' := chase_rank_strict n x0 h H i f).
                                 rewrite H3 in *. rewrite H0 in *. simpl in Htmp'.
                                 assert (proj1_sig (to_nat i) < proj1_sig (to_nat f)).
                                     apply Htmp'; eauto. eapply trans_chase with (t0:=t); eauto.
                                 assert (Htmp'' := Lt.lt_not_le _ _ H16). apply Htmp''. eauto with arith.
                    
                arrays h h'; rewrite H0; reflexivity.
                constructor.

      (* i ≠ x *)
      einduction (chase_dec n x0 h _ _ b).
      
        eapply affected_update_le; eauto using chase_new_heap.
            constructor. eauto using ascend_new_heap.
            arrays h h'. rewrite H0; rewrite H1. simpl.
            assert (Htmp := chase_rank n x0 h H i x H10).
            assumption.
        eapply update_ascent_le; eauto.
            constructor; eauto using ascend_new_heap.
            arrays h h'; rewrite H0. rewrite H6. simpl. assumption.
            arrays h h'. rewrite H1. unfold getF at 3. unfold getF at 1. unfold cell_parent. unfold cell_rank.
            assert (xr' ≤ yr). induction H4. eauto with arith. destruct H4. rewrite H4. reflexivity.
            rewrite <- H8 in H11. assumption.
            arrays h h'. repeat rewrite H1. 
            unfold getF at 1. unfold getF at 2. unfold cell_rank; unfold cell_parent.
            intro Heq. assert (xr' = yr). rewrite <- H8. assumption.
            rewrite H11 in *. unfold getF.
            induction H4. exfalso; eapply Lt.lt_irrefl; eauto. destruct H4. assumption.
            arrays h h'; rewrite H1. simpl.
            intro Hbad.
            assert (getF(h[x0<|y|>]) ≤ getF(h[x0<|x|>])).
                eapply chase_rank; eauto using ascend_new_heap, chase_new_heap.
            arrays h h'. rewrite H8 in H11. rewrite H0 in H11. simpl in H11.
            assert (xr = yr). eapply Le.le_antisym; eauto.
            subst xr.
            induction H4. 
                assert (Htmp := Lt.lt_not_le _ _ H4). firstorder.
                destruct H4. subst xr'.
                assert (Htmp := Lt.lt_not_le _ _ H12). apply Htmp.
                Check chase_rank_strict.
                assert (proj1_sig (to_nat y) < proj1_sig (to_nat x)).
                    eapply chase_rank_strict; eauto.
                    induction (fin_dec _ y x); eauto. subst x. exfalso. apply Htmp. reflexivity.
                    eapply chase_new_heap; eauto.
                    arrays h h'. rewrite H8. rewrite H0. reflexivity.
                    eauto with arith.
      
        eapply union_identity; eauto.
          eapply ascend_new_heap; eauto.
          intro X. apply H10. eapply chase_new_heap; eauto.
          arrays h h'; rewrite H0; reflexivity.
          constructor.

          constructor. assumption.

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
      
      (* new conditional goal *)
      arrays h h'. intro Heq. rewrite H2 in Heq. unfold getF at 2 in Heq. unfold cell_rank in *.
      rewrite Heq in *. rewrite H0 in *. unfold getF in H4. unfold getF in H5.
      rewrite Lt.le_lt_or_eq_iff in H1.
      induction H1.
          apply H5. eapply Le.le_antisym; eauto with arith.
          subst xr'. firstorder.

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
      
      (* new conditional goal *)
      arrays h h'.
  (* refl *)
  destruct H; constructor; eauto using ascend_new_heap.
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
  rewrite immutable_vals with (h':=h'). reflexivity. 
  intro. arrays h h'. eauto.
  assumption.
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
    
    repeat rewrite immutable_vals with (h:=h2)(h':=h). assumption.
    destruct H3 as [Y [Hno [HcY HfY]]].
    exists Y. 
        repeat rewrite immutable_vals with (h:=h2)(h':=h). 
        intuition; eauto using chase_new_heap.
    repeat rewrite immutable_vals with (h:=h2)(h':=h). assumption.
    repeat rewrite immutable_vals with (h:=h2)(h':=h). assumption.

    rewrite H in H1. rewrite (immutable_vals _ _ h h2) in H2. rewrite H in H4.
    eapply path_union; eauto. 
    constructor. repeat red. exists y. compute; reflexivity.
    constructor. repeat red. exists x. compute; reflexivity.
    
    rewrite (immutable_vals  _ _ h h2) in H1.
    rewrite (immutable_vals  _ _ h h2) in H3.
    eapply bump_rank; eauto.
  (* refl *)
  eapply uf_id.
Qed.
    
Hint Resolve precise_φ precise_δ.

Lemma refl_δ : forall n, hreflexive (δ (S n)).
Proof.
  intros; red; intros. constructor.
Qed.
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
  (pf:forall h, x=y/\newrank>oldrank \/ 
                    (newrank=oldrank/\newrank ≤ getF (f:=rank)(FT:=nat) (h[h[A]<|y|>])
                     /\ (newrank = getF(f:=rank)(FT:=nat)(h[h[A]<|y|>]) -> fin_lt x y = true)))
: rgref Γ bool Γ :=
  old <- rgret (A ~> x) ;
  observe-field-explicit cell_parent for old --> parent as oparent, pfp in (λ x h, getF x = oparent);
  observe-field-explicit (@cell_rank (S n)) for old --> rank as orank, pfp in (λ x h, getF x = orank);
  match (orb (negb (fin_beq oparent (*old ~> parent*) x))
          (negb (beq_nat orank (*old~>rank*) oldrank)))
  with
  (*then*) |true => rgret false
  (*else*)|false=> (
      new <- alloc' any local_imm local_imm (mkCell (S n) newrank y) _ _ _ _ _ _; (*Alloc (mkCell n newrank y);*)
      (*fCAS( A → x , old, convert new _ _ _ _ _ _ _ _)*)
      (@field_cas_core _ _ _ _ _ _ _ _ A x _ _ old (convert new _ _ _ _ _ _ _ _) _)
  )
  end
.
Next Obligation. compute; intros; subst; eauto. Qed.
Next Obligation. compute; intros; subst; eauto. Qed.
Next Obligation.
  
  unfold UpdateRoot_obligation_13.
  unfold UpdateRoot_obligation_14.
  unfold UpdateRoot_obligation_15.
  unfold UpdateRoot_obligation_16.
  unfold UpdateRoot_obligation_17.
  unfold UpdateRoot_obligation_18.
  unfold UpdateRoot_obligation_19.
  unfold UpdateRoot_obligation_20.
  unfold UpdateRoot_obligation_21.
  unfold UpdateRoot_obligation_22.
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

  induction (pf h) as [a | b].
  (* bump rank *)
  destruct a. subst y.
  apply bump_rank with (xr := oldrank) (xr' := newrank).
  Axiom cell_ctor_complete : forall n (c:cell n), c = mkCell _ (getF c) (getF c).
  rewrite (cell_ctor_complete _ (h[h[A]<|x|>])). f_equal; eauto.
  subst. compute [getF cell_rank]. eauto.
  subst. compute [getF cell_parent]. eauto.
  eauto with arith.
  rewrite <- convert_equiv. eauto.

  (* path union *)
  eapply path_union.
  
  cut (h[ h[A]<|x|>] = mkCell _ oldrank x).
  intro t; apply t.

  rewrite (cell_ctor_complete _ (h[ _ ])).
  f_equal; eauto.
  subst. compute [getF cell_rank]. eauto.
  subst. compute [getF cell_parent]. eauto.

  rewrite <- convert_equiv. apply H0. firstorder.
  
  destruct b. subst oldrank. subst orank. reflexivity.
  reflexivity.
  destruct b.
  destruct H4.
  inversion H4.
      right. split; try reflexivity. intuition. rewrite fin_lt_nat in *. assumption.
  left.
  assert (forall a b c, a ≤ b -> S b = c -> a < c).
      intros. compute. assert (S a ≤ S b). apply le_n_S; eauto.
      rewrite H9 in H10. assumption.
  eapply H8; eauto.

Qed. (* UpdateRoot guarantee (δ n) *)

(** Coq is bad at automatically unfolding uf to an Array, so we give it a hint *)
Global Instance uf_fields {n:nat} : FieldTyping (uf n) (fin _) := array_fields.
Global Instance uf_field_index {n:nat}{T:Set}{f:fin _} : FieldType (uf n) (fin _) f (ref{_|_}[_,_]) :=
  array_field_index.
Definition uf_fielding : forall n f, FieldType (uf n) (t n) f (ref{cell n|any}[local_imm,local_imm]).
  unfold uf. intros. apply @array_field_index.
Defined.

Lemma chase_dec': forall n x h i j, φ n x h -> chase n x h i j \/ ~chase n x h i j.
Proof.
  intros. induction (fin_dec _ i j). subst. left. constructor.
  apply chase_dec; eauto.
Qed.

Definition sameset_chasing {n:nat} i j : hpred (uf n) :=
  λ x h, 
    exists Y,
       chase n x h i Y /\
       chase n x h j Y.
Lemma sameset_chasing_stable :
  forall n i j, stable (@sameset_chasing n i j) (δ n).
Proof.
  intros. red. intros. unfold sameset_chasing in *.
  destruct H as [Y [HiY HjY]].
  induction H0.
  + (* compression *)
    (* If Y-->f (Y below f) or i and j both above f, then unaffected.
          if f is on the path from i or j to Y, then ex Y' that the new stuff points to, and Y-->Y'.
   *) 
    assert (chase n x h Y f -> 
            forall b, chase n x h b Y -> chase n (array_write x f c) h b Y).
        clear H0. clear H1. clear H2. clear H3.
        intros.
        induction H0.
            induction H1. constructor.
            induction (fin_dec _ f i0). subst i0. constructor.
            eapply trans_chase. apply IHchase; eauto.
            rewrite read_past_updated_cell; eauto. 
            induction H1. constructor.
            induction (fin_dec _ f i0).
               subst i0. assert (f = t). eapply Hdouble; eauto. destruct H; eassumption.
                 eapply trans_chase; try eassumption.
                 eapply trans_chase'; try eassumption. auto.
               subst t.
               assert (f = f0). eapply Hdouble; eauto. destruct H; eassumption.
               eapply trans_chase; eauto.
               eapply trans_chase'; eauto. constructor.
               subst f0. constructor.
               
               eapply trans_chase; eauto.
               rewrite read_past_updated_cell; eauto.
               rewrite H3. apply IHchase0; eauto.
               intros.
               specialize (IHchase HiY0 HjY0).
               assert (chase n x h i0 t). eapply trans_chase; eauto.
               specialize (IHchase H5).
               induction (fin_dec _ i0 t). subst i0.
                   assert (t0 = t). eapply Hdouble; eauto. destruct H; eassumption.
                     eapply trans_chase; eauto. constructor.
                   rewrite H6. constructor.
               eapply chase_step; eauto. clear IHchase0.
               rewrite read_past_updated_cell; eauto.

    induction (chase_dec' n x h Y f); eauto.
        exists Y. split; eauto using chase_new_heap.
            
        assert (Y <> f). eauto using no_chase_irrefl.
        destruct H1 as [Y' [Hnochase [HcY' HfY']]].
        assert (getF(h[c]) <> f). eauto using no_chase_irrefl.
        (** When would we need to change the choice of common ancestor?
            For the choice of common ancestor to become invalid, it would require that overwriting f would break either i or j's path to Y, AND that the actual value we overwrite with doesn't restore the path.  So this means we only need to change Y when BOTH of the following hold:
          1. i->f->Y and/or j->f->Y, AND
          2. not (getF(h[c]) -> Y) 

          If neither of i or j reaches f, the i-j-Y triad is either above f (we already checked not(Y->f), so they're not below f),
          below getF(h[c]), or in another set entirely, so the whole of both paths can be reused.

          If i or j reaches f but getF(h[c])->Y, we can reuse the path up until f, then stick on the new (unaffected) path.

          When we are in the case of the write breaking the paths to Y, we know f->Y, f->Y', getF(h[c])->Y', and not(getF(h[c])->Y).
          Clearly Y<>Y'.
          Since f->Y and f->Y', Y->Y' or Y'->Y (new lemma).
          Y'->Y and getF(h[c])->Y' implies getF(h[c])->Y, which is a contradiction, so just Y->Y'. (all in original heap/array)
          This means that i->Y' and j->Y' in the original heap.
          So we can choose Y' as the new common ancestor,
          and reuse the {i,j}->Y' path until we hit f, then tack on the unaffected getF(h[c])->Y' path.

          Now I just have to get the induction structure to work out.
         *)
        induction (chase_dec' n x h (getF(h[c])) Y); try assumption.
            assert (chase n (array_write x f c) h' (getF(h[c])) Y).
                apply chase_new_heap with (h:=h).
                clear H4 H3 H2 HcY' HfY' HiY HjY.
                induction H7. constructor.
                eapply trans_chase.
                eapply IHchase. eapply no_chase_step. apply Hnochase. eapply no_chase_irrefl. eassumption. assumption. assumption. assumption.
                rewrite read_past_updated_cell. assumption.
                assert (i0 <> f). eauto using no_chase_irrefl.
                auto.
            exists Y. split.
                clear dependent j. clear H2 H3 H4.
                induction HiY. constructor.
                specialize (IHHiY H5 H6 H7 H8).
                induction (fin_dec _ f i). subst i.
                    eapply trans_chase. apply H8.
                      rewrite read_updated_cell. arrays h h'. reflexivity.
                    eapply trans_chase. apply IHHiY.
                      rewrite read_past_updated_cell. arrays h h'. auto.
                    assumption.
                clear dependent i. clear H2 H3 H4.
                induction HjY. constructor.
                specialize (IHHjY H5 H6 H7 H8).
                induction (fin_dec _ f i). subst i.
                    eapply trans_chase. apply H8.
                      rewrite read_updated_cell. arrays h h'. reflexivity.
                    eapply trans_chase. apply IHHjY.
                      rewrite read_past_updated_cell. arrays h h'. auto.
                    assumption.

        admit.


  + (* union *) 
    exists Y.
    assert (forall q, q<>x ->
              getF (h[A<|q|>]) = getF (h[(array_write A x c)<|q|>])).
        intros q Hne. 
        rewrite read_past_updated_cell; eauto.
    induction (fin_dec _ i x).
        subst i. 
        Check @getF.
        assert (forall n (x:uf n) h (a b: fin n), chase n x h a b -> getF (h[x<|a|>]) = a -> a = b).
            intros. induction H5. auto. fcong i t. auto.
        assert (x = Y). eapply H5. eassumption. rewrite H. reflexivity. subst x.
        split. constructor.
        clear HiY H0 H1 H5 H3.
        induction (fin_dec _ Y j). subst j. constructor.
        induction HjY. exfalso. auto.
        induction (fin_dec _ f t). subst t.
            eapply trans_chase; try apply H0. constructor. arrays h' h. 
        eapply trans_chase; try apply H0. eapply IHHjY. assumption. assumption. assumption.
        arrays h' h. 

        cut (forall a b, chase n A h a b -> chase n (array_write A x c) h' a b).
        eauto.
        intros. induction H5. constructor.
        induction (fin_dec _ i0 x). subst i0.
            rewrite H in H6. subst t. simpl in H5. simpl in IHchase. assumption.
            eapply trans_chase; eauto. arrays h' h.

  + (* bump rank *) 
    exists Y.
    assert (forall q, 
              getF (h[A<|q|>]) = getF (h[(array_write A x c)<|q|>])).
        intros q. induction (fin_dec _ x q).
        subst q. rewrite read_updated_cell. rewrite H1. rewrite H. reflexivity.
        rewrite read_past_updated_cell; eauto.
    assert (forall n (A:uf n) h x c i j,
                (forall q, getF (h[A<|q|>]) = getF (h[(array_write A x c)<|q|>])) ->
                (chase n A h i j <->
                          chase n (array_write A x c) h i j)).
        intros. split; intros.
        induction H4. constructor.
                eapply trans_chase; eauto.
                rewrite <- H3. assumption.
        induction H4. constructor.
                eapply trans_chase; eauto.
                rewrite H3. assumption.
    repeat rewrite <- H3.
    intuition; eauto using chase_new_heap.
    intros; arrays h' h; eauto.
    intros; arrays h' h; eauto.
  + (* id *) exists Y; intuition; eauto using chase_new_heap.
Grab Existential Variables. exact h. exact h. exact h. exact h.
Qed.
Definition nonroot_rank {n:nat} i (rnk:nat) : hpred (uf n) :=
  λ x h, getF (h[x<|i|>]) <> i /\ getF (h[x<|i|>]) = rnk.
Lemma nonroot_rank_stable : forall n i rnk, stable (nonroot_rank i rnk) (δ n).
Proof.
  intros. red. intros. 
  destruct H.
  induction H0.
  + induction (fin_dec _ f i). red. subst f.
    rewrite read_updated_cell. arrays h h'.
    rewrite <- H2. split; try solve[eauto].
    destruct H3 as [Y [Hno _]]. intro Hbad.
    fold fin in *. rewrite Hbad in Hno.
    apply Hno. constructor.
    red. rewrite read_past_updated_cell. arrays h h'.
    split; eauto. eauto.
  + induction (fin_dec _ x i). subst x. rewrite H0 in H.
    exfalso. apply H. reflexivity.
    red. rewrite read_past_updated_cell; eauto. 
    arrays h h'. split; eauto.
  + induction (fin_dec _ x i). subst x. rewrite H0 in H.
    exfalso. apply H; eauto.
    split; rewrite read_past_updated_cell; arrays h h'; eauto.
  + split; arrays h h'; eauto.
Qed.
Hint Resolve nonroot_rank_stable.


(** *** Find operation *)
Program Definition Find {Γ n} (r:ref{uf (S n)|φ _}[δ _, δ _]) (f:Fin.t (S n)) : rgref Γ (Fin.t (S n)) Γ :=
  RGFix _ _ (fun find_rec f =>
               (*let c : (ref{cell _|any}[local_imm,local_imm]) := (r ~> f) in*)
               observe-field-explicitP (uf_fielding _ _) for r --> f as c, pfc 
                 in (λ x h, sameset_chasing f (getF (h[c])) x h)  (* CAS gives back information *)
                  ⊓ (λ x h, getF(h[c]) ≤ getF(h[x<|(getF(h[c]))|>]))
                  ;
               (*let p := c ~> parent in*)
               observe-field-explicit cell_parent for c --> parent as p, pfp
                 in (λ x h, getF x = p);
               match (fin_beq p f) with
               (*if (fin_beq p f)*)
               (*then*) | true => rgret f
               (*else*) | false => (
                   observe-field-explicit (@cell_rank (S n)) for c --> rank as rnk, pfrnk
                     in (λ x h, getF x = rnk);
                   (* Sequentially: r[f].parent *)
                   observe-field-explicitP (uf_fielding _ _) for r --> p as p_ptr, pf_p_ptr
                     in (λ x h, sameset_chasing p 
                                                (getF (h[p_ptr]))
                                                x h)
                      (* rank(p) ≤ rank(p.parent) *)
                      ⊓ (λ x h, getF(h[p_ptr]) ≤ getF(h[x<|(getF(h[p_ptr]))|>]))
                      ⊓ (λ x h, getF(h[c]) ≤ getF(h[p_ptr]))
                      ⊓ (λ x h, getF(h[p_ptr]) <> p -> nonroot_rank p (getF(h[p_ptr])) x h)
                      ⊓ (λ x h, getF(h[p_ptr]) <> p ->
                                ( (getF(h[p_ptr])) < (getF(h[x<|(getF(h[p_ptr]))|>])) \/ proj1_sig (to_nat p) < proj1_sig (to_nat (getF(h[p_ptr])))))
                      ; (* CAS gives back information *)
                   (* Sequentially: r[r[f].parent].parent *)
                   observe-field-explicit cell_parent for p_ptr --> parent as gparent, pfgp
                                                                                         in (λ x h, getF x = gparent); 
                   c' <- Alloc! (mkCell _ rnk gparent ) ;
                   (*_ <- fCAS( r → f, c, convert_P _ _ _ c');*)
                   _ <- @field_cas_core _ _ _ _ _ _ _ _ r f _ _ c (convert_P _ _ _ c') _;
                   find_rec p
               ) end
            ) f
  .
Next Obligation.
  split.
 red. exists (getF (h[h[r]<|f0|>])).
                 split. eapply trans_chase. constructor. auto.
                        constructor. 
                        

  destruct H0. 
  eapply chase_rank. assumption. eapply trans_chase. constructor. reflexivity.
                        
Qed.
Lemma rank_lb_stable : forall n r i, 
                         stable (λ x h, r ≤ getF (h[x<|i|>]))
                                (δ n).
Proof.
  intros. red. intros.
  induction H0.
  + induction (fin_dec _ f i). 
      subst f. rewrite read_updated_cell. arrays h h'. rewrite <- H1. assumption.
      rewrite read_past_updated_cell; auto. arrays h h'. auto.
  + induction (fin_dec _ x i).
      subst x. rewrite read_updated_cell. arrays h h'. rewrite H1.
        rewrite H0 in H. simpl in H. simpl. eauto with arith.
      rewrite read_past_updated_cell; auto. arrays h h'. auto. 
  + induction (fin_dec _ x i).
      subst x. rewrite read_updated_cell. arrays h h'. rewrite H2.
        rewrite H0 in H. eauto with arith.
      rewrite read_past_updated_cell; auto. arrays h h'. auto.
  + arrays h h'. assumption.
Qed.


Next Obligation. 
  apply pred_and_stable.
red. intros. 
                 assert (Htmp := sameset_chasing_stable _ f0 (getF (h[t])) x x' h h').
                 arrays h h'. apply Htmp; eauto. 

  red. intros. arrays h h'.
  assert (Htmp := rank_lb_stable _ (getF (h'[t])) (getF (h'[t])) x x' h h').
  simpl in Htmp. apply Htmp. arrays h h'. auto. auto.
Qed.
Next Obligation. compute; intros; subst; eauto. Defined.
Next Obligation. compute; intros; subst; eauto. Defined.
 
Next Obligation. 
  split. 
  split.
  split.
  split.

  red. exists (getF (h[h[r]<|p|>])). split. eapply trans_chase. constructor. auto. constructor. 
  eapply chase_rank. destruct H0. assumption. eapply trans_chase. constructor. reflexivity.
  destruct (pfc h). rewrite pfp in H1. assumption.

  intros. red. split. assumption. reflexivity.

  intros. set (p_ptr := h[r]<|p|>). fold p_ptr. fold p_ptr in H.
  assert (getF(h[p_ptr]) ≤ getF (h[h[r]<|getF(h[p_ptr])|>]) ).
    eapply chase_rank. destruct H0. assumption. eapply trans_chase. constructor. reflexivity.
  Require Import Coq.Arith.Lt.
  induction (le_lt_or_eq _ _ H1).
  + left. apply H2.
  + right. destruct H0. eapply chase_rank_strict.
    eassumption. auto.
    Check (trans_chase _ x h p (getF(h[p_ptr])) (getF (h [x <| getF (h [p_ptr]) |>]))).
    Check (trans_chase _ x h p (getF(h[p_ptr])) (getF (h [p_ptr]))).
    assert (asdf := trans_chase _ x h p (getF(h[p_ptr])) (getF (h [p_ptr]))).
    simpl getF at 5 in asdf.
    apply asdf. constructor. reflexivity.
    unfold p_ptr at 1 in H2. simpl getF at 3 in H2. apply H2.
Qed.

Next Obligation. 
  apply pred_and_stable. 
  apply pred_and_stable. 
  apply pred_and_stable.
  apply pred_and_stable.

  red. intros. 
                 assert (Htmp := sameset_chasing_stable _ p (getF (h[t])) x x' h h').
                 arrays h h'. apply Htmp; eauto. 

  red. intros. arrays h h'.
  assert (Htmp := rank_lb_stable _ (getF (h'[t])) (getF (h'[t])) x x' h h').
  simpl in Htmp. apply Htmp. arrays h h'. auto. auto.
  
  red. intros. arrays h h'. assumption.

  intros x x' h h'.
  intros. eapply nonroot_rank_stable; eauto. arrays h h'. apply H. assumption.

  
  red. intros. arrays h h'.
  specialize (H H1).
  induction H0.
  + (* compression *) (* preserves ranks *)
    assert (forall q, @eq nat (getF(h[x<|q|>])) (getF(h[(array_write x f1 c0)<|q|>]))).
        intros. induction (fin_dec _ q f1). subst f1. rewrite read_updated_cell. rewrite <- H2. reflexivity.
        rewrite read_past_updated_cell; eauto.
    unfold getF in H6. unfold cell_rank in H6. arrays h' h. 
    induction H; eauto.
        rewrite <- H6. auto.
  + (* union *) (* if <, <+≤=<. if =, induct on xr≤xr'.*)
    set (qq := getF(f:=parent)(h'[t])).
    unfold getF in qq. unfold cell_parent in qq. fold qq. fold qq in H.
    induction (fin_dec _ x qq).
        rewrite <- a in *. arrays h h'. rewrite H0 in *. rewrite H2.
            induction H. left.  eauto with arith.
                         right. assumption.
        arrays h h'.
  + (* bump rank *) (* same as union case *)
    set (qq := getF(f:=parent)(h'[t])).
    unfold getF in qq. unfold cell_parent in qq. fold qq. fold qq in H.
    induction (fin_dec _ x qq).
        rewrite <- a in *. arrays h h'. rewrite H0 in *. rewrite H3.
            induction H. left.  eauto with arith.
                         right. assumption.
        arrays h h'.
  + (* id *) auto.
Qed.

Next Obligation. compute; intros; subst; eauto. Defined.
Next Obligation. exact any. Defined.
Next Obligation. unfold Find_obligation_16. eauto. Qed.
Next Obligation. intuition. Qed.
Next Obligation. unfold Find_obligation_16. eauto. Qed.

Lemma cellres : forall n, @res (cell n) local_imm local_imm _ = cell n.
intros. simpl. reflexivity.
Defined.

Lemma chase_two_ordering : forall n x h a b c, chase n x h a b ->
                            chase n x h a c ->
                            chase n x h b c \/ chase n x h c b.
Proof.
  intros.

  generalize dependent c.
  induction H.
  + firstorder.
  + intros. induction H1.
    - right. eapply trans_chase; eauto.
    - fcong t0 t.
      apply IHchase. assumption.
Qed.
Lemma chase_append : forall n x h a b c,
                       chase n x h a b ->
                       chase n x h b c ->
                       chase n x h a c.
Proof.
  intros.
  induction H. assumption.
  eapply trans_chase. apply IHchase. assumption. assumption.
Qed.

(*
Definition local_sort {n} i : hpred (uf n) :=
  λ x h, 
  (forall j, terminating_ascent n x h j) ->
  getF (h[x<|i|>]) = i \/
  (
    getF (h[x<|i|>]) ≤ getF (h[x<| getF (h[x<|i|>]) |>]) /\
    (@eq nat (getF (h[x<|i|>])) (getF (h[x<| getF (h[x<|i|>]) |>])) ->
        proj1_sig (to_nat i) < proj1_sig (to_nat (getF (h[x<|i|>])))
     )
  ).
Lemma stable_local_sort : forall n i, stable (local_sort i) (δ n).
Proof.
  intros. red. intros. unfold local_sort in *.
  induction H0; intros.
  + destruct H0. induction (H H0).
    - induction (fin_dec _ f i).
      subst f. rewrite read_updated_cell. right. arrays h h'.
      destruct H2 as [Y [Hno _]].
      assert ((getF (h'[c])) <> i). eapply no_chase_irrefl. eassumption.
      rewrite read_past_updated_cell. firstorder. auto.
      rewrite read_past_updated_cell; auto. arrays h h'. left; auto.
    - induction (fin_dec _ f i). subst f. rewrite read_updated_cell.
      destruct H2 as [Y [Hno _]]. arrays h h'.
      assert ((getF (h'[c])) <> i). eapply no_chase_irrefl. eassumption.
      right. rewrite read_past_updated_cell; auto.
      destruct H6. right.
      rewrite read_past_updated_cell. arrays h h'.
      destruct H2 as [Y [Hno _]]. arrays h h'.
      assert ((getF (h'[c])) <> f). eapply no_chase_irrefl. eassumption.
      assert (forall X, 
                @eq nat (getF (h'[(array_write x f c)<|X|>]))
                        (getF (h'[x<|X|>]))).
          intros. induction (fin_dec _ X f). subst X. rewrite read_updated_cell. auto.
          rewrite read_past_updated_cell; auto.
      rewrite H8. auto. auto.
  + (* union *) 
(*Hint Resolve stable_local_sort.*)
    *)
 
Next Obligation. (* δ *)

  unfold Find_obligation_25 in *.
  unfold Find_obligation_24 in *.
  unfold Find_obligation_23 in *.
  unfold Find_obligation_16 in *.
  (*unfold Find_obligation_14 in *.*)
  symmetry in Heq_anonymous. rewrite fin_beq_neq in Heq_anonymous.
  
  assert (Htmp := heap_lookup2 h r). inversion Htmp; subst.
  
  (* TODO: check out chase_rank, and chase_rank_strict, which will
     directly give the rank/index comparisons for f0 and p.
     Combined with rank/index comparisons for p and gparent,
     that will give us the transitive results for two goals,
     as well as implying the absence of a chase from gparent to f0.
  *)
  assert (getF(h[c']) ≤ getF(h[(h[r]<|gparent|>)])).
      induction (fin_dec _ p gparent).
        (* p/gparent is root *)
        subst gparent. 
        assert (Htmp' := heap_lookup2 h c').
        destruct Htmp'. rewrite H1; eauto. 
        assert (mkCell _ rnk p = h[h[r]<|f0|>]).
            rewrite (cell_ctor_complete _ (h[h[r]<|f0|>])).
            simpl. rewrite pfp. rewrite pfrnk. reflexivity.
        rewrite H2. apply chase_rank. destruct Htmp; auto.
        eapply trans_chase; eauto. rewrite <- H2. constructor.

        destruct (pf_p_ptr h). 
        destruct H0. destruct H0. destruct H0. rewrite pfgp in H4.
        etransitivity; try eassumption.
        rewrite pfrnk in H3. 
        assert (Htmp' := heap_lookup2 h c').
        destruct Htmp'. solve[rewrite H6; eauto].
 
  eapply path_compression. 
  + eauto. (* stray dead rt arg *)
  + assumption.
  + rewrite conversion_P_refeq.
    assert (Htmp' := heap_lookup2 h c'). destruct Htmp'. rewrite H2; eauto.
    solve[compute; eauto].
  + rewrite conversion_P_refeq.  
    assert (Htmp' := heap_lookup2 h c'). destruct Htmp'. rewrite H2; eauto.
    simpl.
    assert (Htmp' := pfc h). destruct Htmp'. red in H3.
    rewrite pfp in H3.
    destruct H3 as [Y [Hf0Y HpY]].
    assert (Htmp' := pf_p_ptr h). red in Htmp'.
    destruct Htmp'. destruct H3.
    destruct H3. destruct H3.
    rewrite pfgp in H3.
    destruct H3 as [Y' [HpY' HgpY']].
    (* TODO: Y = set f and gparent belong to... Still need to prove
       the negative conjunct, though, (not gparent-->f)!
       How should we do this?  Note that the following tempting
       predicate is *not* stable:
           sameset_chasing a b ⊓ λ x h, ~chase n x h a b
       I'm already working on proving the first conjunct
       stable, and it looks completeable.  The second
       conjunct is not stable; a parent getting bumped to point
       past a grandparent right before a grandchild is bumped to
       its grandparent is precisely why we can't just require
       a chase from the updated index to the grandparent
       in the compression case of δ.

    *) 
    assert (~chase _ (h[r]) h gparent f0).
        assert (H3 : True) by auto. (* filler for hoisted code *)
        intro.
        assert (getF(h[h[r]<|gparent|>]) ≤ getF(h[h[r]<|f0|>])).
            eapply chase_rank. assumption. assumption.
        simpl getF at 2 in H10. unfold cell_rank in *. rewrite pfrnk in H10.
        rewrite H2 in H0; eauto.
        assert(rnk = getF(h[h[r]<|gparent|>])).
            eapply le_antisym; eauto.
        rewrite pfrnk in H7. rewrite pfgp in H8. rewrite pfgp in *; eauto.
        induction (fin_dec _ gparent p).
            subst gparent. clear H5 H6. unfold getF in H11. unfold cell_rank in H11.
            rewrite <- H11 in H8.
            assert (rnk = getF(h[p_ptr])).
                eapply le_antisym; eauto.
            assert (proj1_sig (to_nat f0) < proj1_sig (to_nat p)).
                eapply chase_rank_strict. eassumption. auto.
                eapply trans_chase. constructor. 
                unfold getF. unfold cell_parent. rewrite pfp. reflexivity.
                compute. rewrite pfrnk. auto.
            assert (proj1_sig (to_nat p) < proj1_sig (to_nat f0)).
                eapply chase_rank_strict. eassumption. auto.
                assumption.
                unfold getF. unfold cell_rank. rewrite pfrnk. auto.
            eapply lt_asym; eauto.
          (* gparent <> p *)
            specialize (H6 b). red in H6. destruct H6.
            specialize (H5 b).
            rewrite <- H12 in *.
            induction H5.
                assert (getF(h[h[r]<|p|>]) < rnk).
                    rewrite H11. apply H5.
                eapply (lt_not_le); eauto.

                assert (rnk = getF(h[h[r]<|p|>])).
                    unfold getF in H11. unfold cell_rank in H11. rewrite <- H11 in H8. 
                    eapply (le_antisym); eauto.
                assert (proj1_sig (to_nat f0) < proj1_sig (to_nat p)).
                    eapply chase_rank_strict; eauto.
                    eapply trans_chase. constructor. simpl. rewrite pfp.

                    reflexivity.
                    simpl. rewrite pfrnk. apply H13.
                assert (proj1_sig (to_nat f0) < proj1_sig (to_nat gparent)).
                    etransitivity; eauto.
                assert (proj1_sig (to_nat gparent) < proj1_sig (to_nat f0)).
                    eapply chase_rank_strict; eauto.
                    induction (fin_dec _ gparent f0).
                        subst gparent. exfalso. eapply lt_asym; eauto.
                        assumption.
                    simpl. rewrite pfrnk. simpl in H11. auto.
                eapply lt_asym; eauto.

    induction (chase_two_ordering _ (h[r]) h p _ _ HpY HpY').
    exists Y'; intuition; eauto using chase_append.
    exists Y; intuition; eauto using chase_append.

  + rewrite conversion_P_refeq.  
    assert (Htmp' := heap_lookup2 h c'). destruct Htmp'. rewrite H2; eauto.
    rewrite H2 in H0; eauto.
  + rewrite conversion_P_refeq.  
    assert (Htmp' := heap_lookup2 h c'). destruct Htmp'. rewrite H2; eauto.
    intros Hrank2.
    induction (fin_dec _ p gparent).
        subst gparent. eapply chase_rank_strict. eassumption. auto.
        eapply trans_chase. constructor. simpl. rewrite pfp. reflexivity.
        simpl. rewrite pfrnk. simpl in Hrank2. assumption.

        unfold getF at 3 in Hrank2. unfold cell_parent in Hrank2.
        specialize (pf_p_ptr h). destruct pf_p_ptr. destruct H3. destruct H3. destruct H3.
        rewrite pfgp in H5. assert (X : gparent <> p) by auto. specialize (H5 X). red in H5.
        destruct H5. rewrite pfgp in H7. rewrite <- H8 in H6. rewrite <- H8 in H7. rewrite pfrnk in H6. simpl getF at 1 in Hrank2.
        assert (Hconverge : forall a b c, a = c -> a ≤ b -> b ≤ c -> a = b).
            intros. subst a. eapply le_antisym; eauto.
        specialize (Hconverge rnk (getF (h [h [r] <| p |>])) (getF (h [h [r] <| gparent |>])) Hrank2 H6 H7).
        assert (@eq nat (getF (h [h [r] <| p |>])) (getF (h [h [r] <| gparent |>]))).
            simpl. simpl in Hconverge. rewrite <- Hconverge. rewrite Hrank2. reflexivity.
        (* Now we know rank(f)=rank(p)=rank(gparent). Each of these links implies that the indices in question are sorted, which is enough to prove our goal by transitivity. *)
        etransitivity.
        destruct Htmp. (* will need h[r] to unify with a variable before creating existential *)
        eapply sort_equiv_rank. eassumption.
        eapply trans_chase. constructor. simpl. rewrite pfp. reflexivity.
        auto.
        simpl. rewrite pfrnk. apply Hconverge.

        (* this second step of transitivity is a bit trickier.
           we don't know that p.parent=gparent in the current
           heap.  But we do know that if the ranks were equal
           at the time we read out p_ptr, then they're sorted. *)
        simpl.
        rewrite pfgp in H4. specialize (H4 X).
        induction H4.
        rewrite <- H8 in H4. simpl getF at 2 in H9. rewrite <- H9 in H4.
        exfalso. apply (lt_irrefl _ H4).
        assumption.
Qed.



Require Import Coq.Arith.Bool_nat.
Definition gt x y := nat_lt_ge_bool y x.

Definition ignore {Γ Γ' T} (C:rgref Γ T Γ') : rgref Γ unit Γ' :=
  _ <- C;
  rgret tt.
(** *** Union operation *)
Check @getF.
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
  try match goal with
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
               match (fin_beq x y) with
               | true => rgret tt
               | false => (
                   observe-field r --> x as oldx, pfx in (λ A h, getF (h[(array_read A x)]) ≥ getF (h[oldx]));
                   observe-field r --> y as oldy, pfy in (λ A h, getF (h[(A<|y|>)]) ≥ getF (h[oldy]));
                   observe-field-explicit (@cell_rank (S n)) for oldx --> rank as xr, pf in (λ (c:cell _) h, getF (FieldType:=cell_rank) c = xr);
                   observe-field-explicit (@cell_rank (S n)) for oldy --> rank as yr, pf in (λ (c:cell _) h, getF (FieldType:=cell_rank) c = yr);
                   ret <-
                   (match (orb (gt xr yr)
                           (andb (beq_nat xr yr)
                                 (gt (to_nat x) (to_nat y)))) with
                   | true => UpdateRoot r y yr x yr _ 
                   | false => UpdateRoot r x xr y xr _ 
                   end);
                   if ret
                   then TryAgain tt
                   else if (beq_nat xr yr)
                        then ignore (UpdateRoot r y yr y (yr + 1) _)
                        else rgret tt
                   
               )
               end
            )
        tt.
Next Obligation.  eapply uf_cell_increasing_rank. Qed.
Next Obligation.  eapply uf_cell_increasing_rank. Qed.
Next Obligation. compute; intuition; subst; eauto. Qed.
Next Obligation. compute; intuition; subst; eauto. Qed.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Lt.
Next Obligation. 
  (* patch old script: *) rename Heq_anonymous into Hne. rename Heq_anonymous0 into Heq_anonymous.
  symmetry in Heq_anonymous.
  rewrite orb_true_iff in Heq_anonymous. induction Heq_anonymous.
  assert (yr < xr). induction (gt xr yr). induction x1; simpl in H0. eauto with arith. inversion H0.
  right. intuition. assert (yr ≤ xr) by eauto with arith.
      etransitivity; eauto. rewrite <- pf with (h:=h). apply pfx.
      rewrite H2 in H1. rewrite <- pf with (h:=h) in H1.
      assert (Htmp := lt_not_le _ _ H1).
      exfalso. apply Htmp. apply pfx.

  rewrite andb_true_iff in H0. destruct H0.
  right. split. reflexivity.
  assert (xr = yr). apply beq_nat_true. assumption.
  subst xr.
  split.
  rewrite <- pf with (h:=h). apply pfx.
  intros.
  induction (gt (proj1_sig (to_nat x0)) (proj1_sig (to_nat y0))).
  induction x1; simpl in H1.
  rewrite fin_lt_nat in *. assumption.
  inversion H1.
Qed.
Next Obligation. 
  (* patch old script: *) rename Heq_anonymous into Hne. rename Heq_anonymous0 into Heq_anonymous.
  symmetry in Heq_anonymous.
  rewrite orb_false_iff in Heq_anonymous. destruct Heq_anonymous.
  induction (gt xr yr). induction x1; simpl in H0. inversion H0.
  right. split; try reflexivity.
  split.
  etransitivity; try apply p. rewrite <- pf0 with (h:=h). apply pfy.
  intros.
  (* If xr ≤ yr, xr = getF(h[h[r]<|y0|>]), then the current rank of y is ≤ yr,
     by pf0 and pfy, yr ≤ current rank of y, thus they're equal (and thus yr=xr).
     But this then implies by H1 that y0 ≤ x0.,, when we're trying to prove x0 < y0.
  *)
  rewrite fin_lt_nat.
  setoid_rewrite pf0 in pfy. unfold ge in pfy.
  assert (yr ≤ xr). rewrite H2. apply pfy.
  assert (xr = yr). eauto with arith.
  subst yr.
  rewrite andb_false_iff in *.
  induction H1.
      rewrite <- beq_nat_refl in H1. inversion H1.
  induction (gt (proj1_sig (to_nat x0)) (proj1_sig (to_nat y0))).
  induction x1; simpl in H1. inversion H1. red in p0.
  inversion p0.
  assert (forall (a b:t (S n)), proj1_sig (to_nat a) = proj1_sig (to_nat b) -> a = b).
      intros a b.
      Check Fin.rect2.
      eapply Fin.rect2 with (a:=a)(b:=b); eauto.
      intros. rewrite proj1_to_nat_comm in H4. simpl in H4. discriminate H4.
      intros. rewrite proj1_to_nat_comm in H4. simpl in H4. discriminate H4.
      intros. repeat rewrite proj1_to_nat_comm in H6. inversion H6. f_equal. firstorder.
  assert (htmp := H4 _ _ H5). subst x0.
  assert (fin_beq_refl : forall (x:t (S n)), fin_beq x x = true).
    intros X.
    clear pfx pfy pf0 pf Hne. clear p0 H5 H4 H2 oldx oldy r x y y0.
    induction X; try reflexivity.
    simpl. firstorder.
  rewrite fin_beq_refl in *. inversion Hne.
  assert (forall a b c, a ≤ b -> S b = c -> a < c).
      intros. compute. assert (S a ≤ S b). apply le_n_S; eauto.
      rewrite H7 in H8. assumption.
  rewrite H4. firstorder.
Qed.
Next Obligation.
  left. split. reflexivity. eauto with arith.
Qed.
  
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
