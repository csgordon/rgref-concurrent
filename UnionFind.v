Require Import RGref.DSL.DSL.
Require Import RGref.DSL.Concurrency.
Require Import RGref.DSL.Fields.
Require Import FinResults.

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
Inductive root (n:nat) (x:uf n) (h:heap) (i:Fin.t n) : Fin.t n -> Prop :=
  | self_root : (getF (h[x<|i|>])) = i ->
                root n x h i i
  | trans_root : forall t r,
                   root n x h t r ->
                   (getF (h[x<|i|>])) = t ->
                   root n x h i r.

Inductive terminating_ascent (n:nat) (x:uf n) (h:heap) (i:Fin.t n) : Prop :=
  | self_ascent : (getF (h[x <| i |>])) = i ->
                  terminating_ascent n x h i
  | trans_ascent : terminating_ascent n x h (getF (h[x <| i |>])) ->
                   terminating_ascent n x h i.

Inductive chase (n:nat) (x:uf n) (h:heap) (i:Fin.t n) : Fin.t n -> Prop :=
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

Lemma ascent_root : forall n x h i, terminating_ascent n x h i -> exists r, root n x h i r.
Proof.
  intros. induction H. exists i; constructor; eauto.
  destruct IHterminating_ascent. exists x0. eapply trans_root; eauto.
Qed.
Lemma root_ascent : forall n x h i rt, root n x h i rt -> terminating_ascent n x h i.
Proof.
  intros. induction H. constructor; eauto.
  apply trans_ascent. rewrite H0. auto.
Qed.    
(** ** Change relations and meta properties. *)
Inductive δ (n:nat) : hrel (uf n) :=
  | path_compression : forall x f c h h' (rt:Fin.t n),
                         φ n x h ->
                         root n x h f rt ->
                         root n x h (getF (h[c])) rt ->
                         (* The chase assumption means we're not permuting reachability,
                            which means we're not introducing a cycle. *)
                         chase n x h f (getF (h[c])) ->
                         δ n x (array_write x f c) h h'
  (** Union sets the parent and rank of a self-parent *)
  | path_union : forall A x xr c h h' y xr' yr,
                   (*root n A h x x ->
                   root n A h y y -> (* MAYBE *)*)
                   h[(array_read A x)] = mkCell n xr x ->
                   h[c] = mkCell n xr' y ->
                   h[(array_read A y)] = mkCell n yr y ->
                   xr < yr \/ (xr=yr /\ (proj1_sig (to_nat x) < proj1_sig (to_nat y))) ->
                   δ n A (array_write A x c) h h'
.

Lemma stable_φ_δ : forall n, stable (φ n) (δ n).
Proof.
  intros. red. intros.
  induction H0.
  (* Compression *)
      destruct H. constructor. intros. 
      (*induction (fin_dec n f i). subst f. *) admit.
  (* Union *)
      destruct H. constructor. intros.
      assert (x = y -> False).
          intros Hbad. subst. rewrite H2 in H0.
          assert (Hcontra : forall x, x < x -> False) by admit.
          inversion H0; subst.
          induction H3. firstorder. destruct H3. firstorder.

      rewrite immutable_vals with (h' := h') in H1.

      assert (Hx_ascent : terminating_ascent n (array_write x0 x c ) h' x).
         apply trans_ascent. rewrite read_updated_cell. rewrite H1. simpl.
         rewrite immutable_vals with (h' := h') in H2.
         apply self_ascent. simpl. rewrite read_past_updated_cell; auto. rewrite H2. auto.

      induction (fin_dec n x i). subst i.
      apply Hx_ascent.
      induction (H i).
        apply self_ascent. rewrite read_past_updated_cell; auto.
            rewrite immutable_vals with (h' := h') in H5; assumption.
        rewrite immutable_vals with (h' := h') in t.
        rewrite immutable_vals with (h' := h') in IHt.
        induction (fin_dec n x (getF (h'[x0<|i|>]))).
            apply trans_ascent. rewrite read_past_updated_cell; auto.
            rewrite <- a. assumption.

        apply trans_ascent. rewrite read_past_updated_cell; auto.
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
Qed.
Lemma precise_root : forall n i j, precise_pred (fun x h => root n x h i j).
Proof.
  intros. red. intros.
  induction H. constructor. rewrite H0 in H. auto.
      repeat constructor. repeat red. exists i. repeat red. reflexivity.
      eapply trans_root. apply IHroot. rewrite <- H0. auto.
      repeat constructor. repeat red. exists i. repeat red. reflexivity.
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
    assert (H' := precise_root). red in H'.
    eapply path_compression. 
    assert (Htmp := precise_φ n). red in Htmp. eapply Htmp. apply H1. auto.
        eauto. rewrite immutable_fields with (h' := h). 
        eapply (precise_root n). eauto. eauto.
    eapply precise_chase. rewrite immutable_vals with (h' := h). eassumption.
    eauto.

    rewrite H in H1. rewrite (immutable_vals _ _ h h2) in H2. rewrite H in H3.
    eapply path_union; eauto. 
    constructor. repeat red. exists y. compute; reflexivity.
    constructor. repeat red. exists x. compute; reflexivity.
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
  intros; red; intros.
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
Program Definition UpdateRoot {Γ n} (A:ref{uf (S n)|φ _}[δ _, δ _]) (x:Fin.t (S n)) (oldrank:nat) (y:Fin.t (S n)) (newrank:nat) : rgref Γ bool Γ :=
  (*let old := (A ~> x) in*)
  old <- rgret (A ~> x) ;
  (*
  if (orb (negb (fin_beq (@field_read _ _ _ _ _ _ _ _ _ _ old parent _ _) (*old ~> parent*) x))
          (negb (beq_nat (@field_read _ _ _ _ _ _ _ _ _ _ old rank _ (@cell_rank n)) (*old~>rank*) oldrank)))
*)
  match (orb (negb (fin_beq (@field_read _ _ _ _ _ _ _ _ _ _ old parent _ _) (*old ~> parent*) x))
          (negb (beq_nat (@field_read _ _ _ _ _ _ _ _ _ _ old rank _ (@cell_rank (S n))) (*old~>rank*) oldrank)))
  with
  (*then*) |true => rgret false
  (*else*)|false=> (
      new <- alloc' any local_imm local_imm (mkCell (S n) newrank y) _ _ _ _ _ _; (*Alloc (mkCell n newrank y);*)
      fCAS(A → x, old, convert new _ _ _ _ _ _ _ _)
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
  Axiom cell_ctor_complete : forall n (c:cell n), c = mkCell _ (getF c) (getF c).
  rewrite (cell_ctor_complete _ (h[ _ ])).
  f_equal; eauto.

  rewrite <- convert_equiv. apply H0. firstorder.

  (** TODO: We don't really need to know that y's rank and parent have
      certain values, and in fact we can't know that since y may be
      reparented between the invocation of UpdateRoot and the success
      of the CAS.  What we should be able to know, and what should
      be sufficient to preserve acyclicity, is a bound on y's rank.
      We really don't need to know the parent.

      I THINK it's the case that the rank only ever increases.  But
      there's no good reference to refine for introducing the bound.
      We're CASing at index x, which is likely unrelated to y (so no
      2fCAS), so refining a ref to the old A~>y is no good.
      Refining the array ref A itself is possible, but sounds hideous.

*)

Admitted. (* UpdateRoot guarantee (δ n) *)

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
                   _ <- fCAS( r → f, c, convert_P _ _ _ c');
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
  edestruct ascent_root. apply H.
  eapply path_compression.  eassumption. eassumption.
  rewrite conversion_P_refeq.
  assert (Htmp' := heap_lookup2 h c'). destruct Htmp'. rewrite H3; eauto. simpl @getF.

      unfold Find_obligation_8. unfold Find_obligation_9.
      unfold Find_obligation_10. unfold Find_obligation_3.
      unfold Find_obligation_4. unfold Find_obligation_1.
      unfold Find_obligation_2.
  inversion H1.
      subst f0.
      assert (
                @field_read _ _ _ _ _ _ _ _ (cellres _) (@local_imm_refl _) 
                 (@field_read _ _ _ _ _ _ _ _ (uf_folding _) (refl_δ _) r x _ (@array_field_index _ _ x))
               parent _ (@cell_parent _) = x).
          intros. rewrite <- field_projection_commutes' with (h := h) (f := parent).
                  rewrite <- field_projection_commutes' with (h := h) (f := x).
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
    
    erewrite <- field_projection_commutes' with (h:=h)(f:=parent); eauto.

    Focus 2.
    rewrite H0. erewrite field_projection_commutes' with (h:=h). reflexivity.
    simpl; eauto.
    
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
Program Definition union {Γ n} (r:ref{uf (S n)|φ _}[δ _, δ _]) (x y:Fin.t (S n)) : rgref Γ unit Γ :=
  RGFix _ _ (fun TryAgain _ =>
               x' <- Find r x;
               y' <- Find r y;
               if (fin_beq x' y')
               then rgret tt
               else (
                   (** TODO: revisit for non-atomic multiple reads, sequencing *)
                   xr <- rgret (@field_read _ _ _ _ _ _ _ _ _ _
                                          (@field_read _ _ _ _ _ _ _ _ (uf_folding (S n)) _ r x (@array_fields (S n) _) (@array_field_index (S n) _ x))
                                          rank _ (@cell_rank (S n)));
                   yr <- rgret (@field_read _ _ _ _ _ _ _ _ _ _
                                          (@field_read _ _ _ _ _ _ _ _ (uf_folding (S n)) _ r y (@array_fields (S n) _) (@array_field_index (S n) _ y))
                                          rank _ (@cell_rank (S n)));
                   _ <-
                   (if (orb (gt xr yr)
                           (andb (beq_nat xr yr)
                                 (gt (to_nat x) (to_nat y))))
                   then _ (** TODO: Swap(x,y); Swap(xr,yr); <-- Is this updating imperative variables? *)
                   else rgret tt) ;
                   ret <- UpdateRoot r x xr y yr;
                   if ret
                   then TryAgain tt
                   else if (beq_nat xr yr)
                        then ignore (UpdateRoot r y yr y (yr + 1))
                        else rgret tt
                   
               )
            )
        tt.
  
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