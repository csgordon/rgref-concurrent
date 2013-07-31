Require Import RGref.DSL.DSL.
Require Import RGref.DSL.Concurrency.
Require Import RGref.DSL.Fields.

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

Section FinResults.

Definition fin_beq {n:nat} (x y:Fin.t n) : bool :=
  Fin.rect2 (fun _ _ _ => bool)
            (* F1 F1 *) (fun _ => true)
            (* F1 FS *) (fun _ _ => false)
            (* FS F1 *) (fun _ _ => false)
            (* FS FS *) (fun _ _ _ rec => rec) x y.

Lemma fin_beq_eq : forall n x y, @fin_beq n x y = true <-> x = y.
Proof.
  intros. split; intros.
  Require Import Coq.Program.Equality.
  (* -> *) induction x; dependent induction y; try reflexivity; try inversion H.
           rewrite (IHx y H1). reflexivity.
  (* <- *) induction x. inversion y; subst; simpl; reflexivity.
                        inversion y; subst. unfold fin_beq in *. simpl in *. eapply IHx. reflexivity.
                        unfold fin_beq in *; simpl in *. eapply IHx. reflexivity.
Qed.
Definition fin_lt {n:nat} (x y:Fin.t n) : bool :=
  Fin.rect2 (fun _ _ _ => bool)
            (* F1 F1 *) (fun _ => false)
            (* F1 FS *) (fun _ _ => true)
            (* FS F1 *) (fun _ _ => false)
            (* FS FS *) (fun _ _ _ rec => rec) x y.
Program Lemma proj1_to_nat_comm : forall n (x:t n), proj1_sig (to_nat (FS x)) = S (proj1_sig (to_nat x)).
Proof.
  intros.
 induction x. compute. reflexivity. rewrite IHx. 
 simpl. induction (to_nat x). simpl. reflexivity.
Qed.
Program Lemma fin_lt_nat : forall n (x y:Fin.t n), @fin_lt n x y = true <-> (to_nat x) < to_nat y.
Proof.
  intros. split.
  Check Fin.rect2.
  eapply Fin.rect2 with (a := x) (b := y); intros.
      inversion H. 
      induction f. simpl. auto with arith. rewrite proj1_to_nat_comm. compute. auto with arith.
      inversion H.
      induction f. repeat rewrite proj1_to_nat_comm. auto with arith.
      rewrite proj1_to_nat_comm. rewrite (@proj1_to_nat_comm _ g).
      auto with arith.
  (* <- *)
  eapply Fin.rect2 with (a := x) (b := y); intros; try solve[inversion H].
      compute; auto.
      simpl. apply H. repeat rewrite proj1_to_nat_comm in H0. inversion H0. constructor. subst. auto with arith.
Qed.

End FinResults.
  
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
Inductive φ (n:nat) : hpred (uf n) :=
  pfφ : forall x h,
          (forall i, terminating_ascent n x h i) ->
          φ n x h.

Lemma ascent_root : forall n x h i, terminating_ascent n x h i -> exists r, root n x h i r.
Proof.
  intros. induction H. exists i; constructor; eauto.
  destruct IHterminating_ascent. exists x0. eapply trans_root; eauto.
Qed.

Inductive δ (n:nat) : hrel (uf n) :=
    (* Technically this permits path extension as well as path compression...
       and permits creating a cycle... *)
  | path_compression : forall x f c h h' (rt:Fin.t n),
                         root n x h f rt ->
                         root n x h (getF (h[c])) rt ->
                         δ n x (array_write x f c) h h'
  (* Union sets the parent and rank of a self-parent *)
  | path_union : forall A x xp xr c h h' y xr' yr yp,
                   root n A h x x ->
                   h[(array_read A x)] = mkCell n xr xp ->
                   h[c] = mkCell n xr' y ->
                   h[(array_read A y)] = mkCell n yr yp ->
                   xr < yr \/ (xr=yr /\ (proj1_sig (to_nat x) < proj1_sig (to_nat y))) ->
                   δ n A (array_write A x c) h h'
.
                         
Axiom stable_φ_δ : forall n, stable (φ n) (δ n).
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
Lemma precise_δ : forall n, precise_rel (δ n).
Admitted.
Hint Resolve precise_φ precise_δ.
Lemma refl_δ : forall n, hreflexive (δ n).
Proof.
  intros; red; intros.
  induction n. (* 0-sized array.... useless, but illegal? *) admit.
  rewrite <- (array_id_update x (@F1 _)) at 2 .
  (* TODO: This seems to require knowledge that x is wf *) assert (φ _ x h) by admit.
  inversion H; subst. specialize (H0 (@F1 _)).
  assert (Htmp := ascent_root _ _ _ _ H0). destruct Htmp.
  eapply path_compression; try eassumption.
  induction H1.
  rewrite H1. eapply self_root; eauto.
  rewrite H2. assumption.
Qed.
  
Hint Resolve refl_δ.

Program Definition alloc_uf {Γ} (n:nat) : rgref Γ (ref{uf n|φ n}[δ n, δ n]) Γ :=
  arr <- indep_array n (fun i pf => Alloc (mkCell n 0 (of_nat_lt pf)));
  Alloc arr.
Next Obligation.
  (* Prove φ of the initial array.  Need the array allocation to expose some summary of the
     initialization process, something like making the result of the allocation function
     depend on the index, together with a conversion that weakens that result (like loosening
     a refinement that the parent pointer is the cell number initially) and some way to
     stitch those together for an array-wide refinement... *)
Admitted.

(* This will show up with any array read. *)
Lemma uf_folding : forall n, rgfold (δ n) (δ n) = Array n (ref{cell n|any}[local_imm,local_imm]).
Proof.
  intros. simpl.
  f_equal. eapply rgref_exchange; try solve [compute; eauto].
  split; red; intros.
      destruct H; auto.
      split; auto. intros. inversion H; subst.
      (* Need to destruct an application of ascent_root... *)
      eapply path_compression; try  rewrite array_id_update.
Admitted.
Hint Resolve uf_folding.
Hint Extern 4 (rgfold _ _ = Array _ _) => apply uf_folding.
Hint Extern 4 (Array _ _ = Array _ _) => apply uf_folding.

Require Import Coq.Arith.Arith.
Program Definition UpdateRoot {Γ n} (A:ref{uf n|φ n}[δ n, δ n]) (x:Fin.t n) (oldrank:nat) (y:Fin.t n) (newrank:nat) : rgref Γ bool Γ :=
  let old := (A ~> x) in
  if (orb (negb (fin_beq (@field_read _ _ _ _ _ _ _ _ _ _ old parent _ _) (*old ~> parent*) x))
          (negb (beq_nat (@field_read _ _ _ _ _ _ _ _ _ _ old rank _ (@cell_rank n)) (*old~>rank*) oldrank)))
  then rgret false
  else (
      new <- alloc any local_imm local_imm (mkCell n newrank y) _ _ _ _ _ _; (*Alloc (mkCell n newrank y);*)
      fCAS(A → x, old, new)
  )
.
Next Obligation. (* TODO: UpdateRoot doesn't carry enough information yet to prove δ.
                    Maybe we need to refine something (A? old?) to say x is not its own parent,
                    in such a way as to provide enough information to prove the union case of δ. *)
Admitted.

(* TODO: Path compression *)
Program Definition Find {Γ n} (r:ref{uf n|φ n}[δ n, δ n]) (f:Fin.t n) : rgref Γ (Fin.t n) Γ :=
  RGFix _ _ (fun find_rec f =>
               let c : (ref{cell n|any}[local_imm,local_imm]) := (r ~> f) in
               let p := c ~> parent in
               if (fin_beq p f)
               then rgret f
               else (
                   c' <- Alloc! (mkCell n (let _ := @cell_rank n in c ~> rank) 
                                         ((@field_read _ _ _ _ _ _ _ _ (uf_folding n) _ r p _ _) ~> parent ) ) ;
                   _ <- fCAS( r → f, c, convert_P _ _ _ c');
                   find_rec p
               )
            ) f
  .
Next Obligation. exact any. Defined.
Next Obligation. unfold Find_obligation_5. eauto. Qed.
Next Obligation. intuition. Qed.
Next Obligation. unfold Find_obligation_5. eauto. Qed.

Axiom field_projection_commutes : 
    forall h F T P R G Res (r:ref{T|P}[R,G]) f
           (rf:rel_fold T) (rgf:@rgfold T rf R G = T) (hrg:hreflexive G) (ftg:FieldTyping T F) (ft:FieldType T F f Res),
      @eq Res (@getF T F _ f _ _ (eq_rec _ (fun x => x) (@fold T rf R G (h[r])) T rgf))
              (@field_read T T F Res P R G rf rgf hrg r f ftg ft).
Axiom field_projection_commutes' : 
    forall h F T P R G Res (r:ref{T|P}[R,G]) f
           (rf:rel_fold T) (rgf:@rgfold T rf R G = T)
           `(forall x, (eq_rec _ (fun x => x) (fold x) T rgf) = x)
           (hrg:hreflexive G) (ftg:FieldTyping T F) (ft:FieldType T F f Res),
      @eq Res (@getF T F _ f _ _ (h[r]))
              (@field_read T T F Res P R G rf rgf hrg r f ftg ft).
Check field_projection_commutes'.
      
Next Obligation.
  unfold Find_obligation_5 in *.
  assert (Htmp := heap_lookup2 h r). inversion Htmp; subst.
  edestruct ascent_root. apply H.
  eapply path_compression.  eassumption.
  rewrite conversion_P_refeq.
  assert (Htmp' := heap_lookup2 h c'). destruct Htmp'. rewrite H3; eauto. simpl @getF.

  inversion H1.
      subst f0.
      assert (forall zz,
                @field_read _ _ _ _ _ _ _ _ zz (@local_imm_refl _) 
                 (@field_read _ _ _ _ _ _ _ _ (uf_folding n) (refl_δ n) r x _ (@array_field_index n _ x))
               parent _ (@cell_parent n) = x).
          intros. rewrite <- field_projection_commutes' with (h := h) (f := parent).
                  rewrite <- field_projection_commutes' with (h := h) (f := x).
                  apply H4.
                  (* Can't induct / destruct / invert on zz *) admit. admit.
      rewrite H5. rewrite H5. apply self_root. assumption.

      subst r0.
      assert (forall zz,
                @field_read _ _ _ _ _ _ _ _ zz (@local_imm_refl _) 
                 (@field_read _ _ _ _ _ _ _ _ (uf_folding n) (refl_δ n) r f0 _ (@array_field_index n _ f0))
               parent _ (@cell_parent n) = t).
          (* TODO: missing connection  getF (h[X]) = X ~> F for some X and F. *) admit.
      rewrite H6. 

      inversion H4.
          subst t.
          assert (forall zz,
                    @field_read _ _ _ _ _ _ _ _ zz (@local_imm_refl _) 
                     (@field_read _ _ _ _ _ _ _ _ (uf_folding n) (refl_δ n) r x _ (@array_field_index n _ x))
                   parent _ (@cell_parent n) = x).
              (* TODO: missing connection  getF (h[X]) = X ~> F for some X and F. *) admit.
          rewrite H5. constructor. assumption.
          subst r0.
          assert (forall zz,
                    @field_read _ _ _ _ _ _ _ _ zz (@local_imm_refl _) 
                     (@field_read _ _ _ _ _ _ _ _ (uf_folding n) (refl_δ n) r t _ (@array_field_index n _ t))
                   parent _ (@cell_parent n) = t0).
              (* TODO: missing connection  getF (h[X]) = X ~> F for some X and F. *) admit.
          rewrite H9. assumption.
Qed.
(* Alternative approach... Unsure if the getF (h[X]) = X ~> F are provable or sound axioms that should
   come from somewhere (either above or below)...

  induction H1.
  assert (root n (h[r]) h i i). constructor. assumption.
  eapply trans_root. eassumption. 
      rewrite <- H1. repeat f_equal. rewrite H1. rewrite H0 in H1.
      inversion H4. clear H6. 
      unfold Find_obligation_1  in *.
      unfold Find_obligation_2  in *.
      unfold Find_obligation_3  in *.
      unfold Find_obligation_4  in *.
      unfold Find_obligation_5  in *.
      unfold Find_obligation_11 in *.
      unfold Find_obligation_12 in *.
      unfold Find_obligation_13 in *.
      unfold Find_obligation_14 in *.
      unfold Find_obligation_15 in *.
      assert (forall x,
                @field_read _ _ _ _ _ _ _ _ x (@local_imm_refl _) 
                 (@field_read _ _ _ _ _ _ _ _ (uf_folding n) (refl_δ n) r i _ (@array_field_index n _ i))
               parent _ (@cell_parent n) = i).
          (* TODO: missing connection  getF (h[X]) = X ~> F for some X and F. *) admit.
      rewrite H6. apply H6.
      assert (forall x,
                @field_read _ _ _ _ _ _ _ _ x (@local_imm_refl _) 
                 (@field_read _ _ _ _ _ _ _ _ (uf_folding n) (refl_δ n) r i _ (@array_field_index n _ i))
               parent _ (@cell_parent n) = i).
          (* TODO: missing connection  getF (h[X]) = X ~> F for some X and F. *) admit.
      rewrite H8. apply H8.

      (* We now know that i's parent is t, and t's parent is t. *)
      assert (t=i). 
          (* TODO: I'm not 100% certain this is true... *)
          admit.
      rewrite H5 in *.
      eapply IHroot; eauto.
Qed. *)
(*
      eapply trans_root. eapply IHroot.
      (* Missing connection between h[r]<|X|>=r~>X *) admit.
      trivial. intros.
      specialize (IHroot c').
      apply IHroot.


simpl. simpl in H1
simpl in H1.
  eapply (trans_root _ _ _ _ ((@field_read _ _ _ _ _ _ _ _ (uf_folding n) _ r f0 _ _) ~> parent)).
  eapply trans_root. apply H1. simpl.
  simpl.
  (* TODO: ... *)
Admitted.
*)

Require Import Coq.Arith.Bool_nat.
Definition gt x y := nat_lt_ge_bool y x.

Definition ignore {Γ Γ' T} (C:rgref Γ T Γ') : rgref Γ unit Γ' :=
  _ <- C;
  rgret tt.

Program Definition union {Γ n} (r:ref{uf n|φ n}[δ n, δ n]) (x y:Fin.t n) : rgref Γ unit Γ :=
  RGFix _ _ (fun TryAgain _ =>
               x' <- Find r x;
               y' <- Find r y;
               if (fin_beq x' y')
               then rgret tt
               else (
                   (* TODO: revisit for non-atomic multiple reads, sequencing *)
                   xr <- rgret (@field_read _ _ _ _ _ _ _ _ _ _
                                          (@field_read _ _ _ _ _ _ _ _ (uf_folding n) _ r x (@array_fields n _) (@array_field_index n _ x))
                                          rank _ (@cell_rank n));
                   yr <- rgret (@field_read _ _ _ _ _ _ _ _ _ _
                                          (@field_read _ _ _ _ _ _ _ _ (uf_folding n) _ r y (@array_fields n _) (@array_field_index n _ y))
                                          rank _ (@cell_rank n));
                   _ <-
                   (if (orb (gt xr yr)
                           (andb (beq_nat xr yr)
                                 (gt (to_nat x) (to_nat y))))
                   then _ (* TODO: Swap(x,y); Swap(xr,yr); <-- Is this updating imperative variables? *)
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
  
Program Definition Sameset {Γ n} (A:ref{uf n|φ n}[δ n,δ n]) x y :=
  RGFix _ _ (fun TryAgain _ =>
               x <- Find A x;
               y <- Find A y;
               if (fin_beq x y)
               then rgret true
               else (if fin_beq ((@field_read _ _ _ _ _ _ _ _ (@uf_folding n) _ A x _ (@array_field_index n _ x)) ~> parent) x
                     then @rgret Γ _ false
                     else TryAgain tt)
            ) tt.
