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
Inductive δ (n:nat) : hrel (uf n) :=
    (* Technically this permits path extension as well as path compression... *)
  | path_compression : forall x f c h h' (rt:Fin.t n),
                         root n x h f rt ->
                         root n x h (getF (h[c])) rt ->
                         δ n x (array_write x f c) h h'
  (* | path_union : ... need to review how rank is used *)
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
Axiom precise_δ : forall n, precise_rel (δ n).
Hint Resolve precise_φ precise_δ.
Axiom refl_δ : forall n, hreflexive (δ n).
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
      split; auto. intros. inversion H; subst. rewrite array_id_update.
      (* Hmm, this ought to be true... should depend on δ's defn, and δ should be local... *) admit.
Qed.
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
      new <- alloc any local_imm local_imm (mkCell n newrank y) _ _ _ _ _ ; (*Alloc (mkCell n newrank y);*)
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
               else find_rec p
            ) f
  .

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
  
