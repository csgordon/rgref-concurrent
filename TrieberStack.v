Require Import RGref.DSL.DSL.
Require Import RGref.DSL.Concurrency.

(** * Trieber Stack
    A lock-free stack implementation. *)
(** ** Basic heap structure, and rely/guarantee interactions *)
(** Luckily, we can escape the induction-induction encoding since
    nodes are constant. *)
Inductive Node : Set :=
  | mkNode : nat -> option (ref{Node|any}[local_imm,local_imm]) -> Node.
Global Instance reach_ts_node : ImmediateReachability Node :=
{ imm_reachable_from_in := fun T P R G r nd =>
                             match nd with (mkNode n tl) =>
                                             imm_reachable_from_in r tl
                             end }.
Global Instance node_contains : Containment Node :=
{ contains := fun R => True }. (* the recursive refs are heap-agnostic (immutable) *)
(* Nodes grant no heap mutation capabilities ever, so every fold is safe. *)
Global Instance node_fold R G : readable_at Node R G :=
  { res := Node ;
    dofold := fun x => x
  }.

(** We'll follow roughly S11.2 of The Art of Multiprocessor Programming:
    a basic Trieber stack, with no backoff or elimination. *)
Inductive deltaTS : hrel (option (ref{Node|any}[local_imm,local_imm])) :=
  | ts_nop : forall n h h', deltaTS n n h h'
  | ts_push : forall n hd hd' h h', h'[hd']=(mkNode n hd) ->
                                    deltaTS hd (Some hd') h h'
  | ts_pop : forall n hd hd' h h', h[hd]=(mkNode n hd') ->
                                   deltaTS (Some hd) hd' h h'.
(** ** Meta properties of TS-specific rely/guarantee relations *)
Lemma precise_deltaTS : precise_rel deltaTS.
Proof.
  red. intros. induction H1.
  constructor.
  eapply ts_push. rewrite <- H0; eauto. constructor. red. unfold reach_option. constructor.
      red. red. reflexivity.
  eapply ts_pop. rewrite <- H; eauto. constructor. constructor. red. red. reflexivity.
Qed.
Hint Resolve precise_deltaTS.
Lemma hrefl_deltaTS : hreflexive deltaTS.
Proof.
  compute. constructor.
Qed.
Hint Resolve hrefl_deltaTS.

                                                       
Definition ts := ref{option (ref{Node|any}[local_imm,local_imm])|any}[deltaTS,deltaTS].

(** ** Standard operations *)
(** *** Allocating a new stack *)
Program Definition alloc_ts {Γ} (u:unit) : rgref Γ ts Γ :=
  Alloc None.

(*Local Obligation Tactic := compute; eauto.*)
(** *** Push operation *)
Program Definition push_ts {Γ} : ts -> nat -> rgref Γ unit Γ :=
  RGFix2 _ _ _ (fun rec s n =>
    let tl := !s in
    (* Eventually, lift allocation out of the loop, do substructural
       allocation, and strongly update tail until insertion *)
    new_node <- Alloc (mkNode n tl);
    success <- CAS(s,tl,Some (convert new_node (fun v h (pf:v=mkNode n tl) => I)
                                               (rel_sub_refl _ local_imm)
                                               (rel_sub_refl _ local_imm) _ 
                                               (rel_sub_refl _ local_imm) _ _ _));
    if success then rgret tt else rec s n).
Next Obligation.
  f_equal. intros. rewrite H. reflexivity.
  eapply (rgref_exchange); try solve[compute; eauto].
  split; red; intros. red in H. destruct H. eauto.
  split; eauto. intros. constructor.
  Defined.
Next Obligation. (* local identity constraint stable wrt local_imm *)
  compute. intros. subst. rewrite <- H0. reflexivity. Qed.
Next Obligation.
  compute; eauto. Qed.
Next Obligation. (* Guarantee satisfaction! *)
  unfold push_ts_obligation_8.
  eapply ts_push. rewrite <- convert_equiv.
  apply (@heap_lookup2 _ (fun v h => v=mkNode n (!s))).
Qed.

(** *** Pop operation *)
Require Import RGref.DSL.Fields.
Inductive nd_fields : Set := val | nxt.
Instance node_field_type : FieldTyping Node nd_fields.
Instance nxt_type : FieldType Node nd_fields nxt (option (ref{Node|any}[local_imm,local_imm])) :=
{ getF := fun x => match x with (mkNode v tl) => tl end;
  setF := fun x val => match x with (mkNode v tl) => mkNode v val end
}.
Check @getF.
Require Import Utf8.
Axiom stable_option_match :
  forall Γ T Γ' A P R G (r:ref{A|P}[R,G]) F f (FT:FieldTyping A F) 
         (Fx:Set) (FTT:FieldType A F f (option Fx)) Pn Ps,
         stable Pn R ->
         (forall (x:Fx), stable (Ps x) R) ->
         (forall x h, P x h -> @getF _ F FT f _ FTT x = None -> Pn x h) ->
         (forall x h v, P x h -> getF x = Some v -> Ps v x h) ->
         (forall (r':ref{A|Pn}[R,G]), r' ≡ r -> rgref Γ T Γ') ->
         (forall n (r':ref{A|Ps n}[R,G]), r' ≡ r -> rgref Γ T Γ') ->
         rgref Γ T Γ'.
(* How do I generalize this a la Mtac? *)
Notation "'fmatch' r ≫ f 'fwith' | 'None' [[ Pn ]] ==> N | 'Some' x [[ Ps ]] ==> S 'end'" :=
  (stable_option_match _ _ _ _ _ _ _ r _ f _ _ _ Pn Ps _ _ _ _ 
                       (fun r' requiv => N)
                       (fun x r' requiv => S))
    (at level 44).

Local Obligation Tactic := intros; compute; eauto.
Program Definition pop_ts {Γ} : ts -> rgref Γ (option nat) Γ :=
  RGFix _ _ (fun rec s =>
    match !s with
    | None => rgret None
    | Some hd => match !hd with
                   | mkNode n tl => 
                       success <- CAS(s,Some hd,tl);
                       if success then rgret (Some n) else rec s
                 end
                 (*fmatch hd ≫ nxt fwith (* Of course, we don't actually want to match on tl here... *)
                  | None [[ any ]] ==> rgret None
                  | Some tl [[ (λ x v h, getF v = Some x) ]] ==> 
                        (success <- CAS(s,Some hd,tl);
                         if success then rgret (Some _) else rec s)
                  end*)
    end).
Next Obligation.
  f_equal. intros. rewrite H. reflexivity.
  eapply (rgref_exchange); try solve[compute; eauto].
  split; red; intros. simpl in H. destruct H. eauto.
  split; eauto. intros. constructor.
Defined.
Next Obligation. (** Guarantee Satisfaction *)
  (** This code is a bit awkward because Coq doesn't have quite the support we need
      to rework binding appropriately.  We're working atomically here with two assertions
      about the equality of a value and a dereference expression.  Really, these
      matches should not see the equality proofs, but should turn the instantaneous
      property into a stable one, and work with the stable assumption.

      In this case, !s = Some hd isn't needed (h[s] = Some hd) is intro'd by CAS.
      !hd = mkNode n tl legitimately implies h[hd] = mkNode n tl (for all h) because
      hd's rely and guarantee are local_imm.

      First thing we'll do is clean up these context issues.
   *)
  subst filtered_var. subst filtered_var0. 
  assert (forall T P R G (r:ref{T|P}[R,G]) B {rf:readable_at T R G} rpf (epf:res=B), deref rpf epf r = asB epf (dofold (h[r]))) by admit. (*OK*)
  erewrite H0 in Heq_anonymous0. unfold pop_ts_obligation_4 in *. simpl in Heq_anonymous0.
  clear Heq_anonymous.
  clear H0.
  (** Now with the context matching a proper implementation of refining matches... *)
  Set Printing Implicit. idtac.
  fold (@local_imm Node). fold (@any Node). fold (@any (option (ref{Node|any}[local_imm,local_imm]))).
  eapply ts_pop. eauto.
Qed. 