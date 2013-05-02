Require Import RGref.DSL.DSL.
Require Import RGref.DSL.Concurrency.

(** Trieber Stack
    A lock-free stack implementation. *)
(** Luckily, we can escape the induction-recursion encoding since
    nodes are constant. *)
Inductive Node : Set :=
  | mkNode : nat -> option (ref{Node|any}[local_imm,local_imm]) -> Node.
Print ImmediateReachability.
Global Instance reach_ts_node : ImmediateReachability Node :=
{ imm_reachable_from_in := fun T P R G r nd =>
                             match nd with (mkNode n tl) =>
                                             imm_reachable_from_in r tl
                             end }.
Print Containment.
Global Instance node_contains : Containment Node :=
{ contains := fun R => True }. (* the recursive refs are heap-agnostic *)
Print rel_fold.
Global Instance node_fold : rel_fold Node :=
{
  rgfold := fun R G => Node; (* Nodes grant no heap mutation permission to reachable state *)
  fold := fun R G nd => nd
}.

(** We'll follow roughly S11.2 of The Art of Multiprocessor Programming:
    a basic Trieber stack, with no backoff or elimination. *)
Inductive deltaTS : hrel (option (ref{Node|any}[local_imm,local_imm])) :=
  | ts_nop : forall n h h', deltaTS n n h h'
  | ts_push : forall n hd hd' h h', h'[hd']=(mkNode n hd) ->
                                    deltaTS hd (Some hd') h h'
  | ts_pop : forall n hd hd' h h', h[hd]=(mkNode n hd') ->
                                   deltaTS (Some hd) hd' h h'.

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

Program Definition alloc_ts {Γ} (u:unit) : rgref Γ ts Γ :=
  Alloc None.

(*Local Obligation Tactic := compute; eauto.*)
Program Definition push_ts {Γ} : ts -> nat -> rgref Γ unit Γ :=
  RGFix2 _ _ _ (fun rec s n =>
    let tl := !s in
    (* Eventually, lift allocation out of the loop, do substructural
       allocation, and strongly update tail until insertion *)
    new_node <- Alloc (mkNode n tl);
    success <- CAS(s,tl,Some (convert new_node (fun v h (pf:v=mkNode n tl) => I)
                                               (rel_sub_refl _ local_imm)
                                               (rel_sub_refl _ local_imm) _ 
                                               (rel_sub_refl _ local_imm)));
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

Program Definition asB T R G B `{rel_fold T} (pf:rgfold R G = B) (b:rgfold R G) : B.
intros. rewrite pf in b. exact b. Defined.
Print asB.

Program Definition pop_ts {Γ} : ts -> rgref Γ (option nat) Γ :=
  RGFix _ _ (fun rec s =>
    match !s with
    | None => rgret None
    | Some hd => match !hd with
                   | mkNode n tl => 
                       success <- CAS(s,Some hd,tl);
                       if success then rgret (Some n) else rec s
                 end
    end).
Next Obligation.
  f_equal. intros. rewrite H. reflexivity.
  eapply (rgref_exchange); try solve[compute; eauto].
  split; red; intros. red in H. destruct H. eauto.
  split; eauto. intros. constructor.
Defined.
Next Obligation. (* Guarantee Satisfaction *)
  (* Need to export a couple assumptions locally inside this lemma:*)
  assert (forall T P R G (r:ref{T|P}[R,G]) B {rf:rel_fold T} rpf (epf:rgfold R G=B), deref rpf epf r = asB R G epf (@fold T _ R G (h[r]))). admit.
  assert (Hs := H _ _ _ _ s). 
  assert (Hhd := H _ _ _ _ hd). 
  erewrite Hhd in Heq_anonymous0. compute in Heq_anonymous0.
  rewrite Hs in Heq_anonymous. (* <-- Can't finish this compute until I fill in admission above. *)
  assert (Htemp : Some hd = h[s]). admit.
  rewrite <- Htemp.
  eapply ts_pop. symmetry. apply Heq_anonymous0.
Qed. 