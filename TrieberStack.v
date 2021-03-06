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
Require Import RGref.DSL.Fields.
Inductive nd_fields : Set := val | nxt.
Instance node_field_type : FieldTyping Node nd_fields.
Instance nxt_type : FieldType Node nd_fields nxt (option (ref{Node|any}[local_imm,local_imm])) :=
{ getF := fun x => match x with (mkNode v tl) => tl end;
  setF := fun x val => match x with (mkNode v tl) => mkNode v val end
}.
Instance val_type : FieldType Node nd_fields val nat :=
{ getF := fun x => match x with (mkNode v tl) => v end;
  setF := fun x val => match x with mkNode v tl => mkNode val tl end
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
    tl <- !s;
    (* Eventually, lift allocation out of the loop, do substructural
       allocation, and strongly update tail until insertion *)
    (* For some reason the AllocNE notation isn't parsing here... *)
    new_node_pf <- (allocne _ _ _ (mkNode n tl) _ _ _ _ _ _ s);
    (*new_node_pf <- (AllocNE (mkNode n tl) s);*)
    let (new_node, nn_ne_s) := new_node_pf in        
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
  eapply ts_push.  rewrite <- convert_equiv.
  Check @heap_lookup2.
  assert (tmp := @heap_lookup2 _ (fun v _ => v=mkNode n ((h[s]))) local_imm local_imm h new_node).
  simpl in tmp.
  rewrite <- tmp. unfold ts in s.
  (* We know new_node and s are not equal, since we allocated new_node with AllocNE while s existed *)
  apply non_ptr_eq_based_nonaliasing. assumption.
Qed.

(** *** Pop operation *)

Require Import Utf8.
Local Obligation Tactic := intros; compute; try subst; intuition; eauto with typeclass_instances.
Program Definition pop_ts {Γ} : ts -> rgref Γ (option nat) Γ :=
  RGFix _ _ (fun rec s =>
    head <- !s;
    match head with
    | None => rgret None
    | Some hd => 
                 observe-field hd --> val as n, pf in (fun a h => @eq nat (getF a) n);
                 (* making the @eq type explicit causes 5 more goals to be auto solved! *)
                 observe-field hd --> nxt as tl', pf' in (fun a h => @eq (option _) (getF a) tl');
                 success <- CAS(s,Some hd,tl');
                 if success then rgret (Some n) else rec s
    end).
Next Obligation. (* options equivalent... *)
  f_equal. intros. rewrite H. reflexivity.
  eapply (rgref_exchange); try solve[compute; eauto].
  split; red; intros. simpl in H. destruct H. eauto.
  split; eauto. intros. constructor.
Defined.
Next Obligation. (* refining hd stability *)
  intros. subst. auto.
Defined.
Next Obligation. (* refining hd stability *)
  intros. subst. auto.
Defined.
Next Obligation. (** Guarantee Satisfaction *)
  eapply ts_pop. 
  assert (field_inj : forall nd, nd = mkNode (getF nd) (getF nd)).
      intros. destruct nd. reflexivity.
  rewrite (field_inj (h[hd])). rewrite pf. rewrite pf'. reflexivity.
Qed.

 
