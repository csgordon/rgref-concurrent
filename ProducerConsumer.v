Require Import RGref.DSL.DSL.
Require Import RGref.DSL.Concurrency.
Require Import TrieberStack.
Require Import Utf8.


Inductive consume : hrel (option (ref{Node|any}[local_imm,local_imm])) :=
  | consume_nop : forall n h h', consume n n h h'
  | consume_pop : forall n hd hd' h h', h[hd]=(mkNode n hd') -> consume (Some hd) (hd') h h'.

Inductive produce : hrel (option (ref{Node|any}[local_imm,local_imm])) :=
  | produce_nop : forall n h h', produce n n h h'
  | produce_push : forall n hd hd' h h', h'[hd']=(mkNode n hd) ->
                                         produce hd (Some hd') h h'.

Lemma precise_consume : precise_rel consume.
Proof.
  red. intros. induction H1; try solve[constructor].
  econstructor. rewrite <- H; eauto. constructor. simpl. constructor. simpl. reflexivity.
Qed.
Lemma precise_produce : precise_rel produce.
Proof.
  red. intros. induction H1; try solve[constructor].
  econstructor. rewrite <- H0; eauto. constructor. simpl. constructor. simpl. reflexivity.
Qed.

Lemma hrefl_consume : hreflexive consume.
Proof.
  constructor.
Qed.
Lemma hrefl_produce : hreflexive produce.
Proof.
  constructor.
Qed.
Hint Resolve precise_produce precise_consume hrefl_consume hrefl_produce.

(* consume and produce are (trivially) subrelations of deltaTS *)
Lemma consume_deltaTS : consume ⊆ deltaTS.
Proof.
  red; intros.
  induction H; econstructor; eauto.
Qed.
Lemma produce_deltaTS : produce ⊆ deltaTS.
Proof.
  red; intros. induction H; econstructor; eauto.
Qed.
Hint Resolve consume_deltaTS produce_deltaTS.

Definition producer := ref{option (ref{Node|any}[local_imm,local_imm])|any}[deltaTS,produce].
Definition consumer := ref{option (ref{Node|any}[local_imm,local_imm])|any}[deltaTS,consume].

Program Definition consumer_of_ts (s : ts) : consumer :=
  convert s _ _ _ _ _ _ _ _.
Program Definition producer_of_ts (s : ts) : producer :=
  convert s _ _ _ _ _ _ _ _.

Program Definition push_producer {Γ} : producer -> nat -> rgref Γ unit Γ :=
  RGFix2 _ _ _ (fun rec s n =>
    tl <- !s;
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
  compute. intros. subst. congruence. Qed.
Next Obligation.
  compute; eauto. Qed.
Next Obligation. (* Guarantee satisfaction! *)
  eapply produce_push.  rewrite <- convert_equiv.
  Check @heap_lookup2.
  assert (tmp := @heap_lookup2 _ (fun v _ => v=mkNode n ((h[s]))) local_imm local_imm h new_node).
  simpl in tmp.
  rewrite <- tmp. unfold ts in s.
  (* type based non-aliasing... writing to a ref{option...} won't affect a ref{Node...} Should clean this up *) admit.
Qed.




Local Obligation Tactic := intros; compute; try subst; intuition; eauto with typeclass_instances.
Program Definition pop_consumer {Γ} : consumer -> rgref Γ (option nat) Γ :=
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
