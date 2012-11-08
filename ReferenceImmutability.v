Require Import RGref.DSL.DSL.

(** * Reference Immutability *)
(** With a definition of reachability, we can define the full immutability relation
    necessary to model traditional reference immutability. *)
Class immutability (A:Set) := {
  immutable_rel : hrel A
}.
Instance reachable_immutable `{A:Set,RA:ImmediateReachability A} : immutability A := 
  { immutable_rel := 
    fun a a' h h' =>
      a=a' /\
      (forall (T:Set)(P:hpred T)(R G:hrel T)(p:ref{T|P}[R,G]), reachable_from_in p a h -> h[p]=h'[p])
  }.
Notation "≈" := (immutable_rel) (at level 40).

(** ** Properties of immutability *)
(** *** Stability *)
Lemma stable_immutable : forall (A:Set)`{ImmediateReachability A}(P:hpred A), precise_pred P -> stable P immutable_rel.
Proof. compute. intros. destruct H2. subst. firstorder. Qed.
Hint Resolve stable_immutable.

(** *** Lemmas about reachability *)
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.
Lemma reachable_footprint : forall (A:Set)`{ImmediateReachability A}(a:A) h h',
                               (forall (T:Set)(P:hpred T)(R G:hrel T)(p:ref{T|P}[R,G]), reachable_from_in p a h -> h[p]=h'[p]) ->
                               forall {T P R G}(p:ref{T|P}[R,G]), reachable_from_in p a h -> reachable_from_in p a h'.
Proof.
  intros. dependent induction H1. constructor. eapply directly_reachable; eauto.
  eapply (trans_reachable A a I i p). eauto.
  rewrite <- H0. eapply IHreachable_from_in; firstorder. eapply H0.
  eapply (trans_reachable _ _ _ _ _ _ H). eauto. eapply directly_reachable; eauto.
Qed.
Hint Resolve reachable_footprint.

Lemma reachable_footprint': forall (A:Set)`{ImmediateReachability A}(a:A) h h',
                               (forall (T:Set)(P:hpred T)(R G:hrel T)(p:ref{T|P}[R,G]), reachable_from_in p a h -> h[p]=h'[p]) ->
                               (forall (T:Set)(P:hpred T)(R G:hrel T)(p:ref{T|P}[R,G]), reachable_from_in p a h' -> h'[p]=h[p]).
Proof.
  intros. symmetry. dependent induction H1. eapply H0. constructor.
                                            eapply H0. constructor; eauto.
                                            eapply IHreachable_from_in. intros. eapply H0.
                                                eapply (trans_reachable _ _ _ _ _ _ H). 
                                                rewrite H0. assumption. constructor; eauto.
Qed.
Hint Resolve reachable_footprint'.

Lemma reachable_footprint2: forall (A:Set)`{ImmediateReachability A}(a:A) h h',
                               (forall (T:Set)(P:hpred T)(R G:hrel T)(p:ref{T|P}[R,G]), reachable_from_in p a h -> h[p]=h'[p]) ->
                               forall {T P R G}(p:ref{T|P}[R,G]), reachable_from_in p a h' -> reachable_from_in p a h.
Proof.
  intros. 
  assert (tmp := reachable_footprint' _ _ _ _ H0).
  eapply reachable_footprint; eauto.
Qed.
Hint Resolve reachable_footprint2.

(** *** Precision *)
Lemma precise_immutable (A:Set){RA:ImmediateReachability A} : precise_rel immutable_rel.
Proof. unfold precise_rel. unfold immutable_rel. unfold reachable_immutable.
  intros; destruct_conjs; subst. firstorder; subst. 
  assert (t1 := reachable_footprint' _ _ _ _ H0).
  assert (t2 := reachable_footprint' _ _ _ _ H).
  assert (t3 := reachable_footprint' _ _ _ _ H2).
  rewrite <- H0; eauto. rewrite <- H; eauto.
Qed.
Hint Resolve precise_immutable.

(** ** Qualifiers *)
Definition writable (T:Set) : Set := ref{T|any}[havoc,havoc].
Definition readable (T:Set){RT:ImmediateReachability T} : Set := ref{T|any}[havoc,≈].
Definition immutable (T:Set){RT:ImmediateReachability T} : Set := ref{T|any}[≈,≈].
Definition refined (T:Set){RT:ImmediateReachability T}(P:hpred T) : Set := ref{T|P}[≈,≈].
