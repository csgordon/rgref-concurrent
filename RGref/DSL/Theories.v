Require Import RGref.DSL.Core.
Require Import RGref.DSL.Monad.

(** * Helpful Constants, Lemmas, and Proof Tactics *)
(** ** General stufff *)
Definition any {A:Set} : hpred A := fun _ => fun _ => True.

Lemma stable_any : forall (A:Set) (R:hrel A), stable any R.
Proof.
  intros; compute; eauto.
Qed.
Hint Resolve stable_any.
Lemma precise_any : forall (A:Set){RA:ImmediateReachability A}, @precise_pred A RA any.
Proof.
  intros; compute; eauto.
Qed.
Hint Resolve precise_any.
Lemma any_true : forall (A:Set) (a:A) h, any a h.
Proof. compute; auto. Qed.
Hint Resolve any_true.

Definition havoc {A:Set} : hrel A := fun _ => fun _ => fun _ => fun _ => True.
Lemma precise_havoc : forall (A:Set)`{ImmediateReachability A}, precise_rel (@havoc A).
Proof. intros; compute; eauto. Qed.
Hint Resolve precise_havoc.
Lemma havoc_true : forall (A:Set) (a a':A) h h', havoc a a' h h'.
Proof. intros; compute; auto. Qed.
Hint Resolve havoc_true.

Definition empty {A:Set} : hrel A := fun _ => fun _ => fun _ => fun _ => False.

Lemma stable_empty : forall (A:Set) (P:hpred A), stable P empty.
Proof.
  compute; intuition.
Qed.
Hint Resolve stable_empty.
Lemma precise_empty : forall (A:Set)`{ImmediateReachability A}, precise_rel empty.
Proof. intros; compute; eauto. Qed.

Definition local_imm {A:Set} : hrel A := fun a => fun a' => fun _ => fun _ => a=a'.
Lemma local_imm_const : forall A, locally_const (@local_imm A).
Proof. intros; firstorder. Qed.
Hint Resolve local_imm_const.

Definition heap_agnostic_pred {A:Set} (P:hpred A) := forall a h h', P a h -> P a h'.
Definition heap_agnostic_rel {A:Set} (R:hrel A) := forall a a' h h' h'' h''', R a a' h h' -> R a a' h'' h'''.

Lemma agnostic_pred_stable : forall (A:Set) (P:hpred A), heap_agnostic_pred P -> stable P local_imm.
Proof.
  compute. intros. subst; intuition; eauto.
Qed.

Hint Resolve agnostic_pred_stable.

(** ** Combinator Lemmas *)

Lemma pred_and_stable : forall (A:Set) (P:hpred A) Q R, stable P R -> stable Q R -> stable (P ⊓ Q) R.
Proof. intros; firstorder. Qed.
Lemma pred_or_stable : forall (A:Set) (P Q:hpred A) R, stable P R -> stable Q R -> stable (P ⊔ Q) R.
Proof. intros; firstorder. Qed.
Lemma rel_and_stable : forall (A:Set) (P:hpred A) R S, stable P R -> stable P S -> stable P (R ⋂ S).
Proof. intros; firstorder. Qed.
Lemma rel_or_stable : forall (A:Set) (P:hpred A) R S, stable P R -> stable P S -> stable P (R ⋃ S).
Proof. intros; firstorder. Qed.
Lemma pred_and_precise : forall (A:Set){RA:ImmediateReachability A}(P Q:hpred A), precise_pred P -> precise_pred Q -> precise_pred (P ⊓ Q).
Proof. intros; firstorder. Qed.
Lemma pred_or_precise : forall (A:Set){RA:ImmediateReachability A}(P Q:hpred A), precise_pred P -> precise_pred Q -> precise_pred (P ⊔ Q).
Proof. intros; firstorder. Qed.
Lemma rel_and_precise : forall (A:Set){RA:ImmediateReachability A}(R S:hrel A), precise_rel R -> precise_rel S -> precise_rel (R ⋂ S).
Proof. intros. compute[precise_rel rel_and] in *. intuition. eauto. eauto. Qed.
Lemma rel_or_precise : forall (A:Set){RA:ImmediateReachability A}(R S:hrel A), precise_rel R -> precise_rel S -> precise_rel (R ⋃ S).
Proof. intros. compute[precise_rel rel_or] in *. intuition. eauto. eauto. Qed.
Require Import Coq.Classes.RelationClasses.
Instance rel_sub_eq_preorder `{A:Set} : PreOrder (@rel_sub_eq A).
Proof. constructor. firstorder. firstorder. Qed.

(** Also need to be able to pull results out of conjunctions *)
Lemma pred_and_proj1 : forall (A:Set) P Q (a:A) (h:heap), (P ⊓ Q) a h -> P a h.
Proof. firstorder. Qed.
Lemma pred_and_proj2 : forall (A:Set) P Q (a:A) (h:heap), (P ⊓ Q) a h -> Q a h.
Proof. firstorder. Qed.

Hint Resolve pred_and_stable rel_and_stable pred_and_precise rel_and_precise.
Hint Resolve pred_or_stable rel_or_stable pred_or_precise rel_or_precise.
