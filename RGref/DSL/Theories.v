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
Lemma havoc_refl : forall (A:Set), hreflexive (@havoc A).
Proof. compute; eauto. Qed.
Hint Resolve havoc_refl.

Definition empty {A:Set} : hrel A := fun _ => fun _ => fun _ => fun _ => False.

Lemma stable_empty : forall (A:Set) (P:hpred A), stable P empty.
Proof.
  compute; intuition.
Qed.
Hint Resolve stable_empty.
Lemma precise_empty : forall (A:Set)`{ImmediateReachability A}, precise_rel empty.
Proof. intros; compute; eauto. Qed.
Hint Resolve precise_empty.

Definition local_imm {A:Set} : hrel A := fun a => fun a' => fun _ => fun _ => a=a'.
Lemma local_imm_const : forall A, locally_const (@local_imm A).
Proof. intros; firstorder. Qed.
Hint Resolve local_imm_const.
Lemma local_imm_precise : forall (T:Set)`{ImmediateReachability T}, precise_rel (@local_imm T).
Proof.
  red; intros. induction H2. red. reflexivity.
Qed.
Hint Resolve local_imm_precise.
Lemma local_imm_refl : forall (T:Set), @hreflexive T local_imm.
Proof.
  compute; eauto.
Qed.
Hint Resolve local_imm_refl.

Definition heap_agnostic_pred {A:Set} (P:hpred A) := forall a h h', P a h -> P a h'.
Definition heap_agnostic_rel {A:Set} (R:hrel A) := forall a a' h h' h'' h''', R a a' h h' -> R a a' h'' h'''.

Lemma agnostic_pred_stable : forall (A:Set) (P:hpred A), heap_agnostic_pred P -> stable P local_imm.
Proof.
  compute. intros. subst; intuition; eauto.
Qed.

Hint Resolve agnostic_pred_stable.

(** *** Option types *)
Inductive optset (A:Set) : hrel (option A) :=
  | optset_nop : forall (o:option A) h h', optset A o o h h'
  | optset_set : forall (a:A) h h', optset A None (Some a) h h'.
Inductive option_reach : forall (A:Set)`(ImmediateReachability A) {T:Set}{P R G} (p:ref{T|P}[R,G]) (ao:option A), Prop :=
  | opt_reach_some : forall (A:Set)(a:A)`(ImmediateReachability A) {T:Set}{P R G} (p:ref{T|P}[R,G]),
                         imm_reachable_from_in p a ->
                         option_reach A _ p (Some a).
Global Instance reach_option {A:Set}`{ImmediateReachability A} : ImmediateReachability (option A) :=
  { imm_reachable_from_in := fun T P R G p oa => option_reach A _ p oa }.
Lemma optset_precise : forall A `(ImmediateReachability A), precise_rel (optset A).
Proof. compute. intros. inversion H2; subst; constructor. Qed.
Hint Resolve optset_precise.
(* TODO: Contains instance for options *)
Global Instance option_fold {A:Set}`{rel_fold A} : rel_fold (option A) :=
  { rgfold := fun R G => option (rgfold havoc (fun a a' h h' => G (Some a) (Some a') h h')) ;
    fold := fun R G o => match o with None => None | Some o' => Some (fold o') end
  }.
Lemma optset_refl : forall (A:Set), hreflexive (optset A).
Proof. compute; intuition; constructor. Qed.
Hint Resolve optset_refl.
Inductive opt_contains {A:Set}`{Containment A} : hrel (option A) -> Prop :=
  | some_contains : forall RR (h h':heap),
                      contains (fun a a' h h' => RR (Some a) (Some a') h h') ->
                      opt_contains RR.
Global Instance option_contains {A:Set}`{Containment A} : Containment (option A) :=
  { contains := opt_contains }.

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
Global Instance rel_sub_eq_preorder `{A:Set} : PreOrder (@rel_sub_eq A).
Proof. constructor. firstorder. firstorder. Qed.
Global Instance pred_sub_eq_preorder `{A:Set} : PreOrder (@pred_sub_eq A).
Proof. constructor; firstorder. Qed.

Lemma pred_sub_refl : forall T (P:hpred T), P⊑P.
Proof.
  reflexivity.
Qed.
Hint Resolve pred_sub_refl.

Lemma rel_sub_refl : forall T (R:hrel T), R⊆R.
Proof.
  reflexivity.
Qed.
Hint Resolve rel_sub_refl.

(** Also need to be able to pull results out of conjunctions *)
Lemma pred_and_proj1 : forall (A:Set) P Q (a:A) (h:heap), (P ⊓ Q) a h -> P a h.
Proof. firstorder. Qed.
Lemma pred_and_proj2 : forall (A:Set) P Q (a:A) (h:heap), (P ⊓ Q) a h -> Q a h.
Proof. firstorder. Qed.

Hint Resolve pred_and_stable rel_and_stable pred_and_precise rel_and_precise.
Hint Resolve pred_or_stable rel_or_stable pred_or_precise rel_or_precise.
