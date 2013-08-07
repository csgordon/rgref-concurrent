Require Import RGref.DSL.DSL.
Require Import MonotonicCounter.
Require Import Utf8.
Require Import Coq.Relations.Relations.

(*Definition spec {T:Set}{P R G} := ref{T|P}[R,G] -> heap -> heap -> Prop.*)
Definition spec (T:Set) := T -> heap -> heap -> Prop.

Definition inc_spec : spec monotonic_counter := (λ c h h', increasing (h[c]) (h'[c]) h h').

Definition localize {T P R G} (R':hrel T) (r:ref{T|P}[R,G]) : relation heap :=
  λ h h', R' (h[r]) (h'[r]) h h'.
Infix "@" := (localize) (at level 35).


Module WithRawRelations.
  Definition rseq {A:Set} (R1 R2 : relation A) : relation A :=
    λ h h', exists h'', R1 h h'' /\ R2 h'' h'.
  Infix "⋆" := (rseq) (at level 39, right associativity).
  Lemma check_rseq_assoc : forall (A B C:relation heap), A ⋆ B ⋆ C = rseq A (rseq B C).
  Proof. intuition. Qed.


  Check same_relation.
  Lemma inc_spec_localized : forall c, same_relation heap (inc_spec c) (increasing@c).
  Proof. intros; intuition. Qed.
  
  Check clos_refl_trans.
  Notation "R *" := (clos_refl_trans heap R) (at level 34).
  
  Definition example_inc_trace (c:monotonic_counter) : relation heap :=
    (havoc@c)⋆((clos_refl_trans heap eq)⋆(havoc@c))*⋆(increasing@c)⋆(havoc@c).
  
  Lemma seq_assoc : forall (Q R S:relation heap) h h', (Q⋆R⋆S) h h' <-> ((Q⋆R)⋆S) h h'.
  Proof.
    intros. unfold rseq. split; intros; intuition.
    destruct H. destruct H. destruct H0. destruct H0. repeat (eexists; intuition; eauto).
    destruct H. destruct H. destruct H. destruct H. repeat (eexists; intuition; eauto).
  Qed.
  Inductive refines : relation heap -> relation heap -> Prop :=
  | refine_refl : forall R, refines R R
  | refine_left : forall Q Q' R, refines Q Q' -> refines (Q⋆R) (Q'⋆R)
  | refine_right : forall Q R R', refines R R' -> refines (Q⋆R) (Q⋆R')
  | refine_merge_passive_l : forall Q, refines (Q⋆(clos_refl_trans heap eq)) Q
  | refine_merge_passive_r : forall Q, refines ((clos_refl_trans heap eq)⋆Q) Q
  | refine_reassoc : forall Q R S, refines (Q⋆R⋆S) ((Q⋆R)⋆S)
  | refine_trans : forall Q R S, refines Q R -> refines R S -> refines Q S
  | refine_clos : forall Q R, refines Q R -> refines (Q* ) (R* )
  (* These rules are a little sketchy: they should really only be applied to remote actions...
     but there's nothing in the current representation from applying them to ellide intermediate
     writes by a non-linearizable implementation... *)
  | refine_idemp_clos : forall Q, inclusion _ (Q* ) Q -> refines (Q* ) Q
  | refine_havoc_l : forall T P R G (l:ref{T|P}[R,G]) Q, refines (havoc@l⋆Q) Q
  | refine_havoc_r : forall T P R G (l:ref{T|P}[R,G]) Q, refines (Q⋆havoc@l) Q
  .
  Infix "≪" := (refines) (at level 63).

  Lemma inc_valid : forall c, example_inc_trace c ≪ (havoc@c)⋆(inc_spec c)⋆(havoc@c).
  Proof.
    intros. unfold example_inc_trace.
    repeat constructor.
    eapply refine_trans.
    eapply refine_reassoc.
    apply refine_left.
    eapply refine_trans. apply refine_left. apply refine_clos. apply refine_merge_passive_r.
    eapply refine_trans. apply refine_left. apply refine_idemp_clos. compute; auto.
    apply refine_havoc_l.
  Qed.
End WithRawRelations.
  (* So this approach is generally feasible, but we'll need to distinguish local and remote actions;
   remote havoc* refines remote havoc, local havoc* (totally non-lin) doesn't refine local havoc (atomic blocK)
   *)
Inductive action : Prop :=
  | id : action
  | remote : relation heap -> action
  | local : relation heap -> action
.
CoInductive trace : Prop :=
  | epsilon : trace
  | obs : action -> trace
  | append : trace -> trace -> trace
  (* 0 or more Iterations *)
  | star : trace -> trace
  (* Nondeterminism *)
  | choice : trace -> trace -> trace
.
Infix "~>" := (append) (at level 49, right associativity).
(*Infix "⋆" := (append) (at level 57, right associativity).*)
Notation "'ε'" := (epsilon) (at level 0).
Coercion obs : action >-> trace.

Program Definition coinc_trace_test (c:monotonic_counter) := 
  (remote (havoc@c)) ~>
  (star ((local (clos_refl_trans heap eq))~>(remote (havoc@c))~>ε)) ~>
  ((local (increasing@c))~>(remote (havoc@c))~>ε).
(*Program Definition coinc_trace_test (c:monotonic_counter) := 
  (remote (havoc@c)) ~>
                     (star ((local (clos_refl_trans heap eq))~>(remote (havoc@c))~>ε)
                           ((local (increasing@c))~>(remote (havoc@c))~>ε)).
Definition coinc_spec (c:monotonic_counter) :=
  (remote (havoc@c))~>(local (increasing@c))~>(remote (havoc@c))~>ε.
*)
Definition coinc_spec (c:monotonic_counter) :=
  (remote (havoc@c))~>(local (increasing@c))~>(remote (havoc@c))~>ε.

(* Better have infinite refinement proofs if we have infinite traces... *)
CoInductive refines : relation trace :=
  | refine_refl : forall R, refines R R
  | refine_local : forall a a' R, inclusion _ a a' -> refines ((local a)~>R) ((local a')~>R)
  | refine_left : forall Q Q' R, refines Q Q' -> refines (Q~>R) (Q'~>R)
  | refine_right : forall Q R R', refines R R' -> refines (Q~>R) (Q~>R')
  (* Ideally associativity would simply be an equivalence in a HIT... Not sure what the status
     of HITs for coinduction is.
   *)
  | refine_reassoc : forall Q R S, refines (Q~>R~>S) ((Q~>R)~>S)
  | refine_reassoc' : forall Q R S, refines ((Q~>R)~>S) (Q~>R~>S)
  | refine_merge_passive_l : forall Q, refines (Q~>(local (clos_refl_trans heap eq))) Q
  | refine_merge_passive_r : forall Q, refines ((local (clos_refl_trans heap eq))~>Q) Q
  | refine_merge_remote_trans : forall Q, transitive _ Q -> refines ((remote Q)~>(remote Q)) (remote Q)
  | refine_merge_local_trans : forall Q, transitive _ Q -> refines ((local Q)~>(local Q)) (local Q)
  | refine_trans : forall Q R S, refines Q R -> refines R S -> refines Q S
  | refine_star : forall Q R, refines Q R -> refines (star Q) (star R)
  | refine_fold_star_a : forall a, refines (a ~> (star (a~>ε))) (star (a~>ε))
(*  | refine_clos : forall Q R, refines Q R -> refines (star Q) (R) <-- Not actually the right semantics *)
(*  | refine_idemp_clos : forall Q, inclusion _ (Q* ) Q -> refines (Q* ) Q*)
(*  | refine_havoc_l : forall T P R G (l:ref{T|P}[R,G]) Q, refines (havoc@l⋆Q) Q
  | refine_havoc_r : forall T P R G (l:ref{T|P}[R,G]) Q, refines (Q⋆havoc@l) Q*)
  | refine_remote_trans : forall a, transitive _ a ->
                                    refines (remote a ~> star (remote a ~> ε)) (remote a ~> ε)
  | refine_remote_trans' : forall a, transitive _ a ->
                                    refines (remote a ~> star (remote a)) (remote a)
  | refine_add_tail : forall R, refines R (R~>ε)
  | refine_drop_tail : forall R, refines (R~>ε) R
.
Infix "≪" := (refines) (at level 63).
CoInductive trace_equiv : relation trace :=
  | teq_refl : forall R, trace_equiv R R
  | teq_unfold_star : forall R, trace_equiv (star R) (star (R~>R))
  | teq_fold_star : forall R, trace_equiv (star (R~>R)) (star R)
  | teq_assoc1 : forall Q R S, trace_equiv (Q~>R~>S) ((Q~>R)~>S)
  | teq_assoc2 : forall Q R S, trace_equiv ((Q~>R)~>S) (Q~>R~>S)
  | teq_add_tail : forall Q, trace_equiv Q (Q~>ε)
  | teq_drop_tail : forall Q, trace_equiv (Q~>ε) Q
  | teq_app : forall Q Q' R R', trace_equiv Q Q' -> trace_equiv R R' -> trace_equiv (Q~>R) (Q'~>R')
.
Infix "≈" := (trace_equiv) (at level 62).
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Classes.Morphisms.
Instance trans_refine : Transitive refines.
Proof. compute; intros. eapply refine_trans; eauto. Qed.
Instance preord_refine : PreOrder refines.
Proof. constructor; auto with typeclass_instances.
       compute. intros; constructor.
Qed.
Definition trace_dup (t:trace) : trace :=
  match t with
  | epsilon => epsilon
  | obs a => obs a
  | append x y => append x y
  | star x => star x
  | choice x y => choice x y
  end.
Lemma trace_dup_eq : forall t, t = trace_dup t.
Proof.
  intros. destruct t; reflexivity.
Qed.
Instance sym_trace_equiv : Symmetric trace_equiv.
Proof.
      compute. intros. 
      destruct H; constructor. admit. admit.
          (*cofix. rewrite (trace_dup_eq x); rewrite (trace_dup_eq y). 
                 destruct sym_trace_equiv; destruct R; simpl; constructor.*)
Qed.

Program Instance trace_setoid : Setoid trace :=
{ equiv := trace_equiv; setoid_equiv := _}.
Next Obligation.
  constructor.
      compute; constructor.
      exact sym_trace_equiv.
      admit. (* Don't have the hang of coinduction yet *)
Qed.

Instance refine_equiv : Proper (trace_equiv ==> trace_equiv ==> iff) refines.
Proof.
  compute. intros; split; intros.
  (* still a coinduction novice *)
Admitted.
Instance equiv_imp : Proper (trace_equiv ==> trace_equiv ==> Basics.impl) trace_equiv.
Proof.
  compute; intros.
  (* More coinduction... *)
Admitted.
Instance equiv_imp' {x} : Proper (trace_equiv ==> Basics.impl) (trace_equiv x).
Admitted.
Instance equiv_imp'' : Proper (trace_equiv ==> eq ==> Basics.impl) (trace_equiv).
Admitted.
Instance equiv_equiv : Proper (trace_equiv ==> trace_equiv ==> iff) trace_equiv.
Proof.
  compute; intros; split; intros.
  setoid_rewrite H0 in H1.
  setoid_rewrite H in H1.
  assumption.
  setoid_rewrite H. setoid_rewrite H1. symmetry. assumption.
Qed.

Lemma cotrace_refinement_test : forall c, coinc_trace_test c ≪ coinc_spec c.
Proof.
  intros; unfold coinc_trace_test; unfold coinc_spec.
  eapply refine_trans. eapply refine_reassoc.
  repeat constructor.
  eapply refine_trans. eapply refine_right. apply refine_star. apply refine_merge_passive_r.
  eapply refine_trans; try eapply refine_drop_tail.
  eapply refine_remote_trans.
  compute; intuition.
Qed.
Instance app_equiv : Proper (trace_equiv ==> trace_equiv ==> trace_equiv) append.
Proof.
  compute; intros. constructor; eauto.
Qed.
Instance app_equiv' {x} : Proper (trace_equiv ==> trace_equiv) (append x).
Proof.
  compute; intros. constructor; eauto. constructor.
Qed.
  
Lemma cotrace_refinement_morphism_test : forall c, coinc_trace_test c ≪ coinc_spec c.
Proof.
  intros; unfold coinc_trace_test; unfold coinc_spec.
  setoid_rewrite teq_assoc1.
  (** To do much more with setoids, we need to be able to rewrite inside trace
     constructors, which means a Proper instance for each constructor... *)
  etransitivity. apply refine_reassoc.
  repeat constructor.
  etransitivity. eapply refine_right. apply refine_star. apply refine_merge_passive_r.
  etransitivity. apply refine_right. apply refine_star. apply refine_drop_tail.
  constructor.
  compute; intuition.
Qed.

(** TODO:
   1: variable binding, probably using some kind of injection of a function from bound vars to traces.
      Trieber stack push/pop is a good test of those, since the binding ensures stack is preserved.
      Could I use the observation of the (possibly refined) guarantee to obviate the need for
      binding?
   2: distinguishing visible local effects that don't change the abstract state from those that do,
      e.g. distinguishing the tail update in MSQ from insertion.  Maybe, if I'm struck with sudden
      insight, this might let me figure out how to do helping updates (the hard part there is probably
      folding).
   3: Commutativity / moving / general handling of allocation
   4: Reachability: e.g., handling update at tail as an update at the head.
      Might consider a refinement axiom like:
      ∀ ℓ₀, (ℓ:ref{T|P}[R,G]), imm_reachable_from ℓ h[l₀] -> 
          (∀ h h', G'@ℓ h h' -> G''@ℓ₀ h h') ->
          G'@ℓ ≪ G''@ℓ₀
      Not sure where that initial outer h comes from, or where we'd get the reachability result.
   5. Allocations?
*)

Require Import TrieberStack.
Definition push_op n (o o':option (ref{Node|any}[local_imm,local_imm])) (h h':heap) : Prop :=
  exists hd, exists hd', h'[hd']=(mkNode n hd) /\ o=hd /\ o'=(Some hd').
CoFixpoint example_push_trace (q:ts) (n:nat) :=
  (remote (deltaTS@q))~>
  (local (clos_refl_trans _ eq))~>
  (remote (deltaTS@q))~>
  (** TODO: allocation followed by more interference? on structure + new allocation? *)
  (choice ((local (clos_refl_trans _ eq))~>(example_push_trace q n))
          ((local ((push_op n)@q))~>ε))~>
  (remote (deltaTS@q)) (* TODO: and interfere on new allocation...? *)
.

Example push_spec (q:ts) n := (remote (deltaTS@q))~>(local ((push_op n)@q))~>(remote (deltaTS@q))~>ε.

Lemma push_refine : forall q n, example_push_trace q n ≪ push_spec q n.
Proof.
  intros.
  cofix. (** If I admit, must clear coIH first, since otherwise the resulting partial term looks unguarded. *)
  unfold push_spec.
  rewrite (trace_dup_eq (example_push_trace q n)).
  compute[example_push_trace trace_dup]. fold example_push_trace.
  etransitivity. apply refine_reassoc.
  etransitivity. apply refine_reassoc.
  etransitivity. apply refine_left. etransitivity. apply refine_left. apply refine_merge_passive_l.
      apply refine_merge_remote_trans.
      (** TODO: transitive (deltaTS@q).  Don't think this actually holds, but we should be able to merge... maybe the
         trace should use the reflexive transitive closure of deltaTS as the interference... *) clear push_refine. admit.
  constructor.
  etransitivity. apply refine_add_tail.
  etransitivity. apply refine_reassoc'.
  constructor.
  assert (forall Q R S, Q ≪ S -> R ≪ S -> (choice Q R) ≪ S) by (clear push_refine; admit). (** Should be new axiom *)
  apply H; clear H.
  etransitivity. apply refine_merge_passive_r.
  (** Messed up coinductive hyp... want [apply push_refine.] but coIH is ≪ push_spec, goal is ≪ local (push_op) *)
  clear push_refine. admit.
  etransitivity. apply refine_drop_tail. reflexivity.
Qed.
