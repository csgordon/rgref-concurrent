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
Definition observe {T P R G} (P':hpred T) (r:ref{T|P}[R,G]) : relation heap :=
  λ h h', h=h' /\ P' (h[r]) h.
Definition assert {T P R G} (P':hpred T) (r:ref{T|P}[R,G]) : relation heap := observe P' r.


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
  | act_id : action
  | act_remote : relation heap -> action
  | act_local : relation heap -> action
.
CoInductive trace {A:Set} : Prop :=
  | epsilon : trace
  | result : A -> trace
  | bind : forall {T:Set} (f:T->trace), trace
  | obs : action -> trace
  | append : trace -> trace -> trace
  (* 0 or more Iterations *)
  | star : trace -> trace
  (* Nondeterminism *)
  | choice : trace -> trace -> trace
.
Infix "~~>" := (append) (at level 49, right associativity).
(*Infix "⋆" := (append) (at level 57, right associativity).*)
Notation "'ε'" := (epsilon) (at level 0).
(*Coercion obs (A:Set) : action >-> (@trace A).*)
Definition remote {A:Set} (R:relation heap) : @trace A := obs (act_remote R).
Definition local {A:Set} (R:relation heap) : @trace A := obs (act_local R).
Notation "(ζ x => e )" := (bind (fun x => e)).

Program Definition coinc_trace_test (c:monotonic_counter) := 
  (remote (havoc@c)) ~~>
  (star ((local (clos_refl_trans heap eq))~~>(remote (havoc@c))~~>ε)) ~~>
  ((local (increasing@c))~~>(remote (havoc@c))~~>(result tt)~~>ε).

Definition coinc_spec (c:monotonic_counter) :=
  (remote (havoc@c))~~>(local (increasing@c))~~>(remote (havoc@c))~~>(result tt)~~>ε.

(* Better have infinite refinement proofs if we have infinite traces... *)
CoInductive refines {A:Set} : relation (@trace A) :=
  | refine_refl : forall R, refines R R
  | refine_local : forall a a' R, inclusion _ a a' -> refines ((local a)~~>R) ((local a')~~>R)
  | refine_left : forall Q Q' R, refines Q Q' -> refines (Q~~>R) (Q'~~>R)
  | refine_right : forall Q R R', refines R R' -> refines (Q~~>R) (Q~~>R')
  | refine_split : forall Q Q' R R', refines Q Q' -> refines R R' -> refines (Q~~>R) (Q'~~>R')
  (* Ideally associativity would simply be an equivalence in a HIT... Not sure what the status
     of HITs for coinduction is.
   *)
  | refine_reassoc : forall Q R S, refines (Q~~>R~~>S) ((Q~~>R)~~>S)
  | refine_reassoc' : forall Q R S, refines ((Q~~>R)~~>S) (Q~~>R~~>S)
  | refine_merge_passive_l : forall Q, refines (Q~~>(local (clos_refl_trans heap eq))) Q
  | refine_merge_passive_r : forall Q, refines ((local (clos_refl_trans heap eq))~~>Q) Q
  | refine_merge_remote_trans : forall Q, transitive _ Q -> refines ((remote Q)~~>(remote Q)) (remote Q)
  | refine_merge_local_trans : forall Q, transitive _ Q -> refines ((local Q)~~>(local Q)) (local Q)
  | refine_trans : forall Q R S, refines Q R -> refines R S -> refines Q S
  | refine_star : forall Q R, refines Q R -> refines (star Q) (star R)
  | refine_fold_star_a : forall a, refines (a ~~> (star (a~~>ε))) (star (a~~>ε))
(*  | refine_clos : forall Q R, refines Q R -> refines (star Q) (R) <-- Not actually the right semantics *)
(*  | refine_idemp_clos : forall Q, inclusion _ (Q* ) Q -> refines (Q* ) Q*)
(*  | refine_havoc_l : forall T P R G (l:ref{T|P}[R,G]) Q, refines (havoc@l⋆Q) Q
  | refine_havoc_r : forall T P R G (l:ref{T|P}[R,G]) Q, refines (Q⋆havoc@l) Q*)
  | refine_remote_trans : forall a, transitive _ a ->
                                    refines (remote a ~~> star (remote a ~~> ε)) (remote a ~~> ε)
  | refine_remote_trans' : forall a, transitive _ a ->
                                    refines (remote a ~~> star (remote a)) (remote a)
  | refine_add_tail : forall R, refines R (R~~>ε)
  | refine_drop_tail : forall R, refines (R~~>ε) R
.
Infix "≪" := (refines) (at level 63).
CoInductive trace_equiv {A:Set} : relation (@trace A) :=
  | teq_refl : forall R, trace_equiv R R
  | teq_unfold_star : forall R, trace_equiv (star R) (star (R~~>R))
  | teq_fold_star : forall R, trace_equiv (star (R~~>R)) (star R)
  | teq_assoc1 : forall Q R S, trace_equiv (Q~~>R~~>S) ((Q~~>R)~~>S)
  | teq_assoc2 : forall Q R S, trace_equiv ((Q~~>R)~~>S) (Q~~>R~~>S)
  | teq_add_tail : forall Q, trace_equiv Q (Q~~>ε)
  | teq_drop_tail : forall Q, trace_equiv (Q~~>ε) Q
  | teq_app : forall Q Q' R R', trace_equiv Q Q' -> trace_equiv R R' -> trace_equiv (Q~~>R) (Q'~~>R')
  | teq_lift_binder : forall Q (T:Set) (f:T->trace), trace_equiv (Q~~>(bind f)) (bind (λ x, Q~~>(f x)))
  | teq_drop_binder : forall Q (T:Set) (f:T->trace), trace_equiv (bind (λ x, Q~~>(f x))) (Q~~>(bind f))
  | teq_append_binder : forall Q (T:Set) (f:T->trace), trace_equiv ((bind f)~~>Q) (bind (λ x, (f x)~~>Q))
  | teq_shrink_binder : forall Q (T:Set) (f:T->trace), trace_equiv (bind (λ x, (f x)~~>Q)) ((bind f)~~>Q)
  | teq_bound : forall (T:Set) (f g:T->trace), (forall x, trace_equiv (f x) (g x)) -> trace_equiv (bind f) (bind g)
  | teq_sym : forall Q R, trace_equiv Q R -> trace_equiv R Q
.
Infix "≈" := (trace_equiv) (at level 62).
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Classes.Morphisms.
Instance trans_refine {A:Set} : Transitive (@refines A).
Proof. compute; intros. eapply refine_trans; eauto. Qed.
Instance preord_refine {A:Set} : PreOrder (@refines A).
Proof. constructor; auto with typeclass_instances.
       compute. intros; constructor.
Qed.
Definition trace_dup {A:Set}(t:@trace A) : trace :=
  match t with
  | epsilon => epsilon
  | result x => result x
  | bind _ f => bind f
  | obs a => obs a
  | append x y => append x y
  | star x => star x
  | choice x y => choice x y
  end.
Lemma trace_dup_eq : forall A (t:@trace A), t = trace_dup t.
Proof.
  intros. destruct t; reflexivity.
Qed.
Instance sym_trace_equiv {A:Set} : Symmetric (@trace_equiv A).
Proof.
      compute. 
      cofix.
      intros.
      destruct H; try solve[constructor].

      constructor; eapply sym_trace_equiv; auto.
      apply teq_bound. intros.  apply teq_sym. apply H. assumption.
Qed.
Instance trans_trace_equiv {A:Set} : Transitive (@trace_equiv A). Admitted.
Instance refl_trace_equiv {A:Set} : Reflexive (@trace_equiv A). Admitted.

Program Instance trace_setoid {A:Set} : Setoid (@trace A) :=
{ equiv := trace_equiv; setoid_equiv := _}.
Next Obligation.
  constructor.
      compute; constructor.
      exact sym_trace_equiv.
      admit.
Qed.

Instance refine_equiv {A:Set} : Proper (trace_equiv ==> trace_equiv ==> iff) (@refines A).
Proof.
  compute. intros; split; intros.
  (* still a coinduction novice *)
Admitted.
Instance equiv_imp {A:Set} : Proper (trace_equiv ==> trace_equiv ==> Basics.impl) (@trace_equiv A).
Proof.
  compute; intros.
  (* More coinduction... *)
Admitted.
Instance equiv_imp' {A:Set} {x} : Proper (trace_equiv ==> Basics.impl) (@trace_equiv A x).
Admitted.
Instance equiv_imp'' {A:Set} : Proper (trace_equiv ==> eq ==> Basics.impl) (@trace_equiv A).
Admitted.
Instance equiv_equiv {A:Set} : Proper (trace_equiv ==> trace_equiv ==> iff) (@trace_equiv A).
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
Instance app_equiv {A:Set} : Proper (trace_equiv ==> trace_equiv ==> trace_equiv) (@append A).
Proof.
  compute; intros. constructor; eauto.
Qed.
Instance app_equiv' {A:Set} {x} : Proper (trace_equiv ==> trace_equiv) (@append A x).
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

(** Solutions sketched, but not precise:
    1. Variable binding
       Using an injection of a function generating traces, which isn't needed too often since
       observing a precise guarantee can often obviate the need to explicitly bind certain names
       TODO: Try refining stack push example to a push spec that uses binding to name the intermediate
       node.... This is a good test of the refinement approach's generality
    2. Return values
       Added by including a return type in the trace type, adding a return predicate. Seems to work.
    3. Distinguishing abstract state updates from concrete-but-not-abstract updates
       Can probably crib around this using the choice operator, using the same physical rep. for
       concrete and abstract states, and making things like caching updates optional.
*)
(** No Solution Yet:
    1. Allocations / multiple shared objects: commutativity, thread-locality, etc.
    2. Reachability: e.g., handling update at tail as an update viewed through the head
      Might consider a refinement axiom like:
      ∀ ℓ₀, (ℓ:ref{T|P}[R,G]), imm_reachable_from ℓ h[l₀] -> 
          (∀ h h', G'@ℓ h h' -> G''@ℓ₀ h h') ->
          G'@ℓ ≪ G''@ℓ₀
      Not sure where that initial outer h comes from, or where we'd get the reachability result.
      I think the hindsight paper set example might be the only example we really need this for,
      unless we do get around to the tail pointer in the MSQ.
*)


Require Import TrieberStack.
Definition push_op n (o o':option (ref{Node|any}[local_imm,local_imm])) (h h':heap) : Prop :=
  exists hd, exists hd', h'[hd']=(mkNode n hd) /\ o=hd /\ o'=(Some hd').
CoFixpoint example_push_trace (q:ts) (n:nat) :=
  (remote (deltaTS@q))~~>
  (local (clos_refl_trans _ eq))~~>
  (remote (deltaTS@q))~~>
  (** TODO: allocation followed by more interference? on structure + new allocation? *)
  (choice ((local (clos_refl_trans _ eq))~~>(example_push_trace q n))
          ((local ((push_op n)@q))~~>ε))~~>
  (result tt)~~>
  (remote (deltaTS@q)) (* TODO: and interfere on new allocation...? *)
.

Example push_spec (q:ts) n :=
  (remote (deltaTS@q))~~>(local ((push_op n)@q))~~>(result tt)~~>(remote (deltaTS@q))~~>ε.

Axiom refine_choice : forall A (Q R S:@trace A), Q ≪ S -> R ≪ S -> (choice Q R) ≪ S.

Lemma push_refine : forall q n, example_push_trace q n ≪ push_spec q n.
Proof.
  intros.
  cofix. (** If I admit, must clear coIH first, since otherwise the resulting partial term looks unguarded. *)
  unfold push_spec.
  rewrite (trace_dup_eq _ (example_push_trace q n)).
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
  etransitivity. Focus 2. apply refine_reassoc'.
  etransitivity. Focus 2. apply refine_reassoc'.
  etransitivity. apply refine_reassoc.
  constructor.
  etransitivity. Focus 2. apply refine_reassoc.
  constructor.
  apply refine_choice.
  etransitivity. apply refine_merge_passive_r.
  (** Messed up coinductive hyp... want [apply push_refine.] but coIH is ≪ push_spec, goal is ≪ local (push_op) *)
  clear push_refine. admit.
  etransitivity. apply refine_drop_tail. reflexivity.
Qed.

Example read_ctr_spec (c:monotonic_counter) :=
  (remote (increasing@c))~~>
  (ζ v => (local (observe (λ x h, x=v) c)~~>(remote (increasing@c))~~>(result v))).

Definition pop_op n x hd' (h h':heap) := exists (hd:ref{Node|any}[local_imm,local_imm]),
                                                  x=(Some hd) /\ (h[hd])=(mkNode n hd').
Example pop_spec (q:ts)  :=
  (remote (deltaTS@q))~~>(ζ v => (local ((pop_op v)@q))~~>(remote (deltaTS@q))~~>(result v)).

Axiom refine_bind_l : forall (A T:Set) (f:T->(@trace A)) Q, (forall t, (f t) ≪ Q) -> (bind f) ≪ Q.
Axiom refine_bind_r : forall (A T:Set) (f:T->(@trace A)) Q, (forall t, Q ≪ (f t)) -> Q ≪ (bind f).
Axiom refine_bind_b : forall (A T:Set) (f g:T->(@trace A)), (forall t, f t ≪ g t) -> bind f ≪ (bind g).

CoFixpoint sample_pop_trace (q:ts) :=
  (remote (deltaTS@q))~~>
  (local (clos_refl_trans _ eq))~~>
  (remote (deltaTS@q))~~>
  (choice ((local (clos_refl_trans _ eq))~~>(sample_pop_trace q))
          (ζ v => (local ((pop_op v)@q))~~>(remote (deltaTS@q))~~>result v)).

Example pop_test : forall q, sample_pop_trace q ≪ pop_spec q.
Proof.
  intros.
  cofix.
  unfold pop_spec.
  rewrite (trace_dup_eq _ (sample_pop_trace q)).
  compute[sample_pop_trace trace_dup]. fold sample_pop_trace.
  etransitivity. apply refine_reassoc. etransitivity. apply refine_left. apply refine_merge_passive_l.
  etransitivity. apply refine_reassoc. etransitivity. apply refine_left. apply refine_merge_remote_trans.
  (** TODO: again, deltaTS isn't actually transitive, we should be using refl-trans-clos *) clear pop_test. admit.
  constructor.
  apply refine_choice.
  (** TODO: again, coIH is slightly mismatched... *) clear pop_test. admit.

  (** could actually use reflexivity here, but I'd rather play with the bind axioms. *)
  apply refine_bind_b. intros. repeat constructor.
Qed.
(* TODO: Should ζ / bind use existential instead of universal? *)
  
Require Import RGref.DSL.Fields.
Class HindsightField (A:Set){F:Set}`{ImmediateReachability A}`{FieldTyping A F} :=
{
  f : F
  (* TODO: extend to a concrete P R G, impose proofs of
     various hindsight properties on them, FieldType A f ref{...} *)
}.
(* Reachability, constrained to the hindsight field *)
Inductive FieldReach (T:Set)`{ImmediateReachability T}{P R G}{F:Set}
                         (f:F)`{FieldType T _ f (ref{T|P}[R,G])} (h:heap) 
    : ref{T|P}[R,G] -> ref{T|P}[R,G] -> Prop :=
| imm_hsr : forall r, FieldReach T f h r r
| step_hsr : forall x y z, FieldReach T f h x y ->
                           getF (h[y]) = z ->
                           FieldReach T f h x z
.
Definition HindsightReach (T:Set){P R G}`{HindsightField T}`{FieldType T _ f (ref{T|P}[R,G])}
                          (h:heap)(src dst:ref{T|P}[R,G]) : Prop :=
  FieldReach T f h src dst.
  

(* TODO: Does this need to be coinductive for elim purposes?  Each observation will be finite... *)
Inductive temporal_backbone {T P R G}{F:Set}`{hsf:HindsightField (F:=F) T}`{FieldType T F f (ref{T|P}[R,G])}
                            : ref{T|P}[R,G] -> ref{T|P}[R,G] -> Set :=
  | init_backbone : forall a, temporal_backbone a a
  | next_backbone : forall a b c, temporal_backbone a b ->
                                  (* getF (h[b]) = c -> Don't think we need this since we really care about the interp... *)
                                  temporal_backbone a c
  | prfx_backbone : forall a b c, temporal_backbone b c -> temporal_backbone a c
.
Fixpoint interp_temporal_backbone {A:Set}
                                  {T P R G}{F:Set}`{HindsightField (F:=F) T }`{FieldType T F f (ref{T|P}[R,G])}
                                  {a b:ref{T|P}[R,G]} (bb:temporal_backbone a b) : @trace A :=
  match bb with
  | init_backbone a => ε
                         (* TODO: interference! *)
  | next_backbone a b c bb_ab => (interp_temporal_backbone bb_ab) ~~> (local (λ h h', h=h' /\ getF (h[b]) = c))
  | prfx_backbone a b c bb_bc => (local (λ h h', h=h' /\ getF (h[a]) = b))~~>(interp_temporal_backbone bb_bc)
  end.
Notation "[| bb |]" := (interp_temporal_backbone bb) (at level 45).
Notation "% a" := (init_backbone a) (at level 30).
Notation "ab ↝ c" := (next_backbone _ _ c ab) (at level 36, left associativity).

Variable r : ref{nat|any}[havoc,havoc].
Variable x : ref{nat|any}[havoc,havoc].
Variable y : ref{nat|any}[havoc,havoc].
Check (%r ↝ x ↝ y).
Eval compute in [| %r ↝ x ↝ y |].


(* Then the Hindsight lemma should be along the lines of:
Axiom hindsight : forall ....,
    [| %src↝...↝dst |]~~>(local (G_act@dst) ≪ (λ x x' h h', HindsightReach h x dst)@src)
or
Axiom hindsight : forall ....,
    [| %src↝...↝dst |]~~>(local (G_act@dst) ≪ (λ x x' h h', HindsightReach h x dst /\ G_act (h[dst]) (h'[dst]) h h')@src)
Still need to deal with interference, and allocations that might happen between the backbone and action
Also need more constraints on R (and G?) to enforce the relevant hindsight constraints... maybe the exact ref
type and this proof should be bundled up in the HindsightField instance...
AND I need to ensure that this axiom actually reflects the results of the HS lemma.  If I need to generalize
it slightly, that seems fine, but I need to ensure this is sound!
*)
Check @temporal_backbone.
Axiom hindsight_maybe : forall A T P R G (F:Set),
                        forall (ir:ImmediateReachability T) (ft:FieldTyping T F) 
                               (hsf:@HindsightField T F ir ft) (ftt:FieldType T F f (ref{T|P}[R,G])),
                        forall (src dst:ref{T|P}[R,G]) (bb:@temporal_backbone T P R G F ir ft hsf ft ftt src dst) G_act,
    [| bb |]~~>(local (G_act@dst)) ≪ (local (A:=A) ((λ (x x':T) h h', HindsightReach T h src dst /\ G_act (h[dst]) (h'[dst]) h h')@src))
.
Check hindsight_maybe.


Section HindsightTesting.

  Require Import Hindsight.
  (* TODO: rewrite locate to use RGFix2 instead of RGFix with a tuple input *)
  CoFixpoint locate_inner_loop (p c:eptr) (k:⊠) : @trace (eptr * eptr) :=
    (remote (deltaE@p))~~>(remote (deltaE@c))~~>
    (** Need conditional treatment... and conversion of ~> to direct heap access *)
    (choice ( (local ((λ x x' h h', x=x'/\h=h'/\((getF x) ≪≪ k)=true)@c))~~>
              (ζ nxt => (local ((λ x x' h h', x=x'/\h=h'/\(getF x)=Some nxt)@c))~~> (* TODO: interfere *)
                        locate_inner_loop c nxt k))
            ( (local ((λ x x' h h', x=x'/\h=h'/\ ((getF x) ≪≪ k)=false)@c))~~>
              (result (p,c)))).
  Program CoFixpoint locate_trace (l:hindsight_list) (k:⊠) : @trace (eptr * eptr) :=
    (remote (local_imm@l))~~>
    (ζ head => (local ((λ x x' h h', x=x' /\ h=h' /\ match x with mkHLB hd tl => hd = head end)@l))~~>
               (remote (deltaE@head))~~>
               (ζ nxt => (local ((λ x x' h h', x=x' /\ h=h' /\ nextOfE x = Some nxt)@head))~~>
                         locate_inner_loop (@convert_P _ _ invE _ _ _ _ _ _ head) nxt k))
    .
  Next Obligation. eapply pred_and_proj1. eassumption. Defined.
    
  Instance e_hind : HindsightField E := { f := nxt }.
  (** TODO: not ideal; the hindsight proof approach is bleeding into the spec.  Maybe we need a
      more general FieldReachable .... f to do this. *) 
  Check @HindsightReach.
  Program Example locate_spec (l:hindsight_list) (k:⊠) : @trace (eptr * eptr) :=
    (remote (local_imm@l))~~>
    (ζ head => (local ((λ x x' h h', x=x' /\ h=h' /\ match x with mkHLB hd tl => hd = head end)@l))~~>
               (remote (deltaE@head))~~>
               (ζ ret => match ret with
                         | (p, c) =>
                           (local ((λ x x' h h',
                                    (*HindsightReach E nxt h (@convert_P _ _ invE _ _ _ _ _ _ head) p /\*)
                                    (** TODO: This is actually broken; the Hindsight machinery assumes the
                                        type of the HSF is the ref type, but here it's an option of the
                                        ref type... *)
                                    @HindsightReach E _ _ _ F _ hs_node_fields e_hind hs_node_fields _ h (@convert_P _ _ invE _ _ _ _ _ _ head) p /\
                                    getF (h[p]) = Some c /\
                                    getF (h[p]) ≪≪ k = true /\
                                    getF (h[c]) ≪≪ k = false
                                   )@(@convert_P _ _ invE _ _ _ _ _ _ head)))~~>
                           (result (p,c))
                         end))
  . (* TODO: more interference... *)
  Next Obligation. (** TODO: FieldType, need to adjust for fns of field type *) admit. Qed.
  Next Obligation. eapply pred_and_proj1; eassumption. Qed.
  Next Obligation. eapply pred_and_proj1; eassumption. Qed.

  Section SuperHack.

    
    (** This is quite a hack; since k is fixed, there's a maximum number of iterations / pointer chases
        from the head, as in the PODC wait-freedom proof, but this isn't necessarily a general technique.
        Still, I need to make some forward progress on this proof... *)
    Fixpoint locate_inner_loop_count n (p c:eptr) (k:⊠) : @trace (eptr * eptr) :=
      (remote (deltaE@p))~~>(remote (deltaE@c))~~>
      (** Need conditional treatment... and conversion of ~> to direct heap access *)
      (match n with
         | S n' => ( (local ((λ x x' h h', x=x'/\h=h'/\((getF x) ≪≪ k)=true)@c))~~>
                     (ζ nxt => (local ((λ x x' h h', x=x'/\h=h'/\(getF x)=Some nxt)@c))~~> (* TODO: interfere *)
                          locate_inner_loop_count n' c nxt k))
         | O =>    ( (local ((λ x x' h h', x=x'/\h=h'/\ ((getF x) ≪≪ k)=false)@c))~~>(result (p,c)))
       end).
    Lemma search_refine : forall n k (X:FieldType E F f eptr) (p c p' c':eptr),
                          exists (bb:@temporal_backbone _ _ _ _ F _ _ e_hind hs_node_fields _ c c'),
        (** TODO: locate_inner_loop already includes a result... And need to think through calls more... *)
        (locate_inner_loop_count n p c k)~~>(result (p',c')) ≪ [| bb |]~~>result (p',c').
    Proof.
      intros n k X. induction n; simpl.
      intros; assert (p' = p /\ c' = c). admit. (** TODO Fix treatment of return... *) destruct H. subst c'; subst p'.
          exists (init_backbone c). simpl.
          (** TODO twiddle remote interference. Could drop local observation, but actually we're refining something
              too weak to be useful in a larger proof; need the result to account for how k relates to heap contents *) admit.
      (* inductive case *)
      intros.
      (** need to lift the variables bound inside the trace (which is itself inside an existential) into
          the context... specifically nxt... *)
      (** Going to just add axioms; ζ is essentially a new binder embedding anyways. First, need to rewrite under
          the existential to get it to the point of commuting... *)
      assert ((remote (deltaE @ p) ~~>
    remote (deltaE @ c) ~~>
    local
      ((λ (x0 x' : E) (h h' : heap), x0 = x' ∧ h = h' ∧ valOfE x0 ≪≪ k = true) @
       c) ~~>
    (ζnxt =>
    local
      ((λ (x0 x' : E) (h h' : heap), x0 = x' ∧ h = h' ∧ nextOfE x0 = Some nxt) @
       c) ~~> locate_inner_loop_count n c nxt k)) ~~> 
   result (p', c')
   ≈
    (ζnxt =>
   (remote (deltaE @ p) ~~>
    remote (deltaE @ c) ~~>
    local
      ((λ (x0 x' : E) (h h' : heap), x0 = x' ∧ h = h' ∧ valOfE x0 ≪≪ k = true) @
       c) ~~>
    local
      ((λ (x0 x' : E) (h h' : heap), x0 = x' ∧ h = h' ∧ nextOfE x0 = Some nxt) @
       c) ~~> locate_inner_loop_count n c nxt k) ~~> 
   result (p', c')) ).
          etransitivity. apply teq_assoc2.
          etransitivity. apply teq_app. reflexivity. apply teq_assoc2.
          etransitivity. apply teq_app. reflexivity. apply teq_app. reflexivity.
                         apply teq_app. apply teq_lift_binder. reflexivity. simpl.
          etransitivity. apply teq_app. reflexivity. apply teq_app. reflexivity.
                         apply teq_append_binder; reflexivity; simpl.
          etransitivity. apply teq_app. reflexivity. apply teq_lift_binder.
          etransitivity. apply teq_lift_binder.
          apply teq_bound.
          intros.
          etransitivity. apply teq_assoc1.
          etransitivity. apply teq_assoc1.
          apply teq_app.
          etransitivity. apply teq_assoc2.
          apply teq_app. reflexivity.
          apply teq_app. reflexivity.
          apply teq_app. reflexivity. reflexivity.
          reflexivity.
      setoid_rewrite H. clear H.
      (** Let's try an axiom to lift a binder out of a trace in an arbitrary context... *)
      assert (hoist : forall {Q T : Set}{f:Q->@trace T}{C : @trace T -> Prop},
                        (forall q, C (f q)) -> C (bind f)). admit.
      eapply hoist. intros.
      destruct (IHn c q p' c') as [bb' ref'].
      exists (prfx_backbone _ _ _ bb').
      unfold interp_temporal_backbone; fold (@interp_temporal_backbone (eptr * eptr)).
      compute [getF].
      (** Now it looks like we're on track... if my proposed hoist axiom is sound...*)
      rewrite (teq_assoc2 _ ([| bb' |])).
      etransitivity. repeat rewrite teq_assoc2. reflexivity.
      etransitivity. rewrite teq_assoc1. rewrite teq_assoc1. rewrite teq_assoc1. reflexivity.
      apply refine_split; eauto.

      (* Missing some interference here *)

      
      
  End SuperHack.

  

  Lemma search_refine : forall k (X:FieldType E F f eptr) (p c p' c':eptr),
                        exists (bb:@temporal_backbone _ _ _ _ F _ _ e_hind hs_node_fields _ c c'),
      (** TODO: locate_inner_loop already includes a result... And need to think through calls more... *)
      (locate_inner_loop p c k)~~>(result (p',c')) ≪ [| bb |]~~>result (p',c').
  Proof.
    intros k X.
    intros p c. induction (locate_inner_loop p c k).
    cofix.
    setoid_rewrite (trace_dup_eq _ (locate_inner_loop _ _ _)). compute[locate_inner_loop trace_dup]. fold locate_inner_loop.
    intros.
    rewrite 

  Lemma hindsight_test : forall l k, locate_trace l k ≪ locate_spec l k.
  Proof.
    intros.





               
  (** TODO: For refinements, a low-effort workaround in place of writing a trace computation is to
      write a type class hierarchy for generating traces of various constructs, and instead of posing
      refinements of f as:
          ∀ ĩ, trace_of (f ĩ) ≪ f_spec ĩ
      posing them as
          ∀ ĩ, exists t, traces t (f ĩ) /\ t ≪ f_spec ĩ
      (roughly).  Then with the type class instances arranged correctly, a simple tactic that matches
          |- exists t, traces t (?f ?i) /\ t ≪ ?spec ?i
      (possibly stamped out for various arities, and dealing with Γs, etc.) and just applies
          eexists; split; repeat apply does_trace
      (for does_trace as the trace typeclass member, or maybe even just eauto with typeclass_instances
      depending on the typeclass details) could be pretty effective.
  *)
    




End HindsightTesting.














(* TODO: Interference! *)
Fixpoint temporal_backbone {T P R G}{A}{F:Set}{f:F}`{HindsightField T _ f}`{FieldType T F f (ref{T|P}[R,G])}
                           (L:list ((ref{T|P}[R,G])*(ref{T|P}[R,G]))) : @trace A :=
  match L with
    | nil => ε
    | cons (b,p) L'=> (local (observe (λ x h, getF x = p) b))~~>
                             (@temporal_backbone T P R G A _ _ _ _ _ _ L')
  end.

Definition hand (A B:heap -> Prop) : heap -> Prop :=
  λ h, A h /\ B h.

Fixpoint current_backbone'  {T P R G}{F:Set}{f:F}`{HindsightField T _ f}`{FieldType T F f (ref{T|P}[R,G])}
                           (L:list ((ref{T|P}[R,G])*(ref{T|P}[R,G]))) : heap -> Prop :=
  match L with
    | nil => (λ _, True)
    | cons (b,p) L'=> hand (λ h, getF (h[b]) = p) (current_backbone' L')
  end.
Definition current_backbone {T P R G}{A}{F:Set}{f:F}`{HindsightField T _ f}`{FieldType T F f (ref{T|P}[R,G])}
                            (L:list ((ref{T|P}[R,G])*(ref{T|P}[R,G]))) : @trace A :=
  (local (λ h h', h = h' /\ current_backbone' L h)).
