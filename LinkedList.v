Require Import Coq.Arith.Arith.
Require Import RGref.DSL.DSL.

(* Since this file is in flux, let's force MonotonicCounter to
   build first so I can check changes to dsl more easily. *)
Require Import MonotonicCounter.

(** * A Prepend-only Linked List
    The most natural way to describe this structure uses
    induction-recursion, the simultaneous definition of a data type
    and a function or predicate type over that datatype. 
    Unfortunately, Coq lacks direct support for this feature.
    (Note: in a pure-functional setting, this is rarely an
    issue because maintaining an external predicate over a
    data structure usually isn't much more effort than the
    inductive-recursive definition.)

    This structure is based on the common-in-folklore encoding of
    induction-recursion into Coq.  A good reference (with a couple
    typos) is Venanzio Capretta's unpublished draft:
    "A Polymorphic Representation of Induction-Recursion"
    http://www.cs.ru.nl/~venanzio/publications/induction_recursion.pdf (Retrieved 9/11/12)

    The core idea is to abstract recursive members and predicates on
    recursive members in the constructors (but not the type itself).
    This makes the structure "large" in that it allows undesired 
    instantiations, but this is then coupled with a predicate over 
    the enlarged structure that ensures it is only instantiated with
    the intended type (itself).  In Venanzio's draft and the standard
    treatment, the structure then becomes a dependent product.
    Rather than using dependent products, we take advantage of the
    refinement predicate included in the ref type constructor.

    A less invasive change from how recursive structures are written in
    pure-functional style is the fact that because refinements
    on recursive members of a data type are defined on the
    /dereference/ of that member, it is not possible to define
    a structural fixpoint (i.e. Coq's Fixpoint) over these
    structures, since a dereference of a pointer is not a syntactic
    subterm.  So in general (including here) we must define predicates
    on linked data structures as data structures in Prop.

    In general, with proper refinements, it should be reasonable to
    define a well-founded relation for some structures and use the
    Fix combinator for recursion.  We find the inductive proposition
    approach simpler in most cases.
    *)

Section RGRefList.

(** The inductive list structure, with the cons constructor
    widened polymorphically to support the induction-recursion
    encoding. *)
Inductive rgrList' : Set :=
  | rgrl_nil' : rgrList'
  | rgrl_cons' : forall (C:Set) (P:hpred C) (R G:hrel C),
                 nat -> ref{C|P}[R,G] -> rgrList'.
Inductive list_imm : hrel rgrList' :=
  | imm_nil : forall h h', list_imm rgrl_nil' rgrl_nil' h h'
  | imm_cons : forall h h' P R G n (tl:ref{rgrList'|P}[R,G]),
               list_imm (h[tl]) (h'[tl]) h h' ->
               list_imm (rgrl_cons' rgrList' P R G n tl) (rgrl_cons' rgrList' P R G n tl) h h'.
(** Ideally we'd like to enforce correct instantiation of 
    the recursive components via a predicate like this:
<<
Inductive lcheck : hpred rgrList' :=
  | chk_nil : forall h, lcheck rgrl_nil' h
  | chk_cons : forall h n (r:ref{rgrList'|lcheck}[local_imm,local_imm]),
                 lcheck (rgrl_cons' rgrList' lcheck local_imm local_imm n r) h.
>>
    Unfortunately, this does not satisfy Coq's strict positivity checker
    (though it is, in fact, strictly positive).  In general, any use of 
    a predicate-being-defined as the hpred argument to ref will
    not satisfy Coq's positivity checker.

    Instead, we define an auxiliary "plumbing" predicate that
    1) forces all R/Gs in references to the same (concrete) value
    2) "plumbs" the given hpred through all references in the list
*)
Inductive plumb : hpred rgrList' -> hpred rgrList' :=
  | plumb_nil : forall P h, plumb P rgrl_nil' h
  | plumb_cons : forall P R G h n (r:ref{rgrList'|P}[R,G]),
                   plumb P (h[r]) h ->
                   plumb P (rgrl_cons' rgrList' P R G n r) h.

Require Import Coq.Program.Equality.
Lemma plumb_stable : forall P, stable P list_imm -> stable (plumb P) list_imm.
Proof.
  intros. compute. firstorder. induction H1; try constructor.
  dependent induction H0.
      (* This SHOULD be using discriminate on two different ctors, but apparently
         this is not discriminable... I suspect -impredicative-set is the issue *)
      rewrite <- x. constructor.
      rewrite <- x. eapply plumb_cons. 
      (* This SHOULD be a matter of just doing "injection x." to prove r and
         tl are equal, substitution, and firstorder reasoning.  Instead,
         I need to work around the fact that because rgrList' is a large
         type in an impredicative universe, I can't project out of it to
         get the equality (even though the equality is in Prop, and the values...
         the values are in Set, which is also impredicative, but they're
         instances of ref, which is small as currently defined. *)
Admitted.
Hint Resolve plumb_stable.

Axiom stable_P_hack : forall P, stable P list_imm.
Hint Resolve stable_P_hack.

(** A remarkable number of the generated proof goals can be solved by
    firstorder reasoning or basic proof search. *)
Obligation Tactic := 
  try solve[firstorder]; try constructor; eauto; compute; auto.

(** I suspect we could simplify away much of this Q stuff, we seem to
    only instantiate Q with any. *)

Definition list P Q := ref{rgrList' | (plumb P) ⊓ P ⊓ Q}[list_imm,list_imm].

Inductive rgr_reach : forall {T:Set}{P R G} (p:ref{T|P}[R,G]) (a:rgrList'), Prop :=
  | rgr_reach_tail : forall T P R G p n, rgr_reach p (rgrl_cons' T P R G n p).
(*  | rgr_reach_trans : forall T P R G (p:ref{T|P}[R,G]) P' R' G' h n tl, 
                        rgr_reach p (h[tl]) ->
                        rgr_reach p (rgrl_cons' rgrList' P' R' G' n tl).*)
Hint Constructors rgr_reach.
Instance reach_rgrList : ImmediateReachability rgrList' :=
  { imm_reachable_from_in := fun T P R G p a => rgr_reach p a}.

Inductive rgr_contains : hrel rgrList' -> Prop :=
  | rgrcontains : forall RR (C:Set){CC:Containment C} P R G n,
                  contains (fun c c' h h' => RR (rgrl_cons' C P R G n c)
                                                (rgrl_cons' C P R G n c')
                                                h
                                                h) ->
                  rgr_contains RR.

Instance contains_rgrList : Containment rgrList' :=
  { contains := rgr_contains }.

(** I don't think I can actually implement relation folding for this encoding!
    the top-level result type would be rgrList' again, because the stupid
    encoding forces the type params into being constructor params, not to
    mention the fact that this encoding must use dependent constructors. :-/
<<  
Fixpoint rgr_fold (R G:hrel rgrList') : Set :=
  

Instance rgrList_fold : rel_fold rgrList' :=
  { rgfold := rgr_fold }.
>>
*)
Instance rgrList_fold : rel_fold rgrList'. Admitted.
Require Import Coq.Program.Equality.
Lemma precise_list_imm : precise_rel list_imm.
Proof. compute[precise_rel imm_reachable_from_in reach_rgrList]. intros. induction H1; eauto; try constructor. 
  try rewrite <- H0; try rewrite <- H; try constructor; try eapply rgr_reach_tail.  
  eapply IHlist_imm; eauto; firstorder. dependent induction H1; subst. 
  eapply H; eauto.
      assert (tmp := rgr_reach_tail _ _ _ _ tl n). 
      assert(@imm_reachable_from_in rgrList' _ _ _ _ _ tl (rgrl_cons' rgrList' P R G n tl)). 
      apply tmp.
      eapply (trans_reachable _ _ _ _ _ _ H1 H2).
  eapply H; eauto.
      assert (tmp := rgr_reach_tail _ _ _ _ tl n). 
      assert(@imm_reachable_from_in rgrList' _ _ _ _ _ tl (rgrl_cons' rgrList' P R G n tl)). 
      apply tmp.
      eapply (trans_reachable _ _ _ _ _ _ H3 H2).
  eapply H0; eauto.
      assert (tmp := rgr_reach_tail _ _ _ _ tl n). 
      assert(@imm_reachable_from_in rgrList' _ _ _ _ _ tl (rgrl_cons' rgrList' P R G n tl)). 
      apply tmp.
      eapply (trans_reachable _ _ _ _ _ _ H3 H2).
      (** TODO: CLEAN THIS UP!!! *)
Qed.
Hint Resolve precise_list_imm.
Lemma plumb_precise : forall P, precise_pred P -> precise_pred (plumb P).
Proof. compute[precise_pred imm_reachable_from_in reach_rgrList]. intros.
  induction H0; eauto; constructor.
  rewrite <- H1; try constructor; try eapply rgr_reach_tail.
  eapply IHplumb; firstorder. eapply H1.
  assert (imm_reachable_from_in r (rgrl_cons' rgrList' P R G n r)). red. unfold reach_rgrList. eapply rgr_reach_tail.
  eapply (trans_reachable _ _ _ _ _ _ H4 H2).
  (** TODO: CLEAN THIS UP!!! *)
Qed.
Hint Resolve plumb_precise.

(* We use the refining alloc' to propagate the allocated form across "statements" *)
Program Definition nil { Γ }{P:hpred rgrList'}`{stable P list_imm}`{precise_pred P}`{forall h, P rgrl_nil' h} : rgref Γ (list P (fun l h=> locally_const list_imm->l=rgrl_nil')) Γ :=
  Alloc! rgrl_nil'.
Next Obligation. firstorder. eapply plumb_stable; eauto. firstorder. Qed.
(** The obligation just solved should be automatically dispatched: obligation hint runs firstorder and eauto, and plumb_stable is a resolution hint! *)
Next Obligation. constructor. Qed. (** And now there's another that should be auto-solved *)
Next Obligation. firstorder. eapply plumb_precise; eauto. firstorder. Qed. (** Ditto! *)

(** Here (and for nil) we use alloc', which strengthens the refinement on the returned value to include
    equality between the allocated value and the allocation.  This is how information like that the
    result of cons is a cons cell is communicated across statements. *)
Program Definition cons { Γ P Q}`{precise_pred P} n (tl meta_tl:@list P Q) 
  : rgref Γ (list P _ (* (fun l h=> locally_const list_imm->l=rgrl_cons' rgrList' P list_imm list_imm n (convert_P _ _ _ tl))*)) Γ :=
  (*Alloc! (rgrl_cons' rgrList' P list_imm list_imm n (convert_P _ _ _ tl)).*)
  alloc' _ _ _ (rgrl_cons' rgrList' P list_imm list_imm n (convert_P _ _ _ tl)) (rgrl_cons' rgrList' P list_imm list_imm n (convert_P _ _ _ meta_tl)) _ _ _ _ _.
Next Obligation. firstorder. eapply plumb_stable; eauto. firstorder. eapply stable_P_hack; eauto. Qed.
(** Again, previous goal is solved by things the obligation tactic should be doing... *)
Next Obligation. constructor.
  rewrite conversion_P_refeq. unfold list in *. eapply pred_and_proj1. eapply pred_and_proj1. eapply heap_lookup2.
  Admitted. (** TODO: Solve obligation *)
Next Obligation. firstorder. eapply plumb_precise; eauto. firstorder. Qed.
(** AGAIN with the stupid goals that should be solved with the obligation hint! *)
Check cons.
Notation "'RGCons' n tl ::" := (@cons _ _ _ _ n tl ({{{tl}}})) (at level 100).

Record list_container {P Q} := mkList {head : @list P Q}.

Inductive reach_list_head : forall {Q Q'}{T:Set}{P R G} (p:ref{T|P}[R,G]) (a:@list_container Q Q'), Prop :=
  | reach_container_head : forall Q Q' T P R G p lst, @reach_list_head Q Q' T P R G p (mkList Q Q' lst).
Instance list_cont_reach {P Q} : ImmediateReachability (@list_container P Q) :=
  { imm_reachable_from_in := @reach_list_head P Q}.
Instance contains_list_cont {P Q}: Containment (@list_container P Q) :=
  { contains := fun RR => contains (fun l l' h h' => RR (mkList P Q l) (mkList P Q l') h h') }.

Inductive prepend {P Q} : hrel (@list_container P Q) :=
  | prepended : forall c c' h h' n pf1 pf2 pf3,
                  h'[head c'] = rgrl_cons' rgrList' P list_imm list_imm n (convert_P pf1 pf2 pf3 (head c)) ->
                  prepend c c' h h'
  | prepend_nop : forall c h h', prepend c c h h'.
Hint Constructors prepend.
Lemma precise_prepend : forall P Q, precise_rel (@prepend P Q).
Proof. unfold precise_rel; intros. induction H1. eapply prepended. rewrite <- H0. eauto.
  constructor. repeat red. destruct c'. simpl. eapply reach_container_head.
  constructor.
 Qed.
Hint Resolve precise_prepend.

(* Folding anything into this list container is a no-op: the head already points to a rgrList' with guarantee list_imm,
   so no further restriction is necessary / possible. *)
Instance lst_cont_fold {P Q}: rel_fold (@list_container P Q) := {
  rgfold := (fun R => fun G => @list_container P Q)
}.

Require Import Coq.Program.Tactics.
Program Definition newList { Γ P}`{precise_pred P} : rgref Γ (ref{(@list_container P any)|any}[prepend,prepend]) Γ :=
  x <- @nil _ P _ _ _;
  Alloc (mkList P any (convert_P _ _ _ x)).
Next Obligation. Admitted. (** Not sure where to pull the assumption that P is true of nil and an arbitrary heap *)
Next Obligation. firstorder. Qed. (** This explicit solution shouldn't be necessary; the local tactic above includes 'try firstorder' first thing! *)

Check @convert_P.
Require Import Coq.Logic.ProofIrrelevance.
Program Definition prefix { Γ }{P:hpred rgrList'}`{precise_pred P} (n:nat) (l:ref{list_container|any}[prepend,prepend]) 
  : rgref Γ unit Γ :=
  (*x <- @cons _ P any _ n (@head _ _ (!l));*)
  (* x <- (RGCons n (@head _ _ (!l)) );*)
  x <- @cons _ P any _ n (@head _ _ (!l)) ({{{@head _ _ (!l)}}});
  [l]:= (mkList P any (@convert_P _ _ ((plumb P) ⊓ P ⊓ any) _ _ _ _ _ _ x)).
Next Obligation. compute. auto. Qed.
Next Obligation. compute. auto. Qed.
Next Obligation. compute; auto. Qed.
Next Obligation. firstorder. Qed. (** This explicit solution shouldn't be necessary; the local tactic above includes 'try firstorder' first thing! *)
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.
Next Obligation.
  eapply prepended.
  unfold list in x.
  assert (w := heap_lookup2 h x).
  unfold pred_and in w. destruct w. assert (@locally_const rgrList' list_imm). repeat intro. induction H2; eauto.
  specialize (H1 H2). clear H2.
  unfold list in *.
  rewrite type_based_nonaliasing.
  compute [head].
  (*Unset Printing Notations.*)
  rewrite conversion_P_refeq. (* Fix some differences in normal form of implicit params... *) unfold pred_and. unfold head in *.
  rewrite H1. repeat f_equal.
  assert ((prefix_obligation_4 Γ P precise_pred0 n l) = (prefix_obligation_10 Γ P precise_pred0 n l x)).
  apply proof_irrelevance. rewrite H2.
  assert ((prefix_obligation_5 Γ P precise_pred0 n l) = (prefix_obligation_11 Γ P precise_pred0 n l x)).
  apply proof_irrelevance.
  reflexivity.

  (** We're now solving a goal:
<<
list_container <> rgrList'
>>
      which is obviously true.  Unforunately, Coq cannot solve this goal with its
      built-in discriminate tactic (for solving inequalities between structurally
      different terms) because apparently Coq does not allow discriminating
      inequalities between terms in Set (e.g., data structure types).  There are
      ways to handle this:

      http://stackoverflow.com/questions/12224318/how-to-solve-goals-with-invalid-type-equalities-in-coq

      by manually projecting type inequalities to value inequalities, but it's 
      not really scalable, and difficult to automate :-/ *)
  admit.
Qed.

End RGRefList.
