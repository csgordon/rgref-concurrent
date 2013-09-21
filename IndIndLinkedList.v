Require Import Coq.Arith.Arith.
Require Import RGref.DSL.DSL.

(** * An Axiomatic Presentation of an Inductive-Inductive Prepend-only Linked List
    The most natural way to describe this structure uses
    mutual inductive types where the first (list structure) indexes
    the second (relation on lists).
    Unfortunately, Coq lacks direct support for this feature.
    (Agda implements it, but lacks tactics and an equivalent of the
    Program extension that we use heavily.)  This feature is called
    induction-induction.

    Induction-induction can be approximated in Coq two ways:
    1) Using -impredicative-set, which causes all sorts of unpleasant issues since
       eliminations out of Set into Type become heavily constrained, or
    2) Using an axiomatic presentation of the data type and constructor,
       with axioms relating the opaque axiomatic constructors to
       computational definitions.

    LinkedList.v takes the first approach.  Here, we take the second.
    *)

Section RGRefList.

Axiom rgrList : Set.
Axiom rgrl_nil : rgrList.
Axiom list_imm : hrel rgrList.
Axiom rgrl_cons : nat -> ref{rgrList|any}[list_imm,list_imm] -> rgrList.
Inductive list_imm' : hrel rgrList :=
  | imm_nil : forall h h', list_imm' rgrl_nil rgrl_nil h h'
  | imm_cons : forall h h' n tl,
               list_imm' (h[tl]) (h'[tl]) h h' ->
               list_imm' (rgrl_cons n tl) (rgrl_cons n tl) h h'.
Axiom imm_ax : list_imm ⊆⊇ list_imm'.

(** A remarkable number of the generated proof goals can be solved by
    firstorder reasoning or basic proof search. *)
Obligation Tactic := 
  try solve[firstorder]; try constructor; eauto; compute; auto.

Definition list := ref{rgrList | any}[list_imm,list_imm].

Inductive rgr_reach : forall {T:Set}{P R G} (p:ref{T|P}[R,G]) (a:rgrList), Prop :=
  | rgr_reach_tail : forall p n, rgr_reach p (rgrl_cons n p).
Hint Constructors rgr_reach.
Instance reach_rgrList : ImmediateReachability rgrList :=
  { imm_reachable_from_in := fun T P R G p a => rgr_reach p a}.

Inductive rgr_contains : hrel rgrList -> Prop :=
  | rgrcontains : forall RR n,
                  contains (fun c c' h h' => RR (rgrl_cons n c)
                                                (rgrl_cons n c')
                                                h
                                                h) ->
                  rgr_contains RR.

Instance contains_rgrList : Containment rgrList :=
  { contains := rgr_contains }.

(** As usual, folding is a mess, and needs to be split into identity folds and component/field folds.
*)
Instance rgrList_fold : readable_at rgrList list_imm list_imm :=
  { res := rgrList ;
    dofold := fun x => x
  }.
Require Import Coq.Program.Equality.
Lemma precise_list_imm : precise_rel list_imm.
Proof. compute[precise_rel imm_reachable_from_in reach_rgrList]. intros.
       destruct (imm_ax). apply H3. compute in H2. specialize (H2 a a' h h' H1).
       induction H2; eauto; try constructor. 
  try rewrite <- H0; try rewrite <- H; try constructor; try eapply rgr_reach_tail.  
  eapply IHlist_imm'; eauto; firstorder.


  eapply H. eapply trans_reachable with (i := tl). constructor. assumption.
  eapply H0. eapply trans_reachable with (i := tl). constructor. assumption.
Qed.
Hint Resolve precise_list_imm.

(* This should be true, though unpleasant to prove. *)
Axiom imm_stable_precise : forall P, precise_pred P -> stable P list_imm.
Hint Resolve imm_stable_precise.

(* We use the refining alloc' to propagate the allocated form across "statements" *)
Program Definition nil { Γ } : rgref Γ (ref{rgrList|(fun l h=> locally_const list_imm->l=rgrl_nil)}[list_imm,list_imm]) Γ :=
  Alloc rgrl_nil.
Next Obligation. intros. rewrite <- (H1 x x' h h'); eauto. Qed.

(** Here (and for nil) we use alloc', which strengthens the refinement on the returned value to include
    equality between the allocated value and the allocation.  This is how information like that the
    result of cons is a cons cell is communicated across statements. *)
  Check @alloc'.
Program Definition cons { Γ } n (tl meta_tl:list) 
  : rgref Γ (ref{rgrList|any⊓(fun l h => locally_const list_imm -> l=rgrl_cons n (convert_P _ _ _ _))}[list_imm,list_imm]) Γ :=
  (*Alloc! (rgrl_cons' rgrList' P list_imm list_imm n (convert_P _ _ _ tl)).*)
  alloc' _ _ _ (rgrl_cons n (convert_P _ _ _ tl)) _ _ _ _ _ _.
Check cons.
Notation "'RGCons' n tl ::" := (@cons _ n tl) (at level 100).

Record list_container := mkList {head : list}.

Inductive reach_list_head : forall {T:Set}{P R G} (p:ref{T|P}[R,G]) (a:list_container), Prop :=
  | reach_container_head : forall T P R G p lst, @reach_list_head T P R G p (mkList lst).
Instance list_cont_reach : ImmediateReachability list_container :=
  { imm_reachable_from_in := @reach_list_head}.
Instance contains_list_cont : Containment (list_container) :=
  { contains := fun RR => contains (fun l l' h h' => RR (mkList l) (mkList l') h h') }.

Inductive prepend : hrel (list_container ) :=
  | prepended : forall c c' h h' n pf1 pf2 pf3,
                  h'[head c'] = rgrl_cons n (convert_P pf1 pf2 pf3 (head c)) ->
                  prepend c c' h h'
  | prepend_nop : forall c h h', prepend c c h h'.
Hint Constructors prepend.
Lemma precise_prepend : precise_rel prepend.
Proof. unfold precise_rel; intros. induction H1. eapply prepended. rewrite <- H0. eauto.
  constructor. repeat red. destruct c'. simpl. eapply reach_container_head.
  constructor.
 Qed.
Hint Resolve precise_prepend.
Lemma refl_prepend : hreflexive prepend.
Proof.
  red. intros. constructor.
Qed.
Hint Resolve refl_prepend.

(* Folding anything into this list container is a no-op: the head already points to a rgrList' with guarantee list_imm,
   so no further restriction is necessary / possible. *)
Instance lst_cont_fold : readable_at list_container prepend prepend := id_fold.

Require Import Coq.Program.Tactics.
Program Definition newList { Γ } : rgref Γ (ref{list_container|any}[prepend,prepend]) Γ :=
  x <- @nil _;
  Alloc (mkList (convert_P _ _ _ x)).

Require Import Coq.Logic.ProofIrrelevance.
Program Definition prefix { Γ } (n:nat) (l:ref{list_container|any}[prepend,prepend]) 
  : rgref Γ unit Γ :=
  (*x <- @cons _ P any _ n (@head _ _ (!l));*)
  (* x <- (RGCons n (@head _ _ (!l)) );*)
  x <- @cons _ n (@head (!l)) ({{{@head (!l)}}});
  [l]:= (mkList (@convert_P _ _ (any) _ _ _ _ _ _ x)).
Next Obligation.
  eapply prepended.
  unfold list in x.
  assert (w := heap_lookup2 h x).
  unfold pred_and in w. destruct w. assert (@locally_const rgrList list_imm). repeat intro.
  destruct imm_ax. specialize (H3 _ _ _ _ H2).
  induction H3; eauto.
  specialize (H1 H2). clear H2.
  unfold list in *.
  rewrite type_based_nonaliasing.
  compute [head].
  (*Unset Printing Notations.*)
  rewrite conversion_P_refeq. (* Fix some differences in normal form of implicit params... *) unfold pred_and. unfold head in *.
  rewrite H1. repeat f_equal.

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
  admit. (* OK: list_container <> rgrList' *)
Qed.

End RGRefList.
