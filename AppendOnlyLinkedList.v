Require Import Coq.Arith.Arith.
Require Import RGref.DSL.DSL.

(** * A "Postpend"-only Linked List
    We side-step the induction-recursion issues we hit in the prepend-only
    example by doing append-only via set-once options.  This makes it
    much easier to prove things about manipulating the list.  The downside
    is that we can't prevent cycles - doing so would need to talk about
    reachability through cons cells in the definition of the list type,
    forcing induction-recursion again.
*)

Section AppendOnlyLinkedList.

Require Import Coq.Program.Equality.

Inductive optset (A:Set) : hrel (option A) :=
  | optset_nop : forall (o:option A) h h', optset A o o h h'
  | optset_set : forall (a:A) h h', optset A None (Some a) h h'.
Inductive option_reach : forall (A:Set)`(ImmediateReachability A) {T:Set}{P R G} (p:ref{T|P}[R,G]) (ao:option A), Prop :=
  | opt_reach_some : forall (A:Set)(a:A)`(ImmediateReachability A) {T:Set}{P R G} (p:ref{T|P}[R,G]),
                         imm_reachable_from_in p a ->
                         option_reach A _ p (Some a).
Instance reach_option {A:Set}`{ImmediateReachability A} : ImmediateReachability (option A) :=
  { imm_reachable_from_in := fun T P R G p oa => option_reach A _ p oa }.
Lemma optset_precise : forall A `(ImmediateReachability A), precise_rel (optset A).
Proof. compute. intros. inversion H2; subst; constructor. Qed.
Hint Resolve optset_precise.

Inductive appList : Set :=
  | rcons : nat -> ref{option appList|any}[optset appList,optset appList] -> appList.


Definition alist := ref{option appList|any}[optset appList, optset appList].


(** A remarkable number of the generated proof goals can be solved by
    firstorder reasoning or basic proof search. *)
Obligation Tactic := 
  try solve[firstorder]; try constructor; eauto; compute; auto.

Require Import Coq.Program.Tactics.

(* TODO: This is only a first cut, and doesn't allow polymorphic recursion.  Eventually we'll need to support
   polymorphic recursion and functions with more curried arguments. *)
Axiom RGFix : forall { Γ Γ' }(t t':Set), ((t -> rgref Γ t' Γ') -> (t -> rgref Γ t' Γ')) -> t -> rgref Γ t' Γ'.

Check @rgfold.
(* TODO: Contains instance for options *)
Instance option_fold {A:Set}`{rel_fold A} : rel_fold (option A) :=
  { rgfold := fun R G => option (rgfold havoc (fun a a' h h' => G (Some a) (Some a') h h')) }.
Instance appList_fold : rel_fold appList :=
  { rgfold := fun R G => appList }. (* TODO: This is technically unsound - need to recursively rewrite tail pointer relations... *)
Lemma optset_refl : forall (A:Set), hreflexive (optset A).
Proof. compute; intuition; constructor. Qed.
Hint Resolve optset_refl.
Inductive opt_contains {A:Set}`{Containment A} : hrel (option A) -> Prop :=
  | some_contains : forall RR (h h':heap),
                      contains (fun a a' h h' => RR (Some a) (Some a') h h') ->
                      opt_contains RR.
Instance option_contains {A:Set}`{Containment A} : Containment (option A) :=
  { contains := opt_contains }.
Instance appList_contains : Containment appList. Admitted.
 (* want something like { contains := fun RR => RR = (optset ...) }. but need to handle cons/option shifting *)

Print ImmediateReachability.
Inductive applist_reachability : forall (T:Set) (P:hpred T) (R G:hrel T), ref{T|P}[R,G] -> appList -> Prop :=
  | tail_reach : forall n tl, applist_reachability (option appList) any (optset appList) (optset appList) tl (rcons n tl).
Instance applist_reachable : ImmediateReachability appList :=
  { imm_reachable_from_in := applist_reachability }.

Program Definition alist_append {Γ}(n:nat)(l:alist) : rgref Γ unit Γ :=
  (RGFix _ _ (fun (rec:alist->rgref Γ unit Γ) =>
             (fun tl => match !tl with
                          | None => ( f <- Alloc None;
                                      [ tl ]:= (Some (rcons n f))
                                    )
                          | Some l' => (match l' with
                                          | rcons n' tl' => rec tl'
                                        end)
                        end))) l.
Next Obligation. compute in Heq_anonymous. compute. rewrite <- Heq_anonymous. constructor. Qed. 

Program Example test1 {Γ} : rgref Γ unit Γ :=
  l <- Alloc None;
  u <- alist_append 3 l;
  v <- alist_append 4 l;
  alist_append 5 l.

End AppendOnlyLinkedList.
