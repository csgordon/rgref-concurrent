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

Inductive appList : Set :=
  | rcons : nat -> ref{option appList|any}[optset appList,optset appList] -> appList.

Definition alist := ref{option appList|any}[optset appList, optset appList].

(** A remarkable number of the generated proof goals can be solved by
    firstorder reasoning or basic proof search. *)
Obligation Tactic := 
  try solve[firstorder]; try constructor; eauto; compute; auto.

Require Import Coq.Program.Tactics.

Global Instance appList_fold : rel_fold appList :=
  { rgfold := fun R G => appList }. (* TODO: This is technically unsound - need to recursively rewrite tail pointer relations... *)

Global Instance appList_contains : Containment appList. Admitted.
 (* want something like { contains := fun RR => RR = (optset ...) }. but need to handle cons/option shifting *)

Print ImmediateReachability.
Inductive applist_reachability : forall (T:Set) (P:hpred T) (R G:hrel T), ref{T|P}[R,G] -> appList -> Prop :=
  | tail_reach : forall n tl, applist_reachability (option appList) any (optset appList) (optset appList) tl (rcons n tl).
Global Instance applist_reachable : ImmediateReachability appList :=
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
