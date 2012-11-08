Require Import Coq.Arith.Arith.
Require Import RGref.DSL.DSL.

(** * A Prepend-only Pure List
   A mutable reference to a functional list, where the reference may only be mutated
   by prepending an element to the list. *)

Inductive prepend_only {A:Set} : hrel (list A) :=
  | prepended : forall a l h h', prepend_only l (a::l)%list h h'
  | prepend_refl : forall l h h', prepend_only l l h h'.
Hint Constructors prepend_only.

Local Obligation Tactic := 
  compute;
  intros; repeat match goal with
          | [ H : prepend_only _ _ _ _ |- _ ] => induction H
          end; eauto.

(** For simplicity, we'll assume A is pure, though in general
    we need containment and folding for lists, which is hard
    because a relation could be sensitive to list size *)
Program Definition prepend_only_list (A:Set)`{PA:pure_type A} := ref (list A) any prepend_only prepend_only.

Program Definition read_list {A}`{pure_type A} (l:prepend_only_list A) : list A := !l.

Program Definition prepend { Γ }{A:Set}`{pure_type A} (a:A) (p:prepend_only_list A) : rgref Γ unit Γ :=
  [p]:=(a::(!p))%list.

Program Definition mkPrependList { Γ }{A:Set}`{pure_type A} (_:unit) : rgref Γ (prepend_only_list A) Γ :=
  Alloc nil.

Program Example test_list { Γ } (u:unit) : rgref Γ (list nat) Γ :=
  x <- mkPrependList tt;
  _ <- prepend 3 x;
  _ <- prepend 4 x;
  rgret (!x).
