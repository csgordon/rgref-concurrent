Require Import Coq.Arith.Arith.
Require Import RGref.DSL.DSL.

(** * A Strictly Positive Monotonic Counter
   A monotonically increasing non-zero counter.
   A slightly better basic example than the plain monotonic counter since this one has a nontrivial refinement. *)

Definition increasing : hrel nat := (fun n n' _ _ => n <= n').
Hint Unfold increasing.

Definition pos : hpred nat := (fun n _ => n > 0).

(** We'll give the Program extension some hints for this module *)
Local Obligation Tactic := intros; eauto with arith; compute; eauto with arith.

(** Now the definition of a verified monotonically increasing counter is
    barely more work than a completely unchecked counter. *)
Program Definition posmonotonic_counter := ref{nat|pos}[increasing,increasing].

Program Definition read_counter (c:posmonotonic_counter) : nat := !c.

Program Definition inc_monotonic { Γ } (p:posmonotonic_counter) : rgref Γ unit Γ :=
  [p]:= !p + 1.

Program Definition mkCounter { Γ } (u:unit) : rgref Γ posmonotonic_counter Γ :=
  Alloc 1.

Program Example test_counter { Γ } (u:unit) : rgref Γ unit Γ :=
  x <- mkCounter tt;
  inc_monotonic x.