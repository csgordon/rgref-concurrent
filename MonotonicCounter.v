Require Import Coq.Arith.Arith.
Require Import RGref.DSL.DSL.

(** * A Monotonic Counter
   A monotonically increasing counter.*)

Definition increasing : hrel nat :=
  (fun n => fun n' => fun _ => fun _ => n <= n').
Hint Unfold increasing.
(** We'll give the Program extension some hints for this module *)
Local Obligation Tactic := intros; eauto with arith; compute; eauto with arith.

(** Now the definition of a verified monotonically increasing counter is
    barely more work than a completely unchecked counter. *)
Program Definition monotonic_counter := ref nat any increasing increasing.

Program Definition read_counter (c:monotonic_counter) : nat := !c.

Program Definition inc_monotonic { Γ } (p:monotonic_counter) : rgref Γ unit Γ :=
  [p]:= !p + 1.

Program Definition mkCounter { Γ } (u:unit) : rgref Γ monotonic_counter Γ :=
  Alloc 0.

Program Example test_counter { Γ } (u:unit) : rgref Γ unit Γ :=
  x <- mkCounter tt;
  inc_monotonic x.