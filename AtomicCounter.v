Require Import Coq.Arith.Arith.
Require Import RGref.DSL.DSL.
Require Import RGref.DSL.Concurrency.

(** * A Lock-free Monotonically Increasing Counter
   A monotonically increasing counter.*)

Definition increasing : hrel nat :=
  (fun n => fun n' => fun _ => fun _ => n <= n').
Hint Unfold increasing.
(** We'll give the Program extension some hints for this module *)
Local Obligation Tactic := intros; eauto with arith; compute; eauto with arith.

(** Now the definition of a verified monotonically increasing counter is
    barely more work than a completely unchecked counter. *)
(** TODO: Eventually need to swith this to special concurrency refs *)
Program Definition monotonic_counter := ref nat any increasing increasing.

Program Definition read_counter (c:monotonic_counter) : nat := !c.

Check RGFix.

Program Definition inc_atomic { Γ } (p:monotonic_counter) : rgref Γ unit Γ :=
  RGFix _ _ (fun retry => fun b =>
  let x := read_counter p in
  success <- (CAS(p,x,x+1));
  (if success then rgret tt else retry false)) false.

Program Definition mkCounter { Γ } (u:unit) : rgref Γ monotonic_counter Γ :=
  Alloc 0.

Program Example test_counter { Γ } (u:unit) : rgref Γ unit Γ :=
  x <- mkCounter tt;
  inc_atomic x.