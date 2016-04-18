Require Import AtomicCounter.
Require Import RGref.DSL.DSL.
Require Import RGref.DSL.Concurrency.

Local Obligation Tactic := intros; eauto with arith; compute; eauto with arith.

(* Extend the atomic counter with a lock-free increment-by-n *)
Program Definition incr {Δ} (p:monotonic_counter) (n:nat) : rgref Δ unit Δ :=
  RGFix _ _ (fun retry (b:bool) =>
  x <- !p;
  success <- (CAS(p,x,x+n));
  if success then rgret tt else retry false) false.        

(* Write a generic imperative iterator *)
Definition forRG {T:Set} {Δ}  : list T -> (T -> rgref Δ unit Δ) -> rgref Δ unit Δ :=
  RGFixT2 _ _ _ (fun forRG (l:list T) (C:T -> rgref Δ unit Δ) =>
  match l with
  | nil => rgret tt
  | cons t l' => (_ <- C t;
                  forRG l' C)
  end).

(* We can write an iteration to increment the counter by each value in the list *)
Definition doIncrements {Δ} (c:monotonic_counter) (l:list nat) : rgref Δ unit Δ :=
  forRG l (fun n => incr c n).

(* And we can write a function of the same arguments, which does something arbitrary but respects the transition invariants of the counter. *)
Definition tooManyIncrements {Δ} (c:monotonic_counter) (l:list nat) : rgref Δ unit Δ :=
  forRG l (fun n => (_ <- incr c n; _ <- incr c n; incr c 1)).
