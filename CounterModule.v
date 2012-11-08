Require Import RGref.DSL.DSL.

(** * Counter Module : Abstract Data Types with Rely-Guarantee References *)

(** Rely-guarantee references work just fine with traditional encapsulation
    methods, such as ML-style modules.  Let's define a module type for an
    abstract counter *)
Module Type Counter.
  Parameter counter_val : Set.
  Parameter increasing_counter : hrel counter_val.
  Definition counter := ref{counter_val|any}[increasing_counter,increasing_counter].
  Parameter read : counter -> nat.
  Parameter increment : forall { Γ }, counter -> rgref Γ unit Γ.
  Parameter create_counter : forall { Γ }, unit -> rgref Γ counter Γ.
End Counter.
(** These are all the same operations described in the MonotonicCounter example.
    In fact, we'll hijack those definitions to define our counter module
    instantiation. *)
Module SomeCounter : Counter.
  Require Import MonotonicCounter.
  Definition counter_val := nat.
  Definition increasing_counter := increasing.
  Definition counter := monotonic_counter.
  Definition read := read_counter.
  Definition increment := @inc_monotonic.
  Definition create_counter := @mkCounter.
End SomeCounter.

(** Now we can experiment with opening the module we just defined. *)
Import SomeCounter.
(** The type counter_val is opaque.  But notice that we exposed the
    fact that the counter type is a reference. *)
Print counter.
Print counter_val.

(** We can write an expression to dereference the reference, but
    because increasing_counter is abstract, we cannot even prove
    the reflexivity requirement to allow the read, let alone
    reason about relation folding. 
<<
Program Definition get_counter_val (c:counter) := deref _ _ c.
>>
*)

(** But we can still use it as a standard ADT. In general, any subcomponent
    of the reference exposed can be encapsulated or not, though the more
    details of relations or predicates that are exposed, the more likely
    it is that extra lemmas will need to be exported from the module in order
    for it to be useful. *)
Example test_some_counter { Γ } (_:unit) : rgref Γ unit Γ :=
  x <- create_counter tt;
  _ <- increment x;
  increment x.
