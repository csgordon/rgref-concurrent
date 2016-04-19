Require Import RGref.DSL.DSL.
Require Import TrieberStack.
Require Import ProducerConsumer.

(* The fact that the stack only escapes this scope as a consumer means that this
   code /will/ terminate: other could either do nothing, or pop some number of elements, but it can't make the stack any larger than three elements *)
Definition client {Δ} (other : consumer -> rgref Δ unit Δ) : rgref Δ unit Δ :=
  stack <- alloc_ts tt;
  _ <- push_ts stack 3;
  _ <- push_ts stack 4;
  _ <- push_ts stack 5;
  _ <- other (consumer_of_ts stack);
  RGFix _ _ (fun again _ =>
               opt <- pop_ts stack;
               match opt with
               | None => rgret tt
               | Some n => again tt
               end) tt.
