Require Import RGref.DSL.DSL.

(** * A Mutable Binary Tree *)

(** ** A Pure Tree of Non-Zero Naturals
   To further familiarize ourselves, we implement a pure-functional tree containing arbitrary non-zero nats. *)

Section PureTree.
Inductive btree' : Set :=
  | lf' : btree'
  | nd' : forall (C:Set) (P:C->Prop) (a b:C) (pa:P a) (pb:P b), nat -> btree'.
Inductive gtz' : btree' -> Prop :=
  | gtzlf : gtz' lf'
  | gtznd : forall (C:Set) (P:C->Prop) (a b:C) (pa:P a) (pb:P b) (n:nat),
                   n > 0 -> gtz' (nd' C P a b pa pb n).
Inductive PTCheck : btree' -> Prop :=
  | lf_check : PTCheck lf'
  | nd_check : forall (n:nat) (a b:btree') (pa:PTCheck a) (pb:PTCheck b) (gta:gtz' a) (gtb:gtz' b),
                      PTCheck (nd' btree' gtz' a b gta gtb n).
Definition btree := {t:btree'|PTCheck t}.
Definition gtz (t:btree) := gtz' (proj1_sig t).
Definition lf := exist _ lf' lf_check.
Definition nd n (a b:btree) pa pb := exist _ (nd' btree' gtz' (proj1_sig a) (proj1_sig b) pa pb n) 
                                             (nd_check n (proj1_sig a) (proj1_sig b) (proj2_sig a) (proj2_sig b) pa pb).

End PureTree.
(*
Axiom sref_axiom : forall (A:Type), Type.
Inductive sref (A:Type) : Type :=
 | mksref : nat -> sref A.
Axiom sref_read : forall {A}, sref A -> A.
(*CoInductive natskel (C:Type) (P:hpred C) (R G:hrel C) : Set :=
  | leaf : natskel C P R G
  | node : nat -> ref{C|P}[R,G] -> natskel C P R G.*)
Inductive natskel (C:Set) (P:C->Prop): Set :=
  | leaf : natskel C P
  | node : nat -> sref (natskel C P) -> natskel C P.

Fixpoint ll_of_len (n:nat) (P:forall {A}, nat->A->Prop): Set :=
  match n with
  | 0 => natskel unit (fun _ => True)
  | S n' => natskel (ll_of_len n' P) (P _ n')
  end.
Check ll_of_len.
Fixpoint sorted {A} (n:nat) : A -> Prop := 
  fun l =>
    match (n,l) with
      | (0,y) => True
      | (S n',leaf) => True
      | (S n',node val tl) => val > 0 /\ sorted (sref_read tl)
    end.

(*CoInductive cotype : Type -> Type :=
  | μ : forall (τ:Set), cotype (natskel τ) -> cotype τ.*)

Inductive sorted : forall {C P}, natskel C P -> Prop :=
  | sleaf : forall C P, sorted (leaf C P)
  | snode : forall C n (tl:natskel C (sorted C sorted), n > 0 -> sorted (sref_read tl) -> sorted (node _ _ n tl)
.


Fixpoint btree 

Definition bound {C P R G}: hpred (natskel C P R G) :=
  fun node => fun h =>
    match node with
    | leaf => True
    | node n tl => n > 0
    end.
*)
