Require Import Arith List.
Set Implicit Arguments.
Require Export Coq.Init.Datatypes.
Require Import Coq.Program.Equality.

(** * Heterogeneous Environment List
    This doesn't diverge too wildly from standard HList implemenations.
    A good reference, and the implementation this version is based on is
    http://adam.chlipala.net/cpdt/html/DataStruct.html
*)

Section envlist.
  (*Definition var := nat.
  Definition var_dec := eq_nat_decide.*)
  Inductive var : Type :=
    | VZero : var
    | VSucc : var -> var.
  Lemma var_dec : forall (a b:var), {a=b}+{a<>b}.
    intro a. induction a; intros; dependent inversion b. left; reflexivity. right. discriminate. right. discriminate.
    induction (IHa v). subst. left; reflexivity. right. intro bad. inversion bad. apply b0. auto.
  Defined.

  Definition tyenv := list (var * Set).
  Inductive tymember (x:var) (t:Set) : list (var*Set) -> Type :=
  | TFirst : forall tl, tymember x t ((x,t)::tl)
  | TLater : forall y ty tl, tymember x t tl -> tymember x t ((y,ty)::tl).
  Fixpoint tyrem (x:var) (t:Set) {l:list(var*Set)} (m:tymember x t l) : list(var*Set):=
    match m with
    | TFirst tl => tl
    | TLater y ty tl tm0 => tyrem tm0
    end.
  
  Inductive envlist : list (var*Set) -> Type:=
  | ENil : envlist nil
  | ECons : forall (x:var) (t:Set) (ls:list (var*Set)), t -> envlist ls -> envlist ((x,t)::ls).
  
  Check ECons.
  Inductive envmember : forall (x:var) (t:Set) (l:list(var*Set)), envlist l -> Type :=
  | EFirst : forall x t val l tl, @envmember x t ((x,t)::l) (ECons x val tl)
  | ELater : forall x t y ty val l tl,
                    @envmember x t _ tl ->
                    @envmember x t ((y,ty)::l) (ECons y val tl).
  Fixpoint envlookup (x:var) (t:Set) {l:list(var*Set)} (e:envlist l) (mem:envmember x t e) : t :=
    match mem with
      | EFirst _ _ v _ _ => v
      | ELater x' t' _ _ _ _ _ next => envlookup (*x' t' _ _*) next
      end. 
  Print envlookup.

  (* This generates a hideous term, but fortunately we never really need to extract it. *)
  Fixpoint tymem2envmem (x:var) (t:Set) {l:list(var*Set)} (tm:tymember x t l) (e:envlist l) : envmember x t e.
  destruct tm. dependent induction e. constructor.
  dependent induction e. constructor. firstorder. Defined.

  
  Fixpoint envrem (x:var) (t:Set) {l:list(var*Set)} (e:envlist l) (mem:envmember x t e) (tm:tymember x t l): envlist (tyrem tm).
  destruct tm. dependent induction e; compute[tyrem]; fold tyrem; auto.
  unfold tyrem; fold tyrem.
  assert (etl : envlist tl). dependent induction e. assumption.
  eapply (envrem x t tl etl). eapply tymem2envmem. assumption.
  Defined.

  Parameter x : var.
  Check envlookup.
  Definition test : nat. refine(@envlookup x nat _ (ECons x 0 ENil) _). constructor. Defined.
  Lemma findx : test = 0. eauto. Qed.


End envlist.

Notation "'ε'" := (@nil (var*Set)).
Notation " x : t , Γ " := ((x,t)::Γ) (at level 30, right associativity).
Notation "∅" := ENil.
Notation " x ↦ v , E " := (ECons x v E) (at level 30, right associativity).

Section env_notation_tests.
  Parameter y : var. Parameter z : var.
  Check (y:nat,z:bool,ε).

  Check (y↦3,z↦true,∅).

End env_notation_tests.
