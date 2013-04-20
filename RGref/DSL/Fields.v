Require Import RGref.DSL.DSL.
Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.Arith.

Definition fin := t. (* Why on earth is this named t in the stdlib??? *)

Definition FieldTypes (n : nat) := fin n -> Set.

Class FieldAccess (T : Set) {n : nat} (ft : FieldTypes n) : Set := {
  fieldOf : forall (obj : T) (x : fin n), ft x ;
  fieldUpdate : forall (obj : T) (x : fin n) (v : ft x), T
}.

(* Field-aware heap access primitives *)
Axiom field_read : forall {T B Res:Set}{P R G}{n:nat}{ft:FieldTypes n}`{rel_fold T}
                          `{rgfold R G = B}
                          `{hreflexive G}
                          `{FieldAccess B n ft}
                          (r:ref{T|P}[R,G]) (f:fin n)
                          `{ft f = Res}, (* <-- another weak pattern matching/conversion hack *)
                          Res.
Axiom field_write : forall {Γ}{T:Set}{P R G}{n:nat}{ft:FieldTypes n}
                           `{FieldAccess T n ft}
                           (r:ref{T|P}[R,G]) (f:fin n) (e : ft f)
                           `{forall h v, P v h -> G v (fieldUpdate v f e) h (heap_write r (fieldUpdate v f e) h)},
                           rgref Γ unit Γ.

Section FieldDemo.

  Inductive D : Set :=
    mkD : nat -> bool -> D.
  Inductive deltaD : hrel D :=
    incCount : forall n n' b h h', n <= n' -> deltaD (mkD n b) (mkD n' b) h h'
  | setFlag : forall n h h', deltaD (mkD n false) (mkD n true) h h'.
  Lemma refl_deltaD : hreflexive deltaD. Proof. red. intros. destruct x. apply incCount. eauto with arith. Qed.
  Hint Resolve refl_deltaD.

  (* This demonstrates why Fin is more heavily used in Agda than Coq.
     Coq's pattern matching is too weak to determine that F1 and FS _ (F1 _)
     is an exhaustive match! *)
  Definition DFieldSize := FieldTypes 2.
  Definition DFieldTypes : FieldTypes 2 :=
    fun f => match f as F with
             | F1 _ => nat
             | FS _ _ => bool
             end. 
  Inductive Dfield : Set := Count | Flag.
  Definition DField2Fin (df : Dfield) : fin 2 := match df with Count => F1 | Flag => FS (F1) end.
  Coercion DField2Fin : Dfield >-> fin.
  Require Import Coq.Program.Equality. (* dependent induction tactic *)
  (* More hacks for weak conversion and pattern matching... *)
  Definition nat2DField (n : nat) : DFieldTypes Count. compute; assumption. Defined.
  Definition nat2DField' (n : nat) : DFieldTypes (@F1 (S O)). compute; assumption. Defined.
  Definition Count2nat (n : DFieldTypes Count) : nat. compute; assumption. Defined.
  Definition bool2DField (b : bool) : DFieldTypes Flag. compute; assumption. Defined.
  Print nat2DField'.
  Instance DAccess : FieldAccess D DFieldTypes.
(* Ideally we'd just directly define, but Coq's pattern matching is weak, so we'll use the refine tactic. :=
  { fieldOf := fun obj x => match obj return (DFieldTypes x) with (mkD n b) =>
                              match x as x return _ with
                              | F1 _ => _
                              | FS _ _ => _
                              end
                            end;

    fieldUpdate := fun obj f v =>
                     match (obj,f) with
                     | (mkD n b,F1 _) => _
                     | (mkD n b,FS _ _) => _
                     end
  }. *)
  constructor. 
  (* fieldOf *) intro obj. intro x. destruct obj.
                dependent induction x; red; auto.
  (* fieldUpdate *) intros obj x v. destruct obj.
                    dependent induction x; compute [DFieldTypes] in *. exact (mkD v b). exact (mkD n v).
  Defined.
(* Print DAccess. (* <-- that is a terrible term due to dependent induction *) *)
  Instance pureD : pure_type D.
  Program Example demo {Γ} (r : ref{D|any}[deltaD,deltaD]) : rgref Γ unit Γ :=
    @field_write Γ D _ _ _ _ _ DAccess r Count (nat2DField ((Count2nat (@field_read _ _ _ _ _ _ _ _ _ _ _ DAccess r (DField2Fin Count) _)) + 1)) _.
  Next Obligation.
    cut (forall f p1 p2 p3, @eq (DFieldTypes f) (@field_read D D _ _ _ _ _ DFieldTypes _ p1 p2 DAccess r f p3)  (@fieldOf D _ DFieldTypes DAccess (@fold D _ deltaD deltaD v) f)).
    intro Hcomp. rewrite Hcomp with (f := F1).
    destruct v. compute [nat2DField Count2nat].
    compute. fold plus. rewrite plus_comm.


End FieldDemo.