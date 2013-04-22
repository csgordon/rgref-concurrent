Require Import RGref.DSL.DSL.
Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.Arith.

(* Field Typing is a tagging mechanism, that fields of T are indexed by F *)
Class FieldTyping (T : Set) (F : Set) : Set := {}.

Class FieldType (T : Set) (F : Set) `{FieldTyping T F} (f:F) (FT : Set) := {
  getF : T -> FT;
  setF : T -> FT -> T
  (* In theory we could also require a proof that it satisfies the theory
     of arrays, e.g. forall x v, getF (setF x v) = v. *)
}.

(* Field-aware heap access primitives *)
Axiom field_read : forall {T B F Res:Set}{P R G}`{rel_fold T}
                          `{rgfold R G = B}
                          `{hreflexive G}
                          (r:ref{T|P}[R,G]) (f:F)
                          `{FieldType B F f Res},
                          Res.
Axiom field_write : forall {Γ}{T F Res:Set}{P R G}
                           (r:ref{T|P}[R,G]) (f:F) (e : Res)
                           `{FieldType T F f Res}
                           `{forall h v, P v h -> G v (setF v e) h (heap_write r (setF v e) h)},
                           rgref Γ unit Γ.

Section FieldDemo.

  Inductive D : Set :=
    mkD : nat -> bool -> D.
  Inductive deltaD : hrel D :=
    incCount : forall n n' b h h', n <= n' -> deltaD (mkD n b) (mkD n' b) h h'
  | setFlag : forall n h h', deltaD (mkD n false) (mkD n true) h h'.
  Lemma refl_deltaD : hreflexive deltaD. Proof. red. intros. destruct x. apply incCount. eauto with arith. Qed.
  Hint Resolve refl_deltaD.

  Inductive Dfield : Set := Count | Flag.
  Instance dfields : FieldTyping D Dfield.
  Instance dfield_count : FieldType D Dfield Count nat := {
    getF := fun v => match v with (mkD n b) => n end;
    setF := fun v fv => match v with (mkD n b) => (mkD fv b) end
  }.
  Instance dfield_flag : FieldType D Dfield Flag bool := {
    getF := fun v => match v with (mkD n b) => b end;
    setF := fun v fv => match v with (mkD n b) => (mkD n fv) end
  }.

  Definition getCount (d:D) := match d with (mkD n b) => n end.
  Definition getFlag (d:D) := match d with (mkD n b) => b end.

(* Print DAccess. (* <-- that is a terrible term due to dependent induction *) *)
  Instance pureD : pure_type D.
  Program Example demo {Γ} (r : ref{D|any}[deltaD,deltaD]) : rgref Γ unit Γ :=
    @field_write Γ D Dfield nat _ _ _ r Count ((@field_read _ D Dfield _ _ _ _ _ _ _ r Count _ _)+1) _ _ _.
(*    @field_write Γ D _ _ _ _ _ DAccess r Count (nat2DField ((Count2nat (@field_read _ _ _ _ _ _ _ _ _ _ _ DAccess r (DField2Fin Count) _)) + 1)) _.
  Next Obligation.
    cut (forall f p1 p2 p3, @eq (DFieldTypes f) (@field_read D D _ _ _ _ _ DFieldTypes _ p1 p2 DAccess r f p3)  (@fieldOf D _ DFieldTypes DAccess (@fold D _ deltaD deltaD v) f)).
    intro Hcomp. rewrite Hcomp with (f := F1).
    destruct v. compute [nat2DField Count2nat].
    compute [fieldOf]. unfold DAccess. unfold DAccess_obligation_1. unfold fold.
    unfold pure_fold. unfold getCount. unfold getFlag. unfold const_id_fold.
    compute [t_rec t_rect]. (* Now pretty sure I screwed up the def of fieldUpdate *)
    Check DAccess_obligation_3.
    compute [DAccess_obligation_3].
    compute -[fieldUpdate].
    compute [fieldOf DFieldTypes DAccess DAccess_obligation_1 fold DAccess_obligation_3]. rewrite plus_comm.
    (* At this point we *should* be done, but the use of dependent induction to work around
       Coq's pattern matching has introduced some uses of JMeq to deal with *)
    generalize (@JMeq_eq (t (S (S O))) (@F1 (S O)) (@F1 (S O)) (@JMeq_refl (t (S (S O))) (@F1 (S O)))).
    intro e. elim e.*)

  Next Obligation. unfold demo_obligation_1. unfold demo_obligation_2.
    Check @getF.
    cut (forall P R G pf1 pf2 r f fs fi, 
           @field_read D D Dfield nat P R G (@pure_fold D pureD) pf1 pf2 r f fs fi = 
                     @getF D Dfield _ f nat _ v).
    intros Hfieldstuff.
    destruct v.
    rewrite Hfieldstuff.
    compute. fold plus. constructor. eauto with arith.
    (* this should be abstracted to a general hypothesis supplied by
       the write framework. *)
    admit.
  Qed.
End FieldDemo.