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
Check @getF. Check @fold. Check @setF.
Axiom field_write : forall {Γ}{T F Res:Set}{P R G}{folder:rel_fold T}
                           (r:ref{T|P}[R,G]) (f:F) (e : Res)
                           `{FieldTyping T F}
                           {ft:FieldType T F f Res}
                           `{forall h v, 
                               P v h -> 
                               (forall Post ft' fte' (pf1:rgfold R G = Post) pf2 x y,
                                   @field_read T Post F Res P R G folder pf1 pf2 r f x y =
                                   @getF (@rgfold T folder R G) F ft' f Res fte' (@fold T folder R G v)) ->
                               G v (@setF T F _ f Res ft v e) h (heap_write r (@setF T F _ f Res ft v e) h)},
                           rgref Γ unit Γ.

Section FieldDemo.

  Inductive D : Set :=
    mkD : nat -> bool -> D.
  Inductive deltaD : hrel D :=
    incCount : forall n n' b h h', n <= n' -> deltaD (mkD n b) (mkD n' b) h h'
  | setFlag : forall n h h', deltaD (mkD n false) (mkD n true) h h'.
  Lemma refl_deltaD : hreflexive deltaD. Proof. red. intros. destruct x. apply incCount. eauto with arith. Qed.
  Hint Resolve refl_deltaD.

  (* I feel like this is reinventing lenses... *)
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

  Instance pureD : pure_type D.
  Program Example demo {Γ} (r : ref{D|any}[deltaD,deltaD]) : rgref Γ unit Γ :=
    @field_write Γ D Dfield nat _ _ _ _ r Count ((@field_read _ D Dfield _ _ _ _ _ _ _ r Count _ _)+1) _ _ _.
  Next Obligation.
    unfold demo_obligation_1. unfold demo_obligation_2.
(*    Check @getF.
    cut (forall T B (v:B) F Res P R G folder pf1 pf2 r f fs fi ft ftb, 
           @field_read T B F Res P R G folder pf1 pf2 r f fs fi = 
                     @getF B F ft f Res ftb v).
    intros Hfieldstuff.*)
    destruct v.
(*    rewrite Hfieldstuff.*) erewrite H0.
    compute. fold plus. constructor. eauto with arith.
  Qed.
End FieldDemo.