Require Import RGref.DSL.DSL.
Require Export Coq.Vectors.Fin.
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

Notation "x ~> f" := (@field_read _ _ _ _ _ _ _ _ _ _ x f _ _) (at level 50).

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

Notation "{[ x ~~> f ]}:= e" := (@field_write _ _ _ _ _ _ _ _ x f e _ _ _) (at level 50).

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




Section Arrays.
(** A functional model of arrays *)
Definition fin := t.
Axiom Array : nat -> Set -> Set.
Axiom new_array : forall (n:nat) (T:Set), T -> Array n T.
Axiom array_read : forall {n:nat}{T:Set}, Array n T -> fin n -> T.
Axiom array_write : forall {n:nat}{T:Set}, Array n T -> fin n -> T -> Array n T.

Axiom array_map : forall {n:nat}{T:Set}{B:Set}, (T->B) -> Array n T -> Array n B.
Axiom array_id_update : forall {n T} (a:Array n T) f, array_write a f (array_read a f) = a.
Axiom read_fresh_array : forall n T e f, array_read (new_array n T e) f = e.
Axiom read_updated_cell : forall n T (a:Array n T) f e, array_read (array_write a f e) f = e.
Axiom read_past_updated_cell: 
    forall n T (a:Array n T) f1 f2 e,
      f2 <> f2 ->
      array_read (array_write a f1 e) f2 = array_read a f2.
Axiom read_map_array : forall n (T B:Set) x (f:T->B) (a:Array n T),
                         array_read (array_map f a) x = f (array_read a x).

Global Instance array_reachable {n:nat}{T:Set}`{ImmediateReachability T} : ImmediateReachability (Array n T) :=
{
  imm_reachable_from_in := fun T P R G r arr =>
                             exists f, imm_reachable_from_in r (array_read arr f)
}.

Global Instance array_fold {n:nat}{T:Set}`{rel_fold T} : rel_fold (Array n T) :=
{
  rgfold := fun R G => Array n (rgfold havoc
                                       (fun x x' h h' =>
                                           forall a f,
                                               array_read a f = x ->
                                               G a (array_write a f x') h h')
                                       );
  fold := fun R G x => array_map fold x
                                       
}.

Global Instance array_contains {n:nat}{T:Set}`{Containment T} : Containment (Array n T) :=
{
  contains := fun R => 
    contains (fun (x x':T) h h' => forall a f, array_read a f = x ->
                                               R a (array_write a f x') h h')
}.

(** Arrays a essentially [fin n]-indexed object, so use those as fields.
    This lets us use fields with things like fCAS *)
Global Instance array_fields {n:nat}{T:Set} : FieldTyping (Array n T) (fin n).
Global Instance array_field_index {n:nat}{T:Set}{f:fin n} : FieldType (Array n T) (fin n) f T := {
  getF := fun v => array_read v f;
  setF := fun v fv => array_write v f fv
}.

Axiom indep_array : forall {Γ} (n:nat) {T:Set}, (forall (i:nat), i<n -> rgref Γ T Γ) -> rgref Γ (Array n T) Γ.

End Arrays.

Notation "a <| x |>" := (array_read a x) (at level 50).
Notation "a <| x ↦ e |>" := (array_write a x e) (at level 51).
