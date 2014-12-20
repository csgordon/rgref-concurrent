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
Axiom mfield_read : forall {T B F Res:Set}{P R G}`{readable_at T R G}
                          `{res = B}
                          `{hreflexive G}
                          (r:ref{T|P}[R,G]) (f:F)
                          `{FieldType B F f Res},
                          forall E, rgref E Res E.

Notation "x ~> f" := (@mfield_read _ _ _ _ _ _ _ _ _ _ x f _ _ _) (at level 50).

Axiom field_write : forall {Γ}{T F Res:Set}{P R G}{folder:readable_at T R G}
                           (r:ref{T|P}[R,G]) (f:F) (e : Res)
                           `{FieldTyping T F}
                           {ft:FieldType T F f Res}
                           `{forall h v, 
                               P v h -> 
                               (*(forall Post ft' fte' (pf1:res = Post) pf2 x y,
                                   @field_read T Post F Res P R G folder pf1 pf2 r f x y =
                                   @getF res F ft' f Res fte' (dofold v)) ->*)
                               h[r]=v ->
                               G v (@setF T F _ f Res ft v e) h (heap_write r (@setF T F _ f Res ft v e) h)},
                           rgref Γ unit Γ.

Notation "{[ x ~~> f ]}:= e" := (@field_write _ _ _ _ _ _ _ _ x f e _ _ _) (at level 50).


Axiom immutable_fields : 
  forall T F H f FT FTT P (r:ref{T|P}[local_imm,local_imm]) h h',
    @getF T F H f FT FTT (h[r]) = @getF T F H f FT FTT (h'[r]).
(*Axiom field_projection_commutes : 
    forall h F T P R G Res (r:ref{T|P}[R,G]) f
           (rf:readable_at T R G) (rgf:res = T) (hrg:hreflexive G) (ftg:FieldTyping T F) (ft:FieldType T F f Res),
      @eq Res (@getF T F _ f _ _ (eq_rec _ (fun x => x) (@dofold T R G rf (h[r])) T rgf))
              (@field_read T T F Res P R G rf rgf hrg r f ftg ft).
Axiom field_projection_commutes' : 
    forall h F T P R G Res (r:ref{T|P}[R,G]) f
           (rf:readable_at T R G) (rgf:res = T)
           `(forall x, (eq_rec _ (fun x => x) (dofold x) T rgf) = x)
           (hrg:hreflexive G) (ftg:FieldTyping T F) (ft:FieldType T F f Res),
      @eq Res (@getF T F _ f _ _ (h[r]))
              (@field_read T T F Res P R G rf rgf hrg r f ftg ft).
*)
(* TODO: these may not work so well for types w/ multiple fields of same type, e.g. 2 nat fields *)
Notation "'field_inj1' ctor" := (forall x, x = ctor (getF x)) (at level 30).
Notation "'field_inj2' ctor" := (forall x, x = ctor (getF x) (getF x)) (at level 30).
Notation "'field_inj3' ctor" := (forall x, x = ctor (getF x) (getF x) (getF x)) (at level 30).
Notation "'field_inj4' ctor" := (forall x, x = ctor (getF x) (getF x) (getF x) (getF x)) (at level 30).
Ltac prove_field_injection :=
  intros;
  match goal with
  | [ |- ?x = ?ctor_app ] => destruct x; reflexivity
  end.

Axiom field_read_refine : forall {Γ Γ' T P R G}{B X F F' : Set}`{readable_at T R G} (fld:res=B)
                                 (r:ref{T|P}[R,G])(f:F)
                                 `{FieldType B F f F'}
                                 (P' : F' -> hpred T),
                            (forall h b, P' (getF (asB fld (dofold b))) b h) ->
                            (forall t, stable (P' t) R) ->
                            (forall t, (forall h, P' t (h[r]) h) ->
                                       rgref Γ X Γ') ->
                            rgref Γ X Γ'.
Notation "'observe-field' r --> f 'as' x , pf 'in' P ';' m" :=
  (@field_read_refine _ _ _ _ _ _ _ _ _ _ _ _ r f _ _ (fun x => P) _ _ (fun x pf => m))
    (at level 65).
Notation "'observe-field-explicit' FT 'for' r --> f 'as' x , pf 'in' P ';' m" :=
  (@field_read_refine _ _ _ _ _ _ _ _ _ _ _ _ r f _ FT (fun x => P) _ _ (fun x pf => m))
    (at level 65).
Axiom field_read_refineP : forall {Γ Γ' T P R G}{B X F F' : Set}`{readable_at T R G} (fld:res=B)
                                 (r:ref{T|P}[R,G])(f:F)
                                 `{FieldType B F f F'}
                                 (P' : F' -> hpred T),
                            (forall h b, b=h[r] -> P b h -> P' (getF (asB fld (dofold b))) b h) ->
                            (forall t, stable (P' t) R) ->
                            (forall t, (forall h, P' t (h[r]) h) ->
                                       rgref Γ X Γ') ->
                            rgref Γ X Γ'.
Notation "'observe-field-explicitP' FT 'for' r --> f 'as' x , pf 'in' P ';' m" :=
  (@field_read_refineP _ _ _ _ _ _ _ _ _ _ _ _ r f _ FT (fun x => P) _ _ (fun x pf => m))
    (at level 65).


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
  (*Program Example demo {Γ} (r : ref{D|any}[deltaD,deltaD]) : rgref Γ unit Γ :=
    @field_write Γ D Dfield nat _ _ _ _ r Count ((@field_read _ D Dfield _ _ _ _ _ _ _ r Count _ _)+1) _ _ _.
  Next Obligation.
    unfold demo_obligation_1. unfold demo_obligation_2.
    destruct v.
(*    rewrite Hfieldstuff.*) erewrite H0.
    compute. fold plus. constructor. eauto with arith.
  Qed.*)
End FieldDemo.




Section Arrays.
(** A functional model of arrays *)
Definition fin := t.
Axiom Array : nat -> Set -> Set.
(** We've decided to prohibit 0-length arrays. *)
Axiom new_array : forall (n:nat) (T:Set), T -> Array (S n) T.
Axiom array_read : forall {n:nat}{T:Set}, Array n T -> fin n -> T.
Axiom array_write : forall {n:nat}{T:Set}, Array n T -> fin n -> T -> Array n T.

Axiom array_map : forall {n:nat}{T:Set}{B:Set}, (T->B) -> Array n T -> Array n B.
Axiom array_id_update : forall {n T} (a:Array n T) f, array_write a f (array_read a f) = a.
Axiom read_fresh_array : forall n T e f, array_read (new_array n T e) f = e.
Axiom read_updated_cell : forall n T (a:Array n T) f e, array_read (array_write a f e) f = e.
Axiom read_past_updated_cell: 
    forall n T (a:Array n T) f1 f2 e,
      f1 <> f2 ->
      array_read (array_write a f1 e) f2 = array_read a f2.
Axiom read_map_array : forall n (T B:Set) x (f:T->B) (a:Array n T),
                         array_read (array_map f a) x = f (array_read a x).

Global Instance array_reachable {n:nat}{T:Set}`{ImmediateReachability T} : ImmediateReachability (Array n T) :=
{
  imm_reachable_from_in := fun T P R G r arr =>
                             exists f, imm_reachable_from_in r (array_read arr f)
}.

(* TODO: Update to readable_at *)
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

Axiom indep_array : forall {Γ} (n:nat) {T:Set}, (forall (i:nat), i<(S n) -> rgref Γ T Γ) -> rgref Γ (Array (S n) T) Γ.
Axiom indep_array_conv_alloc :
    forall {Γ} (n:nat) {T0:forall (i:nat) (pf:i<(S n)), Set}
           {T:Set} {P:hpred (Array (S n) T)} {R G}, 
    (forall (i:nat) (pf:i<(S n)), rgref Γ (T0 i pf) Γ) ->
    forall
    (cnv : forall i (pf:i<(S n)), T0 i pf -> T),
    (forall A h,
        (forall i (pf:i<(S n)), exists (f0 : T0 i pf), array_read A (of_nat_lt pf) = cnv i pf f0) ->
        P A h) ->
    rgref Γ (ref{(Array (S n) T)|P}[R,G]) Γ.


End Arrays.

Notation "a <| x |>" := (array_read a x) (at level 50).
Notation "a <| x ↦ e |>" := (array_write a x e) (at level 51).
