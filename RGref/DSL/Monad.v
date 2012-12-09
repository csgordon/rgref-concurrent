Require Import RGref.DSL.Core.
Require Export RGref.DSL.LinearEnv.

(** * A Monad for RGref programs *)

(* TODO: Should probably be a type-class *)
Inductive splits : Set -> Set -> Set -> Prop :=
  | natsp : splits nat nat nat
  | boolsp : splits bool bool bool
  | unitsp : splits unit unit unit
  | pairsp : forall A A' A'' B B' B'', 
               splits A A' A'' ->
               splits B B' B'' ->
               splits (A*B) (A'*B') (A''*B'')
  | listsp : forall A A' A'', splits A A' A'' -> splits (list A) (list A') (list A'')
  | funsp : forall (A B:Set),
               splits (forall x:A, B) (forall x:A, B) (forall x:A, B)
. 
Inductive rgref (Γ:tyenv) (T:Set) (Γ':tyenv) : Type :=
  | mkRGR :  envlist Γ -> T -> envlist Γ' -> (heap -> heap) -> rgref Γ T Γ'.

(* TODO: Really bind should be doing some kind of framing on environments, a subenv type thing. *)
Program Definition rgref_bind {Γ Γ' Γ'':tyenv}{t t':Set} (a:rgref Γ t Γ') (b:t->rgref Γ' t' Γ'') : rgref Γ t' Γ'' :=
  match a with
  | mkRGR _ va _ ha =>
    match b va with
    | mkRGR _ vb _ hb =>
      mkRGR _ _ _ _ vb _ (fun h => hb (ha h))
    end
  end.

(* TODO: To actually define this properly, bind needs to do framing and ret should use the empty env. *)
Axiom rgret : forall {Γ:tyenv}{A:Set}(a:A), rgref Γ A Γ .
(*  := mkRGR Γ A Γ e a e (fun h=>h).*)

Axiom dropvar : forall {Γ} (v:var) (t:Set) (tm:tymember v t Γ), rgref Γ unit (tyrem tm).

(** The core problem with folding here is that we want the user (and automated provers!) to see the same dereference on either side of
    G's state.  But G applies to elements of A, not [R,G]>>A.  We could introduce an internal "cheat_deref" that skipped
    folding, but then the two sides aren't equal, and many automated tactics that treat !e as essentially an uninterpreted
    symbol fail because the pre and post values use different uninterpreted symbols.  Another alternative is to 
    ALSO add an axiom relating the behaviors of deref and cheat_deref, but this will run into serious issues with
    polymorphism over A and [R,G]>>A.  John Major equality might handle this okay, but I haven't had much success using
    JMeq for anything yet.

    A slightly different approach would be to have a folding version of heap-specific dereference, and do the guarantee
    validity check in a context with the assumption that ∀ e, !e = h[e]>> (where h[x]>> is the folding specific-heap read).
    This still runs into some JMeq issues (e.g. ∀ x h, JMeq h[x] h[x]>>), but they might be easier to deal with.

    A less serious (easier to solve) version of this occurs with reflexivity checks on G for reads.  Still need two symbols,
    one for devs that checks reflexivity on reads, the other for metatheory proofs like satisfying G, with either an axiom
    or per-context assumption that their results are equal (eq equal, since the types are equal, unless we're also solving
    the general folding issue at the same time).

    In practice the folding shouldn't matter too much (for pure types, folding is identity), but we need to support it
    in general.  Eventually both store and write will need to take rel_fold A instances so they can use them in proofs
    and obligation statements.
*)
(** TODO: Fix store to work properly with the linear environment. *)
(*Axiom store : forall {Γ:dyn_env}{A:Set}{P R G}(x:var)(e:A)
                 {varty:exists ptr, lookup x Γ = Some (existT (fun x:Set=>x) (ref{A|P}[R,G]) ptr)}
                 {guar:forall h l, lookup x Γ = Some (existT (fun x:Set=>x) (ref{A|P}[R,G]) l) ->
                   G (!l) e h (heap_write l e h)}
                 {pres:(forall h (l:ref{A|P}[R,G]), P (!l) h -> P e (heap_write l e h))}
                 , rgref Γ unit Γ.*)
(* TODO: Figure out how to model environments in a way that doesn't require projecting out of a sigT into Set, which apparently is prohibited. *)
Program Axiom write' : forall {Γ:tyenv}{A:Set}`{rel_fold A}{P R G}`{hreflexive G}(x:ref{A|P}[R,G])(e:A)
                      (meta_x_deref:A) (meta_e_fold:A) 
                      (** These meta args are notationally expanded x and e using the identity relation folding *)
                 (*{guar:forall h, G (!x) e h (heap_write x e h)} *)
                 {guar:forall h, (forall A (fa:rel_fold A), fa = meta_fold) -> G (meta_x_deref) e h (heap_write x e h)}
                 (** temporarily not using meta_e_fold... the cases where I needed the "nop" behavior are once where the types are actually equal *)
                 {pres:(forall h, P meta_x_deref h -> P meta_e_fold (heap_write x meta_e_fold h))}
                 , rgref Γ unit Γ.
Notation "[ x ]:= e" := (@write' _ _ _ _ _ _ _ x e ({{{!x}}}) ({{{e}}}) _ _) (at level 70).
(** TODO: heap writes that update the predicate.  Because of the monadic style, we'll actually
   need a new axiom and syntax support for this, to rebind the variable at the strengthened type *)
(* TODO: Figure out how to model environments in a way that doesn't require projecting out of a sigT into Set, which apparently is prohibited. *)

Definition locally_const {A:Set} (R:hrel A) := forall a a' h h', R a a' h h' -> a=a'.


Axiom alloc : forall {Γ}{T:Set}{RT:ImmediateReachability T}{CT:Containment T}{FT:rel_fold T} P R G (e:T), 
                stable P R ->        (* predicate is stable *)
                (forall h, P e h) -> (* predicate is true *)
                precise_pred P ->    (* P precise *)
                precise_rel R ->     (* R precise *)
                precise_rel G ->     (* G precise *)
                rgref Γ (ref{T|P}[R,G]) Γ.
Notation "'Alloc' e" := (alloc _ _ _ e _ _ _ _ _) (at level 70).
(** Sometimes it is useful to refine P to give equality with the allocated value, which
    propagates assumptions and equalities across "statements." *)
Axiom alloc' : forall {Γ}{T:Set}{RT:ImmediateReachability T}{CT:Containment T}{FT:rel_fold T} P R G (e:T) (meta_e:T),
                stable P R ->        (* predicate is stable *)
                (forall h, P e h) -> (* predicate is true *)
                precise_pred P ->    (* P precise *)
                precise_rel R ->     (* R precise *)
                precise_rel G ->     (* G precise *)
                 rgref Γ (ref{T|P ⊓ (fun t=>fun h=> (locally_const R -> t=meta_e))}[R,G]) Γ.
Notation "Alloc! e" := (alloc' _ _ _ e ({{{e}}}) _ _ _ _ _) (at level 70).
                                 

  
Notation "x <- M ; N" := (rgref_bind M (fun x => N)) (at level 49, right associativity).

Axiom varalloc' : forall {Γ}{T:Set}{RT:ImmediateReachability T}{CT:Containment T}{FT:rel_fold T} P R G (v:var) (e:T) (meta_e:T),
                stable P R ->        (* predicate is stable *)
                (forall h, P e h) -> (* predicate is true *)
                precise_pred P ->    (* P precise *)
                precise_rel R ->     (* R precise *)
                precise_rel G ->     (* G precise *)
                 rgref Γ unit (v:ref{T|P ⊓ (fun t=>fun h=> (locally_const R -> t=meta_e))}[R,G],Γ).
Notation "VarAlloc! v e" := (varalloc' _ _ _ v e ({{{e}}}) _ _ _ _ _) (at level 70).



(** ** Fixpoints *)
(** Possibly non-terminating fixpoint combinators. *)
(* TODO: This is only a first cut, and doesn't allow polymorphic recursion. *)
Axiom RGFix : forall { Γ Γ' }(t t':Set), ((t -> rgref Γ t' Γ') -> (t -> rgref Γ t' Γ')) -> t -> rgref Γ t' Γ'.
Axiom RGFix2 : forall { Γ Γ' }(t t2 t':Set), ((t -> t2 -> rgref Γ t' Γ') -> (t -> t2 -> rgref Γ t' Γ')) -> t -> rgref Γ t' Γ'.
Axiom RGFix3 : forall { Γ Γ' }(t t2 t3 t':Set), ((t -> t2 -> t3 -> rgref Γ t' Γ') -> (t -> t2 -> t3 -> rgref Γ t' Γ')) -> t -> rgref Γ t' Γ'.
Axiom RGFix4 : forall { Γ Γ' }(t t2 t3 t4 t':Set), ((t -> t2 -> t3 -> t4 -> rgref Γ t' Γ') -> (t -> t2 -> t3 -> t4 -> rgref Γ t' Γ')) -> t -> rgref Γ t' Γ'.