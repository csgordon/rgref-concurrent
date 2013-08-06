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
Inductive rgref (Δ:tyenv) (T:Set) (Δ':tyenv) : Type :=
  (*| mkRGR :  envlist Δ -> T -> envlist Δ' -> (heap -> heap) -> rgref Δ T Δ'.*)
  | mkRGR : (envlist Δ * heap -> T * envlist Δ' * heap) -> rgref Δ T Δ'.

(* TODO: Really bind should be doing some kind of framing on environments, a subenv type thing. *)
Definition rgref_bind {Δ Δ' Δ'':tyenv}{t t':Set} (a:rgref Δ t Δ') (b:t->rgref Δ' t' Δ'') : rgref Δ t' Δ'' :=
  match a with
    | mkRGR transA => mkRGR _ _ _
                            (fun eh => match transA eh with
                                         | (x,e',h') => match b x with
                                                          | mkRGR transB => transB (e',h')
                                                        end
                                       end)
  end.

(* TODO: To actually define this properly, bind needs to do framing and ret should use the empty env. *)
Definition rgret {Δ:tyenv}{A:Set}(a:A) : rgref Δ A Δ :=
  mkRGR Δ A Δ (fun eh => match eh with (e,h) => (a,e,h) end).

Axiom dropvar : forall {Δ} (v:var) (t:Set) (tm:tymember v t Δ), rgref Δ unit (tyrem tm).

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
(*Axiom store : forall {Δ:dyn_env}{A:Set}{P R G}(x:var)(e:A)
                 {varty:exists ptr, lookup x Δ = Some (existT (fun x:Set=>x) (ref{A|P}[R,G]) ptr)}
                 {guar:forall h l, lookup x Δ = Some (existT (fun x:Set=>x) (ref{A|P}[R,G]) l) ->
                   G (!l) e h (heap_write l e h)}
                 {pres:(forall h (l:ref{A|P}[R,G]), P (!l) h -> P e (heap_write l e h))}
                 , rgref Δ unit Δ.*)
Program Axiom write' : forall {Δ:tyenv}{A:Set}`{rel_fold A}{P R G}`{hreflexive G}(x:ref{A|P}[R,G])(e:A)
                      (meta_x_deref:A) (meta_e_fold:A) 
                      (** These meta args are notationally expanded x and e using the identity relation folding *)
                 (*{guar:forall h, G (!x) e h (heap_write x e h)} *)
                 {guar:forall h, (forall A (fa:rel_fold A), fa = meta_fold) -> G (meta_x_deref) e h (heap_write x e h)}
                 (** temporarily not using meta_e_fold... the cases where I needed the "nop" behavior are once where the types are actually equal *)
                 {pres:(forall h, P meta_x_deref h -> P meta_e_fold (heap_write x meta_e_fold h))}
                 , rgref Δ unit Δ.
Notation "[ x ]:= e" := (@write' _ _ _ _ _ _ _ x e ({{{!x}}}) ({{{e}}}) _ _) (at level 70).
(** TODO: heap writes that update the predicate.  Because of the monadic style, we'll actually
   need a new axiom and syntax support for this, to rebind the variable at the strengthened type *)

(** Interactions between pure terms and monadic terms *)
(** valueOf should be treated as roughly a more serious version of unsafePerformIO;
    it's a coreturn like the latter, but should actually never be written in user programs! *)
Definition valueOf {Δ Δ'}{A:Set} (e:envlist Δ) (h:heap) (m:rgref Δ A Δ') : A :=
  match m with
    | mkRGR f => match f (e,h) with (x,_,_) => x end
  end.
(** pureApp is essentially based on valueOf... Technically this is weaker than what's in the paper,
    since dependently-typed pure functions are allowed if the instantiation of the range type is
    closed, but right now I don't need the expressiveness and can't figure out how to properly treat the
    dependency in binding B. 
    
    I supposed technically this makes rgref an indexed functor (in the Haskell sense), and with a
    small tweak, an applicative functor if we need it. *)
Definition pureApp {Δ Δ'}{A:Set}`{splits A A A}{B:Set} (f:A->B) (m:rgref Δ A Δ') : rgref Δ B Δ' :=
  match m with
    | mkRGR body => mkRGR _ _ _ (fun eh => match body eh with (a,e,h) => (f a, e, h) end)
  end.

(** This is just strong enough to get the race-free counter example to go through... Need to strengthen this at some point. *)
Lemma weak_pureApp_morphism :
  forall Δ Δ' τ env h (e:rgref Δ τ Δ') (sp:splits τ τ τ) (f:τ->τ) (P:τ->τ->Prop),
    (forall v:τ, P v (f v)) ->
    P (valueOf env h e) (valueOf env h (@pureApp _ _ _ sp _ f e)).
Proof.
  intros. destruct e. unfold pureApp. unfold valueOf.
  induction (p (env,h)). induction a. auto.
Qed.

(* Impure read expression (using a direct ref value) *)
Program Axiom read_imp : forall {Δ}{A B:Set}`{rel_fold A}{P R G}`{hreflexive G}`{rgfold R G = B}(x:ref{A|P}[R,G]), rgref Δ B Δ.

(* Writing with an impure source expression (and direct ref value) *)
Program Axiom write_imp_exp : forall {Δ Δ'}{A:Set}`{rel_fold A}{P R G}`{hreflexive G}(x:ref{A|P}[R,G])(e:rgref Δ A Δ')
                              (meta_x_deref:rgref Δ A Δ') (meta_e_fold:rgref Δ A Δ')
                              {guar:forall h env, G (valueOf env h meta_x_deref) (valueOf env h e) h (heap_write x (valueOf env h e) h)}
                              {pres:(forall h env, P (valueOf env h meta_x_deref) h -> P (valueOf env h meta_e_fold) (heap_write x (valueOf env h meta_e_fold) h))}
                              , rgref Δ unit Δ'.
Notation "[[ x ]]:= e" := (@write_imp_exp _ _ _ _ _ _ _ _ x e ({{{read_imp x}}}) ({{{e}}}) _ _) (at level 70).

Definition locally_const {A:Set} (R:hrel A) := forall a a' h h', R a a' h h' -> a=a'.


Axiom alloc : forall {Δ}{T:Set}{RT:ImmediateReachability T}{CT:Containment T}{FT:rel_fold T} P R G (e:T), 
                stable P R ->        (* predicate is stable *)
                (forall h, P e h) -> (* predicate is true *)
                precise_pred P ->    (* P precise *)
                precise_rel R ->     (* R precise *)
                precise_rel G ->     (* G precise *)
                G ⊆ R ->
                rgref Δ (ref{T|P}[R,G]) Δ.
Notation "'Alloc' e" := (alloc _ _ _ e _ _ _ _ _ _) (at level 70).
(** Sometimes it is useful to refine P to give equality with the allocated value, which
    propagates assumptions and equalities across "statements." *)
Axiom alloc' : forall {Δ}{T:Set}{RT:ImmediateReachability T}{CT:Containment T}{FT:rel_fold T} P R G (e:T) (meta_e:T),
                stable P R ->        (* predicate is stable *)
                (forall h, P e h) -> (* predicate is true *)
                precise_pred P ->    (* P precise *)
                precise_rel R ->     (* R precise *)
                precise_rel G ->     (* G precise *)
                G ⊆ R ->
                 rgref Δ (ref{T|P ⊓ (fun t=>fun h=> (locally_const R -> t=meta_e))}[R,G]) Δ.
Notation "Alloc! e" := (alloc' _ _ _ e ({{{e}}}) _ _ _ _ _ _) (at level 70).
                                 

  
Notation "x <- M ; N" := (rgref_bind M (fun x => N)) (at level 49, right associativity).

Axiom varalloc' : forall {Δ}{T:Set}{RT:ImmediateReachability T}{CT:Containment T}{FT:rel_fold T} P R G (v:var) (e:T) (meta_e:T),
                stable P R ->        (* predicate is stable *)
                (forall h, P e h) -> (* predicate is true *)
                precise_pred P ->    (* P precise *)
                precise_rel R ->     (* R precise *)
                precise_rel G ->     (* G precise *)
                 rgref Δ unit (v:ref{T|P ⊓ (fun t=>fun h=> (locally_const R -> t=meta_e))}[R,G],Δ).
Notation "VarAlloc! v e" := (varalloc' _ _ _ v e ({{{e}}}) _ _ _ _ _) (at level 70).



(** ** Fixpoints *)
(** Possibly non-terminating fixpoint combinators. *)
(* TODO: This is only a first cut, and doesn't allow polymorphic recursion. *)
Axiom RGFix : forall { Δ Δ' }(t t':Set), 
    ((t -> rgref Δ t' Δ') -> (t -> rgref Δ t' Δ')) -> t -> rgref Δ t' Δ'.
Axiom RGFix2 : forall { Δ Δ' }(t t2 t':Set), 
    ((t -> t2 -> rgref Δ t' Δ') -> (t -> t2 -> rgref Δ t' Δ')) -> 
    t -> t2 -> rgref Δ t' Δ'.
Axiom RGFix3 : forall { Δ Δ' }(t t2 t3 t':Set), 
    ((t -> t2 -> t3 -> rgref Δ t' Δ') -> (t -> t2 -> t3 -> rgref Δ t' Δ')) -> 
    t -> t2 -> t3 -> rgref Δ t' Δ'.
Axiom RGFix4 : forall { Δ Δ' }(t t2 t3 t4 t':Set), 
    ((t -> t2 -> t3 -> t4 -> rgref Δ t' Δ') -> (t -> t2 -> t3 -> t4 -> rgref Δ t' Δ')) ->
    t -> t2 -> t3 -> t4 -> rgref Δ t' Δ'.

(** *** Fixpoint definitional axioms *)
Axiom RGFix_unfold : forall {Γ Γ'}(t t':Set)(f:(t -> rgref Γ t' Γ') -> (t -> rgref Γ t' Γ')),
                       RGFix t t' f = f (RGFix t t' f).
Axiom RGFix2_unfold : forall {Γ Γ'}(t t2 t':Set)(f:(t -> t2 -> rgref Γ t' Γ') -> (t -> t2 -> rgref Γ t' Γ')),
                       RGFix2 t t2 t' f = f (RGFix2 t t2 t' f).
