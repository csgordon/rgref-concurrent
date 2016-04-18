Require Import RGref.DSL.Core.
Require Export RGref.DSL.Theories.
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

(** Ideally deref would have the type
<<
forall {A:Set}`{rel_fold A}{P:hpred A}{R G:hrel A}, hreflexive G -> ref A P R G -> rgfold R G.
>>
But unforunately, Coq's default type conversion procedure doesn't fully reduce the rgfold instance,
which in most cases is reduced naturally by
<<
cbv iota delta beta
>>
But that reduction is stronger than default conversion (at least in 8.3... still building 8.4).
*)
Axiom mderef : forall {A:Set}{B:Set}{P:hpred A}{R G:hrel A}`{readable_at A R G}, hreflexive G -> res = B -> ref A P R G -> forall {E}, rgref E B E.
(*Axiom deref : forall {A:Set}{P:hpred A}{R G:hrel A}, ref A P R G -> A.*)
Notation "! e" := (mderef _ _ e) (at level 30). (* with reflexivity, add an _ in there *)

(* This axiom asserts that all folds that produce the same result type operate equally on
   the underlying values. This is fragile if a developer specifies multiple instances for
   folding the same type.  This is a weaker version of a more general axiom that
   the relationship between the results of folds of different result types depends on the
   relationship between results of the fold members of the instances when applied to the
   same value.  This version is really only useful for equating identity folds with
   the identity meta_fold instance results. *)
Axiom mderef_conversion : forall (A B:Set) P R G RA1 RA2 rf1 rf2 fe1 fe2,
                         @mderef A B P R G RA1 rf1 fe1 = @mderef A B P R G RA2 rf2 fe2.



(** TODO: Fix store to work properly with the linear environment. *)
Program Definition asB T R G B `{readable_at T R G} (pf:res = B) (b:res) : B.
intros. rewrite pf in b. exact b. Defined.

Program Axiom store : forall {Δ:tyenv}{A:Set}{P R G}`{readable_at A R G}`{res=A}`{hreflexive G}
                             (x:ref{A|P}[R,G])(e:A)
                             (guar:(forall (h:heap),
                                      P (h[x]) h -> G (h[x]) e h (heap_write x e h)))
                             (pres:(forall h, P (h[x]) h -> P e (heap_write x e h))),
                                      rgref Δ unit Δ.
Notation "[ x ]:= e" := (@store _ _ _ _ _ _ _ _ x e _ _) (at level 70).
                                    

(*Program Axiom write' : forall {Δ:tyenv}{A:Set}`{rel_fold A}{P R G}`{hreflexive G}(x:ref{A|P}[R,G])(e:A)
                      (meta_x_deref:A) (meta_e_fold:A) 
                      (** These meta args are notationally expanded x and e using the identity relation folding *)
                 (*{guar:forall h, G (!x) e h (heap_write x e h)} *)
                 {guar:forall h, (forall A (fa:rel_fold A), fa = meta_fold) -> G (meta_x_deref) e h (heap_write x e h)}
                 (** temporarily not using meta_e_fold... the cases where I needed the "nop" behavior are once where the types are actually equal *)
                 {pres:(forall h, P meta_x_deref h -> P meta_e_fold (heap_write x meta_e_fold h))}
                 , rgref Δ unit Δ.*)
(** Notation "[ x ]:= e" := (@write' _ _ _ _ _ _ _ x e ({{{!x}}}) ({{{e}}}) _ _) (at level 70).*)
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

(* Sometimes it's useful to observe a cell to introduce a subsequent refinement *)
Axiom read_refine : forall {Γ Γ' T P R G B X}
                           `{readable_at T R G}
                           (fld : res = B)
                      (r:ref{T|P}[R,G])
                      (P' : B -> hpred T) , (** TODO: Do we need to constrain how the B is used? *)
                      (forall h b, P' (asB fld (dofold b)) b h) ->
                      (forall t, stable (P' t) R) ->
                      (forall t, (forall h, P' t (h[r]) h) -> 
                                 rgref Γ X Γ') ->
                      rgref Γ X Γ'.
Notation "'observe' r 'as' x , pf 'in' P ';' m" :=
  (@read_refine _ _ _ _ _ _ _ _ _ _ r (fun x => P) _ _ (fun x pf => m))
    (at level 65).


(* Writing with an impure source expression (and direct ref value) *)
Program Axiom write_imp_exp : forall {Δ Δ'}{A:Set}{P R G}`{readable_at A R G}`{hreflexive G}(x:ref{A|P}[R,G])(e:rgref Δ A Δ')
(* TODO: These Δs are ordered wrong...*)(meta_x:rgref Δ A Δ') (meta_e:rgref Δ A Δ')
                              {guar:forall h env, G (valueOf env h meta_x) (valueOf env h e) h (heap_write x (valueOf env h e) h)}
                              {pres:(forall h env, P (valueOf env h meta_x) h -> P (valueOf env h meta_e) (heap_write x (valueOf env h meta_e) h))}
                              , rgref Δ unit Δ'.
Notation "[[ x ]]:= e" := (@write_imp_exp _ _ _ _ _ _ _ _ x e ({{{read_imp x}}}) ({{{e}}}) _ _) (at level 70).

Axiom alloc : forall {Δ}{T:Set}{RT:ImmediateReachability T}{CT:Containment T}
                     P R G {FT:readable_at T R G} (e:T), 
                stable P R ->        (* predicate is stable *)
                (forall h, P e h) -> (* predicate is true *)
                precise_pred P ->    (* P precise *)
                precise_rel R ->     (* R precise *)
                precise_rel G ->     (* G precise *)
                G ⊆ R ->             (* self-splitting *)
                rgref Δ (ref{T|P}[R,G]) Δ.
Notation "'Alloc' e" := (alloc _ _ _ e _ _ _ _ _ _) (at level 70).

(** Sometimes it is useful to know explicitly that some other reference from before allocation is
    not equal to the fresh allocation *)
Axiom allocne : forall {Δ}{T:Set}{RT:ImmediateReachability T}{CT:Containment T}
                     P R G {FT:readable_at T R G} (e:T), 
                stable P R ->        (* predicate is stable *)
                (forall h, P e h) -> (* predicate is true *)
                precise_pred P ->    (* P precise *)
                precise_rel R ->     (* R precise *)
                precise_rel G ->     (* G precise *)
                G ⊆ R ->             (* self-splitting *)
                forall {A' P' G' R'} (old : ref{A'|P'}[R',G']),
                rgref Δ (sigT (fun (r:(ref{T|P}[R,G])) => (~(r ≡ old))) ) Δ.
Notation "'AllocNE' e r" := (allocne _ _ _ e _ _ _ _ _ _ r) (at level 65).

(** Sometimes it is useful to refine P to give equality with the allocated value, which
    propagates assumptions and equalities across "statements." *)
Axiom alloc' : forall {Δ}{T:Set}{RT:ImmediateReachability T}{CT:Containment T}
                      P R G {FT:readable_at T R G} (e:T),
                stable P R ->        (* predicate is stable *)
                (forall h, P e h) -> (* predicate is true *)
                precise_pred P ->    (* P precise *)
                precise_rel R ->     (* R precise *)
                precise_rel G ->     (* G precise *)
                G ⊆ R ->             (* self-splitting *)
                 rgref Δ (ref{T|P ⊓ (fun t=>fun h=> (locally_const R -> t=e))}[R,G]) Δ.
Notation "Alloc! e" := (alloc' _ _ _ e _ _ _ _ _ _) (at level 70).
                                 

  
Notation "x <- M ; N" := (rgref_bind M (fun x => N)) (at level 49, right associativity).

Axiom varalloc' : forall {Δ}{T:Set}{RT:ImmediateReachability T}{CT:Containment T}
                         P R G {FT:readable_at T R G} (v:var) (e:T),
                stable P R ->        (* predicate is stable *)
                (forall h, P e h) -> (* predicate is true *)
                precise_pred P ->    (* P precise *)
                precise_rel R ->     (* R precise *)
                precise_rel G ->     (* G precise *)
                 rgref Δ unit (v:ref{T|P ⊓ (fun t=>fun h=> (locally_const R -> t=e))}[R,G],Δ).
Notation "VarAlloc! v e" := (varalloc' _ _ _ v e _ _ _ _ _) (at level 70).



(** ** Fixpoints *)
(** Possibly non-terminating fixpoint combinators. *)
(* TODO: This is only a first cut, and doesn't allow polymorphic recursion. *)
Axiom RGFix : forall { Δ Δ' }(t t':Set), 
    ((t -> rgref Δ t' Δ') -> (t -> rgref Δ t' Δ')) -> t -> rgref Δ t' Δ'.
Axiom RGFix2 : forall { Δ Δ' }(t t2 t':Set), 
    ((t -> t2 -> rgref Δ t' Δ') -> (t -> t2 -> rgref Δ t' Δ')) -> 
    t -> t2 -> rgref Δ t' Δ'.
Axiom RGFixT2 : forall { Δ Δ' }(t t2:Type) (t':Set), 
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
