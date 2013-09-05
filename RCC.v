Require Import RGref.DSL.DSL.

Definition pred_trans {A:Set}(P Q:hpred A) : hrel A :=
  fun a a' h h' => P a h /\ Q a' h'.
Infix "-->" := (pred_trans) (at level 50).


(** * A Module Type for RCC/Java implementation *)
Module Type RCC.
  (** Assume a lock *)
  Parameter lock : Set.
  (** Wrap references with an extra lock parameter, but by keeping the actual
      definition opaque, only primitives exposed by this module can be used
      to access the heap. *)
  Parameter rccref : forall (A:Set), hpred A -> hrel A -> hrel A -> lock -> Set.
  Notation "rcc[ l ]{ τ | P }[ R , G ]" := (rccref τ P R G l) (at level 80).
  
  (** We need a lock witness, and opaque locked/unlocked predicates. *)
  Parameter lockwitness : lock -> Set. (*(l:lock) := ... (* must be data type with reachable l *)*)
  Parameter locked : forall {l:lock}, hpred (lockwitness l).
  Parameter unlocked : forall {l:lock}, hpred (lockwitness l).

  (** Because the witness will always be in the linear context, we can't just re-export a pure
      read.  Unfortunately this pushes all RCC reads into imperative land, where proofs are less
      pleasant / direct. *)
  Parameter rcc_read : forall {Γ A B P R G}`{rel_fold A}{l:lock}{w:var}{pf:tymember w (ref{lockwitness l | locked}[empty,locked-->unlocked]) Γ}(r:rccref A P R G l),
                              hreflexive G -> rgfold R G = B -> rgref Γ B Γ.
  (** We expose hwrite, because we need a way for clients to prove obligations that this module
      must translate down to the real RGref primitives, but without exposing the fact that
      rccrefs are just rgrefs.  This means re-exporting some axioms needed to state client obligations. *)
  Parameter hwrite : forall {l A P R G} (p:rccref A P R G l) (v:A) (h:heap), heap.
(*  Parameter rcc_write : forall {Γ A}`{rel_fold A}{P R G}`{hreflexive G}{l:lock}{w:var}{pf:tymember w (ref{lockwitness l | locked}[empty,locked-->unlocked]) Γ}(x:rccref A P R G l)(e:A)
                               (meta_x:A)(meta_e:A) (* meta args *)
                               {guar:forall h, (forall A (fa:rel_fold A), fa = meta_fold) -> G (meta_x) e h (hwrite x e h)}
                               {pres:(forall h, P meta_x h -> P meta_e (hwrite x meta_e h))}
                               , rgref Γ unit Γ.
*)
  Parameter rcc_write : forall {Γ Γ'}{A:Set}`{rel_fold A}{P R G}`{hreflexive G}{l:lock}{w:var}{pf:tymember w (ref{lockwitness l | locked}[empty,locked-->unlocked]) Γ}(x:rccref A P R G l)(e:rgref Γ A Γ')
                               (meta_x_deref:rgref Γ A Γ') (meta_e_fold:rgref Γ A Γ')
                               {guar:forall h env, G (valueOf env h meta_x_deref) (valueOf env h e) h (hwrite x (valueOf env h e) h)}
                               {pres:(forall h env, P (valueOf env h meta_x_deref) h -> P (valueOf env h meta_e_fold) (hwrite x (valueOf env h meta_e_fold) h))}
                               , rgref Γ unit Γ'.

  Parameter rcc_alloc : forall {Γ}{T:Set}{RT:ImmediateReachability T}{CT:Containment T}{FT:rel_fold T} P R G (l:lock) (e:T), 
                stable P R ->        (* predicate is stable *)
                (forall h, P e h) -> (* predicate is true *)
                precise_pred P ->    (* P precise *)
                precise_rel R ->     (* R precise *)
                precise_rel G ->     (* G precise *)
                (G ⊆ R) ->
                rgref Γ (rccref T P R G l) Γ.
  (** Both of these should be introducing and removing witnesses in the linear context.  Since that's
      currently not implemented, for this sketch we're going closer to the desired source language. *)
  Parameter acquire : forall {Γ}(w:var)(l:lock), rgref Γ unit (w:ref{lockwitness l | locked}[empty,locked-->unlocked],Γ).
  Parameter release : forall {Γ}{l:lock}(w:var){pf:(tymember w (ref{lockwitness l | locked}[empty,locked-->unlocked]) Γ)}, rgref Γ unit (tyrem pf).
End RCC.
(** TODO: define folding over rcc refs *)
(** * A Partial RCC Implementation *)
Module RCCImpl : RCC.
  Parameter lock : Set.
  Definition rccref A P R G (l:lock) := ref A P R G.
  Notation "rcc[ l ]{ τ | P }[ R , G ]" := (rccref τ P R G l) (at level 80).
  Definition lockwitness := fun (l:lock) => unit.
  Definition locked : forall {l:lock}, hpred (lockwitness l) := fun l => any.
  Definition unlocked : forall {l:lock}, hpred (lockwitness l) := fun l => any.

  (** Note that the witness arguments should really be monadic in the implementation; I'm prototyping
      actual source code.  Sort of... still using the monadic return type... *)
  Program Definition rcc_read {Γ A B P R G}`{rel_fold A}{l:lock}{w:var}{pf:tymember w (ref{lockwitness l | locked}[empty,locked-->unlocked]) Γ}(r:rccref A P R G l)
                      (hrefl:hreflexive G)(fold:rgfold R G = B) : rgref Γ B Γ := read_imp Γ A B _ _ _ _ _ _ r.

  Definition hwrite := fun l:lock => @heap_write.
  (** Clients prove goals over the abstracted rcc reads; the module internally converts those for write's use *)
(*  Program Definition rcc_write {Γ A}`{rel_fold A}{P R G}`{hreflexive G}{l:lock}(w:var){pf:tymember w (ref{lockwitness l | locked}[empty,locked-->unlocked]) Γ}(x:rccref A P R G l)(e:A)
                               (meta_x:A)(meta_e:A) (* meta args *)
                               {guar:forall h, (forall A (fa:rel_fold A), fa = meta_fold) -> G (meta_x) e h (heap_write x e h)}
                               {pres:(forall h, P meta_x h -> P meta_e (heap_write x meta_e h))}
                               : rgref Γ unit Γ :=
      @write' Γ A _ P R G _ x e meta_x meta_e _ _.*)
  Program Definition rcc_write {Γ Γ'}{A:Set}`{rel_fold A}{P R G}`{hreflexive G}{l:lock}{w:var}{pf:tymember w (ref{lockwitness l | locked}[empty,locked-->unlocked]) Γ}(x:rccref A P R G l)(e:rgref Γ A Γ')
                               (meta_x_deref:rgref Γ A Γ') (meta_e_fold:rgref Γ A Γ')
                               {guar:forall h env, G (valueOf env h meta_x_deref) (valueOf env h e) h (hwrite l _ _ _ _ x (valueOf env h e) h)}
                               {pres:(forall h env, P (valueOf env h meta_x_deref) h -> P (valueOf env h meta_e_fold) (hwrite _ _ _ _ _ x (valueOf env h meta_e_fold) h))}
                               : rgref Γ unit Γ' :=
                               @write_imp_exp Γ Γ' A P R G _ _ x e meta_x_deref meta_e_fold guar pres.

  Program Definition rcc_alloc {Γ}{T:Set}{RT:ImmediateReachability T}{CT:Containment T}{FT:rel_fold T} P R G (l:lock) (e:T) 
                `(stable P R)        (* predicate is stable *)
                `((forall h, P e h)) (* predicate is true *)
                `(precise_pred P)    (* P precise *)
                `(precise_rel R)     (* R precise *)
                `(precise_rel G)     (* G precise *)
                `(G ⊆ R)
                : rgref Γ (rccref T P R G l) Γ :=
      alloc _ _ _ e _ _ _ _ _ _.
  Parameter acquire : forall {Γ}(w:var)(l:lock), rgref Γ unit (w:ref{lockwitness l | locked}[empty,locked-->unlocked],Γ).
  Parameter release : forall {Γ}{l:lock}(w:var){pf:(tymember w (ref{lockwitness l | locked}[empty,locked-->unlocked]) Γ)}, rgref Γ unit (tyrem pf).
End RCCImpl.

(** * Using the RCC Module : A race-free counter *)
Require Import Coq.Arith.Arith.
Import RCCImpl.
(** rccref is opaque. *)
(** TODO: Figure out how to stash this notation /inside/ the module! *)
Notation "'RCCAlloc' l e" := (rcc_alloc _ _ _ l e _ _ _ _ _) (at level 70).
Section RaceFreeMonotonicCounter.
  Definition increasing : hrel nat :=
    fun n n' _ _ => n <= n'.

  Hint Unfold increasing.
  Local Obligation Tactic := intros; eauto with arith; compute; auto with arith; repeat constructor.

  Program Definition rf_monotonic_counter (l:lock) := rccref nat any increasing increasing l.
  Program Definition read_counter {Γ}{l:lock}{w:var}{pf:tymember w (ref{lockwitness l | locked}[empty,locked-->unlocked]) Γ}
    (c:rf_monotonic_counter l) : rgref Γ nat Γ :=
    @rcc_read _ _ _ _ _ _ _ l w _ c _ _.
  Check @rcc_write.
  Local Obligation Tactic := intros; compute [increasing hreflexive]; eauto; try apply natsp.
  Program Definition inc_monotonic {Γ l}{w:var}{pf:tymember w (ref{lockwitness l|locked}[empty,locked-->unlocked]) Γ} (p:rf_monotonic_counter l) : rgref Γ unit Γ :=
    (* We can't directly add to the read result because that result is monadic.  Instead we have to use pureApp. *)
    @rcc_write Γ Γ nat _ any increasing increasing _ l _ _ p
        (@pureApp _ _ _ _ _ (plus 1) (@rcc_read Γ _ _ _ _ _ _ l w pf p _ _))
        ({{{@rcc_read Γ _ _ _ _ _ _ l w pf p _ _}}})
        ({{{@pureApp _ _ _ _ _ (plus 1) (@rcc_read Γ _ _ _ _ _ _ l w pf p _ _)}}}) _ _.
  Next Obligation.
    (* And again, tripped up by opacity of Program's obligation solutions... *)
    unfold inc_monotonic_obligation_8. unfold inc_monotonic_obligation_6.
    unfold inc_monotonic_obligation_5. unfold inc_monotonic_obligation_7.
    unfold inc_monotonic_obligation_4.
    (* Can't just do eauto with arith anymore, because we need to apply some axioms about the behavior of imperative code. *)
    (* TODO: Double-check: we're using the same env for write checks that correspond to both before and after executing e,
             which is only okay when Γ = Γ'... *)
    apply weak_pureApp_morphism; eauto with arith.
  Qed.

  Local Obligation Tactic := intros; eauto with arith; compute; auto with arith; repeat constructor.
  Program Definition mkRFCounter {Γ} (l:lock) : rgref Γ (rf_monotonic_counter l) Γ :=
    (*RCCAlloc l 0.*)
    rcc_alloc _ _ _ l 0 _ _ _ _ _ _.
  (** Again, remember that the lock witness should really be in a monadic context *)
  Parameter w : var.
  Program Example test_counter {Γ} (l:lock) : rgref Γ unit Γ :=
    x <- mkRFCounter l;
    _ <- acquire w l;
    _ <- @inc_monotonic _ _ w _ x;
    @release _ _ w _.

  
End RaceFreeMonotonicCounter.
