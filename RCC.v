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

  (** Note that the witness arguments should really be monadic in the implementation; I'm prototyping
      actual source code. I'm also making them explicit, because they aren't inferred normally, but
      are inferred when using Program. *)
  Parameter rcc_read : forall {A B P R G}`{rel_fold A}{l:lock}(w:ref{lockwitness l | locked}[empty,locked-->unlocked])(r:rccref A P R G l),
                              hreflexive G -> rgfold R G = B -> B.
  (** We expose hwrite, because we need a way for clients to prove obligations that this module
      must translate down to the real RGref primitives, but without exposing the fact that
      rccrefs are just rgrefs.  This means re-exporting some axioms needed to state client obligations. *)
  Parameter hwrite : forall {l A P R G} (p:rccref A P R G l) (v:A) (h:heap), heap.
  Parameter rcc_write : forall {Γ A}`{rel_fold A}{P R G}`{hreflexive G}{l:lock}(w:ref{lockwitness l | locked}[empty,locked-->unlocked])(x:rccref A P R G l)(e:A)
                               (meta_x:A)(meta_e:A) (* meta args *)
                               {guar:forall h, (forall A (fa:rel_fold A), fa = meta_fold) -> G (meta_x) e h (hwrite x e h)}
                               {pres:(forall h, P meta_x h -> P meta_e (hwrite x meta_e h))}
                               , rgref Γ unit Γ.

  Parameter rcc_alloc : forall {Γ}{T:Set}{RT:ImmediateReachability T}{CT:Containment T}{FT:rel_fold T} P R G (l:lock) (e:T), 
                stable P R ->        (* predicate is stable *)
                (forall h, P e h) -> (* predicate is true *)
                precise_pred P ->    (* P precise *)
                precise_rel R ->     (* R precise *)
                precise_rel G ->     (* G precise *)
                rgref Γ (rccref T P R G l) Γ.
  (** Both of these should be introducing and removing witnesses in the linear context.  Since that's
      currently not implemented, for this sketch we're going closer to the desired source language. *)
  Parameter acquire : forall {Γ}(l:lock), rgref Γ (ref{lockwitness l | locked}[empty,locked-->unlocked]) Γ.
  Parameter release : forall {Γ}{l:lock}, ref{lockwitness l | locked}[empty,locked-->unlocked] -> rgref Γ unit Γ.
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
  Program Definition rcc_read {A B P R G}`{rel_fold A}{l:lock}(w:ref{lockwitness l | locked}[empty,locked-->unlocked])(r:rccref A P R G l)
                      (hrefl:hreflexive G)(fold:rgfold R G = B) := deref hrefl fold r.
  Definition hwrite := fun l:lock => @heap_write.
  (** Clients prove goals over the abstracted rcc reads; the module internally converts those for write's use *)
  Program Definition rcc_write {Γ A}`{rel_fold A}{P R G}`{hreflexive G}{l:lock}(w:ref{lockwitness l | locked}[empty,locked-->unlocked])(x:rccref A P R G l)(e:A)
                               (meta_x:A)(meta_e:A) (* meta args *)
                               {guar:forall h, (forall A (fa:rel_fold A), fa = meta_fold) -> G (meta_x) e h (heap_write x e h)}
                               {pres:(forall h, P meta_x h -> P meta_e (heap_write x meta_e h))}
                               : rgref Γ unit Γ :=
      @write' Γ A _ P R G _ x e meta_x meta_e _ _.

  Program Definition rcc_alloc {Γ}{T:Set}{RT:ImmediateReachability T}{CT:Containment T}{FT:rel_fold T} P R G (l:lock) (e:T) 
                `(stable P R)        (* predicate is stable *)
                `((forall h, P e h)) (* predicate is true *)
                `(precise_pred P)    (* P precise *)
                `(precise_rel R)     (* R precise *)
                `(precise_rel G)     (* G precise *)
                : rgref Γ (rccref T P R G l) Γ :=
      alloc _ _ _ e _ _ _ _ _.

  Parameter acquire : forall {Γ}(l:lock), rgref Γ (ref{lockwitness l | locked}[empty,locked-->unlocked]) Γ.
  Parameter release : forall {Γ}{l:lock}, ref{lockwitness l | locked}[empty,locked-->unlocked] -> rgref Γ unit Γ.
End RCCImpl.

(** * Using the RCC Module : A race-free counter *)
Require Import Coq.Arith.Arith.
Import RCCImpl.
(** rccref is opaque. *)
(** TODO: Figure out how to stash this notation /inside/ the module! *)
Notation "'rccwrite' x <:= e" := (@write' _ _ _ _ _ _ _ _ x e ({{{!x}}}) ({{{e}}}) _ _) (at level 60).
Notation "'RCCAlloc' l e" := (rcc_alloc _ _ _ l e _ _ _ _ _) (at level 70).
Section RaceFreeMonotonicCounter.
  Definition increasing : hrel nat :=
    fun n n' _ _ => n <= n'.

  Hint Unfold increasing.
  Local Obligation Tactic := intros; eauto with arith; compute; auto with arith.

  Program Definition rf_monotonic_counter (l:lock) := rccref nat any increasing increasing l.
  Program Definition read_counter {l:lock}{w:ref{lockwitness l | locked}[empty,locked-->unlocked]}(c:rf_monotonic_counter l) : nat :=
    @rcc_read _ _ _ _ _ _ l w c _ _.
  Check @rcc_write.
  Program Definition inc_monotonic {Γ l}(w:ref{lockwitness l|locked}[empty,locked-->unlocked]) (p:rf_monotonic_counter l) : rgref Γ unit Γ :=
    (*rccwrite p <:= ((rcc_read p _ _) + 1).*)
    @rcc_write Γ nat _ any increasing increasing _ l _ p (rcc_read _ p _ _ + 1) ({{{rcc_read _ p _ _}}}) ({{{rcc_read _ p _ _ + 1}}}) _ _.
  Program Definition mkRFCounter {Γ} (l:lock) : rgref Γ (rf_monotonic_counter l) Γ :=
    (*RCCAlloc l 0.*)
    rcc_alloc _ _ _ l 0 _ _ _ _ _.
  (** Again, remember that the lock witness should really be in a monadic context *)
  Program Example test_counter {Γ} (l:lock) : rgref Γ unit Γ :=
    x <- mkRFCounter l;
    w <- acquire l;
    _ <- inc_monotonic _ x;
    release w.
  
End RaceFreeMonotonicCounter.
