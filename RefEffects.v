Require Import RGref.DSL.DSL.

Class Library {T:Set}(o:T) : Prop := {}.
Class Safe {T:Set}(t:T) : Prop := {}.
Class SafeType (T:Set) : Prop := {}.
Instance safe_lib {T:Set}{o:T}`{Library T o} : Safe o.
Instance val_of_safe_type {T:Set}`{SafeType T}(t:T) : Safe t.
Instance puretype_safe {T:Set}`{pure_type T} : SafeType T.

Instance safe_app {A:Set}{B:A->Set}(f:forall (x:A), B x)(a:A)`{Safe _ f}`{Safe _ a} : Safe (f a).
Check safe_app.

Program Axiom safewrite : forall {Γ:tyenv}{A:Set}`{rel_fold A}{P R G}`{hreflexive G}(x:ref{A|P}[R,G])(e:A)`{Safe A e}
                      (meta_x_deref:A) (meta_e_fold:A) 
                      (** These meta args are notationally expanded x and e using the identity relation folding *)
                 {guar:forall h, (forall A (fa:rel_fold A), fa = meta_fold) -> G (meta_x_deref) e h (heap_write x e h)}
                 {pres:(forall h, P meta_x_deref h -> P meta_e_fold (heap_write x meta_e_fold h))}
                 , rgref Γ unit Γ.
Notation "[ x ]:= e" := (@safewrite _ _ _ _ _ _ _ x e _ ({{{!x}}}) ({{{e}}}) _ _) (at level 70).


Section SafeCounter.
  Require Import Coq.Arith.Arith.
  (** * A Monotonic Counter
   A monotonically increasing counter.*)

  Definition increasing : hrel nat :=
    (fun n => fun n' => fun _ => fun _ => n <= n').
  Hint Unfold increasing.
  (** We'll give the Program extension some hints for this module *)
  Local Obligation Tactic := intros; eauto with arith; compute; eauto with arith.
          
  (** Now the definition of a verified monotonically increasing counter is
    barely more work than a completely unchecked counter. *)
  Program Definition monotonic_counter := ref nat any increasing increasing.
          
  Program Definition read_counter (c:monotonic_counter) : nat := !c.
          
  Program Definition inc_monotonic { Γ } (p:monotonic_counter) : rgref Γ unit Γ :=
    [p]:= !p + 1.

  Print inc_monotonic.
  
  Program Definition mkCounter { Γ } (u:unit) : rgref Γ monotonic_counter Γ :=
    Alloc 0.

  Program Example test_counter { Γ } (u:unit) : rgref Γ unit Γ :=
    x <- mkCounter tt;
    inc_monotonic x.

End SafeCounter.

  Instance fn_fold {T : Set}{B : T -> Set} : rel_fold (forall x : T, B x) := {
    rgfold := fun _ _ => (forall x : T, B x);
    fold := fun _ _ x => x
  }.

Section MemoTable.

  Variable B : nat -> Set.
  Variable fn : forall (x:nat), B x.
  Parameter safe_fn : Safe fn.
  Existing Instance safe_fn.

  Definition prefernat {P:nat->Set}(f:forall x:nat, P x)(a:nat) : forall x:nat, P x.
    refine(let v := f a in
             (fun x => if eq_nat_dec x a then _ else f x)).
    subst. exact v.
  Defined.
  Print prefernat.

  Definition obs_equiv {A:Set}{P:A->Set}(f g:forall x, P x)(_ _:heap) :=
    forall x, f x = g x.
  Lemma obs_eq_refl : forall A P, hreflexive (@obs_equiv A P).
  Proof. intros; red. compute. eauto. Qed.
  Hint Resolve obs_eq_refl.

  Instance prior_safe (r:ref{forall x:nat,B x|any}[obs_equiv,obs_equiv]) (n:nat)
    : Safe (@prefernat B (@deref _ _ _ _ _ _ (obs_eq_refl _ _) eq_refl r) n).
  
  Program Definition prioritize {Γ} (r:ref{forall x:nat,B x|any}[obs_equiv,obs_equiv]) (n:nat) : rgref Γ unit Γ :=
    [r]:= prefernat (!r) n.
  Next Obligation.
    red. unfold prefernat. intros. induction (eq_nat_dec x n); intuition; eauto.
    subst. compute. eauto.
  Qed.
  
  (* Cannot type-check, because one of the generated obligations is
         Safe (fun x => !r x) -- which would tie Landin's knot
  Program Definition bad_prioritize {Γ} (r:ref{forall x:nat,B x|any}[obs_equiv,obs_equiv]) (n:nat) : rgref Γ unit Γ :=
    [r]:= (fun x => (!r) x).
  *)

End MemoTable.

  Instance n2n : ImmediateReachability (nat -> nat) := { imm_reachable_from_in := fun _ _ _ _ _ _ => False }.
  Print Containment.
  Instance n2nc : Containment (nat -> nat) := {contains := fun _ => False}.

  Instance n2n' : ImmediateReachability (forall x : nat, (fun _ : nat => nat) x) := { imm_reachable_from_in := fun _ _ _ _ _ _ => False }.
  Lemma precise_obs_equiv : precise_rel (@obs_equiv nat (fun _ => nat)).
  Proof. compute. intuition. Qed.
  Hint Resolve precise_obs_equiv.

  Program Example test1 {Γ} : rgref Γ unit Γ :=
    r <- Alloc S;
    prioritize _ r 0.

  (* TODO: Need to have safe Alloc for this to fail where it should... *)
  Program Example should_not_typecheck {Γ} (r:ref{nat|any}[havoc,havoc]) : rgref Γ unit Γ :=
    r <- Alloc (fun x => !r);
    prioritize _ r 0.

  Extraction prefernat.
  Recursive Extraction test1.
