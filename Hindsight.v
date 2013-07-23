Require Import RGref.DSL.DSL.
Require Import RGref.DSL.Fields.
Require Import RGref.DSL.Concurrency.
Require Import Utf8.

(* Apparently there's no model of the infinite integers in Agda OR Coq.  So I'll postulate one as χ. *)
Axiom infinite_ints : Set.
Notation "⊠" := (infinite_ints).
Axiom inf : ⊠.
Notation "∞" := inf.
Axiom ninf : ⊠.
Notation "-∞" := ninf.
Axiom ii_lt : ⊠ → ⊠ → Prop.
Infix "≪" := ii_lt (at level 50).
Axiom ii_lt_b : ⊠ → ⊠ → bool.
Infix "≪≪" := ii_lt_b (at level 50).
Axiom ninf_lt_inf : -∞ ≪ ∞.
Axiom inf_eqb : ⊠ → ⊠ → bool.
Axiom ii_lt_trans : forall x y z, x ≪ y -> y ≪ z -> x ≪ z.
  
   
  (*postulate
    _≈_ : ∀ {τ : Set}{P : hpred τ}{R : hrel τ}{G : hrel τ} → Ref τ P R G → Ref τ P R G → Bool*)

(** * Verifying Linearizability with Hindsight *)
(** Overall, this structure must have the following invariants and step restrictions, based on the PODC'10 paper
     and the technical report Noam Rinetzky provided:
     - DONE - φH: head is non-null
     - DONE - φT: tail is non-null
     - DONE - φTn : The tail node has no successor
     - .... - φn : Every node other than the tail has a successor
     - DONE - φ∞ : Key of the tail is ∞
     - DONE - φ-∞ : Key of the head is -∞
     - DONE - φ< : Key of each node is < key of successor
     - .... - φrT : tail node is reachable from every node
     - IMPL - φac : list is acyclic (seems to follow from φrT and φTn...)
     - IMPL - φs : The list is sorted (seems to follow from φ<)
     -- Slight modification.  The PODC paper gives the following:
        - φUB : A node is marked iff it's a backbone node
     -- But that assumes marking and physical removal are atomic.  They won't be.  So the TR version
     -- Noam provided substitutes a weaker invariant:
     - .... - φub : A node is unmarked only if it is a backbone node
     - DONE - δH : value of head ptr never changes
     - DONE - δT : value of tail ptr never changes
     - DONE - δk : key of a node never changes
     - DONE - δm : marked nodes never become unmarked
     - .... - δe : exterior node does not become a backbone node (seems to follow from φUB and δm... not from φub...)
     - DONE - δen : successor of an exterior node does not change (succ of marked node doesn't change)
     - DONE - δbn : if a backbone successor changes, the node must remain a backbone (unmarked)
     Remember that a backbone node is one reachable from the head, and only unmarked nodes are backbone nodes.
     Marked nodes are removed, exterior nodes.

     DONE = done
     IMPL = implicit in data representation (e.g. option vs. not option for nullable vs. non-null )

  *)
(** We'll axiomatize an inductive-inductive characterization, including elimination and the computational behavior
    of the eliminator. *)
  Axiom E : Set.
  Axiom deltaE : hrel E.
  Axiom invE : hpred E.
  Axiom mkE : ⊠ -> bool -> option (ref{E|invE}[deltaE,deltaE]) -> E.
  Axiom destruct_E : forall (e:E), exists n m tl, e = mkE n m tl.
  Axiom E_rect : forall (T:E->Type) (body:forall n m tl, T (mkE n m tl)) (e:E), T e.
  Axiom E_rect' : forall (e:E) (T:E->Type) (body:forall n m tl (pf:e=mkE n m tl), T (mkE n m tl)), T e.
  Axiom E_rect_red : forall T body n m tl, E_rect T body (mkE n m tl) = body n m tl.
  Axiom E_rect'_red : forall T  n' m' tl' (body:forall n m tl, mkE n' m' tl'=mkE n m tl -> T (mkE n m tl)),
                        E_rect' (mkE n' m' tl') T body = body n' m' tl' (eq_refl (mkE n' m' tl')).
  Axiom mkE_inj : forall n n' m m' tl tl', mkE n m tl = mkE n' m' tl' -> n=n' /\ m=m' /\ tl=tl'.
  Ltac injectE :=
    match goal with
        | [ H : mkE _ _ _ = mkE _ _ _ |- _ ] => let a := fresh in let b := fresh in let c := fresh in
                                                destruct (mkE_inj _ _ _ _ _ _ H) as [a [b c]]; clear H
    end.
  Definition valOfE (e:E) : ⊠ := E_rect (fun _ => ⊠) (fun n m tl => n) e.
  Definition markedOfE (e:E) : bool := E_rect (fun _ => bool) (fun n m tl => m) e.
  Inductive deltaE' : hrel E :=
  (* Implicitly:
     - δk : The key of a node does not change
     - δen : successor of exterior (marked) node doesn't change
  *)
  | deltaE_refl : forall n m nxt h h',
                    (match nxt with None => True | Some tl => valOfE (h'[tl]) = valOfE (h[tl]) end) ->
                    deltaE' (mkE n m nxt) (mkE n m nxt) h h'
  (* δm : A marked node does not become unmarked (we encode the complement of this relation) *)
  | deltaE_mark : forall n next h h',
                    (valOfE (h'[next]) = valOfE (h[next])) ->
                    deltaE' (mkE n false (Some next)) (mkE n true (Some next)) h h'
  (* δbn : if a backbone successor changes, it remains a backbone (unmarked) in the new heap
           (part 1 of 2: also need to support removal) *)
  | deltaE_insert : forall n tl tl' h h' n',
                      (* only insert unmarked nodes *)
                      h'[tl']=(mkE n' false (Some tl)) -> (* note final heap *)
                      n ≪ n' ->
                      deltaE' (mkE n false (Some tl)) (mkE n false (Some tl')) h h' (* can assume Some b/c of sentinels *)
   (* δbn : if a backbone successor changes, it remains a backbone (unmarked) in the new heap
            (part 2 of 2: see insertion above) *)
  | deltaE_remove : forall n tl n' tl' h h',
                      n ≪ n' -> (* should be easy to prove at writes, handy to have explicit for stability proof *)
                      (* only remove marked nodes *)
                      h[tl] = (mkE n' true (Some tl')) -> (* note initial heap *)
                      deltaE'  (mkE n false (Some tl)) (mkE n false (Some tl')) h h'
  with invE' : hpred E :=
    pf_invE : forall h n m next,
                (* φ_< : The key of every node is smaller than the key of its successor *)
                (match next with None => True | Some tl => exists n', n ≪ n' /\ valOfE (h[tl])=n' end) ->
                invE' (mkE n m next) h.
  (* Let's try just baking equality in since we're equating elements of Prop anyways, rather than the iff used in other examples. *)
  Axiom inv : invE = invE'.
  Axiom delt : deltaE = deltaE'.
  Ltac fixdefs := try rewrite inv in *; try rewrite delt in *.

  Inductive head_props : hpred E :=
    (* φ-∞ : Key of the head is -∞ *)
    head_props_ctor : forall h tl, head_props (mkE -∞ false (Some tl)) h.
  Inductive tail_props : hpred E :=
    (* φTn : The tail node has no successor
       φ∞ : Key of the tail is ∞ *)
    tail_props_ctor : forall h, tail_props (mkE ∞ false None) h.
  Inductive HindsightListBlock : Set :=
    (* φH, φT: head and tail are non-null, encoded as not being options *)
    mkHLB : ref{E|(invE ⊓ head_props)}[deltaE,deltaE] -> 
            ref{E|(invE ⊓ tail_props)}[deltaE,deltaE] -> 
            HindsightListBlock.

  (* The actual hindsight list.
     - δH, δT : head and tail refs don't change, encoded in locally-const
  *)
  Definition hindsight_list := ref{HindsightListBlock|any}[local_imm,local_imm].

  (*
    nextOfE : E -> Maybe (Ref E invE deltaE deltaE)
    nextOfE (mkE n m next) = next*)

  Definition eptr := ref{E|invE}[deltaE,deltaE].

  Lemma stable_nodes : stable invE deltaE.
  Proof.
    fixdefs.
    red; intros.
    induction H0; inversion H; repeat injectE; subst; eauto.
        (*refl*) induction nxt; constructor; eauto.
                 destruct H2. destruct H1. exists x. intuition. rewrite H0; eauto.
        (*mark*) destruct H2; destruct H1; eexists; intuition. exists x. rewrite <- H2 in *. eauto. 
        (*ins*) destruct H3. destruct H2. constructor. exists n'. intuition. rewrite H0. compute.
                 rewrite E_rect_red.
                 reflexivity.
        (*rm *) constructor.
                 assert (Htmp := heap_lookup2 h' tl').
                 assert (Htmp' : invE' (h' [tl']) h'). rewrite <- inv. assumption.
                 clear Htmp. inversion Htmp'; subst.
                 exists n'; intuition.
                 (* The issue is that we don't presently have any explicit connection between h[tl'] and h'[tl'].
                    They should either be the same (in this case definitely, but proving the acyclicity etc. is hard)
                    or constrained by the R on tl', which in this case is [deltaE invE], which preserves n. *)

                 (*destruct H1. destruct H1. constructor.
                 rewrite H0 in H2. compute in H2. subst.
                 assert (Htmp := heap_lookup2 h tl). inversion Htmp; subst.
                 assert (Htmp' := heap_lookup2 h tl'). inversion Htmp'; subst.
                 rewrite H0 in Htmp. inversion Htmp. crunchE.
                 destruct H6. destruct H6.
                 exists x0. split. apply (ii_lt_trans n x); eauto.*)
  Admitted.
  Hint Resolve stable_nodes.
  Lemma stable_tail : stable tail_props deltaE.
  Proof.
    fixdefs.
    red; intros.
    Require Import Coq.Program.Equality.
    dependent induction H0; inversion H; subst; repeat injectE; subst; eauto; try constructor.
    inversion H4. inversion H5. (* <-- Can't append when next is already Some *)
    inversion H4. inversion H5. 
  Qed.
  Hint Resolve stable_tail.
  Lemma stable_head : stable head_props deltaE.
  Proof.
    fixdefs.
    red; intros.
    Require Import Coq.Program.Equality.
    dependent induction H0; inversion H; subst; repeat injectE; subst; eauto; try constructor.
    inversion H4; subst.
    (* IMPORTANT: This is the mark case of deltaE, which permits marking the head.
       (Marking the tail is prohibited because we only mark nodes with (Some _) tails.)
       We shouldn't be allowed to mark the head for removal. Doing so also breaks linearizability,
       which is probably why the Hindsight paper doesn't enforce this constraint.
       TODO: Is there some way to spin this as an important clarification or minor bug fix to
             the Hindsight paper?  How do I present this.  Is the stability just irrelevant
             for the Hindsight paper, since they observe that all actions fall within those
             steps, and preserve these properties (since they don't mark the head)?
       TODO: Make sure this isn't just me doing a bad job translating the Hindsight paper's invariants.
     *)
  Admitted.
  Hint Resolve stable_head.
    
  Inductive e_reaching : forall (T:Set) P R G, ref{T|P}[R,G] -> E -> Prop :=
    tl_ptr_reach : forall n m r, e_reaching _ _ _ _ r (mkE n m (Some r)).
  Global Instance e_reach : ImmediateReachability E := { imm_reachable_from_in := e_reaching }.
  Global Instance e_cont : Containment E :=
  { contains := (fun Rel =>
                   forall n m R (r:ref{E|invE}[deltaE,deltaE]) h h',
                     R (h[r]) (h'[r]) h h' ->
                     Rel (mkE n m (Some r)) (mkE n m (Some r)) h h') }.
  Print rel_fold.
  (* The new ind-ind trick loses the ability to weaken every structural member of an inductive type,
     so this needs the pending folding update to treat only reflexive folds and field-access folds. *)
  Program Instance fold_e : rel_fold E :=
  { rgfold := (fun R G => E);
    fold := (fun R' G' e => e
                              (*match e with
                          | mkE n m None =>
                              mkE T P R (fun x x' h h' => G x x' h h' /\
                                                            forall n' m' r, h[r]=x -> h'[r]=x' ->
                                                              G' (mkE T P R G n' m' (Some r)) (mkE T P R G n' m' (Some r)) h h') n m None
                          | mkE T P R G n m (Some tl) =>
                              mkE T P R (fun x x' h h' => G x x' h h' /\
                                                            (forall n' m' r (ir:ImmediateReachability T), h[r]=x -> h'[r]=x' ->
                                                              G' (mkE T P R G n' m' (Some r)) (mkE T P R G n' m' (Some r)) h h'))
                                  n m (Some (@convert_G T P R G _ _ _ _ tl))
                          end*) )
  }.

  Lemma precise_invE : precise_pred invE.
  Proof.
    fixdefs.
    red. intros. inversion H. induction next; subst; try solve[constructor; eauto].
    constructor. rewrite <- H0. assumption. constructor. constructor.
  Qed.
  Lemma precise_tail : precise_pred tail_props.
  Proof.
    red; intros. inversion H; subst. constructor.
  Qed.
  Lemma precise_head : precise_pred head_props. (* This doesn't constrain tail reachability yet! *)
  Proof.
    red; intros. inversion H; subst.
    constructor.
  Qed.
  Hint Resolve precise_invE precise_tail precise_head.
  Lemma precise_deltaE : precise_rel deltaE.
  Proof.
    fixdefs.
    red; intros. inversion H1; subst; try constructor.
    induction nxt; eauto. rewrite <- H0. rewrite <- H. eauto. repeat constructor. repeat constructor.
    rewrite <- H0. rewrite <- H. eauto. repeat constructor. repeat constructor.
    eapply deltaE_insert. rewrite <- H0. eauto. repeat constructor. eauto.
    eapply deltaE_remove. eauto. rewrite <- H. eauto. repeat constructor.
  Qed.
  Hint Resolve precise_deltaE.
  Lemma refl_deltaE : hreflexive deltaE.
  Proof.
    fixdefs.
    compute. intros.
    assert (Htmp := destruct_E x).
    destruct Htmp as [n [m [tl H]]].
    rewrite H.
    clear H.
    constructor.
    induction tl; eauto.
  Qed.
  Hint Resolve refl_deltaE.

  (** At this point, I need more type class instances.... Really folding only makes sense for
      fully parametric types like pairs.  Per-field folding makes sense for everything
      else.  So I do need to split that typeclass, and move the folding requirement from
      allocation (which needs to work for whole or partial folding types) to dereference
      and field dereference.

      Also, it seems like containment can pretty much always be defined in terms of immediate
      reachability...
  *)
  Check @imm_reachable_from_in.
  Instance general_containment {T:Set}{ir:ImmediateReachability T} : Containment T :=
  { contains := (fun Rel => forall A P R G r x h h',
                              @imm_reachable_from_in T ir A P R G r x ->
                              R (h[r]) (h'[r]) h h' ->
                              Rel x x h h') }.
  (** Not 100% on this.  This constrains Rel to be locally reflexive, which is too strong.
      Pair needs to be derivable from this, and pair_contains allows components to
      change! It's okay to bake ref_contains into this, but other valid instances
      of one-off Containment instances composed with ref_contains need to be
      derivable from any general approach.

      I think the conclusion needs to be pulled 'back a level' in the heap: for any location l
      in the original heap h such that h[l]=x, Rel h[l] h'[l] h h'.  This allows for cyclic structures.

   *)
  Inductive r_hlb : forall T P R G (r:ref{T|P}[R,G]), HindsightListBlock -> Prop :=
    | r_hd : forall hd tl, r_hlb E (invE ⊓ head_props) deltaE deltaE hd (mkHLB hd tl)
    | r_tl : forall hd tl, r_hlb E (invE ⊓ tail_props) deltaE deltaE tl (mkHLB hd tl).
  Global Instance reach_hlb : ImmediateReachability HindsightListBlock := { imm_reachable_from_in := r_hlb }.
  Instance fold_HLB : rel_fold HindsightListBlock. Admitted.
                                                     
           
  Program Definition init_HL {Γ}(_:unit) : rgref Γ hindsight_list Γ :=
    tail <- Alloc (mkE ∞ false None);
    head <- Alloc (mkE -∞ false (Some (convert_P _ _ _ tail)));
    Alloc (mkHLB head tail).
  Next Obligation.
    split; try constructor; eauto.
    assert (forall x h, invE' x h -> invE x h). fixdefs. auto.
    apply H0. constructor; eauto.
  Qed. (* Tail P *)
  Next Obligation. eapply pred_and_proj1; eauto. Qed.
  Next Obligation.
    assert (forall x h, invE' x h -> invE x h). fixdefs. auto.
    split; intuition; eauto.
    apply H0. constructor.
    rewrite conversion_P_refeq.
    assert (Htmp := heap_lookup2 h tail). destruct Htmp. inversion H2; subst.
    exists ∞. intuition; eauto. apply ninf_lt_inf. compute. rewrite E_rect_red. reflexivity.
    constructor.
  Qed.
    
  Check @convert_P.
  Program Definition locate {Γ} (l:hindsight_list) (k:⊠) : rgref Γ (eptr * eptr) Γ :=
    match !l with
      | mkHLB H T =>
        E_rect' (!H) (fun _ => rgref Γ (eptr * eptr) Γ)
               (fun n m next pf => match next with
                                    | None => False_rect _ _ (* TODO: Contradiction *)
                                    | Some tl =>
                                      RGFix _ _
                                            (fun rec x =>
                                               match x with
                                               | (p, c) => if (valOfE (!c) ≪≪ k)
                                                           then rec (c, _) (* TODO: convert option eptr to an eptr, provable since k ≪≪ ∞ *)
                                                           else rgret (p, c)
                                               end
                                            )
                                            ((@convert_P _ _ invE _ _ _ _ _ _ H), tl)
                                  end)
    end
  .
  Next Obligation. Admitted. (* folding.. *)
  Next Obligation. (* Now with tie b/t ! and some heap, can invalidate the None using head_props *) Admitted.
  Next Obligation. eapply pred_and_proj1; eauto. Qed.

(*
    {- TODO: I feel like the return type might need to be refined to give the relationship between k and the node values -}
    locate : hindsight-list → ⊠ → ● (pair eptr eptr)
    locate l k = case (! l) of λ { (mkHLB H T) ->
                      case (! H) of λ { (mkE n m nothing) -> {!!}; -- should be impossible due to sentinels.  Deducable w/ special match
                      (mkE inf m (just c₀)) ->
                      loop-cont (mkPair (convert-P H invE _) c₀)
                        (λ x → case x of λ {
                              (mkPair p c) -> if ((valOfE (! c)) ≪≪ k)
                                         then return (mkPair true (mkPair c {!!}))
                                              {- Above, must convert Maybe eptr to eptr.
                                                 Should eventually be able to prove safety using
                                                 tail reachability + all valid inputs (maybe k
                                                 should be ℤ?) should be ≪≪ ∞. -}
                                         else return (mkPair false (mkPair p c))
                      }) (λ x → return {!!})
                 }}
*)

  Program Definition contains {Γ} (l:hindsight_list) (k:⊠) : rgref Γ bool Γ :=
    pc <- locate l k;
    rgret (inf_eqb (valOfE (!(snd pc))) k).

(*
    contains : hindsight-list → ⊠ → ● Bool
    contains l k =
      pc ← locate l k ,
      return (case pc of λ { (mkPair p c) -> valOfE (! c) == k })
*)
  Program Definition remove {Γ} (l:hindsight_list) (k:⊠) : rgref Γ bool Γ :=
    (* bool changed = false; *)
    RGFix _ _ (fun rec (_:unit) =>
                 pc <- locate l k;
               (* Remaining pseudo-code from the PODC'10 TR:
                  atomic {
                      if (p.n==c && !p.m && !c.m) {
                          if (c.k != k) return changed
                          c.m = true;
                          changed = true;
                      }
                  }
                  atomic {
                      if (changed) {
                          if (p.n==c && !p.m) {
                              p.n = c.n;
                              return true;
                          }
                      }
                  }
               *)
               (* Aside from the complexity of managing the changed flag in the linearizability proof,
                  this code (the more granular version!) still touches a lot of non-contiguous memory atomically! *)
                 _
              ) _.
  Next Obligation. Admitted.
(*
    {- This is the TR version of the Hindsight paper -}
    remove : hindsight-list -> ⊠ -> ● Bool
    remove l k = loop-cont false (λ changed ->
                     pc ← (locate l k) ,
                     {!!}
                 )
                 (return)
*)
  Program Definition add {Γ} (l:hindsight_list) (k:⊠) : rgref Γ bool Γ :=
    RGFix _ _ (fun rec (_:unit) =>
                 pc <- locate l k;
                 match pc with
                 | (p, c) =>
                   if inf_eqb _ k (* c.k == k *)
                   then rgret false
                   else _
                          (* Unreasonable pseudocode from PODC paper:
                             atomic {
                                 if (p.n == c && !p.m && !c.m) {
                                     E t = alloc(E);
                                     t.m = false;
                                     t.k = k;
                                     t.n = c; <-- Going to need the CAS+control-flow to do conditional sharing...
                                     p.n = t;
                                     return true;
                                 }
                             }
                             This still touches two disjoint locations in the test, allocates a multi-word object, and writes into p.n atomically....
                             *)
                              
                 end
              ) _.
  Next Obligation. Admitted.
(*
    mb : Maybe eptr -> Maybe eptr -> Bool
    mb (just x) (just x') = x ≈ x'
    mb _ _ = false
                 
    add : hindsight-list -> ⊠ -> ● Bool
    add l k = loop-cont false (λ x →
                  {- Ideally this should be outside the loop, substructural in Γ, and Γ≺Δ should restore the 'any'
                     invariant for the loop -}
                  t ← alloc any (λ x x' x0 x1 → ⊥) havoc (mkE k false nothing) (λ h → tt) ,
                  pc ← locate l k ,
                  (case pc of λ { (mkPair p c) ->
                      if valOfE (! c) == k
                      then return (mkPair false false)
                      else (_ ← ([ t ]:=< mkE k false (just c) > {!!}) , -- should be field write, needs strong update; t in Γ!
                            (if mb (nextOfE (! p)) (just c) ∧ (not (markedOfE (! p)))
                             then {!!} -- fCAS p Node-next c (convert-P t ...) {!!}, handle success/failure
                             else return (mkPair true x))) -- continue, arg irrelevant
                  })
              )
              (return)
*)
