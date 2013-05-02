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
     Remember than a backbone node is one reachable from the head, and only unmarked nodes are backbone nodes.
     Marked nodes are removed, exterior nodes.

  *)
  Inductive E : Set :=
    mkE : forall C P R G,
            ⊠ -> bool -> option (ref{C|P}[R,G]) -> E.
  Definition valOfE (e:E) : ⊠ := match e with mkE C P R G n m tl => n end.
  Definition markedOfE (e:E) : bool := match e with mkE C P R G n m tl => m end.
  Inductive deltaE (P:hpred E): hrel E :=
  (* Implicitly:
     - δk : The key of a node does not change
     - δen : successor of exterior (marked) node doesn't change
  *)
  | deltaE_refl : forall R G n m nxt h h',
                    (match nxt with None => True | Some tl => valOfE (h'[tl]) = valOfE (h[tl]) end) ->
                    deltaE P (mkE E P R G n m nxt) (mkE E P R G n m nxt) h h'
  (* δm : A marked node does not become unmarked (we encode the complement of this relation) *)
  | deltaE_mark : forall n R G next h h',
                    (match next with None => True | Some tl => valOfE (h'[tl]) = valOfE (h[tl]) end) ->
                    deltaE P (mkE E P R G n false next) (mkE E P R G n true next) h h'
  (* δbn : if a backbone successor changes, it remains a backbone (unmarked) in the new heap
           (part 1 of 2: also need to support removal) *)
  | deltaE_insert : forall n R G tl tl' h h' n',
                      (* only insert unmarked nodes *)
                      h'[tl']=(mkE E P R G n' false (Some tl)) -> (* note final heap *)
                      n ≪ n' ->
                      deltaE P (mkE E P R G n false (Some tl)) (mkE E P R G n false (Some tl')) h h' (* can assume Some b/c of sentinels *)
   (* δbn : if a backbone successor changes, it remains a backbone (unmarked) in the new heap
            (part 2 of 2: see insertion above) *)
  | deltaE_remove : forall R G n tl n' tl' h h',
                      n ≪ n' -> (* should be easy to prove at writes, handy to have explicit for stability proof *)
                      (* only remove marked nodes *)
                      h[tl] = (mkE E P R G n' true (Some tl')) -> (* note initial heap *)
                      deltaE P (mkE E P R G n false (Some tl)) (mkE E P R G n false (Some tl')) h h'
  .
  Inductive invE : hpred E :=
    pf_invE : forall h n m P next,
                (* φ_< : The key of every node is smaller than the key of its successor *)
                (match next with None => True | Some tl => exists n', n ≪ n' /\ valOfE (h[tl])=n' end) ->
                invE (mkE E P (deltaE P) (deltaE P) n m next) h.

  Inductive head_props : hpred E :=
    (* φ-∞ : Key of the head is -∞ *)
    head_props_ctor : forall h tl, head_props (mkE E invE (deltaE invE) (deltaE invE) -∞ false (Some tl)) h.
  Inductive tail_props : hpred E :=
    (* φTn : The tail node has no successor
       φ∞ : Key of the tail is ∞ *)
    tail_props_ctor : forall h, tail_props (mkE E invE (deltaE invE) (deltaE invE) ∞ false None) h.
  Inductive HindsightListBlock : Set :=
    (* φH, φT: head and tail are non-null, encoded as not being options *)
    mkHLB : ref{E|(invE ⊓ head_props)}[deltaE invE,deltaE invE] -> 
            ref{E|(invE ⊓ tail_props)}[deltaE invE,deltaE invE] -> 
            HindsightListBlock.

  (* The actual hindsight list.
     - δH, δT : head and tail refs don't change, encoded in locally-const
  *)
  Definition hindsight_list := ref{HindsightListBlock|any}[local_imm,local_imm].

  (*
    nextOfE : E -> Maybe (Ref E invE deltaE deltaE)
    nextOfE (mkE n m next) = next*)

  Definition eptr := ref{E|invE}[deltaE invE,deltaE invE].

  (** Unfortunately, using the impredicative encoding for mutually inductive datatypes with mutual indexing
     means injectivity can't work on equalities between Es: it would produce an equality on
     two elements of Set, which is in Type, thereby performing a large elimination into a predicative
     universe.  To work around this, I'm adding injectivity axioms for E.

     THIS IS UNSOUND.

     But the ways I want to use them should not actually produce contradictions, and I'm working around
     an implementation limitation of Coq's support for mutual inductive types. *)
  Axiom e_inj1 : forall C D P P' R R' G G' n n' m m' tl tl', mkE C P R G n m tl = mkE D P' R' G' n' m' tl' -> C = D.
  (* Technically this axiom also adds functional extensionality and proof irrelevance in Prop... *)
  Axiom e_inj2 : forall C P P' R R' G G' n n' m m' tl tl', mkE C P R G n m tl = mkE C P' R' G' n' m' tl' -> P = P' /\ R = R' /\ G = G'.
  Axiom e_inj3 : forall C P R G n n' m m' tl tl', mkE C P R G n m tl = mkE C P R G n' m' tl' -> n=n' /\ m=m' /\ tl=tl'.

  Ltac crunchE :=
    repeat match goal with
    | [ h : mkE ?c ?p ?r ?g ?n ?m ?tl = mkE ?d ?q ?s ?t ?n2 ?m2 ?tl2 |- _ ] => let H := fresh in
                                                                                 let H' := fresh in
                                                                                   let H'' := fresh in
                                                                                   destruct (e_inj3 _ _ _ _ _ _ _ _ _ _ h) as [H [H' H'']]; clear h; subst
    | [ h : mkE ?c ?p ?r ?g ?n ?m ?tl = mkE ?d ?q ?s ?t ?n' ?m' ?tl' |- _ ] => let H := fresh in
                                                                                 let H' := fresh in
                                                                                   let H'' := fresh in
                                                                                   destruct (e_inj2 _ _ _ _ _ _ _ _ _ _ _ _ _ h) as [H [H' H'']]; subst
    | [ h : mkE ?c ?p ?r ?g ?n ?m ?tl = mkE ?d ?q ?s ?t ?n' ?m' ?tl' |- _ ] => let H := fresh in
                                                                                 let H' := fresh in
                                                                                   let H'' := fresh in
                                                                                   destruct (e_inj1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ h) as [H [H' H'']]; subst
    end.
  Unset Ltac Debug.

  Lemma stable_nodes : stable invE (deltaE invE).
  Proof.
    red; intros.
    induction H0; inversion H; subst; crunchE; eauto.
        (*refl*) induction nxt; constructor; eauto.
                 destruct H1. destruct H1. exists x. intuition. rewrite H0; eauto.
        (*mark*) induction next; constructor; eauto. destruct H1; destruct H1; eexists; intuition. rewrite <- H2 in *. rewrite H0; eauto.
        (*ins*) destruct H2. destruct H2. constructor. exists n'. intuition. rewrite H0. compute. reflexivity.
        (*rm *) constructor.
                 assert (Htmp := heap_lookup2 h' tl'). inversion Htmp; subst.
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

  Inductive e_reaching (T:Set) P R G : ref{T|P}[R,G] -> E -> Prop :=
    tl_ptr_reach : forall n m r, e_reaching T P R G r (mkE T P R G n m (Some r)).
  Global Instance e_reach : ImmediateReachability E := { imm_reachable_from_in := e_reaching }.
  Global Instance e_cont : Containment E :=
  { contains := (fun Rel => forall T P (R G:hrel T) n m r h h', R (h[r]) (h'[r]) h h' -> Rel (mkE T P R G n m (Some r)) (mkE T P R G n m (Some r)) h h') }.
  Print rel_fold.
  Program Instance fold_e : rel_fold E :=
  { rgfold := (fun R G => E);
    fold := (fun R' G' e => match e with
                          | mkE T P R G n m None =>
                              mkE T P R (fun x x' h h' => G x x' h h' /\
                                                            forall n' m' r, h[r]=x -> h'[r]=x' ->
                                                              G' (mkE T P R G n' m' (Some r)) (mkE T P R G n' m' (Some r)) h h') n m None
                          | mkE T P R G n m (Some tl) =>
                              mkE T P R (fun x x' h h' => G x x' h h' /\
                                                            (forall n' m' r (ir:ImmediateReachability T), h[r]=x -> h'[r]=x' ->
                                                              G' (mkE T P R G n' m' (Some r)) (mkE T P R G n' m' (Some r)) h h'))
                                  n m (Some (@convert_G T P R G _ _ _ _ tl))
                          end)
  }.
  Next Obligation. Admitted. (* Not sure where to find an ImmReach...*)
  Next Obligation. red; intros. Admitted. (* Should be precise... need to prove this eventually *)
  Next Obligation. red. intros. intuition. Defined.

  Lemma precise_invE : precise_pred invE.
  Proof.
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
      derivable from any general approach. *)
  Inductive r_hlb : forall T P R G (r:ref{T|P}[R,G]), HindsightListBlock -> Prop :=
    | r_hd : forall hd tl, r_hlb E (invE ⊓ head_props) (deltaE invE) (deltaE invE) hd (mkHLB hd tl)
    | r_tl : forall hd tl, r_hlb E (invE ⊓ tail_props) (deltaE invE) (deltaE invE) tl (mkHLB hd tl).
  Global Instance reach_hlb : ImmediateReachability HindsightListBlock := { imm_reachable_from_in := r_hlb }.
  Instance fold_HLB : rel_fold HindsightListBlock. Admitted.
                                                     
           
  Program Definition init_HL {Γ}(_:unit) : rgref Γ hindsight_list Γ :=
    tail <- Alloc (mkE E invE (deltaE invE) (deltaE invE) ∞ false None);
    head <- Alloc (mkE E invE (deltaE invE) (deltaE invE) -∞ false (Some (convert_P _ _ _ tail)));
    Alloc (mkHLB head tail).
  Next Obligation. Admitted. (* stability *)
  Next Obligation. split; try constructor; eauto. Qed. (* Tail P *)
  Next Obligation. Admitted. (* precision of deltaE *)
  Next Obligation. Admitted. (* again *)
  Next Obligation. eapply pred_and_proj1; eauto. Qed.
    
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

    contains : hindsight-list → ⊠ → ● Bool
    contains l k =
      pc ← locate l k ,
      return (case pc of λ { (mkPair p c) -> valOfE (! c) == k })

    {- This is the TR version of the Hindsight paper -}
    remove : hindsight-list -> ⊠ -> ● Bool
    remove l k = loop-cont false (λ changed ->
                     pc ← (locate l k) ,
                     {!!}
                 )
                 (return)
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
