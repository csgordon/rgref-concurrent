Require Import RGref.DSL.DSL.
Require Import AppendOnlyLinkedList.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.

(** * Unsoundness Examples Requiring Coq Extensions to Fix
    This file contains examples of known unsoundnesses in the RGref implementation.  Not arbitrary
    unsoundness examples (like assuming false, etc.), but specifically those that are easy to fall
    over accidentally, and would require extensions to Coq to fix.  Things that are simply bugs
    in the RGref design don't go here (those are fixable bugs).  These bugs require either a Coq
    plugin, custom hacked up Coq version, or external frontend checks to restrict certain
    expressions further than can be done within Coq itself.
*)

(** ** Dangerous Projections into Computations
    This example highlights the dangers from allowing arbitrary proof terms (really, any term with
    a non-closed dependent type) to flow into raw computations:
*)
Program Definition BAD_alist_append {Γ}(n:nat)(l:alist) : rgref Γ unit Γ :=
  (RGFix _ _ (fun (rec:alist->rgref Γ unit Γ) =>
             (fun tl => match !tl with
                          | None => ( f <- Alloc None;
                                      u <- [ tl ]:= (Some (rcons n f));
                                      rgret u
                                      (*x <- Alloc None;
                                      [ tl ]:= (Some (rcons (S n) x))*)
                                    )
                          | Some l' => (match l' with
                                          | rcons n' tl' => rec tl'
                                        end)
                        end))) l.
Next Obligation. compute in Heq_anonymous. compute. rewrite <- Heq_anonymous. constructor. Qed.  
(** The specific issue with this example is that using a match inside a Program Definition
    adds an equality proof to the context for goals inside the match clauses.  In this case,
    in the None branch of the match, the assumption << !tl=None >> is added to the context.
    For the first write in that clause, we want and need that assumption, in order to prove
    the original heap value was None so the write satisfies optset.  But the assumption is
    still present when discharging proofs about the /second/ write, at which point the
    assumption no longer holds!
*)
(** *** Possible Solutions
    In general, the only terms than can flow from pure (possibly dependently typed) terms
    into computations are those with closed types.  However, in this case we want the
    equality proof to flow into the context for the first guarantee proof, but not the second.
    
    We need some way to restrict where proofs are used.  Worse, if there was nested matching,
    we could end up with 2 or more of these assumptions, and only those not invalidated by the
    first write could soundly be allowed at the second.  This is tricky, and proving certain
    assumptions aren't invalidated introduces additional burden.

    Possibly a better approach (if we're willing to either hack up or clone and modify the Program
    extension) would be to try introducing these assumptions via the P component of the reference.
    It's not totally obvious how this would work, though: (λ v h. v = None) is not stable w.r.t.
    optset!

    Likely we'll also require some custom match/if construct that uses some trickery to restrict
    where proofs flow when the branches are some kind of computation expression.
*)
    