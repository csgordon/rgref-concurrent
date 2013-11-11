Require Import RGref.DSL.DSL.
Require Import RGref.DSL.Fields.


(* CAS Axioms and notations *)
Axiom cas_core : forall Γ T P R G (r : ref{T|P}[R,G]) (e0 : T) (e' : T),
                        (forall (h:heap), h[r]=e0 -> G e0 e' h (heap_write r e' h)) ->
                        rgref Γ bool Γ.

Notation "CAS( r , e , e' )" := (cas_core _ _ _ _ _ r e e' _) (at level 70).

Axiom field_cas_core : forall Γ T P R G F FT `{FieldTyping T F} 
                              (r : ref{T|P}[R,G]) (f:F) `{FieldType T F f FT}
                              (fv0 : FT) (fv' : FT),
                              (forall h v, h[r]=v -> getF v = fv0 ->
                                           G v (setF v fv') h (heap_write r (setF v fv') h)) ->
                              rgref Γ bool Γ.

Notation "fCAS( r → f , e , e' )" := (@field_cas_core _ _ _ _ _ _ _ _ r f _ _ e e' _) (at level 70).

(* Additional specializations of CAS and allocation that are useful for concurrency. *)
(* TODO: This is only safe if Esafe 0 e *)
Notation "LinAlloc[ v ] e" := (varalloc' (fun x h => x=e) local_imm havoc v e _ _ _ _ _) (at level 70).
Axiom lin_convert : forall {Γ T P R G} v P' R' G'
                      {mem:tymember v (ref{T|P}[R,G]) Γ},
                      P⊑P'  -> (* refinement weakening *)
                      G'⊆G -> (* permission weakening *)
                      R⊆R' -> (* interference weakening *)
                      G'⊆R' -> (* self-splitting *)
                      stable P' R' ->
                      rgref Γ (ref{T|P'}[R',G']) (tyrem mem).
(* Conversion / sharing fCAS *)
Axiom field_cas_share : forall {Γ T P R G F FT} `{FieldTyping T F}
                               {aT aP aR aG aP' aR' aG'}
                               (v:var)
                                (mem:tymember v (ref{aT|aP}[aR,aG]) Γ),
                                aP⊑aP' -> (* refinement weakening *)
                                aG'⊆aG -> (* permission weakening *)
                                aR⊆aR' -> (* interference weakening *)
                                aG'⊆aR' -> (* self-splitting *)
                                stable aP' aR' ->
                              forall
                              (r : ref{T|P}[R,G]) (f:F) `{FieldType T F f FT}
                              (fv0 : FT) (fv' : ref{aT|aP'}[aR',aG'] -> FT),
                              (forall h v s, h[r]=v -> getF v = fv0 ->
                                             aP (h[s]) h ->
                                             G v (setF v (fv' s)) h (heap_write r (setF v (fv' s)) h)) ->
                              rgref Γ bool (tyrem mem).
Notation "share_field_CAS( r → f , e , e' , v , mem )" := 
    (@field_cas_share _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ v mem _ _ _ _ _ r f _ _ e e' _)
    (at level 65).


Axiom field_cas_share' : forall {Γ T P R G F FT} `{FieldTyping T F}
                               {aT aP}{aR aG:hrel aT}{aP'}{aR' aG':hrel aT}
                               (v:var)
                                (mem:tymember v (ref{aT|aP}[aR,aG]) Γ),
                                aP⊑aP' -> (* refinement weakening *)
                                aG'⊆aG -> (* permission weakening *)
                                (* aR⊆aR' -> (* interference weakening *) *)
                                (forall a a' h h',
                                   aP a h -> aR a a' h h' -> aR' a a' h h'
                                ) -> (* refined interference weakening *)
                                aG'⊆aR' -> (* self-splitting *)
                                stable aP' aR' ->
                                forall xP xR xG (l:ref{aT|xP}[xR,xG]),
                              forall
                              (r : ref{T|P}[R,G]) (f:F) `{FieldType T F f FT}
                              (fv0 : FT) (fv' : ref{aT|aP'}[aR',aG'] -> FT),
                              (forall h v s, h[r]=v -> getF v = fv0 ->
                                             aP (h[s]) h ->
                                             (not (xG ⊆ aR) \/ (not (aG ⊆ xR)) -> not (s ≡ l)) ->
                                             G v (setF v (fv' s)) h (heap_write r (setF v (fv' s)) h)) ->
                              rgref Γ bool (tyrem mem).
Notation "share_field_CAS'( r → f , e , e' , v , mem , l )" := 
    (@field_cas_share' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ v mem _ _ _ _ _ _ _ _ l r f _ _ e e' _)
    (at level 65).


(* Conversion / sharing DCAS, for two adjacent fields *)
(* Seems necessary for the Hindsight implementation *)
Axiom dcas_share : forall {Γ T P R G F FTf FTg} `{FieldTyping T F}
                               {aT aP aR aG aP' aR' aG'}
                               (v:var)
                                (mem:tymember v (ref{aT|aP}[aR,aG]) Γ),
                                aP⊑aP' -> (* refinement weakening *)
                                aG'⊆aG -> (* permission weakening *)
                                aR⊆aR' -> (* interference weakening *)
                                aG'⊆aR' -> (* self-splitting *)
                                stable aP' aR' ->
                              forall
                              (r : ref{T|P}[R,G]) 
                              (f:F) `{FieldType T F f FTf} (fv0 : FTf) (fv' : FTf)
                              (g:F) `{FieldType T F g FTg} (gv0 : FTg) (gv' : ref{aT|aP'}[aR',aG'] -> FTg),
                              (forall h v s, h[r]=v -> 
                                             getF v = fv0 ->
                                             getF v = gv0 ->
                                             aP (h[s]) h ->
                                             G v 
                                               (setF (setF v fv') (gv' s))
                                               h (heap_write r 
                                                             (setF (setF v fv') (gv' s)) h)) ->
                              rgref Γ bool (tyrem mem).
Notation "DCASs( r , f , f0 , f' , g , g0 , g' , v , mem )" := 
    (@dcas_share _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ v mem _ _ _ _ _ r f _ _ f0 f' g _ _ g0 g' _)
    (at level 65).
