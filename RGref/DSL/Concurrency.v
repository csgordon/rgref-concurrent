Require Import RGref.DSL.DSL.
Require Import RGref.DSL.Fields.


(* CAS Axioms and notations *)
Axiom cas_core : forall Γ T P R G (r : ref{T|P}[R,G]) (e0 : T) (e' : T),
                        (forall h, h[r]=e0 -> G e0 e' h (heap_write r e' h)) ->
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
Notation "LinAlloc[ v ] e" := (varalloc' (fun x h => x=e) empty havoc v e ({{{e}}}) _ _ _ _ _) (at level 70).
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
