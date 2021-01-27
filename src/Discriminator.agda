-- MIT License

-- Copyright (c) 2021 Luca Ciccone and Luca Padovani

-- Permission is hereby granted, free of charge, to any person
-- obtaining a copy of this software and associated documentation
-- files (the "Software"), to deal in the Software without
-- restriction, including without limitation the rights to use,
-- copy, modify, merge, publish, distribute, sublicense, and/or sell
-- copies of the Software, and to permit persons to whom the
-- Software is furnished to do so, subject to the following
-- conditions:

-- The above copyright notice and this permission notice shall be
-- included in all copies or substantial portions of the Software.

-- THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
-- EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
-- OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
-- NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
-- HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
-- WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
-- FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
-- OTHER DEALINGS IN THE SOFTWARE.

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.List using ([]; _∷_; _∷ʳ_; _++_)
open import Data.List.Properties using (∷-injective)

open import Relation.Nullary
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Unary using (_∈_; _∉_; _⊆_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂; cong)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)

open import Function.Base using (case_of_)

open import Common

module Discriminator {ℙ : Set} (message : Message ℙ)
  where

open import Trace message
open import SessionType message
open import HasTrace message
open import TraceSet message
open import Transitions message
open import Subtyping message
open import Divergence message
open import Session message
open import Semantics message

make-diverge-backward :
  ∀{T S α}
  (tα : T HasTrace (α ∷ []))
  (sα : S HasTrace (α ∷ [])) ->
  T ↑ S ->
  after tα ↑ after sα ->
  DivergeBackward tα sα
make-diverge-backward tα sα divε divα none = divε
make-diverge-backward tα sα divε divα (some none) =
  subst₂ (λ u v -> after u ↑ after v) (sym (⊑-has-trace-after tα)) (sym (⊑-has-trace-after sα)) divα

has-trace-after-split :
  ∀{T φ ψ} ->
  (tφ : T HasTrace φ)
  (tφψ : T HasTrace (φ ++ ψ)) ->
  has-trace-after tφ (split-trace tφ tφψ) ≡ tφψ
has-trace-after-split (_ , tdef , refl) tφψ = refl
has-trace-after-split (_ , tdef , step inp tr) (_ , sdef , step inp sr)
  rewrite has-trace-after-split (_ , tdef , tr) (_ , sdef , sr) = refl
has-trace-after-split (T , tdef , step (out fx) tr) (S , sdef , step (out gx) sr)
  rewrite has-trace-after-split (_ , tdef , tr) (_ , sdef , sr) =
  cong (S ,_) (cong (sdef ,_) (cong (λ z -> step z sr) (cong out (Defined-eq (transitions+defined->defined sr sdef) gx))))

disc-set-has-outputs :
  ∀{T S φ x} ->
  T <: S ->
  φ ∈ DiscSet T S ->
  T HasTrace (φ ∷ʳ O x) ->
  S HasTrace φ ->
  φ ∷ʳ O x ∈ DiscSet T S
disc-set-has-outputs {_} {S} {φ} {x} sub (inc tφ sφ div←φ) tφx _ with S HasTrace? (φ ∷ʳ O x)
... | yes sφx =
  let tφ/x = split-trace tφ tφx in
  let sφ/x = split-trace sφ sφx in
  let divφ = subst₂ (λ u v -> after u ↑ after v) (⊑-has-trace-after tφ) (⊑-has-trace-after sφ) (div←φ (⊑-refl φ)) in
  let divx = _↑_.divergence divφ {[]} {x} none tφ/x sφ/x in
  let divφ←x = make-diverge-backward tφ/x sφ/x divφ divx in
  let div←φx = subst₂ DivergeBackward (has-trace-after-split tφ tφx) (has-trace-after-split sφ sφx) (append-diverge-backward tφ sφ tφ/x sφ/x div←φ divφ←x) in
  inc tφx sφx div←φx
... | no nsφx = exc refl tφ sφ tφx nsφx div←φ
disc-set-has-outputs sub (exc eq tψ sψ tφ nsφ div←ψ) tφx sφ = ⊥-elim (nsφ sφ)

defined-becomes-nil :
  ∀{T φ S} ->
  Defined T ->
  ¬ Defined S ->
  Transitions T φ S ->
  ∃[ ψ ] ∃[ x ] (φ ≡ ψ ∷ʳ I x × T HasTrace ψ × ¬ T HasTrace φ)
defined-becomes-nil def ndef refl = ⊥-elim (ndef def)
defined-becomes-nil def ndef (step (inp {_} {x}) refl) =
  [] , x , refl , (_ , inp , refl) , inp-has-no-trace λ { (_ , def , refl) → ⊥-elim (ndef def) }
defined-becomes-nil def ndef (step inp tr@(step t _)) with defined-becomes-nil (transition->defined t) ndef tr
... | ψ , x , eq , tψ , ntφ =
  I _ ∷ ψ , x , cong (I _ ∷_) eq , inp-has-trace tψ , inp-has-no-trace ntφ
defined-becomes-nil def ndef (step (out fx) tr) with defined-becomes-nil fx ndef tr
... | ψ , x , refl , tψ , ntφ =
  O _ ∷ ψ , x , refl , out-has-trace tψ , out-has-no-trace ntφ

sub+diverge->defined : ∀{T S} -> T <: S -> T ↑ S -> Defined T × Defined S
sub+diverge->defined nil<:any div with _↑_.with-trace div
... | _ , def , tr = ⊥-elim (contraposition (transitions+defined->defined tr) (λ ()) def)
sub+diverge->defined (end<:def (inp _) def) _ = inp , def
sub+diverge->defined (end<:def (out _) def) _ = out , def
sub+diverge->defined (inp<:inp _ _) _ = inp , inp
sub+diverge->defined (out<:out _ _ _) _ = out , out

sub+diverge->has-empty-trace : ∀{T S} -> T <: S -> T ↑ S -> DiscSet T S []
sub+diverge->has-empty-trace nil<:any div with _↑_.with-trace div
... | tφ = ⊥-elim (nil-has-no-trace tφ)
sub+diverge->has-empty-trace (end<:def e def) div with _↑_.with-trace div | _↑_.without-trace div
... | tφ | nsφ rewrite end-has-empty-trace e tφ = ⊥-elim (nsφ (defined->has-empty-trace def))
sub+diverge->has-empty-trace (inp<:inp _ _) div = inc (_ , inp , refl) (_ , inp , refl) λ { none → div }
sub+diverge->has-empty-trace (out<:out _ _ _) div = inc (_ , out , refl) (_ , out , refl) λ { none → div }

discriminator : SessionType -> SessionType -> SessionType
discriminator T S = decode (co-semantics (disc-set->semantics T S)) .force

discriminator-disc-set-sub : (T S : SessionType) -> CoSet ⟦ discriminator T S ⟧ ⊆ DiscSet T S
discriminator-disc-set-sub T S rφ =
  co-inversion {DiscSet T S} (decode-sub (co-semantics (disc-set->semantics T S)) rφ)

discriminator-disc-set-sup : (T S : SessionType) -> DiscSet T S ⊆ CoSet ⟦ discriminator T S ⟧
discriminator-disc-set-sup T S dφ =
  decode-sup (co-semantics (disc-set->semantics T S)) (co-definition {DiscSet T S} dφ)

sub+diverge->discriminator-defined : ∀{T S} -> T <: S -> T ↑ S -> Defined (discriminator T S)
sub+diverge->discriminator-defined {T} {S} sub div =
  has-trace->defined (co-set-right->left {DiscSet T S} {⟦ discriminator T S ⟧} (discriminator-disc-set-sup T S) (co-definition {DiscSet T S} {[]} (sub+diverge->has-empty-trace sub div)))

input-does-not-win :
  ∀{T S φ x} (tφ : T HasTrace φ) -> Transitions T (φ ∷ʳ I x) S -> ¬ Win (after tφ)
input-does-not-win (_ , _ , refl) (step inp _) ()
input-does-not-win (_ , def , step inp tr) (step inp sr) w = input-does-not-win (_ , def , tr) sr w
input-does-not-win (_ , def , step (out _) tr) (step (out _) sr) w = input-does-not-win (_ , def , tr) sr w

ends-with-output->has-trace : ∀{T S φ x} -> Transitions T (φ ∷ʳ O x) S -> T HasTrace (φ ∷ʳ O x)
ends-with-output->has-trace tr = _ , output-transitions->defined tr , tr

co-trace-swap : ∀{φ ψ} -> co-trace φ ≡ ψ -> φ ≡ co-trace ψ
co-trace-swap {φ} eq rewrite sym eq rewrite co-trace-involution φ = refl

co-trace-swap-⊑ : ∀{φ ψ} -> co-trace φ ⊑ ψ -> φ ⊑ co-trace ψ
co-trace-swap-⊑ {[]} none = none
co-trace-swap-⊑ {α ∷ _} (some le) rewrite co-action-involution α = some (co-trace-swap-⊑ le)

co-complete : ∀{X φ} -> φ ∈ Complete X -> co-trace φ ∈ Complete (CoSet X)
co-complete {X} (complete xφ F) =
  complete (co-definition {X} xφ) λ le xψ -> let le' = co-trace-swap-⊑ le in
                                             let eq = F le' xψ in
                                             co-trace-swap eq

co-complete-2 : ∀{X φ} -> co-trace φ ∈ Complete (CoSet X) -> φ ∈ Complete X
co-complete-2 {X} (complete wit F) =
  complete (co-inversion {X} wit) λ le xψ -> let le' = ⊑-co-trace le in
                                             let eq = F le' (co-definition {X} xψ) in
                                             co-trace-injective eq

co-trace->co-set : ∀{X φ} -> co-trace φ ∈ Complete X -> φ ∈ Complete (CoSet X)
co-trace->co-set {_} {φ} cxφ with co-complete cxφ
... | res rewrite co-trace-involution φ = res

discriminator-after-sync->defined :
  ∀{R T S T' φ} ->
  T <: S ->
  (rdef : Defined (discriminator T S))
  (rr : Transitions (discriminator T S) (co-trace φ) R)
  (tr : Transitions T φ T') ->
  Defined R
discriminator-after-sync->defined {R} {T} {S} sub rdef rr tr with Defined? R
... | yes rdef' = rdef'
... | no nrdef' with defined-becomes-nil rdef nrdef' rr
... | ψ , x , eq , rψ , nrφ rewrite eq with input-does-not-win rψ rr
... | nwin with contraposition (decode+complete->win (co-semantics (disc-set->semantics T S)) rψ) nwin
... | ncψ with decode-sub (co-semantics (disc-set->semantics T S)) rψ
... | dsψ with contraposition (disc-set-complete-1 dsψ) (contraposition co-trace->co-set ncψ)
... | nnsψ with has-trace-double-negation nnsψ
... | sψ with let tr' = subst (λ z -> Transitions _ z _) (co-trace-swap eq) tr in
              let tr'' = subst (λ z -> Transitions _ z _) (co-trace-++ ψ (I x ∷ [])) tr' in
              ends-with-output->has-trace tr''
... | tψ with disc-set-has-outputs sub dsψ tψ sψ
... | dsφ with decode-sup (co-semantics (disc-set->semantics T S)) (co-definition {DiscSet T S} dsφ)
... | rφ = let rφ' = subst (_ HasTrace_) (co-trace-++ (co-trace ψ) (O x ∷ [])) rφ in
           let rφ'' = subst (λ z -> _ HasTrace (z ++ _)) (co-trace-involution ψ) rφ' in
           ⊥-elim (nrφ rφ'')

after-trace-defined : ∀{T T' φ} -> T HasTrace φ -> Transitions T φ T' -> Defined T'
after-trace-defined (_ , def , refl) refl = def
after-trace-defined (_ , def , step inp tr) (step inp sr) = after-trace-defined (_ , def , tr) sr
after-trace-defined (_ , def , step (out _) tr) (step (out _) sr) = after-trace-defined (_ , def , tr) sr

after-trace-defined-2 : ∀{T φ} (tφ : T HasTrace φ) -> Defined (after tφ)
after-trace-defined-2 (_ , def , _) = def

⊑-after : ∀{φ ψ} -> φ ⊑ ψ -> Trace
⊑-after {_} {ψ} none = ψ
⊑-after (some le) = ⊑-after le

⊑-after-co-trace : ∀{φ ψ} (le : φ ⊑ ψ) -> ⊑-after (⊑-co-trace le) ≡ co-trace (⊑-after le)
⊑-after-co-trace none = refl
⊑-after-co-trace (some le) = ⊑-after-co-trace le

extend-transitions :
  ∀{T S φ ψ}
  (le : φ ⊑ ψ)
  (tr : Transitions T φ S)
  (tψ : T HasTrace ψ) ->
  Transitions S (⊑-after le) (after tψ)
extend-transitions none refl (_ , _ , sr) = sr
extend-transitions (some le) (step inp tr) (_ , sdef , step inp sr) = extend-transitions le tr (_ , sdef , sr)
extend-transitions (some le) (step (out _) tr) (_ , sdef , step (out _) sr) = extend-transitions le tr (_ , sdef , sr)

discriminator-compliant : ∀{T S} -> T <: S -> T ↑ S -> FairComplianceS (discriminator T S # T)
discriminator-compliant {T} {S} sub div {R' # T'} reds with unzip-red* reds
... | φ , rr , tr with sub+diverge->discriminator-defined sub div | sub+diverge->defined sub div
... | rdef | tdef , sdef with discriminator-after-sync->defined sub rdef rr tr
... | rdef' with decode-sub (co-semantics (disc-set->semantics T S)) (_ , rdef' , rr)
... | dsφ rewrite co-trace-involution φ =
  case completion sub dsφ of
  λ { (inj₁ (ψ , lt , cψ@(complete dsψ _))) ->
      let rψ = decode-sup (co-semantics (disc-set->semantics T S)) (co-definition {DiscSet T S} dsψ) in
      let tψ = disc-set-subset dsψ in
      let rr' = subst (λ z -> Transitions _ z _) (⊑-after-co-trace (⊏->⊑ lt)) (extend-transitions (⊑-co-trace (⊏->⊑ lt)) rr rψ) in
      let tr' = extend-transitions (⊏->⊑ lt) tr tψ in
      let winr = decode+complete->win (co-semantics (disc-set->semantics T S)) rψ (co-complete cψ) in
      let reds' = zip-red* rr' tr' in
      _ , reds' , win#def winr (after-trace-defined-2 tψ)
    ; (inj₂ (cφ , nsφ)) ->
      let winr = decode+complete->win (co-semantics (disc-set->semantics T S)) (_ , rdef' , rr) (co-complete cφ) in
      _ , ε , win#def winr (after-trace-defined (disc-set-subset dsφ) tr) }

discriminator-not-compliant : ∀{T S} -> T <: S -> T ↑ S -> ¬ FairComplianceS (discriminator T S # S)
discriminator-not-compliant {T} {S} sub div comp with comp ε
... | _ , reds , win#def w def with unzip-red* reds
... | φ , rr , sr with decode+win->complete (co-semantics (disc-set->semantics T S)) (_ , win->defined w , rr) w
... | cφ with co-complete-2 {DiscSet T S} cφ
... | csφ with disc-set-complete-2 sub csφ
... | nsφ = nsφ (_ , def , sr)
