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
open import Data.Unit
open import Data.Product
open import Data.Maybe
open import Data.Sum
open import Data.List using (_++_; []; _∷_; _∷ʳ_; length)
open import Data.List.Properties using (∷-injective)

open import Relation.Nullary
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Unary using (_∈_; _⊆_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong)

open import Function.Base using (case_of_)

open import Common

module Divergence {ℙ : Set} (message : Message ℙ)
  where

open import SessionType message
open import Session message
open import Trace message
open import HasTrace message
open import TraceSet message
open import Transitions message
open import Semantics message
open import Subtyping message

DivergeForward : SessionType -> SessionType -> Trace -> Set

record _↑_ (T : SessionType) (S : SessionType) : Set where
  coinductive
  field
    trace : Trace
    with-trace : T HasTrace trace
    without-trace : ¬ S HasTrace trace
    divergence : DivergeForward T S trace

DivergeForward T S φ =
  ∀{ψ x}
  (pre : ψ ⊑ φ)
  (tψx : T HasTrace (ψ ∷ʳ O x))
  (sψx : S HasTrace (ψ ∷ʳ O x)) -> after tψx ↑ after sψx

diverge-before-input : ∀{f g x} -> f x .force ↑ g x .force -> inp f ↑ inp g
_↑_.trace (diverge-before-input {_} {_} {x} div) = I x ∷ _↑_.trace div
_↑_.with-trace (diverge-before-input div) = inp-has-trace (_↑_.with-trace div)
_↑_.without-trace (diverge-before-input div) = inp-has-no-trace (_↑_.without-trace div)
_↑_.divergence (diverge-before-input div) none (_ , _ , step () _) _
_↑_.divergence (diverge-before-input div) (some le) (_ , tdef , step inp tr) (_ , sdef , step inp sr) =
  _↑_.divergence div le (_ , tdef , tr) (_ , sdef , sr)

DivergeBackward : ∀{T S φ} -> T HasTrace φ -> S HasTrace φ -> Set
DivergeBackward {_} {_} {φ} tφ sφ =
  ∀{ψ} (pre : ψ ⊑ φ) -> after (⊑-has-trace pre tφ) ↑ after (⊑-has-trace pre sφ)

⊑-diverge-backward :
  ∀{T S φ ψ}
  {tφ  : T HasTrace φ}
  {sφ  : S HasTrace φ}
  (pre : ψ ⊑ φ) ->
  DivergeBackward tφ sφ ->
  DivergeBackward (⊑-has-trace pre tφ) (⊑-has-trace pre sφ)
⊑-diverge-backward {_} {_} {_} {_} {tφ} {sφ} pre div pre'  rewrite ⊑-tran-has-trace pre' pre tφ | ⊑-tran-has-trace pre' pre sφ =
  div (⊑-tran pre' pre)

data DiscSet : SessionType -> SessionType -> Trace -> Set where
  inc : ∀{T S φ}
        (tφ : T HasTrace φ)
        (sφ : S HasTrace φ)
        (div←φ : DivergeBackward tφ sφ) -> DiscSet T S φ
  exc : ∀{T S φ ψ x}
        (eq : φ ≡ ψ ∷ʳ O x)
        (tψ : T HasTrace ψ)
        (sψ : S HasTrace ψ)
        (tφ : T HasTrace φ)
        (nsφ : ¬ S HasTrace φ)
        (div←ψ : DivergeBackward tψ sψ) -> DiscSet T S φ

⊑-proper : ∀{φ ψ α} -> φ ⊑ (ψ ∷ʳ α) -> φ ⊑ ψ ⊎ φ ≡ ψ ∷ʳ α
⊑-proper {[]} {[]} none = inj₁ none
⊑-proper {_ ∷ []} {[]} (some none) = inj₂ refl
⊑-proper {[]} {_ ∷ _} none = inj₁ none
⊑-proper {_} {_ ∷ _} (some pre) with ⊑-proper pre
... | inj₁ pre' = inj₁ (some pre')
... | inj₂ refl = inj₂ refl

disc-set->closed : (T S : SessionType) -> PrefixClosed (DiscSet T S)
disc-set->closed T S pre (inc tφ sφ div←φ) =
  inc (⊑-has-trace pre tφ) (⊑-has-trace pre sφ) (⊑-diverge-backward pre div←φ)
disc-set->closed T S pre (exc refl tψ sψ tφ nsφ div←ψ) with ⊑-proper pre
... | inj₁ pre' = inc (⊑-has-trace pre' tψ) (⊑-has-trace pre' sψ) (⊑-diverge-backward pre' div←ψ)
... | inj₂ refl = exc refl tψ sψ tφ nsφ div←ψ

input-lemma : ∀{φ x ψ χ y} -> φ ++ I x ∷ ψ ≡ χ ∷ʳ O y -> (φ ∷ʳ I x) ⊑ χ
input-lemma {[]} {_} {_} {I x ∷ χ} refl = some none
input-lemma {x ∷ φ} {_} {_} {[]} eq with ∷-injective eq
... | (_ , eq') = ⊥-elim (absurd-++-≡ eq')
input-lemma {x ∷ φ} {_} {_} {y ∷ χ} eq with ∷-injective eq
... | (refl , eq'') = some (input-lemma eq'')

disc-set-input : ∀{φ x ψ} {T S : SessionType} -> DiscSet T S (φ ++ I x ∷ ψ) ->
  T HasTrace (φ ∷ʳ I x) × S HasTrace (φ ∷ʳ I x)
disc-set-input {φ} {x} {ψ} (inc tφ sφ div←φ) with ⊑-precong-++ {φ} {I x ∷ []} {I x ∷ ψ} (some none)
... | pre = ⊑-has-trace pre tφ , ⊑-has-trace pre sφ
disc-set-input (exc eq tχ sχ _ _ _) with input-lemma eq
... | pre = ⊑-has-trace pre tχ , ⊑-has-trace pre sχ

disc-set-output : ∀{φ x ψ} {T S : SessionType} -> DiscSet T S (φ ++ O x ∷ ψ) -> T HasTrace (φ ∷ʳ O x)
disc-set-output {φ} {x} {ψ} (inc tφx sφx _) =
  let pre = ⊑-precong-++ {φ} {O x ∷ []} {O x ∷ ψ} (some none) in
  ⊑-has-trace pre tφx
disc-set-output {φ} {x} {ψ} (exc _ _ _ tφx _ _) =
  let pre = ⊑-precong-++ {φ} {O x ∷ []} {O x ∷ ψ} (some none) in
  ⊑-has-trace pre tφx

disc-set->coherent : (T S : SessionType) -> Coherent (DiscSet T S)
disc-set->coherent T S ti to =
  let (ti[] , _) = disc-set-input ti in
  let to[] = disc-set-output to in
  ⊥-elim (coherent (sem-sound T) ti[] to[])

disc-set->semantics : (T S : SessionType) -> Semantics (DiscSet T S)
closed (disc-set->semantics T S) = disc-set->closed T S
coherent (disc-set->semantics T S) = disc-set->coherent T S

disc-set-subset : ∀{T S} -> DiscSet T S ⊆ ⟦ T ⟧
disc-set-subset (inc tφ _ _) = tφ
disc-set-subset (exc _ _ _ tφ _ _) = tφ

disc-set-disjoint :
  ∀{T S φ} ->
  φ ∈ DiscSet T S ->
  ¬ S HasTrace φ ->
  ∃[ ψ ] ∃[ x ] (φ ≡ ψ ∷ʳ O x × S HasTrace ψ)
disc-set-disjoint (inc _ sφ _) nsφ = ⊥-elim (nsφ sφ)
disc-set-disjoint (exc eq _ sψ _ _ _) nsφ = _ , _ , eq , sψ

-- --| BEGIN MAXIMAL TRACES |--

diverge-forward-input :
  ∀{f g x φ} -> DivergeForward (inp f) (inp g) (I x ∷ φ)
             -> DivergeForward (f x .force) (g x .force) φ
diverge-forward-input div pre (_ , tdef , tr) (_ , sdef , sr) = div (some pre) (_ , tdef , step inp tr) (_ , sdef , step inp sr)

diverge-forward-input' :
  ∀{f g x φ} -> DivergeForward (f x .force) (g x .force) φ
             -> DivergeForward (inp f) (inp g) (I x ∷ φ)
diverge-forward-input' div none (_ , _ , step () _) (_ , _ , _)
diverge-forward-input' div (some le) (_ , tdef , step inp tr) (_ , sdef , step inp sr) = div le (_ , tdef , tr) (_ , sdef , sr)

diverge-forward-output :
  ∀{f g x φ} -> DivergeForward (out f) (out g) (O x ∷ φ)
             -> DivergeForward (f x .force) (g x .force) φ
diverge-forward-output div pre (_ , tdef , tr) (_ , sdef , sr) =
  div (some pre)
      (_ , tdef , step (out (transitions+defined->defined tr tdef)) tr)
      (_ , sdef , step (out (transitions+defined->defined sr sdef)) sr)

-- the next lemma says that if T ↑ S and φ is the trace that
-- discriminates between them, then we have divergence along any
-- common prefix of φ shared by both T and S

diverge-forward->backward :
  ∀{T S φ ψ}
  (tφ  : T HasTrace φ)
  (nsφ : ¬ S HasTrace φ)
  (div : DivergeForward T S φ)
  (pre : ψ ⊑ φ)
  (tψ  : T HasTrace ψ)
  (sψ  : S HasTrace ψ) ->
  DivergeBackward tψ sψ
_↑_.trace (diverge-forward->backward tφ nsφ div pre tψ sψ none) = _
_↑_.with-trace (diverge-forward->backward tφ nsφ div pre tψ sψ none) = tφ
_↑_.without-trace (diverge-forward->backward tφ nsφ div pre tψ sψ none) = nsφ
_↑_.divergence (diverge-forward->backward tφ nsφ div pre tψ sψ none) = div
diverge-forward->backward (_ , tdef , step inp tr) nsφ div (some pre) (_ , tdef' , step (inp {f}) tr') (_ , sdef , step (inp {g}) sr) (some pre') =
  diverge-forward->backward (_ , tdef , tr) (contraposition inp-has-trace nsφ) (diverge-forward-input {f} {g} div) pre (_ , tdef' , tr') (_ , sdef , sr) pre'
diverge-forward->backward (_ , tdef , step (out _) tr) nsφ div (some pre) (_ , tdef' , step (out {f} _) tr') (_ , sdef , step (out {g} _) sr) (some pre') =
  diverge-forward->backward (_ , tdef , tr) (contraposition out-has-trace nsφ) (diverge-forward-output {f} {g} div) pre (_ , tdef' , tr') (_ , sdef , sr) pre'

prefix-last-element : ∀{φ φ' ψ ψ' x y} -> φ ⊑ ψ -> φ ≡ φ' ++ O x ∷ [] -> ψ ≡ ψ' ∷ʳ O y -> ψ ≡ φ ⊎ φ ⊑ ψ'
prefix-last-element none e1 e2 = inj₂ none
prefix-last-element {φ' = []} {ψ' = []} (some pre) e1 e2 with ∷-injective e1 | ∷-injective e2
... | (_ , e1') | (_ , e2') rewrite e1' | e2' = inj₁ refl
prefix-last-element {φ' = []} {ψ' = x ∷ ψ'} (some _) e1 e2 with ∷-injective e1 | ∷-injective e2
... | (eq1 , e1') | (eq2 , e2') rewrite eq1 | eq2 | e1' | e2' = inj₂ (some none)
prefix-last-element {φ' = x ∷ φ'} {ψ' = []} (some pre) e1 e2 with ∷-injective e1 | ∷-injective e2
... | (eq1 , e1') | (eq2 , e2') rewrite e1' | e2' = ⊥-elim (absurd-++-⊑ pre)
prefix-last-element {φ' = x ∷ φ'} {ψ' = x₁ ∷ ψ'} (some pre) e1 e2 with ∷-injective e1 | ∷-injective e2
... | (eq1 , e1') | (eq2 , e2') rewrite eq1 | eq2 with prefix-last-element pre e1' e2'
... | inj₁ eq rewrite eq = inj₁ refl
... | inj₂ pre' = inj₂ (some pre')

disc-set-maximal-1 :
  ∀{T S φ} ->
  φ ∈ DiscSet T S ->
  ¬ S HasTrace φ ->
  φ ∈ Maximal (DiscSet T S)
disc-set-maximal-1 dsφ nsφ with disc-set-disjoint dsφ nsφ
... | _ , _ , refl , sψ =
  maximal dsφ λ le ds' ->
  let _ , _ , eq , sψ' = disc-set-disjoint ds' (contraposition (⊑-has-trace le) nsφ) in
  case prefix-last-element le refl eq of λ
  { (inj₁ refl) → refl
  ; (inj₂ le') → ⊥-elim (contraposition (⊑-has-trace le') nsφ sψ') }

has-trace-after : ∀{T φ ψ} (tφ : T HasTrace φ) -> after tφ HasTrace ψ -> T HasTrace (φ ++ ψ)
has-trace-after (_ , _ , refl) tφψ = tφψ
has-trace-after (_ , tdef , step inp tr) tφψ = inp-has-trace (has-trace-after (_ , tdef , tr) tφψ)
has-trace-after (_ , tdef , step (out _) tr) tφψ = out-has-trace (has-trace-after (_ , tdef , tr) tφψ)

has-no-trace-after : ∀{T φ ψ} (tφ : T HasTrace φ) -> ¬ after tφ HasTrace ψ -> ¬ T HasTrace (φ ++ ψ)
has-no-trace-after (_ , _ , refl) tφ/nψ = tφ/nψ
has-no-trace-after (_ , tdef , step inp tr) tφ/nψ = inp-has-no-trace (has-no-trace-after (_ , tdef , tr) tφ/nψ)
has-no-trace-after (_ , tdef , step (out _) tr) tφ/nψ = out-has-no-trace (has-no-trace-after (_ , tdef , tr) tφ/nψ)

append-diverge-backward :
  ∀{T S φ ψ}
  (tφ : T HasTrace φ)
  (sφ : S HasTrace φ)
  (tφ/ψ : after tφ HasTrace ψ)
  (sφ/ψ : after sφ HasTrace ψ)
  (div←φ : DivergeBackward tφ sφ)
  (divφ←ψ : DivergeBackward tφ/ψ sφ/ψ) ->
  DivergeBackward (has-trace-after tφ tφ/ψ) (has-trace-after sφ sφ/ψ)
append-diverge-backward (_ , tdef , refl) (_ , sdef , refl) tφ/ψ sφ/ψ div←φ divφ←ψ pre = divφ←ψ pre
append-diverge-backward (_ , tdef , step t tr) (_ , sdef , step s sr) tφ/ψ sφ/ψ div←φ divφ←ψ none = div←φ none
append-diverge-backward (_ , tdef , step inp tr) (_ , sdef , step inp sr) tφ/ψ sφ/ψ div←φ divφ←ψ (some pre) =
  append-diverge-backward (_ , tdef , tr) (_ , sdef , sr) tφ/ψ sφ/ψ (λ pre -> div←φ (some pre)) divφ←ψ pre
append-diverge-backward (_ , tdef , step (out _) tr) (_ , sdef , step (out _) sr) tφ/ψ sφ/ψ div←φ divφ←ψ (some pre) =
  append-diverge-backward (_ , tdef , tr) (_ , sdef , sr) tφ/ψ sφ/ψ (λ pre -> div←φ (some pre)) divφ←ψ pre

append-snoc : ∀{φ ψ : Trace}{α : Action} -> φ ++ (ψ ∷ʳ α) ≡ (φ ++ ψ) ∷ʳ α
append-snoc {[]} = refl
append-snoc {β ∷ φ} = cong (β ∷_) (append-snoc {φ})

completion :
  ∀{φ T S} ->
  T <: S ->
  φ ∈ DiscSet T S ->
  (∃[ ψ ] (φ ⊏ ψ × ψ ∈ Maximal (DiscSet T S))) ⊎ (φ ∈ Maximal (DiscSet T S) × ¬ S HasTrace φ)
completion {φ} sub (inc tφ sφ div←φ) with div←φ (⊑-refl _)
... | div rewrite ⊑-has-trace-after tφ | ⊑-has-trace-after sφ =
  let χ = _↑_.trace div in
  let tφ/χ = _↑_.with-trace div in
  let sφ/nχ = _↑_.without-trace div in
  let divφ→χ = _↑_.divergence div in
  let subφ = sub-after tφ sφ sub in
  let ψ , x , ψ⊑χ , tφ/ψ , sφ/ψ , tφ/ψx , sφ/nψx = sub-excluded subφ tφ/χ sφ/nχ in
  let tφψ = has-trace-after tφ tφ/ψ in
  let sφψ = has-trace-after sφ sφ/ψ in
  let tφψx = has-trace-after tφ tφ/ψx in
  let sφnψx = has-no-trace-after sφ sφ/nψx in
  let divφ←ψ = diverge-forward->backward tφ/χ sφ/nχ divφ→χ ψ⊑χ tφ/ψ sφ/ψ in
  let div←ψ  = append-diverge-backward tφ sφ tφ/ψ sφ/ψ div←φ divφ←ψ in
  let ds = exc {_} {_} {φ ++ (ψ ∷ʳ O x)} {φ ++ ψ} {x} (append-snoc {φ} {ψ} {O x}) tφψ sφψ tφψx sφnψx div←ψ in
  inj₁ (φ ++ (ψ ∷ʳ O x) , ⊏-++ , disc-set-maximal-1 ds sφnψx)
completion sub ds@(exc _ _ _ _ nsφ _) =
  inj₂ (disc-set-maximal-1 ds nsφ , nsφ)

disc-set-maximal-2 :
  ∀{T S φ} ->
  T <: S ->
  φ ∈ Maximal (DiscSet T S) ->
  ¬ S HasTrace φ
disc-set-maximal-2 sub (maximal dφ F) sφ with completion sub dφ
... | inj₁ (ψ , φ⊏ψ , maximal dψ _) = ⊏->≢ φ⊏ψ (sym (F (⊏->⊑ φ⊏ψ) dψ))
... | inj₂ (_ , nsφ) = nsφ sφ

--| END MAXIMAL TRACES |--

-- Sia R il session type determinato da disc-set T S quando T ↑
-- S. L'obiettivo è dimostrare che R |- T e ¬ R |- S
--
-- R |- T
--
-- Ogni riduzione di (R # T) può essere completata a (R' # T') in
-- cui Win R' e Defined T'
--
-- Siccome le tracce di R sono incluse in quelle di T, basta
-- dimostrare che ogni traccia di R può essere completata, cioè che
-- ogni traccia di disc-set T S è prefisso di una traccia completa
-- di disc-set T S.
--
-- ∀ φ ∈ R => ∃ ψ : φ ++ ψ ∈ Maximal R
--
-- ¬ R |- S
--
-- Dimostrare che ogni traccia completa di R non è una traccia di S.
--
-- Maximal R ∩ ⟦ S ⟧ ≡ ∅
