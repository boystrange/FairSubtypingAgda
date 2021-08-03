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

{-# OPTIONS --guardedness #-}

open import Data.Empty
open import Data.Product
open import Data.List using ([]; _∷_; _∷ʳ_; _++_)

open import Relation.Nullary
open import Relation.Unary using (_∈_; _⊆_;_∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.HeterogeneousEquality as Het

open import Common

module HasTrace {ℙ : Set} (message : Message ℙ)
  where

open import Trace message
open import SessionType message
open import Transitions message

_HasTrace_ : SessionType -> Trace -> Set
_HasTrace_ T φ = ∃[ S ] (Defined S × Transitions T φ S)

after : ∀{T φ} -> T HasTrace φ -> SessionType
after (S , _ , _) = S

-- data _HasTrace_ : SessionType -> Trace -> Set where
--   does : ∀{T φ S} (tr : Transitions T φ S) (def : Defined S) -> T Does φ

_HasTrace?_ : (T : SessionType) (φ : Trace) -> Dec (T HasTrace φ)
nil HasTrace? _ = no λ { (_ , () , refl)
                       ; (_ , _ , step () _) }
inp f HasTrace? [] = yes (_ , inp , refl)
inp f HasTrace? (I x ∷ φ) with x ∈? f
... | no nfx = no λ { (_ , def , step inp tr) → nfx (transitions+defined->defined tr def) }
... | yes fx with f x .force HasTrace? φ
... | yes (_ , def , tr) = yes (_ , def , step inp tr)
... | no ntφ = no λ { (_ , def , step inp tr) → ntφ (_ , def , tr) }
inp f HasTrace? (O x ∷ φ) = no λ { (_ , _ , step () _) }
out f HasTrace? [] = yes (_ , out , refl)
out f HasTrace? (I x ∷ φ) = no λ { (_ , _ , step () _) }
out f HasTrace? (O x ∷ φ) with x ∈? f
... | no nfx = no λ { (_ , _ , step (out fx) _) → nfx fx }
... | yes fx with f x .force HasTrace? φ
... | yes (_ , def , tr) = yes (_ , def , step (out fx) tr)
... | no ntφ = no λ { (_ , def , step (out fx) tr) → ntφ (_ , def , tr) }

has-trace->defined : ∀{T φ} -> T HasTrace φ -> Defined T
has-trace->defined (_ , tdef , tr) = transitions+defined->defined tr tdef

inp-has-trace : ∀{f x φ} -> f x .force HasTrace φ -> inp f HasTrace (I x ∷ φ)
inp-has-trace (_ , def , tr) = _ , def , step inp tr

inp-has-no-trace : ∀{f x φ} -> ¬ f x .force HasTrace φ -> ¬ inp f HasTrace (I x ∷ φ)
inp-has-no-trace nφ (_ , def , step inp tr) = nφ (_ , def , tr)

out-has-trace : ∀{f x φ} -> f x .force HasTrace φ -> out f HasTrace (O x ∷ φ)
out-has-trace (_ , def , tr) = _ , def , step (out (transitions+defined->defined tr def)) tr

out-has-no-trace : ∀{f x φ} -> ¬ f x .force HasTrace φ -> ¬ out f HasTrace (O x ∷ φ)
out-has-no-trace nφ (_ , def , step (out fx) tr) = nφ (_ , def , tr)

out-has-no-trace->undefined : ∀{f x} -> ¬ out f HasTrace (O x ∷ []) -> ¬ Defined (f x .force)
out-has-no-trace->undefined {f} {x} nt with x ∈? f
... | yes fx = ⊥-elim (nt (_ , fx , step (out fx) refl))
... | no nfx = nfx

unprefix-some : ∀{α φ ψ} -> (α ∷ ψ) ⊑ (α ∷ φ) -> ψ ⊑ φ
unprefix-some (some pre) = pre

⊑-has-trace : ∀{T φ ψ} -> ψ ⊑ φ -> T HasTrace φ -> T HasTrace ψ
⊑-has-trace none (_ , tdef , tr) = _ , transitions+defined->defined tr tdef , refl
⊑-has-trace (some pre) (_ , tdef , step t tr) =
  let _ , sdef , sr = ⊑-has-trace pre (_ , tdef , tr) in
  _ , sdef , step t sr

split-trace : ∀{T φ ψ} (tφ : T HasTrace φ) -> T HasTrace (φ ++ ψ) -> after tφ HasTrace ψ
split-trace (_ , tdef , refl) tφψ = tφψ
split-trace (_ , tdef , step inp tr) (_ , sdef , step inp sr) = split-trace (_ , tdef , tr) (_ , sdef , sr)
split-trace (_ , tdef , step (out _) tr) (_ , sdef , step (out _) sr) = split-trace (_ , tdef , tr) (_ , sdef , sr)

join-trace : ∀{T φ ψ} (tφ : T HasTrace φ) -> after tφ HasTrace ψ -> T HasTrace (φ ++ ψ)
join-trace (_ , _ , refl) tφ/ψ = tφ/ψ
join-trace (_ , tdef , step t tr) tφ/ψ =
  let (_ , sdef , sr) = join-trace (_ , tdef , tr) tφ/ψ in
  _ , sdef , step t sr

⊑-has-co-trace : ∀{T φ ψ} -> φ ⊑ ψ -> T HasTrace (co-trace ψ) -> T HasTrace (co-trace φ)
⊑-has-co-trace le tψ = ⊑-has-trace (⊑-co-trace le) tψ

⊑-tran-has-trace : ∀{T φ ψ χ} (pre1 : φ ⊑ ψ) (pre2 : ψ ⊑ χ) ->
  (tχ : T HasTrace χ) ->
  ⊑-has-trace pre1 (⊑-has-trace pre2 tχ) ≡ ⊑-has-trace (⊑-tran pre1 pre2) tχ
⊑-tran-has-trace none none tχ = refl
⊑-tran-has-trace none (some pre2) (fst , fst₁ , step t snd) = refl
⊑-tran-has-trace (some pre1) (some pre2) (_ , def , step _ tr) rewrite ⊑-tran-has-trace pre1 pre2 (_ , def , tr) = refl

⊑-has-trace-after : ∀{T φ} (tφ : T HasTrace φ) -> ⊑-has-trace (⊑-refl φ) tφ ≡ tφ
⊑-has-trace-after (_ , _ , refl) = refl
⊑-has-trace-after (_ , tdef , step inp tr) rewrite ⊑-has-trace-after (_ , tdef , tr) = refl
⊑-has-trace-after (_ , tdef , step (out _) tr) rewrite ⊑-has-trace-after (_ , tdef , tr) = refl

nil-has-no-trace : ∀{φ} -> ¬ nil HasTrace φ
nil-has-no-trace (_ , () , refl)
nil-has-no-trace (_ , _ , step () _)

end-has-empty-trace : ∀{φ T} -> End T -> T HasTrace φ -> φ ≡ []
end-has-empty-trace (inp U) (_ , _ , refl) = refl
end-has-empty-trace (inp U) (_ , def , step inp refl) = ⊥-elim (U _ def)
end-has-empty-trace (inp U) (_ , def , step inp (step t _)) = ⊥-elim (U _ (transition->defined t))
end-has-empty-trace (out U) (_ , _ , refl) = refl
end-has-empty-trace (out U) (_ , _ , step (out !x) _) = ⊥-elim (U _ !x)

has-trace-++ : ∀{T φ ψ} -> T HasTrace (φ ++ ψ) -> T HasTrace φ
has-trace-++ tφψ = ⊑-has-trace ⊑-++ tφψ

trace-coherence : ∀{T φ ψ₁ ψ₂ x y} -> T HasTrace (φ ++ I x ∷ ψ₁) -> T HasTrace (φ ++ O y ∷ ψ₂) -> ⊥
trace-coherence {_} {[]} (_ , _ , step inp _) (_ , _ , step () _)
trace-coherence {_} {I _ ∷ _} (_ , tdef , step inp tr) (_ , sdef , step inp sr) = trace-coherence (_ , tdef , tr) (_ , sdef , sr)
trace-coherence {_} {O _ ∷ _} (_ , tdef , step (out _) tr) (_ , sdef , step (out _) sr) = trace-coherence (_ , tdef , tr) (_ , sdef , sr)

defined->has-empty-trace : ∀{T} -> Defined T -> T HasTrace []
defined->has-empty-trace inp = _ , inp , refl
defined->has-empty-trace out = _ , out , refl

has-trace-double-negation : ∀{T φ} -> ¬ ¬ T HasTrace φ -> T HasTrace φ
has-trace-double-negation {T} {φ} p with T HasTrace? φ
... | yes tφ = tφ
... | no ntφ = ⊥-elim (p ntφ)

{- New -}
not-nil-has-trace : ∀{ϕ} → ¬ (nil HasTrace ϕ)
not-nil-has-trace (.(inp _) , inp , step () _)
not-nil-has-trace (.(out _) , out , step () _)

trace-after-in : ∀{f x ϕ} → (inp f) HasTrace (I x ∷ ϕ) → (f x .force) HasTrace ϕ
trace-after-in (_ , def , step inp red) = _ , def , red

trace-after-out : ∀{f x ϕ} → (out f) HasTrace (O x ∷ ϕ) → (f x .force) HasTrace ϕ
trace-after-out (_ , def , step (out _) red) = _ , def , red

inp-hastrace->defined : ∀{f x tr} → (inp f) HasTrace (I x ∷ tr) → x ∈ dom f
inp-hastrace->defined (_ , def , step inp refl) = def
inp-hastrace->defined (_ , def , step inp (step red _)) = transition->defined red

empty-inp-has-empty-trace : ∀{f ϕ} → EmptyContinuation f → (inp f) HasTrace ϕ → ϕ ≡ []
empty-inp-has-empty-trace e (_ , _ , refl) = refl
empty-inp-has-empty-trace {f} e (_ , _ , step (inp {x = x}) reds) with Defined? (f x .force)
empty-inp-has-empty-trace {f} e (_ , def , step (inp {x = _}) refl) | no ¬def = ⊥-elim (¬def def)
empty-inp-has-empty-trace {f} e (_ , _ , step (inp {x = _}) (step t _)) | no ¬def = ⊥-elim (¬def (transition->defined t))
... | yes def = ⊥-elim (e _ def)

empty-out-has-empty-trace : ∀{f ϕ} → EmptyContinuation f → (out f) HasTrace ϕ → ϕ ≡ []
empty-out-has-empty-trace e (_ , _ , refl) = refl
empty-out-has-empty-trace e (_ , _ , step (out def) _) = ⊥-elim (e _ def)