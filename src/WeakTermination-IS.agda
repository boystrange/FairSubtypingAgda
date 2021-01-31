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

open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤)
open import Data.Bool renaming (Bool to 𝔹)
open import Data.Product
open import Data.Sum
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (∷-injectiveʳ)
import Data.Fin as Fin

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (_∈_; _∉_; _⊆_; Satisfiable)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import is-lib.InfSys

module WeakTermination-IS where

open import Common

message : Message 𝔹
message = record{_?=_ = Data.Bool._≟_}

open import SessionType message
open import Trace message
open import Transitions message
open import HasTrace message
open import TraceSet message

U : Set
U = SessionType

data RuleNames : Set where
  nil inp out : RuleNames

data CoRuleNames : Set where
  inp out : CoRuleNames

nil-r : MetaRule U
nil-r .C = ⊤
nil-r .comp _ =
  [] ,
  ----
  nil , ⊤

inp-r : MetaRule U
inp-r .C = Continuation
inp-r .comp f =
  f true .force ∷ f false .force ∷ [] ,
  ------------------------------------
  inp f , ⊤

out-r : MetaRule U
out-r .C = Continuation
out-r .comp f =
  f true .force ∷ f false .force ∷ [] ,
  ------------------------------------
  out f , ⊤

inp-co-r : MetaRule U
inp-co-r .C = Continuation × 𝔹
inp-co-r .comp (f , x) =
  f x .force ∷ [] ,
  --------------------
  inp f , (x ∈ dom f)

out-co-r : MetaRule U
out-co-r .C = Continuation × 𝔹
out-co-r .comp (f , x) =
  f x .force ∷ [] ,
  --------------------
  out f , (x ∈ dom f)

WeakTerminationS : SessionType -> Set
WeakTerminationS T = ∀{φ} -> φ ∈ ⟦ T ⟧ -> ∃[ ψ ] (φ ++ ψ ∈ Maximal ⟦ T ⟧)

WeakTerminationIS : IS U
Names WeakTerminationIS = RuleNames
rules WeakTerminationIS nil    = nil-r
rules WeakTerminationIS inp    = inp-r
rules WeakTerminationIS out    = out-r

WeakTerminationCOIS : IS U
WeakTerminationCOIS .Names = CoRuleNames
WeakTerminationCOIS .rules inp = inp-co-r
WeakTerminationCOIS .rules out = out-co-r

WeakTermination : SessionType -> Set
WeakTermination = FCoInd⟦ WeakTerminationIS , WeakTerminationCOIS ⟧

WeakTerminationI : SessionType -> Set
WeakTerminationI = Ind⟦ WeakTerminationIS ∪ WeakTerminationCOIS ⟧

lemma-inp : ∀{f φ x} -> φ ∈ Maximal ⟦ f x .force ⟧ -> I x ∷ φ ∈ Maximal ⟦ inp f ⟧
lemma-inp (maximal wit F) =
  maximal (inp-has-trace wit) λ { (some le) (_ , def , step inp tr) → cong (_ ∷_) (F le (_ , def , tr)) }

lemma-out : ∀{f φ x} -> φ ∈ Maximal ⟦ f x .force ⟧ -> O x ∷ φ ∈ Maximal ⟦ out f ⟧
lemma-out (maximal wit F) =
  maximal (out-has-trace wit) λ { (some le) (_ , def , step (out _) tr) → cong (_ ∷_) (F le (_ , def , tr)) }

lemma-end : ∀{f} -> true ∉ dom f -> false ∉ dom f -> [] ∈ Maximal ⟦ inp f ⟧
lemma-end nft nff = maximal (_ , inp , refl)
  λ { {[]} none _ → refl
    ; {O _ ∷ _} none (_ , _ , step () _)
    ; {I false ∷ ψ} none (_ , def , step inp tr) → ⊥-elim (nff (transitions+defined->defined tr def))
    ; {I true ∷ ψ} none (_ , def , step inp tr) → ⊥-elim (nft (transitions+defined->defined tr def)) }

lemma-win : ∀{f} -> true ∉ dom f -> false ∉ dom f -> [] ∈ Maximal ⟦ out f ⟧
lemma-win nft nff = maximal (_ , out , refl)
  λ { {[]} none _ → refl
    ; {I _ ∷ _} none (_ , _ , step () _)
    ; {O false ∷ ψ} none (_ , def , step (out ff) _) → ⊥-elim (nff ff)
    ; {O true ∷ ψ} none (_ , def , step (out ft) _) → ⊥-elim (nft ft) }

may-terminate : ∀{T} -> Defined T -> WeakTerminationI T -> Satisfiable (Maximal ⟦ T ⟧)
may-terminate () (fold (inj₁ nil , _ , refl , _ , _))
may-terminate _ (fold (inj₁ inp , f , refl , _ , premise)) with true ∈? f | false ∈? f
... | yes ft | yes ff = let _ , cψ = may-terminate ft (premise Fin.zero) in _ , lemma-inp cψ
... | yes ft | no nff = let _ , cψ = may-terminate ft (premise Fin.zero) in _ , lemma-inp cψ
... | no nft | yes ff = let _ , cψ = may-terminate ff (premise (Fin.suc Fin.zero)) in _ , lemma-inp cψ
... | no nft | no nff = _ , lemma-end nft nff
may-terminate _ (fold (inj₁ out , f , refl , _ , premise)) with true ∈? f | false ∈? f
... | yes ft | yes ff = let _ , cψ = may-terminate ft (premise Fin.zero) in _ , lemma-out cψ
... | yes ft | no nff = let _ , cψ = may-terminate ft (premise Fin.zero) in _ , lemma-out cψ
... | no nft | yes ff = let _ , cψ = may-terminate ff (premise (Fin.suc Fin.zero)) in _ , lemma-out cψ
... | no nft | no nff = _ , lemma-win nft nff
may-terminate _ (fold (inj₂ inp , C , refl , fx , premise)) with may-terminate fx (premise Fin.zero)
... | _ , cψ = _ , lemma-inp cψ
may-terminate _ (fold (inj₂ out , (_ , x) , refl , fx , premise)) with may-terminate fx (premise Fin.zero)
... | _ , cψ = _ , lemma-out cψ

wt-sound : WeakTermination ⊆ WeakTerminationS
wt-sound wt (_ , def , refl) = may-terminate def (fcoind-to-ind wt)
wt-sound wt (_ , def , step t tr) with wt .CoInd⟦_⟧.unfold
wt-sound wt (_ , def , step (inp {_} {false}) tr) | inp , C , refl , sc , premise =
  let _ , cψ = wt-sound (premise (Fin.suc Fin.zero)) (_ , def , tr) in
  _ , lemma-inp cψ
wt-sound wt (_ , def , step (inp {_} {true}) tr) | inp , C , refl , sc , premise =
  let _ , cψ = wt-sound (premise Fin.zero) (_ , def , tr) in
  _ , lemma-inp cψ
wt-sound wt (_ , def , step (out {_} {false} fx) tr) | out , C , refl , sc , premise =
  let _ , cψ = wt-sound (premise (Fin.suc Fin.zero)) (_ , def , tr) in
  _ , lemma-out cψ
wt-sound wt (_ , def , step (out {_} {true} fx) tr) | out , C , refl , sc , premise =
  let _ , cψ = wt-sound (premise Fin.zero) (_ , def , tr) in
  _ , lemma-out cψ

lemma-input-maximal : ∀{f x} -> WeakTerminationS (inp f) -> WeakTerminationS (f x .force)
lemma-input-maximal {f} {x} spec tφ with x ∈? f
... | no nfx = ⊥-elim (nfx (has-trace->defined tφ))
... | yes fx with spec (inp-has-trace tφ)
... | _ , cψ = _ , input-maximal cψ

lemma-output-maximal : ∀{f x} -> WeakTerminationS (out f) -> WeakTerminationS (f x .force)
lemma-output-maximal {f} {x} spec tφ with x ∈? f
... | no nfx = ⊥-elim (nfx (has-trace->defined tφ))
... | yes fx with spec (out-has-trace tφ)
... | _ , cψ = _ , output-maximal cψ

wt-consistent : WeakTerminationS ⊆ ISF[ WeakTerminationIS ] WeakTerminationS
wt-consistent {nil} spec = nil , _ , refl , _ , λ ()
wt-consistent {inp f} spec =
  inp , f , refl , _ , λ { Fin.zero           → lemma-input-maximal spec
                         ; (Fin.suc Fin.zero) → lemma-input-maximal spec }
wt-consistent {out f} spec =
  out , f , refl , _ , λ { Fin.zero           → lemma-output-maximal spec
                         ; (Fin.suc Fin.zero) → lemma-output-maximal spec}

undefined->terminates : ∀{T} -> ¬ Defined T -> WeakTerminationI T
undefined->terminates {nil}   _   = apply-ind (inj₁ nil) _ λ ()
undefined->terminates {inp f} und = ⊥-elim (und inp)
undefined->terminates {out f} und = ⊥-elim (und out)

input-maximal->terminates : ∀{f x} -> [] ∈ Maximal ⟦ inp f ⟧ -> WeakTerminationI (f x .force)
input-maximal->terminates {f} {x} (maximal (_ , inp , refl) F) with x ∈? f
... | no nfx = undefined->terminates nfx
... | yes fx with F none (_ , fx , step inp refl)
... | ()

output-maximal->terminates : ∀{f x} -> [] ∈ Maximal ⟦ out f ⟧ -> WeakTerminationI (f x .force)
output-maximal->terminates {f} {x} (maximal (_ , out , refl) F) with x ∈? f
... | no nfx = undefined->terminates nfx
... | yes fx with F none (_ , fx , step (out fx) refl)
... | ()

bounded-lemma : ∀{T φ} -> φ ∈ Maximal ⟦ T ⟧ -> WeakTerminationI T
bounded-lemma {nil} (maximal (_ , () , refl) _)
bounded-lemma {inp f} c[]@(maximal (_ , def , refl) F) =
  apply-ind (inj₁ inp) _ λ{Fin.zero → input-maximal->terminates c[] ; (Fin.suc Fin.zero) → input-maximal->terminates c[]}
bounded-lemma {out f} c[]@(maximal (_ , def , refl) F) =
  apply-ind (inj₁ out) _ λ{Fin.zero → output-maximal->terminates c[] ; (Fin.suc Fin.zero) → output-maximal->terminates c[]}
bounded-lemma {nil} (maximal (_ , _ , step () _) _)
bounded-lemma {inp f} cφ@(maximal (_ , def , step inp tr) F) =
  apply-ind (inj₂ inp) (transitions+defined->defined tr def) λ{Fin.zero → bounded-lemma (input-maximal cφ)}
bounded-lemma {out f} cφ@(maximal (_ , def , step (out fx) tr) F) =
  apply-ind (inj₂ out) fx λ{Fin.zero → bounded-lemma (output-maximal cφ)}

wt-bounded : WeakTerminationS ⊆ WeakTerminationI
wt-bounded {nil} spec = fold (inj₁ nil , _ , refl , _ , λ ())
wt-bounded {inp f} spec with spec (_ , inp , refl)
... | _ , cψ = bounded-lemma cψ
wt-bounded {out f} spec with spec (_ , out , refl)
... | _ , cψ = bounded-lemma cψ

wt-maximal : WeakTerminationS ⊆ WeakTermination
wt-maximal =
  bounded-coind[ WeakTerminationIS , WeakTerminationCOIS ] WeakTerminationS wt-bounded wt-consistent
