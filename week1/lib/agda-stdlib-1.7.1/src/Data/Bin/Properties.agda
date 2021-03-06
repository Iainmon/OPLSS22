------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use `Data.Nat.Binary` instead.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bin.Properties where

{-# WARNING_ON_IMPORT
"Data.Bin.Properties was deprecated in v1.2.
Use Data.Nat.Binary.Properties instead."
#-}

open import Data.Bin
open import Data.Digit using (Bit; Expansion)
import Data.Fin.Base as Fin
import Data.Fin.Properties as π½β
open import Data.List.Base using (List; []; _β·_)
open import Data.List.Properties using (β·-injective)
open import Data.Nat.Base
  using (β; zero; zβ€n; sβ€s)
  renaming (suc to 1+_; _+_ to _+β_; _*_ to _*β_; _β€_ to _β€β_)
import Data.Nat.Properties as ββ
open import Data.Product using (projβ; projβ; uncurry)
open import Function.Base using (_β_)
open import Relation.Binary
open import Relation.Binary.Consequences
open import Relation.Binary.PropositionalEquality
  using (_β‘_; _β’_; refl; sym; isEquivalence; respβ; decSetoid; cong; congβ)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (mapβ²)
open import Relation.Nullary.Product using (_Γ-dec_)

------------------------------------------------------------------------
-- (Bin, _β‘_) is a decidable setoid

1#-injective : β {as bs} β as 1# β‘ bs 1# β as β‘ bs
1#-injective refl = refl

infix 4 _β_ _ββ_

_ββ_ : β {base} β Decidable (_β‘_ {A = Expansion base})
_ββ_ []       []       = yes refl
_ββ_ []       (_ β· _)  = no Ξ»()
_ββ_ (_ β· _) []        = no Ξ»()
_ββ_ (x β· xs) (y β· ys) =
  mapβ² (uncurry (congβ _β·_)) β·-injective (x Fin.β y Γ-dec xs ββ ys)

_β_ : Decidable {A = Bin} _β‘_
0#    β 0#    = yes refl
0#    β bs 1# = no Ξ»()
as 1# β 0#    = no Ξ»()
as 1# β bs 1# = mapβ² (cong _1#) 1#-injective (as ββ bs)

β‘-isDecEquivalence : IsDecEquivalence _β‘_
β‘-isDecEquivalence = record
  { isEquivalence = isEquivalence
  ; _β_           = _β_
  }

β‘-decSetoid : DecSetoid _ _
β‘-decSetoid = decSetoid _β_

------------------------------------------------------------------------
-- (Bin _β‘_ _<_) is a strict total order

<-trans : Transitive _<_
<-trans (less ltβ) (less ltβ) = less (ββ.<-trans ltβ ltβ)

<-asym : Asymmetric _<_
<-asym (less lt) (less gt) = ββ.<-asym lt gt

<-irrefl : Irreflexive _β‘_ _<_
<-irrefl refl (less lt) = ββ.<-irrefl refl lt

β·Κ³-mono-< : β {a b as bs} β as 1# < bs 1# β (a β· as) 1# < (b β· bs) 1#
β·Κ³-mono-< {a} {b} {as} {bs} (less lt) = less (begin
  1+ (mβ +β nβ *β 2) β€β¨ sβ€s (ββ.+-monoΛ‘-β€ _ (π½β.toββ€pred[n] a)) β©
  1+ (1 +β nβ *β 2)  β‘β¨ refl β©
  1+ nβ *β 2         β€β¨ ββ.*-mono-β€ lt ββ.β€-refl β©
  nβ *β 2            β€β¨ ββ.mβ€n+m (nβ *β 2) mβ β©
  mβ +β nβ *β 2      β)
  where
  open ββ.β€-Reasoning
  mβ = Fin.toβ a;   mβ = Fin.toβ b
  nβ = toβ (as 1#); nβ = toβ (bs 1#)

β·Λ‘-mono-< : β {a b bs} β a Fin.< b β (a β· bs) 1# < (b β· bs) 1#
β·Λ‘-mono-< {a} {b} {bs} lt = less (begin
  1 +β (mβ  +β n *β 2)  β‘β¨ sym (ββ.+-assoc 1 mβ (n *β 2)) β©
  (1 +β mβ) +β n *β 2   β€β¨ ββ.+-monoΛ‘-β€ _ lt β©
  mβ  +β n *β 2   β)
  where
  open ββ.β€-Reasoning
  mβ = Fin.toβ a; mβ = Fin.toβ b; n = toβ (bs 1#)

1<[23] : β {b} β [] 1# < (b β· []) 1#
1<[23] {b} = less (ββ.mβ€n+m 2 (Fin.toβ b))

1<2+ : β {b bs} β [] 1# < (b β· bs) 1#
1<2+ {_} {[]}     = 1<[23]
1<2+ {_} {b β· bs} = <-trans 1<[23] (β·Κ³-mono-< {a = b} 1<2+)

0<1+ : β {bs} β 0# < bs 1#
0<1+ {[]}     = less (sβ€s zβ€n)
0<1+ {b β· bs} = <-trans (less (sβ€s zβ€n)) 1<2+

<ββ’ : β {a b} β a < b β a β’ b
<ββ’ lt eq = asymβirr (respβ _<_) sym <-asym eq lt

<-cmp : Trichotomous _β‘_ _<_
<-cmp 0#            0#            = triβ (<-irrefl refl) refl (<-irrefl refl)
<-cmp 0#            (_ 1#)        = tri< 0<1+ (<ββ’ 0<1+) (<-asym 0<1+)
<-cmp (_ 1#)        0#            = tri> (<-asym 0<1+) (<ββ’ 0<1+ β sym) 0<1+
<-cmp ([] 1#)       ([] 1#)       = triβ (<-irrefl refl) refl (<-irrefl refl)
<-cmp ([] 1#)       ((b β· bs) 1#) = tri< 1<2+ (<ββ’ 1<2+) (<-asym 1<2+)
<-cmp ((a β· as) 1#) ([] 1#)       = tri> (<-asym 1<2+) (<ββ’ 1<2+ β sym) 1<2+
<-cmp ((a β· as) 1#) ((b β· bs) 1#) with <-cmp (as 1#) (bs 1#)
... | tri<  lt Β¬eq Β¬gt =
  tri< (β·Κ³-mono-< lt)  (<ββ’ (β·Κ³-mono-< lt)) (<-asym (β·Κ³-mono-< lt))
... | tri> Β¬lt Β¬eq  gt =
  tri> (<-asym (β·Κ³-mono-< gt)) (<ββ’ (β·Κ³-mono-< gt) β sym) (β·Κ³-mono-< gt)
... | triβ Β¬lt refl Β¬gt with π½β.<-cmp a b
...   | triβ Β¬ltβ² refl Β¬gtβ² =
  triβ (<-irrefl refl) refl (<-irrefl refl)
...   | tri<  ltβ² Β¬eq  Β¬gtβ² =
  tri< (β·Λ‘-mono-< ltβ²)  (<ββ’ (β·Λ‘-mono-< ltβ²)) (<-asym (β·Λ‘-mono-< ltβ²))
...   | tri> Β¬ltβ² Β¬eq  gtβ²  =
  tri> (<-asym (β·Λ‘-mono-< gtβ²)) (<ββ’ (β·Λ‘-mono-< gtβ²) β sym) (β·Λ‘-mono-< gtβ²)

<-isStrictTotalOrder : IsStrictTotalOrder _β‘_ _<_
<-isStrictTotalOrder = record
  { isEquivalence = isEquivalence
  ; trans         = <-trans
  ; compare       = <-cmp
  }

<-strictTotalOrder : StrictTotalOrder _ _ _
<-strictTotalOrder = record
  { Carrier            = Bin
  ; _β_                = _β‘_
  ; _<_                = _<_
  ; isStrictTotalOrder = <-isStrictTotalOrder
  }
