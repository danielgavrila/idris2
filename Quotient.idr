module Quotient

import Data.Nat
import Data.Nat.Division
import Data.Nat.Equational
import Data.Nat.Order
import Data.Fin
import Data.Fin.Extra
import Data.Nat.Order.Properties
%default total
N,M,D:Nat
N=16
M=4
D=3





-- use elemSmallerThanBound
res1:LT 1 3
res1 = boundModNatNZ 13 3  SIsNonZero

res2:LTE 3 5
pr1: 3 `lte` 5 = True
pr1 = Refl
res2 = lteIsLTE 3 5 pr1

res3: LT 2 5
res3 = res2

DivisionTheorem' : (numer, denom : Nat) -> (0 prf1 : NonZero denom)
               -> numer =  (modNatNZ numer denom prf1) +  (divNatNZ numer denom prf1)*denom 
DivisionTheorem' numer denom prf1   = rewrite sym $ fstDivmodNatNZeqDiv numer denom prf1 prf1 in
                                      rewrite sym $ sndDivmodNatNZeqMod numer denom prf1 prf1 in
                                      DivisionTheoremDivMod numer denom prf1 


prfDT:13 = 1+M*D
prfDT = DivisionTheorem' 13 3   SIsNonZero 

is3lt4: lt 3 4 =True
is3lt4 = Refl





-- plusZeroLeftNeutral : (right : Nat) -> fromInteger 0 + right = right
-- plusZeroRightNeutral : (left : Nat) -> left + Z = left

-- plusLteLeft : (a : Nat) -> LTE b c -> LTE (a + b) (a + c)
-- plusLteRight : (c : Nat) -> LTE a b -> LTE (a + c) (b + c)

|||what is in the left side of equation will become the goal of rewrite
|||e.g `a = b +c `, the term `a` is on the left side will appear in the goal type
|||or in other words what is on the right side of equation `b+c` will be replaced 
|||compound of rewrite evaluate the goal from left to right, first rewrite the `b+0` then `b+c`

sumRewrite: (a,b,c : Nat) -> ( b + c = a )   ->  LTE  ( b + Z ) ( b + c ) -> LTE b  a
sumRewrite a b c prf tgt = 
                           rewrite sym $ plusZeroRightNeutral b  in 
                           rewrite sym $ prf  in tgt


sumOrderLeft: (a,b,c : Nat) -> ( b + c = a )   ->   LTE b  a
sumOrderLeft a b c prf = let tgt : LTE  ( b + Z ) ( b + c )
                             tgt = plusLteLeft b zeroAlwaysSmaller -- LTEZero
                         in
                         rewrite sym $ plusZeroRightNeutral b  in 
                         rewrite sym $ prf  in tgt

sumOrderRight: (a,b,c : Nat) -> ( a = b + c  )   ->   LTE c  a
sumOrderRight a b c prf = let tgt : LTE  ( Z + c ) ( b + c )
                              tgt = plusLteRight c zeroAlwaysSmaller -- LTEZero
                          in
                          rewrite sym $ plusZeroLeftNeutral c  in 
                          rewrite prf  in tgt 

quotMultDenom: (numer, denom : Nat) -> (0 prf : NonZero denom) ->(divNatNZ numer denom prf)*denom `LTE`  numer 
quotMultDenom numer denom prf = let divTheorem : ( numer  = (modNatNZ numer denom prf) + (divNatNZ numer denom prf)*denom )
                                    divTheorem = DivisionTheorem' numer denom prf 
                                in
                                sumOrderRight numer   (modNatNZ numer denom prf)  ((divNatNZ numer denom prf)*denom)  divTheorem 
{-

-}

LTEIsTransitive' : (m : Nat) -> (n : Nat) -> (o : Nat) ->
                           LTE m n -> LTE (S n) o ->
                           LT  m  o -- this last type is equal with LTE (S m)  o
LTEIsTransitive' m  n o                 mlten             nlteo        = let msucc_lte_nsucc : LTE (S m) (S n) 
                                                                             msucc_lte_nsucc = shift m n mlten
                                                                         in
                                                                         LTEIsTransitive (S m) (S n) o  msucc_lte_nsucc nlteo 

doubleBound :{bound :Nat } -> (numFin : Fin bound) -> Nat
doubleBound  numFin = let b1 = bound
                      in
                      plus b1 b1 
f1: Fin 7
f1 = 3

quotMultDenomSmaller : {bound :Nat } -> (numFin : Fin bound) -> (denom : Nat) -> (0 prf : NonZero denom) -> (divNatNZ (finToNat numFin) denom prf)*denom `LT`  bound 
quotMultDenomSmaller numFin denom prf = let numer : Nat
                                            numer = finToNat numFin
                                            mult1 : Nat
                                            mult1 =  (divNatNZ numer denom prf)*denom
                                            res: mult1 `LTE`  numer
                                            res = quotMultDenom numer denom prf
                                            smallerBound : LT numer bound
                                            smallerBound = elemSmallerThanBound numFin
                                        in
                                        LTEIsTransitive' mult1 numer bound res smallerBound



-- quotMultDenom  13 4 SIsNonZero

-- LTEIsTransitive : (m : Nat) -> (n : Nat) -> (o : Nat) -> LTE m n -> LTE n o -> LTE m o

