module Quotient

import Data.Nat
import Data.Nat.Division
import Data.Nat.Equational
import Data.Nat.Order
import Data.Fin
import Data.Nat.Order.Properties
%default total
N,M,D:Nat
N=16
M=4
D=3





-- use elemSmallerThanBound
res1,res2:LT 1 3
res1 = boundModNatNZ 13 3  SIsNonZero

pr1: 1 `lt` 3 = true
res2 = ltIsLT 1 3 pr1

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

-- quotMultDenom  13 4 SIsNonZero

                                

