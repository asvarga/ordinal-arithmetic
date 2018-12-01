
{-@ LIQUID "--reflection" @-}
-- {-@ LIQUID "--exact-data-cons" @-}
-- {-@ LIQUID "--ple" @-}
-- {-@ LIQUID "--higherorder"     @-}



{-@ normal_nat :: n:Nat -> {normal (nat2ord' n)} @-}
-- normal_nat 0 = ()
-- normal_nat p = normal_nat 0
-- normal_nat 0 = normal Zero
-- normal_nat p = normal (Ord Zero p Zero)
-- normal_nat 0 =   normal (nat2ord' 0)
--              === normal Zero
--              === True
--              *** QED
-- normal_nat p =   normal (nat2ord' p)
--              === normal (Ord Zero p Zero)
--              === normal Zero
--              === True
--              *** QED
-- normal_nat n = [normal Zero, normal (nat2ord' n)] *** QED 


-- {-@ comp_i_i_EQ :: i:Int -> {(compInt i i == EQ)} @-}
-- comp_i_i_EQ :: Int -> ()
-- comp_i_i_EQ i = compInt i i === EQ *** QED

-- {-@ comp_x_x_EQ :: x:Ordinal -> {(compOrd x x == EQ)} @-}
-- comp_x_x_EQ :: Ordinal -> ()
-- comp_x_x_EQ Zero = compOrd Zero Zero === EQ *** QED
-- comp_x_x_EQ (Ord a n b) =   compOrd (Ord a n b) (Ord a n b)
--                         ==? EQ ? (comp_x_x_EQ a &&& comp_i_i_EQ n &&& comp_x_x_EQ b) 
--                         *** QED 



{-@ die :: {v:String | false} -> a @-}
die :: String -> a
die msg = error msg
{-@ lAssert  :: {v:Bool | v == True} -> a -> a @-}
lAssert True  x = x
lAssert False _ = die "yikes, assertion fails!"
yes = lAssert (1 + 1 == 2) ()
-- no  = lAssert (1 + 1 == 3) ()


