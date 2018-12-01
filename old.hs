

{-@ normal_nat :: n:Nat -> {normal (nat2ord' n)} @-}
normal_nat 0 = normal Zero
normal_nat p = normal (Ord Zero p Zero)
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
