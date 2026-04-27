-- don't delete me! i am an example of writing recursive nested functions

g :: [Int] -> [Int]
g a = 
  let f :: Int -> Int = \ b -> (case b of 0 -> 0 ; _ -> let n = b-1 in f n) in 
  (case a of [] -> [] ; (x:xs) -> (f x) : g xs)