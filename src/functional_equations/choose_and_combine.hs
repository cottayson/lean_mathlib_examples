module CC where

data Variable = X | Y | Z | W deriving (Show, Eq)

toLowerCase c =
  case c of
    'X' -> 'x'
    'Y' -> 'y'
    'Z' -> 'z'
    'W' -> 'w'
    ch  -> ch

stringToLowerCase res = map toLowerCase $ show $ res

-- |
-- >>> choose 0 [X, Y, Z]
-- [[]]
-- >>> choose 1 [X]
-- [[X]]
-- >>> choose 1 [X, Y]
-- [[X],[Y]]
-- >>> choose 1 [X, Y, Z]
-- [[X],[Y],[Z]]
-- >>> choose 2 [X]
-- []
-- >>> choose 2 [X, Y]
-- [[X,Y]]
-- >>> choose 2 [X, Y, Z]
-- [[X,Y],[X,Z],[Y,Z]]
-- 
-- >>> choose 3 ['a','b','c']
-- ["abc"]
-- >>> choose 4 ['a','b','c']
-- []
-- >>> choose 4 ['a','b','c','d']
-- ["abcd"]
choose :: Int -> [a] -> [[a]]
choose 0 _  = [[]]
choose k [] = []
choose k (x:xs) = map (x:) (choose (k-1) xs) ++ choose k xs

-- |
-- >>> combine 1 [X]
-- [[X]]
-- >>> combine 1 [X, Y]
-- [[X],[Y]]
-- >>> combine 1 [X, Y, Z]
-- [[X],[Y],[Z]]
-- >>> combine 2 [X]
-- [[X,X]]
-- >>> combine 2 [X, Y]
-- [[X,X],[X,Y],[Y,Y]]
-- >>> combine 2 [X, Y, Z]
-- [[X,X],[X,Y],[X,Z],[Y,Y],[Y,Z],[Z,Z]]
-- 
-- >>> combine 3 ['a','b','c']
-- ["aaa","aab","aac","abb","abc","acc","bbb","bbc","bcc","ccc"]
-- >>> combine 4 ['a', 'b']
-- ["aaaa","aaab","aabb","abbb","bbbb"]
combine :: Int -> [a] -> [[a]]
combine 0 _  = [[]] -- can fit [] or [[]]
combine k [] = []
combine k xxs@(x:xs) = map (x:) (combine (k-1) xxs) ++ combine k xs