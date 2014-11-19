module Generic (occurrences) where
import Data.List

occurrences :: (Eq a, Ord a) => [a] -> [(a, Int)]
occurrences elems =  [ (head l, length l) | l <- group $ sort elems ]

