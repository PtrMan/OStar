module Misc where

import qualified Data.List as List
import qualified Data.Set as Set

-- enumerates all values from 0 to 1-count
enumerateInt :: Int -> [Int]
enumerateInt count = List.take count $ List.iterate (+1) 0

-- Is symetric and excessive
combinatorialProduct :: [a] -> [b]    -> [(a, b)]
combinatorialProduct    []     _      =  []
combinatorialProduct    _      []     =  []
combinatorialProduct    inputA inputB =
	let
		resultList = List.concat $ map (singleProduct inputA) inputB
	in
		resultList
	where
		singleProduct :: [a] -> b -> [(a, b)]
		singleProduct list element = map (\x -> (x, element)) list


removeMultipleElements list = Set.toList $ Set.fromList list