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

getAllCombinations :: [a] -> Int -> [[a]]
getAllCombinations list remaining
	| remaining == 1 = map (\x -> [x]) list
	| remaining > 1  =
		let
			newRemaining = remaining - 1
			recursiveResult = getAllCombinations list newRemaining

			combined = combinatorialProduct list recursiveResult

			result = map convertTupleToList combined
		in
			result
		where
			convertTupleToList :: (a, [a]) -> [a]
			convertTupleToList (first, list) = [first] ++ list

			b :: [[a]] -> a -> [[a]]
			b lists prefix =
				map convertTupleToList $ zip (List.repeat prefix) lists


-- a b 2 -> a a b b
repeatN :: [a] -> Int -> [a]
repeatN list times = List.concat $ List.map (repeatNInternal times) list
--	where
--		repeatNInternal x = List.take times $ List.repeat x
repeatNInternal times x = List.take times $ List.repeat x