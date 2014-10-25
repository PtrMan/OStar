{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Term where

import qualified Data.Set as Set
import qualified Data.List as List

import VariableData

data TermNode =
	LeafTag {leafTag :: String} |
	LeafVariable {variable :: VariableData} |
	Branch {tree :: TermData}
		deriving (Ord, Eq)

instance Show TermNode where
  show (LeafTag x) = "<LeafTag " ++ show x ++ ">"
  show (LeafVariable x) = "<LeafVariable " ++ show x ++ ">"
  show (Branch x)    = "<Branch " ++ show x ++ ">"

data TermData = TermData { nodeTag :: String
						 ,  left :: TermNode
						 , right :: TermNode
						 } deriving (Ord, Eq)

instance Show TermData where
  show (TermData nodeTag delta tau) = "<TermData " ++ show nodeTag ++ " " ++ show delta ++ " " ++ show tau ++ ">"

-- helper
-- returns the nth element from a tree

-- <<works>>
-- test
-- *Main> takeNthFromTree 1 (Branch (TermData "*" (LeafTag "a") (LeafTag "b")))
-- <LeafTag "a">
-- *Main> takeNthFromTree 0 (Branch (TermData "*" (LeafTag "a") (LeafTag "b")))
-- <Branch <TermData "*" <LeafTag "a"> <LeafTag "b">>>
-- *Main> takeNthFromTree 2 (Branch (TermData "*" (LeafTag "a") (LeafTag "b")))
-- <LeafTag "b">

takeNthFromTree :: Int -> TermNode -> TermNode
takeNthFromTree selectedElement inputTree =
	let
		resultTuple = takeNthFromTreeInternal selectedElement 0 inputTree
	in case resultTuple of
		(Just result, _) -> result
		-- on choice for the other because it indicates a deep bug and should terminate the program
	where
		-- returns the nth element from a tree
		--                         selectedElement   currentCounter     input tree     result
		-- the result is t tuple consisting of the result node and the (incremented) counter
		takeNthFromTreeInternal :: Int            -> Int             -> TermNode    -> (Maybe TermNode,  Int)

		takeNthFromTreeInternal selectedElement currentCounter inputTree
			| selectedElement == currentCounter = (Just inputTree, -1)

		takeNthFromTreeInternal _ currentCounter (LeafTag _) = (Nothing, currentCounter+1)
		takeNthFromTreeInternal _ currentCounter (LeafVariable _) = (Nothing, currentCounter+1)
		takeNthFromTreeInternal selectedElement currentCounter (Branch (TermData _ leftTermNode rightTermNode)) =
			let
				resultOfLeft = takeNthFromTreeInternal selectedElement (currentCounter+1) leftTermNode
			in case resultOfLeft of
				(Just resultNode, _) -> (Just resultNode, -1)
				(Nothing, resultCounter) -> takeNthFromTreeInternal selectedElement resultCounter rightTermNode

-- helper
-- replaces inputTree at the selected element with replacingTree

-- <<works>>
-- test
-- *Main> replaceNthInTreeInternal 2 0  (LeafTag "c") (Branch (TermData "*" (LeafTag "a") (LeafTag "b")))
-- (<Branch <TermData "*" <LeafTag "a"> <LeafTag "c">>>,-1)
-- *Main> replaceNthInTree 1  (LeafTag "c") (Branch (TermData "*" (LeafTag "a") (LeafTag "b")))
-- <Branch <TermData "*" <LeafTag "c"> <LeafTag "b">>>
-- *Main> replaceNthInTree 0  (LeafTag "c") (Branch (TermData "*" (LeafTag "a") (LeafTag "b")))
-- <LeafTag "c">

replaceNthInTree :: Int -> TermNode -> TermNode -> TermNode
replaceNthInTree selectedElement replacingTree inputTree =
	let
		(result, _) = replaceNthInTreeInternal selectedElement 0 replacingTree inputTree
	in
		result
	where
		--                          selectedElement   currentCounter     replacement tree    input tree       result
		replaceNthInTreeInternal :: Int            -> Int             -> TermNode         -> TermNode    ->   (TermNode,  Int)
		replaceNthInTreeInternal selectedElement currentCounter replacingTree inputTree
			| selectedElement == currentCounter = (replacingTree, -1)

		replaceNthInTreeInternal selectedElement currentCounter replacingTree (Branch (TermData branchTag leftTermNode rightTermNode)) =
			let
				resultOfLeft = replaceNthInTreeInternal selectedElement (currentCounter+1) replacingTree leftTermNode
			in case resultOfLeft of
				(leftResultNode, -1) -> ((Branch (TermData branchTag leftResultNode rightTermNode)), -1)
				(leftResultNode, leftCounter) ->
					let
						resultOfRight = replaceNthInTreeInternal selectedElement leftCounter replacingTree rightTermNode
					in case resultOfRight of
						(rightResultNode, -1) -> ((Branch (TermData branchTag leftTermNode rightResultNode)), -1)
						(rightResultNode, rightCounter) -> (rightResultNode, rightCounter)

		replaceNthInTreeInternal _ currentCounter _ (LeafTag tagContent) = ((LeafTag tagContent), currentCounter+1)
		replaceNthInTreeInternal _ currentCounter _ (LeafVariable variableContent) = ((LeafVariable variableContent), currentCounter+1)



-- helper
-- counts the items in a tree
countItemsInTree :: TermNode -> Int
countItemsInTree (Branch (TermData _ left right)) = 1 + (countItemsInTree left) + (countItemsInTree right)
countItemsInTree (LeafVariable _) = 1
countItemsInTree (LeafTag _) = 1

-- counts the leafnodes in a tree
countLeafNodesInTree :: TermNode -> Int
countLeafNodesInTree (Branch (TermData _ left right)) = (countLeafNodesInTree left) + (countLeafNodesInTree right)
countLeafNodesInTree (LeafVariable _) = 1
countLeafNodesInTree (LeafTag _) = 1

areVariablesAppearingInTerm :: TermNode -> Bool
areVariablesAppearingInTerm (Branch (TermData _ left right)) = (areVariablesAppearingInTerm left) || (areVariablesAppearingInTerm right)
areVariablesAppearingInTerm (LeafVariable _) = True
areVariablesAppearingInTerm (LeafTag _) = False

-- gets the indices of all leafnodes of an term
getIndicesOfLeafNodesInTree :: TermNode -> [Int]
getIndicesOfLeafNodesInTree term = getIndicesOfLeafNodesInTreeWithFilter term (\x -> True)

-- TODOTEST
-- gets the indices of all leafnodes of an term where the filter applies
getIndicesOfLeafNodesInTreeWithFilter :: TermNode -> (TermNode -> Bool) -> [Int]
getIndicesOfLeafNodesInTreeWithFilter term filter =
		fst (getIndicesOfLeafNodesInTreeWithFilterInternal 0 [] term)
	where
		--                                               currentCounter    currentResult    inputTree    result
		getIndicesOfLeafNodesInTreeWithFilterInternal :: Int            -> [Int]         -> TermNode  -> ([Int], Int)
		getIndicesOfLeafNodesInTreeWithFilterInternal currentCounter currentResult (LeafTag leafTag)
			| filter (LeafTag leafTag) == True = (currentResult ++ [currentCounter], currentCounter+1)
			| True                             = (currentResult                    , currentCounter+1)
		getIndicesOfLeafNodesInTreeWithFilterInternal currentCounter currentResult (LeafVariable variableData)
			| filter (LeafVariable variableData) == True = (currentResult ++ [currentCounter], currentCounter+1)
			| True                                       = (currentResult                    , currentCounter+1)
		getIndicesOfLeafNodesInTreeWithFilterInternal currentCounter currentResult (Branch (TermData _ leftTermNode rightTermNode)) =
			let
				(resultListOfLeft, resultCounterOfLeft) = getIndicesOfLeafNodesInTreeWithFilterInternal (currentCounter+1) currentResult leftTermNode
				(resultListOfRight, resultCounterOfRight) = getIndicesOfLeafNodesInTreeWithFilterInternal resultCounterOfLeft resultListOfLeft rightTermNode
			in
				(resultListOfRight, resultCounterOfRight)


getAllSubtermAsSet :: TermNode -> Set.Set TermNode
getAllSubtermAsSet (Branch (TermData tag left right)) =
	let
		selfAsNode = Branch (TermData tag left right)
		setOfLeft = getAllSubtermAsSet left
		setOfRight = getAllSubtermAsSet right
	in
		Set.unions [Set.fromList [selfAsNode], setOfLeft, setOfRight]

getAllSubtermAsSet leaf = Set.fromList [leaf]


-- definition 10
-- Termsize
getTermSize :: TermNode -> Int
-- we just redirect it to the numberOfNodes
getTermSize term = countItemsInTree term


-- printing for output
getStringOfTerm :: TermNode -> String
getStringOfTerm (LeafTag tag) = tag
getStringOfTerm (LeafVariable (VariableData delta tau)) = delta ++ ":" ++ tau
getStringOfTerm (Branch (TermData tag left right)) = (getStringOfTerm left) ++ tag ++ (getStringOfTerm right)


getStringOfTerms :: [TermNode] -> String
getStringOfTerms terms =
	let
		stringOfTerms = map getStringOfTerm terms
	in
		List.concatMap (\x -> x ++ "\n") stringOfTerms
