{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}

import qualified System.Random as Random
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.List as List

import Control.Exception
import Data.Typeable

import Term
import VariableData
import Item
import AxiomTag
import Misc

import qualified AStar as AStar

-- TODO< inside evaluation function --- if the performance rating of the top candidates is 0, drop the candidates (return nothing) >

-- TODO
-- * check if connection function loops when it sees loops


data AxiomData = AxiomData {
	tag :: AxiomTag, -- tau
	t :: TermNode,
	tTick :: TermNode
} deriving (Eq, Ord)

-- NOTE< assumes the tag is equal >
instance Show AxiomData where
  show (AxiomData tag t tTick) = "<AxiomData " ++ show tag ++ " " ++ show t ++ " " ++ show tTick ++ ">"

data VariableNameNotFoundException = VariableNameNotFoundException {
	variablename :: String
} deriving (Show, Typeable)

instance Exception VariableNameNotFoundException




-- Definition 6 (Assignment)  An assignmnt is a partial function from variables to terms.

-- throws the exception VariableNameNotFoundException
rewriteTryToApplyAxiom :: Maybe (Random.StdGen, Agent) -> AxiomData                           -> TermNode    -> MatchResult TermNode
-- required for the rewriting, because else we can't rewrite fro example
-- 1
-- with the axiom (Type, 1, Number)
rewriteTryToApplyAxiom    (Just (_, _))                   (AxiomData Type axiomT  axiomTTick)    applyedTerm
	| axiomT == applyedTerm = Success axiomTTick
	| True                  = TypeCheckFailure

rewriteTryToApplyAxiom    computationContext              (AxiomData Equal axiomT axiomTTick)    applyedTerm =
	-- first we try to map the axiom to the term
	let
		matchingResult = tryToAssignTermNodeToVariables axiomT Map.empty applyedTerm
		in case matchingResult of
			MatchError           -> MatchError
			MultipleValuesForKey -> MultipleValuesForKey
			Success matchingVariables ->
				let
					(random0, random1) = case computationContext of
						Just (computationContextRandom, _) -> Random.split computationContextRandom
						Nothing -> (undefined, undefined)

					-- PERFORMANCE< of the computationContext is Nothing this doesn't need to be calculated, we do it non the less because it simplifies the code >
					rewrittenOrginalTerms = rewriteTermNode matchingVariables applyedTerm
					rewrittenOrginalTermsTypeValid = isTypeValid random0 rewrittenOrginalTerms applyedTerm

					rewrittenTerm = rewriteTermNode matchingVariables axiomTTick
					rewrittenTermTypeValid = isTypeValid random1 rewrittenTerm axiomTTick

					-- combine the A-Computation results for the type checks of the rewrite of the orginal term and the rewritten term
					existsValidTypePath = rewrittenOrginalTermsTypeValid && rewrittenTermTypeValid
				in
					if existsValidTypePath then
						Success rewrittenTerm
					else
						TypeCheckFailure
				where
					-- if it is needed, this checks if there is a A-Computation for the "Type"
					isTypeValid :: Random.StdGen -> TermNode -> TermNode -> Bool
					isTypeValid random resultTerm sourceTerm =
						let
							isComputationContextSet = case computationContext of
								Just _ -> True
								Nothing -> False
						in
							if (not isComputationContextSet) then
								True
							else
								let
									Just (_, computationContextAgent) = computationContext
									listOfTypeCheckingResultTerms = agentComputation False (Just Type) random computationContextAgent resultTerm
									listOfTypeCheckingResultTermsContainsSourceTerm = List.elem sourceTerm listOfTypeCheckingResultTerms
								in
									listOfTypeCheckingResultTermsContainsSourceTerm

					--rewrite variables termData = rewriteTermNode variables (Branch termData)

					-- function which does the rewriting
					-- replaces TermNodes of variables with the corresponding stored TermNodes in "variables"
					--                 map of variables           TermNode
					rewriteTermNode :: Map.Map String TermNode -> TermNode -> TermNode
					rewriteTermNode variables  (Branch (TermData nodeTag leftTermNode rightTermNode))   = Branch( TermData nodeTag (rewriteTermNode variables leftTermNode) (rewriteTermNode variables rightTermNode))
					rewriteTermNode variables  (LeafVariable (VariableData variableDelta variableTau))  = lookupAndReturnTermNode variables variableDelta
					rewriteTermNode variables  (LeafTag leafTag)                                        = LeafTag leafTag
					

					-- function which looks up the variable and throws a exception if it wasn't found
					lookupAndReturnTermNode variables variableDelta =
						case (Map.lookup variableDelta variables) of
							Just termNode -> termNode
							Nothing -> throw (VariableNameNotFoundException variableDelta)
	where
		-- tries to match a Term with Variables to a Term
		-- assigns varibles to the mtched (sub)terms
		--                                ruleTerm    input variableMapping      applyedTerm    result mapping
		tryToAssignTermNodeToVariables :: TermNode -> Map.Map String TermNode -> TermNode    -> MatchResult (Map.Map String TermNode)

		-- for a leafTag in the rule we do nothing
		tryToAssignTermNodeToVariables (LeafTag leafTag) map _ = Success map

		-- usual exact match
		tryToAssignTermNodeToVariables (LeafVariable (VariableData variableDelta _)) variableMapping applyedTerm
			| Map.notMember variableDelta variableMapping = Success (Map.insert variableDelta applyedTerm variableMapping)
		    | True                                        = MultipleValuesForKey

		-- for tree banches it is required to apply it to both sides of the branch
		tryToAssignTermNodeToVariables (Branch (TermData ruleNodeTag ruleLeft ruleRight)) variableMapping (Branch (TermData applyedNodeTag applyedLeft applyedRight) )
			| ruleNodeTag == applyedNodeTag =
				let
					afterLeft = tryToAssignTermNodeToVariables ruleLeft variableMapping applyedLeft
				in case afterLeft of
					Success resultMap    -> tryToAssignTermNodeToVariables ruleRight resultMap applyedRight
					MatchError           -> MatchError
					MultipleValuesForKey -> MultipleValuesForKey

		-- if all other matches fail we return a match error
		tryToAssignTermNodeToVariables _ _ _ = MatchError

rewriteTryToApplyAxiom computationContext (AxiomData _ _ _) applyedTerm = MatchError





-- TODO< get rid of computationContext >
-- TODO MEDIUM PERFORMANCE< rewriteTryToApplyAxiomWithAStar and agentComputationWithAStar should use a common datastructure for more performance? >

-- throws the exception VariableNameNotFoundException
rewriteTryToApplyAxiomWithAStar :: Maybe Agent -> AxiomData                           -> TermNode    -> MatchResult TermNode
--rewriteTryToApplyAxiomWithAStar    (Just _)                        (AxiomData Type axiomT  axiomTTick)    applyedTerm
--	| axiomT == applyedTerm = Success axiomTTick
--	| True                  = TypeCheckFailure

rewriteTryToApplyAxiomWithAStar    computationContext              (AxiomData _ axiomT axiomTTick)    applyedTerm =
	-- first we try to map the axiom to the term
	let
		isComputationContextSet = case computationContext of
			Just _ -> True
			Nothing -> False

		matchingResult = tryToAssignTermNodeToVariables axiomT Map.empty applyedTerm
		in case matchingResult of
			MatchError           -> MatchError
			MultipleValuesForKey -> MultipleValuesForKey
			Success matchingVariables ->
				let
					-- PERFORMANCE< of the computationContext is Nothing this doesn't need to be calculated, we do it non the less because it simplifies the code >
					rewrittenOrginalTerms = rewriteTermNode matchingVariables applyedTerm
					rewrittenOrginalTermsTypeValid = isTypeValid rewrittenOrginalTerms applyedTerm

					rewrittenTerm = rewriteTermNode matchingVariables axiomTTick
					rewrittenTermTypeValid = isTypeValid rewrittenTerm axiomTTick

					-- combine the A-Computation results for the type checks of the rewrite of the orginal term and the rewritten term
					existsValidTypePath = rewrittenOrginalTermsTypeValid && rewrittenTermTypeValid
				in
					if existsValidTypePath then
						Success rewrittenTerm
					else
						TypeCheckFailure
				where
					-- if it is needed, this checks if there is a A-Computation for the "Type"
					isTypeValid :: TermNode -> TermNode -> Bool
					isTypeValid resultTerm sourceTerm =
							if (not isComputationContextSet) then
								True
							else
								let
									Just computationContextAgent = computationContext
									(isReachableByTypeOnly, _) = agentComputationWithAStar False (Just Type) computationContextAgent resultTerm sourceTerm
								in
									isReachableByTypeOnly

					--rewrite variables termData = rewriteTermNode variables (Branch termData)

					-- function which does the rewriting
					-- replaces TermNodes of variables with the corresponding stored TermNodes in "variables"
					--                 map of variables           TermNode
					rewriteTermNode :: Map.Map String TermNode -> TermNode -> TermNode
					rewriteTermNode variables  (Branch (TermData nodeTag leftTermNode rightTermNode))   = Branch( TermData nodeTag (rewriteTermNode variables leftTermNode) (rewriteTermNode variables rightTermNode))
					rewriteTermNode variables  (LeafVariable (VariableData variableDelta variableTau))  = lookupAndReturnTermNode variables variableDelta
					rewriteTermNode variables  (LeafTag leafTag)                                        = LeafTag leafTag
					

					-- function which looks up the variable and throws a exception if it wasn't found
					lookupAndReturnTermNode variables variableDelta =
						case (Map.lookup variableDelta variables) of
							Just termNode -> termNode
							Nothing -> throw (VariableNameNotFoundException variableDelta)
	where
		-- tries to match a Term with Variables to a Term
		-- assigns varibles to the mtched (sub)terms
		--                                ruleTerm    input variableMapping      applyedTerm    result mapping
		tryToAssignTermNodeToVariables :: TermNode -> Map.Map String TermNode -> TermNode    -> MatchResult (Map.Map String TermNode)

		-- for a leafTag in the rule we do nothing
		tryToAssignTermNodeToVariables (LeafTag leafTag) map _ = Success map

		-- usual exact match
		tryToAssignTermNodeToVariables (LeafVariable (VariableData variableDelta _)) variableMapping applyedTerm
			| Map.notMember variableDelta variableMapping = Success (Map.insert variableDelta applyedTerm variableMapping)
		    | True                                        = MultipleValuesForKey

		-- for tree banches it is required to apply it to both sides of the branch
		tryToAssignTermNodeToVariables (Branch (TermData ruleNodeTag ruleLeft ruleRight)) variableMapping (Branch (TermData applyedNodeTag applyedLeft applyedRight) )
			| ruleNodeTag == applyedNodeTag =
				let
					afterLeft = tryToAssignTermNodeToVariables ruleLeft variableMapping applyedLeft
				in case afterLeft of
					Success resultMap    -> tryToAssignTermNodeToVariables ruleRight resultMap applyedRight
					MatchError           -> MatchError
					MultipleValuesForKey -> MultipleValuesForKey

		-- if all other matches fail we return a match error
		tryToAssignTermNodeToVariables _ _ _ = MatchError

--rewriteTryToApplyAxiomWithAStar computationContext (AxiomData _ _ _) applyedTerm = MatchError





-- definition 10
-- Termsize
getTermSizeForAxiom :: AxiomData -> Int
getTermSizeForAxiom (AxiomData _ t tTick) = (getTermSize t) + (getTermSize tTick)

getTermSizeOfTheory :: [AxiomData] -> Int
getTermSizeOfTheory theory = List.sum (List.map getTermSizeForAxiom theory)

-- Definition 11 (Agent computation)
-- TODO< constraints from outside >

-- axiomTagFilter can be an axiom type which the axioms are filtered For

-- returns a list of terms of the done production/transformation

agentComputation :: Bool       -> Maybe AxiomTag -> Random.StdGen -> Agent                                                                                                 -> TermNode -> [TermNode]
agentComputation    checkTypes    axiomTagFilter    random           (Agent agentT agentC agentWorkingMemoryCapacity agentAssimilationCapacity agentAccommodationCapacity)    term     =
	let
		usedAxioms = case axiomTagFilter of 
			Just filteredTag -> List.filter (axiomFilterHelper filteredTag) (Set.toList agentT)
			Nothing -> (Set.toList agentT)
	in
		agentComputationInternal usedAxioms random (Agent agentT agentC agentWorkingMemoryCapacity agentAssimilationCapacity agentAccommodationCapacity) term agentAssimilationCapacity
	where
		axiomFilterHelper :: AxiomTag -> AxiomData                    -> Bool
		axiomFilterHelper    compareTag  (AxiomData compareTag2 _ _ ) =  compareTag == compareTag2

		agentComputationInternal :: [AxiomData] -> Random.StdGen -> Agent                                                                                                 -> TermNode -> Int                   -> [TermNode]
		agentComputationInternal    _              _                _                                                                                                        _           0                     =  []
		agentComputationInternal    usedAxioms     random           (Agent agentT agentC agentWorkingMemoryCapacity agentAssimilationCapacity agentAccommodationCapacity)    term        remainingComputations =
			let
				(random0, random1) = Random.split random

				orginalAgent = (Agent agentT agentC agentWorkingMemoryCapacity agentAssimilationCapacity agentAccommodationCapacity)

				filteredRewrittenTerms = getResultsOfRewriteWithAxiomsUsingFilter random1 (filterHelper agentWorkingMemoryCapacity) term usedAxioms
				elementsInFilteredRewrittenTerms = List.length filteredRewrittenTerms
			in
				if elementsInFilteredRewrittenTerms == 0 then
					[]
				else
					-- TODO< choose just one by random or do a a-star search? >
					-- here we just choose a random element (if it is possible)
					let
						(chosenTermIndexTake, random2) = Random.randomR (0, elementsInFilteredRewrittenTerms-1) random
						chosenRewrittenTerm = filteredRewrittenTerms !! chosenTermIndexTake
					in
						[chosenRewrittenTerm] ++ (agentComputationInternal usedAxioms random0 orginalAgent chosenRewrittenTerm (remainingComputations - 1))
			where
				-- does ensure that the Term Size is small enought for the agent
				filterHelper :: Int -> TermNode -> Bool
				filterHelper maximum appliedTerm = (getTermSize appliedTerm) < maximum

				getResultsOfRewriteWithAxiomsUsingFilter :: Random.StdGen -> (TermNode -> Bool) -> TermNode -> [AxiomData] -> [TermNode]
				getResultsOfRewriteWithAxiomsUsingFilter random filterFunction appliedTerm axioms =
					let
						-- try to rewrite the axioms
						-- [MatchResult TermNode]
						rewrittenMatchResults = map mapHelper (zip axioms (List.repeat appliedTerm))

						-- filter the MatchResults for valid matches and translate to list of terms
						filteredValidTerms0 = List.filter filterHelper rewrittenMatchResults
						filteredValidTerms1 = List.map convertSuccessfulMatchResultToTerm filteredValidTerms0

						-- filter with filter
						filteredValidTerms2 = List.filter filterFunction filteredValidTerms1
					in
						filteredValidTerms2
					where
						-- helper, tries to rewrite the Term with the axiom
						mapHelper :: (AxiomData, TermNode) -> MatchResult TermNode
						mapHelper (axiom, appliedTerm)
							| checkTypes =
								let
									agent = Agent agentT agentC agentWorkingMemoryCapacity agentAssimilationCapacity agentAccommodationCapacity
								in
									       rewriteTryToApplyAxiom (Just (random, agent)) axiom appliedTerm
							| True       = rewriteTryToApplyAxiom Nothing axiom appliedTerm

						filterHelper :: MatchResult TermNode -> Bool
						filterHelper (Success _) = True
						filterHelper _ = False

						-- only defined for Success term
						convertSuccessfulMatchResultToTerm :: MatchResult TermNode -> TermNode
						convertSuccessfulMatchResultToTerm (Success term) = term

-- all possible transistions is returned for debugging
agentComputationWithAStar :: Bool       -> Maybe AxiomTag  -> Agent -> TermNode   -> TermNode -> (Bool, [TermNode])
agentComputationWithAStar    checkTypes    axiomTagFilter     agent    startTerm     goalTerm =
	let
		(Agent agentT agentC agentWorkingMemoryCapacity agentAssimilationCapacity agentAccommodationCapacity) = agent

		usedAxioms = case axiomTagFilter of 
			Just filteredTag -> List.filter (axiomFilterHelper filteredTag) (Set.toList agentT)
			Nothing -> (Set.toList agentT)

		-- first we build a list of all possible transitions
		-- TODO< should actually be incorperated into an custom A* algorithm because it could save a lot of time >
		allPossibleTransitions = getAllPossibleTransitionsOfTerms agent startTerm checkTypes agentAssimilationCapacity agentWorkingMemoryCapacity usedAxioms

		aStarGraphFunctionWithTransistions = aStarGraphFunction allPossibleTransitions
	in
		if (List.length allPossibleTransitions) == 0
		then
			(False, [])
		else
			let
				aStarSearchResult = AStar.aStar aStarGraphFunctionWithTransistions aStarDistanceFunction aStarheuristicDistanceFunction aStarIsGoal startTerm
			in
				case aStarSearchResult of
					Just optiomalSolution -> (True, [startTerm] ++ optiomalSolution)
					Nothing -> (False, [startTerm])
	where
		-- MOVEHERE getAllPossibleTransitionsOfTerms

		axiomFilterHelper :: AxiomTag -> AxiomData                    -> Bool
		axiomFilterHelper    compareTag  (AxiomData compareTag2 _ _ ) =  compareTag == compareTag2

		---------------------------------------------
		-- these are all helpers for the A* Algorithm

		aStarGraphFunction :: [(TermNode, TermNode)] -> TermNode -> Set.Set TermNode
		aStarGraphFunction possibleTransitions currentTerm =
			let
				listFilteredForCurrentTerms = List.filter filterForCurrentTermAsSource possibleTransitions
				reachableNodes = List.map getDestinationOfTuple listFilteredForCurrentTerms
			in
				-- HACK< because a function hangs >
				-- TODO< revert
				
				Set.difference (Set.fromList reachableNodes) (Set.fromList [currentTerm])
				-- Set.fromList reachableNodes
			where
				filterForCurrentTermAsSource :: (TermNode, TermNode) -> Bool
				filterForCurrentTermAsSource (term, _) = term == currentTerm

				getDestinationOfTuple :: (TermNode, TermNode) -> TermNode
				getDestinationOfTuple (_, destination) = destination

		aStarDistanceFunction :: TermNode -> TermNode -> Int
		aStarDistanceFunction a b = 1

		aStarheuristicDistanceFunction :: TermNode -> Int
		aStarheuristicDistanceFunction _ = 0

		aStarIsGoal :: TermNode -> Bool
		aStarIsGoal term = term == goalTerm









getAllPossibleTransitionsOfTerms :: Agent -> TermNode   -> Bool       -> Int                       -> Int                        -> [AxiomData] -> [(TermNode, TermNode)]
getAllPossibleTransitionsOfTerms    agent    startTerm     checkTypes    agentAssimilationCapacity    agentWorkingMemoryCapacity     usedAxioms =
	let
		-- list of nodes for which the possible transistions with the application of axioms is left to be checked
		-- the remaining searchdepth is also stored
		openList = [(startTerm, agentAssimilationCapacity)]

		(_, foundPossibleApplications) = applyHelper (openList, Set.empty) (usedAxioms, agentWorkingMemoryCapacity) -- DEBUGGING applyWhile applyHelper (openList, []) (usedAxioms, agentWorkingMemoryCapacity)
	in
		Set.toList foundPossibleApplications
	where
		-- DEBUGGING
		--applyHelperTest ::  ([(TermNode, Int)], [(TermNode, TermNode)]) -> ([AxiomData], Int) -> ([(TermNode, Int)], [(TermNode, TermNode)])
		--applyHelperTest current passThrough =
		--	let
		--		applyResult = applyHelper current passThrough

		--	in case applyResult of
		--		Nothing -> current
		--		Just resultOfCall -> applyHelperTest resultOfCall passThrough


		-- searches for all possible rewrites of the terms
		-- this is done until a maximal depth is reached
		applyHelper :: ([(TermNode, Int)], Set.Set (TermNode, TermNode)) -> ([AxiomData], Int) -> ([(TermNode, Int)], Set.Set (TermNode, TermNode))
		applyHelper ([], resultThusFar) _ = ([], resultThusFar)

		-- we terminate the search for open list elements where the remaining depth is 0
		applyHelper ((_, 0):remainingOpenList, resultUntilNow) (usedAxioms, agentWorkingMemoryCapacity) = applyHelper (remainingOpenList, resultUntilNow) (usedAxioms, agentWorkingMemoryCapacity)

		applyHelper ((currentOpenListElement, currentRemainingDeep):remainingOpenList, _) (usedAxioms, agentWorkingMemoryCapacity) =
			let
				nextRemainingDepth = currentRemainingDeep - 1

				termsAfterApplicationOfTheorems = getResultsOfRewriteWithAxiomsUsingFilter (filterHelper agentWorkingMemoryCapacity) currentOpenListElement usedAxioms

				termTermTransitions = List.zip (List.repeat currentOpenListElement) termsAfterApplicationOfTheorems
				filteredTermTermTransitions = List.filter termTermTransitionFilter termTermTransitions
				termTermTransitionsAsSet = Set.fromList filteredTermTermTransitions
				additionalRemainingOpenList = List.zip termsAfterApplicationOfTheorems (List.repeat nextRemainingDepth)

				(_, recursiveResult) = applyHelper (remainingOpenList ++ additionalRemainingOpenList, termTermTransitionsAsSet) (usedAxioms, agentWorkingMemoryCapacity)
			in
				([], Set.union termTermTransitionsAsSet recursiveResult) -- DEBUG applyHelper (remainingOpenList ++ additionalRemainingOpenList, termTermTransitions) (usedAxioms, agentWorkingMemoryCapacity)
			where
				-- does ensure that the Term Size is small enought for the agent
				filterHelper :: Int -> TermNode -> Bool
				filterHelper maximum appliedTerm = (getTermSize appliedTerm) < maximum

				getResultsOfRewriteWithAxiomsUsingFilter :: (TermNode -> Bool) -> TermNode -> [AxiomData] -> [TermNode]
				getResultsOfRewriteWithAxiomsUsingFilter filterFunction appliedTerm axioms =
					let
						-- try to rewrite the axioms
						-- [MatchResult TermNode]
						rewrittenMatchResults = map (rewriteHelper agent False) (zip axioms (List.repeat appliedTerm))

						-- filter the MatchResults for valid matches and translate to list of terms
						filteredValidTerms0 = List.filter filterHelper rewrittenMatchResults
						filteredValidTerms1 = List.map convertSuccessfulMatchResultToTerm filteredValidTerms0

						-- filter with filter
						filteredValidTerms2 = List.filter filterFunction filteredValidTerms1
					in
						filteredValidTerms2
					where
						-- MOVEHERE rewriteHelper

						filterHelper :: MatchResult TermNode -> Bool
						filterHelper (Success _) = True
						filterHelper _ = False

						-- only defined for Success term
						convertSuccessfulMatchResultToTerm :: MatchResult TermNode -> TermNode
						convertSuccessfulMatchResultToTerm (Success term) = term

				termTermTransitionFilter :: (TermNode, TermNode) -> Bool
				termTermTransitionFilter (a, b) = not $ a == b




-- helper, tries to rewrite the Term with the axiom
-- helper, tries to rewrite the Term with the axiom
rewriteHelper :: Agent -> Bool -> (AxiomData, TermNode) -> MatchResult TermNode
rewriteHelper agent checkTypes (axiom, appliedTerm)
-- BUGTRACE
-- | checkTypes = rewriteTryToApplyAxiomWithAStar (Just agent) axiom appliedTerm
	| True       = rewriteTryToApplyAxiomWithAStar Nothing axiom appliedTerm









-- Definition 13 (Item Computation)
doesAgentComputeItem :: Agent -> Item -> Bool
doesAgentComputeItem agent (Item itemTag t1 t2 _) =
	let
		(doesCompute, _) = agentComputationWithAStar True (Just itemTag) agent t1 t2
	in
		doesCompute

-- Definition 14 (Performance)
calcPerformanceSum :: Random.StdGen -> Agent -> [Item] -> Int
calcPerformanceSum    random           agent    items  =  List.sum (calcIndividualPerformance agent items)

calcPerformanceSumAStar :: Agent -> [Item] -> Int
calcPerformanceSumAStar    agent    items  =  List.sum (calcIndividualPerformance agent items)

calcIndividualPerformance :: Agent -> [Item] -> [Int]
calcIndividualPerformance    agent    items  =
		map mapItemToScore items
	where
		-- calculates the score of an item
		mapItemToScore :: Item -> Int
		mapItemToScore (Item itemTag t1 t2 itemU)
			| doesAgentComputeItem agent (Item itemTag t1 t2 itemU) = itemU
			| True                                                  = 0

-- des take a random subtree from treeA and inserts it into a random position in treeB
-- Definition 15 (Crossover)

-- <<works>>

crossover :: Random.StdGen -> TermNode -> TermNode -> TermNode

crossover random treeA treeB =
	let
		numberOfItemsInTreeA = countItemsInTree treeA
		(chosenElementToCutFromA, random2) = Random.randomR (0, numberOfItemsInTreeA-1) random

		-- now we cut a subtree from a tree
		subtree = takeNthFromTree chosenElementToCutFromA treeA

		numberOfItemsInTreeB = countItemsInTree treeB
		(chosenElementToInsertIntoB, _) = Random.randomR (0, numberOfItemsInTreeB-1) random2

		replacedTree = replaceNthInTree chosenElementToInsertIntoB subtree treeB

	in
		replacedTree

-- does a excessive crossover
-- returns all combinations of crossover which are possible
crossoverExcessive :: TermNode -> TermNode -> Set.Set TermNode
crossoverExcessive treeA treeB =
	let
		treeASubterms = getAllSubtermAsSet treeA
		treeBSubterms = getAllSubtermAsSet treeB

		treeASubtermsAsList = Set.toList treeASubterms
		treeBSubtermsAsList = Set.toList treeBSubterms

		unionOfSetsOfCrossoverResult = Set.unions $ map (\iterationTerm -> getAllCrossoverOfTermWithTerms iterationTerm treeASubtermsAsList) treeBSubtermsAsList
	in
		unionOfSetsOfCrossoverResult
	where
		getAllCrossoverOfTermWithTerms :: TermNode -> [TermNode] -> Set.Set TermNode
		getAllCrossoverOfTermWithTerms term terms =
			let
				numberOfItemsInTerm = countItemsInTree term
				-- list with all possible number of the subterms of 'term'
				numbersOfTermsInTerm = enumerateInt numberOfItemsInTerm

				-- list with functions which replace nth subterm with the input
				replaceNthInTreeFunctions = List.map (\chosenNumber -> replaceNthInTree chosenNumber term) numbersOfTermsInTerm

				-- [(function which takes a term aand returns the tree with the replaced tree, term to apply)]
				productsOfFunctionsAndApplyedTerms = combinatorialProduct replaceNthInTreeFunctions terms

				resultTermsAsList = List.map applyFunction productsOfFunctionsAndApplyedTerms
				resultTermsAsSet = Set.fromList resultTermsAsList
			in
				resultTermsAsSet
			where
				applyFunction :: (TermNode -> TermNode, TermNode) -> TermNode
				applyFunction (func, term) = func term

				-- applyFunction :: (TermNode -> TermNode) -> TermNode -> TermNode
				-- applyFunction func term = func term


		--getAllCrossoverOfTermWithTerms term terms = Set.unions $ List.map (getAllCrossoverOfTermTerm term) terms

		--getAllCrossoverOfTermTerm :: TermNode -> TermNode -> Set.Set TermNode
		--getAllCrossoverOfTermTerm a b =
		--	let
		--		numberOfItemsInA = countItemsInTree a
		--		numberOfItemsInB = countItemsInTree b
		--	in

data Side = LeftSide | RightSide

-- NOTE< not after specification, whole algorithm producesstrange result(s) >

-- does a analyzing excessive crossover
-- * search for all unique node tags
-- * get all leafes
-- * recombine branches of unique node tags with all possible instantiations of the saved leaves

excessiveCrossover :: [TermNode] -> Int -> Set.Set TermNode
excessiveCrossover terms maximalComplexity =
	let
		uniqueNodeTagsAsSet = Set.unions $ List.map getUnqiueNodeTagsOfTerm terms
		uniqueLeafesAsSet = Set.unions $ List.map getAllLeafTagsOfTerm terms

		resultTermsOfOnlyLeafesAsList = List.map createLeafFromTag $ Set.toList uniqueLeafesAsSet
		uniqueNodeTagsAsList = Set.toList uniqueNodeTagsAsSet

		remainingSteps = quot (maximalComplexity-1) 2 + 1
		resultAsList = combinePossibleTermsRecursive remainingSteps resultTermsOfOnlyLeafesAsList resultTermsOfOnlyLeafesAsList uniqueNodeTagsAsList
		resultAsSet = Set.fromList resultAsList
	in
		resultAsSet
	where
		-- is called iterativly to build bigger and bigger trees, which can be again be combined
		-- this simplifies the algorithm and saves some calculation-time
		generatePossibleCombinationsOfBiggerTermWithSmallerTerms :: [TermNode] -> [TermNode] -> [String] -> [TermNode]
		generatePossibleCombinationsOfBiggerTermWithSmallerTerms biggerList leafList nodeTags = 
			let
				result = removeMultipleElements $ List.concat $ List.map generatePossibleCombinationsOfBiggerTermWithSmallerTerm leafList
			in
				result
			where
				-- uses variables of top function
				generatePossibleCombinationsOfBiggerTermWithSmallerTerm :: TermNode -> [TermNode]
				generatePossibleCombinationsOfBiggerTermWithSmallerTerm currentLeaf =
					let
						productOfTagAndBiggerTerm = combinatorialProduct biggerList nodeTags
						resultListForLeft = List.map (\x -> createBranchWithTagAndTerm LeftSide x currentLeaf) productOfTagAndBiggerTerm
						resultListForRight = List.map (\x -> createBranchWithTagAndTerm RightSide x currentLeaf) productOfTagAndBiggerTerm
					in
						resultListForLeft ++ resultListForRight
					where
						createBranchWithTagAndTerm :: Side -> (TermNode, String) -> TermNode -> TermNode
						createBranchWithTagAndTerm LeftSide (a, tag) b = Branch (TermData tag a b)
						createBranchWithTagAndTerm RightSide (a, tag) b = Branch (TermData tag b a)

		createLeafFromTag :: String -> TermNode
		createLeafFromTag tag = LeafTag tag

		combinePossibleTermsRecursive :: Int -> [TermNode] -> [TermNode] -> [String] -> [TermNode]
		combinePossibleTermsRecursive 0 _ _ _ = undefined
		combinePossibleTermsRecursive 1 previousResult _ _ = previousResult
		combinePossibleTermsRecursive remainingCounter previousResult leafTerms nodeTags =
			let
				possibleResultTrees = generatePossibleCombinationsOfBiggerTermWithSmallerTerms previousResult leafTerms nodeTags
			in
				combinePossibleTermsRecursive (remainingCounter-1) possibleResultTrees leafTerms nodeTags


templatedCrossover :: [TermNode] -> Set.Set TermNode
templatedCrossover terms =
	let
		uniqueLeafetagsAsSet = Set.unions $ List.map getAllLeafTagsOfTerm terms
		uniqueLeafetagsAsList = Set.toList uniqueLeafetagsAsSet
		uniqueTermTemplatesAsSet = getUniqueTermTemplatesAsSet terms
		uniqueTermTemplatesAsList = Set.toList uniqueTermTemplatesAsSet
		
		uniqueLeafes = List.map getleafWithleafTag uniqueLeafetagsAsList

		allPossibleCombinationsAsList = List.concat $ List.map (getAllPossibleLeafCombinationsOfTerm uniqueLeafes) uniqueTermTemplatesAsList
		allPossibleCombinationsAsSet = Set.fromList allPossibleCombinationsAsList
	in
		allPossibleCombinationsAsSet
	where
		getUniqueTermTemplatesAsSet :: [TermNode] -> Set.Set TermNode
		getUniqueTermTemplatesAsSet terms =
				Set.fromList $ map getTemplateOfTerm terms
			where
				getTemplateOfTerm :: TermNode -> TermNode
				getTemplateOfTerm (LeafTag _) = LeafTag "@"
				getTemplateOfTerm (LeafVariable _) = LeafTag "@"
				getTemplateOfTerm (Branch (TermData tag left right)) =
					let
						leftResult = getTemplateOfTerm left
						rightResult = getTemplateOfTerm right
					in
						(Branch (TermData tag leftResult rightResult))

		-- other cases indicate programming error
		getAllPossibleLeafCombinationsOfTerm :: [TermNode] -> TermNode -> [TermNode]
		getAllPossibleLeafCombinationsOfTerm uniqueLeafes (LeafTag "@") = uniqueLeafes
		getAllPossibleLeafCombinationsOfTerm uniqueLeafes (Branch (TermData tag left right)) =
			let
				leftResult  = getAllPossibleLeafCombinationsOfTerm uniqueLeafes left
				rightResult = getAllPossibleLeafCombinationsOfTerm uniqueLeafes right

				combinatesOfLeftAndRight = combinatorialProduct leftResult rightResult
				result = map (convertTupleToBranch tag) combinatesOfLeftAndRight
			in
				result
			where
				convertTupleToBranch :: String -> (TermNode, TermNode) -> TermNode
				convertTupleToBranch tag (left, right) = (Branch (TermData tag left right))

		getleafWithleafTag :: String -> TermNode
		getleafWithleafTag tag = LeafTag tag


-- Definition 16
-- Abstraction

-- NOTE< until now we don't return a failiure if the abstraction is not possible >

tryAbstraction :: Item -> Maybe AxiomData
tryAbstraction (Item itemTag t1 t2 _) =
	let
		(uniqueNamesForTagsInT1, _) = findUniqueNamesForTags t1 Map.empty 0
		rewrittenT1 = rewriteTermWithTagMapping t1 uniqueNamesForTagsInT1
		rewrittenT2 = rewriteTermWithTagMapping t2 uniqueNamesForTagsInT1
	in
		(Just (AxiomData itemTag rewrittenT1 rewrittenT2))

-- helper function for tryAbstraction
-- tries to attach unique variablenames to values of the Term
findUniqueNamesForTags :: TermNode -> Map.Map String VariableData -> Int -> (Map.Map String VariableData, Int)
findUniqueNamesForTags (Branch (TermData _ leftNode rightNode)) map counter =
	let
		(resultMapFromLeft, counterFromLeft) = findUniqueNamesForTags leftNode map counter
	in
		findUniqueNamesForTags rightNode resultMapFromLeft counterFromLeft

findUniqueNamesForTags (LeafTag tag) map counter
    -- if it is allready inside we don't overwrite it
	| Map.member tag map = (map, counter)
	-- if not we add it and increment the counter
	| True =
		let 
			-- ASK< does it (the conversion from int to string) work with the haskell compiler too >
			uniqueVariableName = (show counter)
		in
			(Map.insert tag (VariableData uniqueVariableName "Aterm") map, counter+1)

-- findUniqueNamesForTags not defined for LeafVariable

-- helper function for tryAbstraction
rewriteTermWithTagMapping :: TermNode -> Map.Map String VariableData -> TermNode
rewriteTermWithTagMapping (Branch (TermData nodeTag leftNode rightNode)) tagMapping =
	let
		rewrittenLeft = rewriteTermWithTagMapping leftNode tagMapping
		rewrittenRight = rewriteTermWithTagMapping rightNode tagMapping
	in
		(Branch (TermData nodeTag rewrittenLeft rewrittenRight))

rewriteTermWithTagMapping (LeafTag tag) tagMapping
	-- if it is contained it gets rewritten
	| Map.member tag tagMapping = case (Map.lookup tag tagMapping) of
		Just lookedupVariabledata -> (LeafVariable lookedupVariabledata)
		-- other case not handled because it is unnecessary
	-- if it is not contained just the orginal LeafTag is returned
	| True = (LeafTag tag)

-- a variable is forbidden
-- because the terms of items are variable-free
-- rewriteTermWithTagMapping (LeafVariable variableData) _ = (LeafVariable variableData)


-- TODO Definition 17 (Recursion)

-- Definition 18 (Memorization)
memorize :: Item -> Maybe AxiomData
memorize (Item tag t1 t2 utility)
	| utility > 0 = Just (AxiomData tag t1 t2)
	| True = Nothing





-- data for handling of the result of tryToAssignTermNodeToVariables
data MatchResult a =
	  MatchError 
	| Success a
	| MultipleValuesForKey
	| TypeCheckFailure -- the Type checking A-Computation was not successful
		deriving (Show)

data SideTwist = RightLeft | LeftRight


data Agent = Agent {
	agentT :: Set.Set AxiomData,
	c :: Set.Set TermNode,
	workingMemoryCapacity :: Int, -- w
	assimilationCapacity :: Int, -- L
	accommodationCapacity :: Int -- D
}

-- Definition 19
-- Occam Function
occamFunction :: Random.StdGen -> [Item] -> Agent -> (Agent, [AxiomData], [VariableData], [TermNode], [(AxiomData, Int              , Int    )], Set.Set TermNode, Set.Set AxiomData)
occamFunction random ipIn (Agent agentT agentC workingMemoryCapacity assimilationCapacity accommodationCapacity) =
	let
		(random2, randomT1) = Random.split random
		(random3, randomT2) = Random.split randomT1
		(random4, randomT3) = Random.split randomT2

		-- first we calculate the set of variables in agentC
		setOfVariables = getAllVariablesAsSetFromTerms agentC

		subtreesFromIn = getAllSubtermFromItems ipIn

		-- replace one ore many leaf nodes of the subtrees by variables setOfVariables
		zetaAsList = replaceOneOrMoreLeafNodesByRandomVariableFromSet subtreesFromIn setOfVariables random3
		zetaAsSet = Set.fromList zetaAsList

		-- union for the new agentC agentC and zeta
		nextAgentC = Set.union agentC zetaAsSet


		-- form the crossover
		-- as described we need to crosover nextAgentC
		-- the trouble is that it need to be translated to axioms
		-- we implement here a conversion from the crossover term to the axiom as follows
		-- create eqal axiom for (left) input term and result term of the crossover
		-- create type axiom for (left) input term and result term of the crossover
		-- then filter for the complexity of the resulting axioms
		delta1 = Set.fromList (crossoverAndConvertToAxioms accommodationCapacity (Set.elems nextAgentC))

		-- abstract all items of In and union
		abstractedInIn = abstractForListAsSet ipIn
		delta2 = Set.union delta1 abstractedInIn

		-- union with recursion from In
		-- TODO
		delta3 = delta2

		-- union with all axiom obtained from items In my memorization
		delta4 = Set.union delta3 (memorizeFromListAndGetResultAsSet ipIn)


		-- now we form the set deltaTick
		deltaTick = filterAxiomSetByAdditionalConditions [areAllVariablesApearingOnBothSidesInAxiom, areNoVariablesAppearingInAxiom] delta4

		agentWithNextC = Agent agentT nextAgentC workingMemoryCapacity assimilationCapacity accommodationCapacity
		(deltaTickTick, debug0) = calcBestNCandidatesOutOfSetOnItems agentWithNextC random4 deltaTick ipIn

		nextAgentT = Set.union agentT deltaTickTick
		resultAgent = Agent nextAgentT nextAgentC workingMemoryCapacity assimilationCapacity accommodationCapacity
	in
		(resultAgent, Set.toList (memorizeFromListAndGetResultAsSet ipIn), Set.toList setOfVariables, subtreesFromIn, debug0, nextAgentC, delta1)
	where
		getAllSubtermFromItems :: [Item] -> [TermNode]
		getAllSubtermFromItems items =
				Set.toList $ Set.unions $ List.map getAllSubtermsOfItem items
			where
				getAllSubtermsOfItem :: Item -> Set.Set TermNode
				getAllSubtermsOfItem (Item _ t1 t2 _) = Set.union (getAllSubtermAsSet t1) (getAllSubtermAsSet t2)


		filterAxiomSetByAdditionalConditions :: [(AxiomData -> Bool)] -> Set.Set AxiomData -> Set.Set AxiomData
		filterAxiomSetByAdditionalConditions filterFunctions axiomSet =
			let
				axiomsAsList = Set.toList axiomSet
				filteredAxiomsAsList = filter anyFilterHelper axiomsAsList
				filteredAxiomsAsSet = Set.fromList filteredAxiomsAsList
			in
				filteredAxiomsAsSet
			where
				-- returns true if any filter returns true
				anyFilterHelper :: AxiomData -> Bool
				anyFilterHelper axiom = List.any (\appliedFilterFunction -> appliedFilterFunction axiom) filterFunctions

		-- helper
		-- used for filtering the axioms
		areAllVariablesApearingOnBothSidesInAxiom :: AxiomData -> Bool
		areAllVariablesApearingOnBothSidesInAxiom (AxiomData _ t tTick) =
			let
				-- get all indices of the leafs which are variables
				indicesOfVariablesInT = getIndicesOfLeafNodesInTreeWithFilter t isTermLeafAVariable
				-- fetch all variables in T as list
				variablesInTAsList = map (\index -> takeNthFromTree index t) indicesOfVariablesInT
				-- convert to set
				variablesInTAsSet = Set.fromList variablesInTAsList

				-- do the same for tTick
				indicesOfVariablesInTTick = getIndicesOfLeafNodesInTreeWithFilter tTick isTermLeafAVariable
				variablesInTTickAsList = map (\index -> takeNthFromTree index tTick) indicesOfVariablesInTTick
				variablesInTTickAsSet = Set.fromList variablesInTTickAsList

				-- now we need to intersect the sets and look if no surive
				intersectedVariables = Set.intersection variablesInTAsSet variablesInTTickAsSet
				areAllVariablesApearingOnBothSides = Set.size intersectedVariables == 0
			in
				areAllVariablesApearingOnBothSides
			where
				isTermLeafAVariable :: TermNode -> Bool
				isTermLeafAVariable (LeafVariable _) = True
				isTermLeafAVariable _ = False

		-- helper
		-- used for filtering the axioms
		areNoVariablesAppearingInAxiom :: AxiomData -> Bool
		areNoVariablesAppearingInAxiom (AxiomData _ t tTick) = (not (areVariablesAppearingInTerm t)) && (not (areVariablesAppearingInTerm tTick))


		memorizeFromListAndGetResultAsSet :: [Item] -> Set.Set AxiomData
		memorizeFromListAndGetResultAsSet items = Set.fromList (memorizeFromList items)

		memorizeFromList :: [Item] -> [AxiomData]
		memorizeFromList items =
			let
				listWithMaybeAxioms = map memorize items
				-- filter
				listWithFilteredMaybeAxioms = filter filterHelper listWithMaybeAxioms
				listWithAxioms = map mapHelper listWithFilteredMaybeAxioms
			in
				listWithAxioms
			where
				filterHelper :: Maybe AxiomData -> Bool
				filterHelper (Just _) = True
				filterHelper Nothing = False

				mapHelper :: Maybe AxiomData -> AxiomData
				mapHelper (Just axiom) = axiom

		crossoverAndConvertToAxioms :: Int                   -> [TermNode] -> [AxiomData]
		crossoverAndConvertToAxioms    accommodationCapacity    terms      =
			let
				allTermsCrossedOverAsSet = excessiveCrossover terms (accommodationCapacity-1)
				allTermsCrossedOverAsList = Set.toList allTermsCrossedOverAsSet

				unfilteredAxioms = List.concat $ List.concat [
									(map (\leftTerm -> makeAxiomsOfTerms Equi leftTerm allTermsCrossedOverAsList) terms),
									(map (\leftTerm -> makeAxiomsOfTerms Type leftTerm allTermsCrossedOverAsList) terms)
									]
				
				filteredList = List.filter filterForMaximalAccommodationCapacity unfilteredAxioms

				-----------------------------------------------------------------------------------------------
				-----------------------------------------------------------------------------------------------
				-----------------------------------------------------------------------------------------------

				--combinationsOfTerms = combinatorialProduct terms terms

				--map (\x -> crossoverExcessive x)

				--crossoverResult = zipWith (\x random -> crossover random (fst x) (snd x)) combinationsOfTerms infiniteListOfRandomGenerators
				
				-- convert to axioms
				--  we zip because for the axiom we need the "orginal" term and the result of the crossover
				--zipedCombinationAndCrossover = zip combinationsOfTerms crossoverResult
				--result = map (\x -> AxiomData Equi (fst (fst x)) (snd x)) zipedCombinationAndCrossover
			in
				filteredList
			where
				makeAxiomsOfTerms :: AxiomTag -> TermNode -> [TermNode] -> [AxiomData]
				makeAxiomsOfTerms    tag         right        leftList  =
					let
						axiomsWithTag = (map (createAxiomWithTag RightLeft) (combinatorialProduct [right] leftList)) ++ 
						                (map (createAxiomWithTag LeftRight) (combinatorialProduct [right] leftList))
					in
						axiomsWithTag
					where
						createAxiomWithTag :: SideTwist -> (TermNode, TermNode) -> AxiomData
						createAxiomWithTag RightLeft (right, left) = AxiomData tag left right
						createAxiomWithTag LeftRight (left, right) = AxiomData tag left right

				excessiveCrossoverOfTermsAsSet :: [TermNode] -> Set.Set TermNode
				excessiveCrossoverOfTermsAsSet terms =
					let
						result = Set.unions $ map excessiveCrossoverOfTuple $ combinatorialProduct terms terms
					in
						result
					where
						excessiveCrossoverOfTuple :: (TermNode, TermNode) -> Set.Set TermNode
						excessiveCrossoverOfTuple (a, b) = crossoverExcessive a b

				filterForMaximalAccommodationCapacity :: AxiomData -> Bool
				filterForMaximalAccommodationCapacity axiom = getTermSizeForAxiom axiom <= accommodationCapacity


		-- helper function
		abstractForListAsSet :: [Item] -> Set.Set AxiomData
		abstractForListAsSet items = 
			let 
				(result, _) = List.mapAccumL mapAccuFunction Set.empty items
			in
				result
			where
				-- Int is only a dummy
				mapAccuFunction :: Set.Set AxiomData -> Item -> (Set.Set AxiomData, Int)
				mapAccuFunction resultSet iterationItem =
					let
						abstractionResult = tryAbstraction iterationItem
					in case abstractionResult of
						Just resultAxiom -> (Set.insert resultAxiom resultSet, 0)
						Nothing -> (resultSet, 0)

		-- helper function
		-- NOTE< Set.size setOfVariables == 0 doesn't need any special treetment >
		replaceOneOrMoreLeafNodesByRandomVariableFromSet :: [TermNode] -> Set.Set VariableData -> Random.StdGen -> [TermNode]
		replaceOneOrMoreLeafNodesByRandomVariableFromSet subtreesFromIn setOfVariables random =
			let
				-- convert it to a list
				-- this saves some unnecessary conversions in the inner functions
				setOfVariablesAsList = Set.elems setOfVariables
				infiniteListOfRandomGenerators = List.iterate (\x -> snd (Random.split x)) random
			in
				map mapHelperFunction (List.zip3 subtreesFromIn infiniteListOfRandomGenerators (List.repeat setOfVariablesAsList))
			where
				mapHelperFunction :: (TermNode, Random.StdGen, [VariableData]) -> TermNode
				mapHelperFunction (term, random, setOfVariablesAsList) = replaceOneOrMoreLeafNodesByRandomVariableFromSetForTermNode term setOfVariablesAsList random

				replaceOneOrMoreLeafNodesByRandomVariableFromSetForTermNode :: TermNode -> [VariableData] -> Random.StdGen -> TermNode
				replaceOneOrMoreLeafNodesByRandomVariableFromSetForTermNode term listOfVariables random =
					let
						numberOfLeafnodes = countLeafNodesInTree term
						(countOfReplacedLeafnodesWithVariables, random2) = Random.randomR (1, numberOfLeafnodes-1) random
						indicesOfLeafnodes = getIndicesOfLeafNodesInTree term
						chosenIndicesOfLeafNodes = choseRandomElementsFromList indicesOfLeafnodes countOfReplacedLeafnodesWithVariables random2

						-- generator for an infinite list of different random number generators
						infiniteListOfRandomGenerators = List.iterate (\x -> snd (Random.split x)) random

						-- iterate over all chosenIndicesOfLeafNodes and call replaceSubtermWithRandomVariableFromSet
						-- finaly return the result
						(resultTerm, _) = List.mapAccumL mapAccuFunction term (zip chosenIndicesOfLeafNodes infiniteListOfRandomGenerators)
					in
						resultTerm
					where
						-- helper function which is used for mapAccumL
						-- gets as parameters
						-- ( 1)  current Term Tree Node
						-- ( 2)  tuple of (Index in Term of the replacement, RNG)
						--
						-- result is the Term where it got replaced plus a dummy variable
						mapAccuFunction :: TermNode -> (Int, Random.StdGen) -> (TermNode, Int)
						mapAccuFunction term (index, random) =
							let
								termWithReplacedLeaf = replaceSubtermWithRandomVariableFromSet term index listOfVariables random
							in
								(termWithReplacedLeaf, 0)

						replaceSubtermWithRandomVariableFromSet :: TermNode -> Int -> [VariableData] -> Random.StdGen -> TermNode
						replaceSubtermWithRandomVariableFromSet term index listOfVariables random
						    | List.length listOfVariables == 0 = term
							| True = 
								let
									-- choose random Variable from set
									numberOfElementsInVariableData = List.length listOfVariables
									(chosenVariableIndex, _) = Random.randomR (0, numberOfElementsInVariableData-1) random
									chosenVariableData = listOfVariables !! chosenVariableIndex

									resultTerm = replaceNthInTree index (LeafVariable chosenVariableData) term
								in
									resultTerm

		-- does the important work of the occam function
		-- choses the best n candidates based on the priority ordering outlined in the paper
		-- DEBUG result is actually only the set, not the tuple, tuple is only returned for debugging purposes
		calcBestNCandidatesOutOfSetOnItems :: Agent -> Random.StdGen -> Set.Set AxiomData        -> [Item] -> (Set.Set AxiomData, [(AxiomData, Int              , Int    )])
		calcBestNCandidatesOutOfSetOnItems    agent    random           potentialCandidateAxioms    items  =
			let
				numberOfMaximalCandidates = 3

				(random0, random1) = Random.split random

				resultCandidatesAsList = calcBestNCandidatesOutOfSetInternal agent numberOfMaximalCandidates random0 potentialCandidateAxioms [] items

				-- sort resultCandidatesAsList by performance
				sortedPotentialCandidatesWithRating = rateAxioms agent [] random1 items resultCandidatesAsList
				
				-- pick top n candidates
				topNCandidatesWithRating = List.take numberOfMaximalCandidates sortedPotentialCandidatesWithRating

				resultAsList = getAxiomsOfTupleList topNCandidatesWithRating
				resultAsSet = Set.fromList resultAsList
			in
				(resultAsSet, sortedPotentialCandidatesWithRating)
			where
				-- rate and sort descending
				rateAxioms :: Agent -> [AxiomData]           -> Random.StdGen -> [Item] -> [AxiomData] -> [(AxiomData, Int              , Int    )]
				rateAxioms    agent    allreadyDefinedAxioms    random           items     axioms      =
					let
						unorderedListOfAxiomsAndPerformanceRating = getListOfPerformancesOfAxioms agent allreadyDefinedAxioms random items axioms
						-- ordering matches with unorderedListOfAxiomsAndPerformanceRating
						termsizesOfTheorems = List.map (\x -> getTermSizeOfTheory (allreadyDefinedAxioms ++ [(fst x)])) unorderedListOfAxiomsAndPerformanceRating

						-- TODO< calculate other criteria and adapt the zip and sort functionality >
						-- * maximum number of variable tokens
						-- * minimal number of variable types
						-- * lexographical as small as possible

						zipedList = List.zip unorderedListOfAxiomsAndPerformanceRating termsizesOfTheorems
						transformedTupleList = List.map transform zipedList

						-- sort it by the many criteria
						sortedBundledAxiomWithPerformance = List.reverse (List.sortBy sortFunction transformedTupleList)
					in
						sortedBundledAxiomWithPerformance
					where
						-- calculates the performances of the agent with each axiom
						-- result - list of : tuple (added axiom, performance rating of allreadyDefinedAxioms and the added axiom on items)
						getListOfPerformancesOfAxioms :: Agent -> [AxiomData]           -> Random.StdGen -> [Item] -> [AxiomData] -> [(AxiomData, Int)]
						getListOfPerformancesOfAxioms    agent    allreadyDefinedAxioms    random           items     axioms      =
							let
								infiniteListOfRandomGenerators = List.iterate (\x -> snd (Random.split x)) random

								axiomsWithRandomGenerators = List.zip axioms infiniteListOfRandomGenerators

								-- calculate the performances we would get if we add one axiom to all axioms and do evaluate the performance
								performancesOfAxioms = List.map (calcPerformanceOfAgentWithAdditionalAxiomsPlusAxiomWithRandom agent items allreadyDefinedAxioms) axiomsWithRandomGenerators

								-- bundle input with performance
								bundledAxiomWithPerformance = List.zip axioms performancesOfAxioms
							in
								bundledAxiomWithPerformance
							where
								calcPerformanceOfAgentWithAdditionalAxiomsPlusAxiomWithRandom :: Agent -> [Item] -> [AxiomData]           -> (AxiomData, Random.StdGen) -> Int
								calcPerformanceOfAgentWithAdditionalAxiomsPlusAxiomWithRandom    agent    items     allreadyDefinedAxioms    (additionalAxiom, random)  =
									calcPerformanceOfAgentWithAdditionalAxiomsPlusAxiom agent random items allreadyDefinedAxioms additionalAxiom

								calcPerformanceOfAgentWithAdditionalAxiomsPlusAxiom :: Agent -> Random.StdGen -> [Item] -> [AxiomData]           -> AxiomData       -> Int
								calcPerformanceOfAgentWithAdditionalAxiomsPlusAxiom    agent    random           items     allreadyDefinedAxioms    additionalAxiom =
									let
										allAxioms = allreadyDefinedAxioms ++ [additionalAxiom]
									in
										calcPerformanceOfAgentWithAdditionalAxioms agent random items allAxioms

								calcPerformanceOfAgentWithAdditionalAxioms :: Agent                                                                                                 -> Random.StdGen -> [Item] -> [AxiomData]      -> Int
								calcPerformanceOfAgentWithAdditionalAxioms    (Agent agentT agentC agentWorkingMemoryCapacity agentAssimilationCapacity agentAccommodationCapacity)    random           items     additionalAxioms =
									let
										modifiedAgentT = Set.union agentT (Set.fromList additionalAxioms)
										modifiedAgent = Agent modifiedAgentT agentC agentWorkingMemoryCapacity agentAssimilationCapacity agentAccommodationCapacity
									in
										calcPerformanceSumAStar modifiedAgent items

						transform :: ((AxiomData, Int), Int             ) -> (AxiomData, Int               , Int)
						transform    ((axiom, rating) , termsizeOfTheory) =  (axiom    , termsizeOfTheory  , rating)

						sortFunction :: (AxiomData, Int               , Int   ) -> (AxiomData, Int               , Int   ) -> Ordering
						sortFunction    (_    , termsizeOfTheoryL  , ratingL)    (_    , termsizeOfTheoryR  , ratingR)
							| ratingL > ratingR = GT
							| termsizeOfTheoryL < termsizeOfTheoryR = GT
							| ratingL == ratingR && termsizeOfTheoryL == termsizeOfTheoryR = EQ
							| True = LT

				getAxiomsOfTupleList :: [(AxiomData, Int, Int)] -> [AxiomData]
				getAxiomsOfTupleList    tupleList               =
					let
						result = List.map mapTupleToAxiom tupleList
					in
						result
					where
						mapTupleToAxiom (axiom, _, _) = axiom


				-- chooses zero or more candidates and
				-- * remove them from the potentialCandidateAxioms set
				-- * add them to the result allreadyChosenCandidates
				calcBestNCandidatesOutOfSetInternal :: Agent -> Int              -> Random.StdGen -> Set.Set AxiomData        -> [AxiomData]              -> [Item] -> [AxiomData]
				calcBestNCandidatesOutOfSetInternal    _        0                   random           _                           allreadyChosenCandidates    _      = allreadyChosenCandidates
				calcBestNCandidatesOutOfSetInternal    agent    remainingChoices    random           potentialCandidateAxioms    allreadyChosenCandidates    items  =
					let
						(random0, random1) = Random.split random

						chosenTopCandidates = getTopnAdditionalAxioms agent allreadyChosenCandidates random0 items (Set.toList potentialCandidateAxioms)

						-- remove the candidates from the set
						newPotentialCandidateAxioms = Set.difference potentialCandidateAxioms (Set.fromList chosenTopCandidates)

						resultOfRecursiveCall = calcBestNCandidatesOutOfSetInternal agent (remainingChoices-1) random1 newPotentialCandidateAxioms (allreadyChosenCandidates ++ chosenTopCandidates) items
					in
						resultOfRecursiveCall ++ chosenTopCandidates
					where
						-- returns top n best candidates which are rated equal
						-- this is done because it fairs up the cometition
						getTopnAdditionalAxioms :: Agent -> [AxiomData]           -> Random.StdGen -> [Item] -> [AxiomData] -> [AxiomData]
						getTopnAdditionalAxioms    agent    allreadyDefinedAxioms    random           items     axioms      =
							let
								sortedBundledAxiomWithPerformance = rateAxioms agent allreadyDefinedAxioms random items axioms

								-- take top n
								resultCandidatesTuples = takeTopNCandidates sortedBundledAxiomWithPerformance
								resultCandidates = getAxiomsOfTupleList resultCandidatesTuples
							in
								resultCandidates
							where
								-- returns the top n candidates which are equal
								-- handles also the case for no candidates
								takeTopNCandidates :: [(AxiomData, Int, Int)] -> [(AxiomData, Int, Int)]
								takeTopNCandidates [] = []
								takeTopNCandidates candidates =
									let
										topCandidate = List.head candidates
										resultCandidates = List.takeWhile (isRatingEqual topCandidate) candidates
									in
										resultCandidates
									where
										isRatingEqual :: (AxiomData, Int              , Int    ) -> (AxiomData, Int              , Int    ) -> Bool
										isRatingEqual    (_        , termsizeOfTheoryL, ratingL)    (_        , termsizeOfTheoryR, ratingR) = termsizeOfTheoryL == termsizeOfTheoryR && ratingL == ratingR

		-- returns all variables in allTermsAsSet
		getAllVariablesAsSetFromTerms :: Set.Set TermNode -> Set.Set VariableData
		getAllVariablesAsSetFromTerms allTermsAsSet =
			let
				allTermsAsList = Set.elems allTermsAsSet
				listOfSetsOfVariablesFromParameter = map getAllVariablesAsSetFromTerm allTermsAsList
				result = Set.unions listOfSetsOfVariablesFromParameter
			in
				result
			where
				getAllVariablesAsSetFromTerm :: TermNode -> Set.Set VariableData
				getAllVariablesAsSetFromTerm (LeafTag _) = Set.empty
				getAllVariablesAsSetFromTerm (LeafVariable variable) = Set.fromList [variable]

				getAllVariablesAsSetFromTerm (Branch (TermData _ leftNode rightNode)) =
					let
						setOfLeft = getAllVariablesAsSetFromTerm leftNode
						setOfRight = getAllVariablesAsSetFromTerm rightNode
					in
						Set.union setOfLeft setOfRight

-- TODO< rip out random crap >
modifiedOccamFunction :: Random.StdGen -> [Item] -> Agent -> (Agent, [(AxiomData, Int, Int)], Set.Set AxiomData)
modifiedOccamFunction    random           ipIn      agent =
	let
		(Agent agentT agentC workingMemoryCapacity assimilationCapacity accommodationCapacity) = agent

		-- TODO< remove random >
		(random3, randomT1) = Random.split random

		-- first we calculate the set of variables in agentC
		setOfVariables = getAllVariablesAsSetFromTerms agentC

		subtreesFromIn = getAllSubtermFromItems ipIn

		-- replace one ore many leaf nodes of the subtrees by variables setOfVariables
		zetaAsList = replaceOneOrMoreLeafNodesByRandomVariableFromSet subtreesFromIn setOfVariables random3
		zetaAsSet = Set.fromList zetaAsList

		-- union for the new agentC agentC and zeta
		nextAgentC = Set.union agentC zetaAsSet


		-- functions which will be executed by tryToFindOptimalCandidatesForDeltaTickTick in succession, if it failed to find any axioms which can be candidates
		appliedFunctionsForFormingOfDeltaTickTick = [
			forDeltaTickTickCrossover accommodationCapacity,
			-- TODO abstraction
			-- TODO recursion
			forDeltaTickTickMemorisation ipIn
			]

		-- DEBUG
		debugAxiomsAfterCrossover = rateAxioms agent ipIn [] (Set.toList $ forDeltaTickTickCrossover accommodationCapacity (Set.toList nextAgentC))

		-- Maybe [AxiomData]
		deltaTickTickAxioms = tryToFindOptimalCandidatesForDeltaTickTick agent ipIn (Set.toList nextAgentC) appliedFunctionsForFormingOfDeltaTickTick

		agentTplus1 = Set.union agentT deltaTickTickAxioms
		resultAgent = (Agent agentTplus1 nextAgentC workingMemoryCapacity assimilationCapacity accommodationCapacity)
	in
		(resultAgent, debugAxiomsAfterCrossover, deltaTickTickAxioms)
	where
		-- this function is used to apply the different kinds of transformations in succession
		-- so it tries the next kind of transformation if all previous ones failed, etc

		-- this function does
		-- for each function in the array with functions
		-- * apply the function to the input terms
		-- * calculate the performance of the axioms
		-- * try to up to 3 top candidates (if they are equal)

		-- * if the function does return a result put the result out
		-- * else try the next function in the list
		--
		-- if all functions fail Nothing is returned
		tryToFindOptimalCandidatesForDeltaTickTick :: Agent -> [Item] -> [TermNode] -> [[TermNode] -> Set.Set AxiomData] -> Set.Set AxiomData
		tryToFindOptimalCandidatesForDeltaTickTick agent items inputTerms functions =
			let
				internalResult = tryToFindOptimalCandidatesForDeltaTickTickInternal agent items inputTerms functions
			in case internalResult of
				Just axioms -> axioms
				Nothing -> Set.empty
			where
				tryToFindOptimalCandidatesForDeltaTickTickInternal :: Agent -> [Item] -> [TermNode] -> [[TermNode] -> Set.Set AxiomData] -> Maybe (Set.Set AxiomData)
				
				-- if no more functions are left we return nothing because the search failed
				tryToFindOptimalCandidatesForDeltaTickTickInternal _ _ _ [] = Nothing

				tryToFindOptimalCandidatesForDeltaTickTickInternal agent items inputTerms (currentFunction:otherFunctions) =
					let
						numberOfMaximalCandidates = 3

						workingAxioms = currentFunction inputTerms

						-- PAPERQUOTE< form the set deltaTick, whose axioms satisfy a few additional conditions: e.g. all variables must appear in both terms of the axioms, or not at all >
						deltaTick2 = filterAxiomSetByAdditionalConditions [areAllVariablesApearingOnBothSidesInAxiom, areNoVariablesAppearingInAxiom] workingAxioms

						-- for testing
						-- 20 goes
						-- 21 hangs
						-- 25 hangs
						deltaTick = deltaTick2 -- Set.fromList [(AxiomData Equi (LeafTag "0")       (Branch (TermData "#" (LeafTag "Digit") (LeafTag "1"))))]-----INVALID Set.fromList $ List.take 21 $ Set.toList deltaTick2

						deltaTickDebug = Set.fromList $ List.take 21 $ Set.toList deltaTick2

						ratedAxioms = rateAxioms agent items [] (Set.toList deltaTickDebug)

						-- sort it by the many criteria
						sortedRatedAxioms = List.reverse (List.sortBy sortFunction ratedAxioms)
						-- * Performance
						-- * Size/Complexity
						-- TODO< calculate other criteria and adapt the zip and sort functionality >
						-- * maximum number of variable tokens
						-- * minimal number of variable types
						-- * lexographical as small as possible

						-- try to find optimal candidates
						-- (taking first, take tuple of ratings, take all others who have the same rating, limit it to 3)
						topnEqualCandidatesAsTuple = takeTopNCandidates sortedRatedAxioms
						topnCandidatesAsTuple = List.take numberOfMaximalCandidates topnEqualCandidatesAsTuple
						topnCandidates = getAxiomsOfTupleList topnCandidatesAsTuple

						-- if this fails we continue with the otherFunctions (recursivly)
					in
						if (List.length topnCandidates) == 0
						then
							tryToFindOptimalCandidatesForDeltaTickTickInternal agent items inputTerms otherFunctions
						else
							Just $ Set.fromList topnCandidates
					where
						-- MOVEHERE rateAxioms

						sortFunction :: (AxiomData, Int           , Int        ) -> (AxiomData, Int         , Int        ) -> Ordering
						sortFunction    (_        , performanceL  , complexityL)    (_        , performanceR, complexityR)
							| performanceL > performanceR = GT
							| complexityL < complexityR = GT
							| performanceL == performanceR && complexityL == complexityR = EQ
							| True = LT

						-- returns the top n candidates which are equal
						-- handles also the case for no candidates
						takeTopNCandidates :: [(AxiomData, Int, Int)] -> [(AxiomData, Int, Int)]
						takeTopNCandidates [] = []
						takeTopNCandidates candidates =
							let
								topCandidate = List.head candidates
								resultCandidates = List.takeWhile (isRatingEqual topCandidate) candidates
							in
								resultCandidates
							where
								isRatingEqual :: (AxiomData, Int         , Int        ) -> (AxiomData, Int         , Int        ) -> Bool
								isRatingEqual    (_        , performanceL, complexityL)    (_        , performanceR, complexityR) = performanceL == performanceR && complexityL == complexityR

						getAxiomsOfTupleList :: [(AxiomData, Int, Int)] -> [AxiomData]
						getAxiomsOfTupleList    tupleList               =
							let
								result = List.map mapTupleToAxiom tupleList
							in
								result
							where
								mapTupleToAxiom (axiom, _, _) = axiom

						----------------------------------------------
						-- filtering main function and filterfunctions

						filterAxiomSetByAdditionalConditions :: [(AxiomData -> Bool)] -> Set.Set AxiomData -> Set.Set AxiomData
						filterAxiomSetByAdditionalConditions filterFunctions axiomSet =
							let
								axiomsAsList = Set.toList axiomSet
								filteredAxiomsAsList = filter anyFilterHelper axiomsAsList
								filteredAxiomsAsSet = Set.fromList filteredAxiomsAsList
							in
								filteredAxiomsAsSet
							where
								-- returns true if any filter returns true
								anyFilterHelper :: AxiomData -> Bool
								anyFilterHelper axiom = List.any (\appliedFilterFunction -> appliedFilterFunction axiom) filterFunctions


						areAllVariablesApearingOnBothSidesInAxiom :: AxiomData -> Bool
						areAllVariablesApearingOnBothSidesInAxiom (AxiomData _ t tTick) =
							let
								-- get all indices of the leafs which are variables
								indicesOfVariablesInT = getIndicesOfLeafNodesInTreeWithFilter t isTermLeafAVariable
								-- fetch all variables in T as list
								variablesInTAsList = map (\index -> takeNthFromTree index t) indicesOfVariablesInT
								-- convert to set
								variablesInTAsSet = Set.fromList variablesInTAsList

								-- do the same for tTick
								indicesOfVariablesInTTick = getIndicesOfLeafNodesInTreeWithFilter tTick isTermLeafAVariable
								variablesInTTickAsList = map (\index -> takeNthFromTree index tTick) indicesOfVariablesInTTick
								variablesInTTickAsSet = Set.fromList variablesInTTickAsList

								-- now we need to intersect the sets and look if no surive
								intersectedVariables = Set.intersection variablesInTAsSet variablesInTTickAsSet
								areAllVariablesApearingOnBothSides = Set.size intersectedVariables == 0
							in
								areAllVariablesApearingOnBothSides
							where
								isTermLeafAVariable :: TermNode -> Bool
								isTermLeafAVariable (LeafVariable _) = True
								isTermLeafAVariable _ = False

						areNoVariablesAppearingInAxiom :: AxiomData -> Bool
						areNoVariablesAppearingInAxiom (AxiomData _ t tTick) = (not (areVariablesAppearingInTerm t)) && (not (areVariablesAppearingInTerm tTick))



		---------------------------------------------------------------
		-- Functions used by tryToFindOptimalCandidatesForDeltaTickTick
		-- which do try to find the best candidates for deltaTickTick

		forDeltaTickTickCrossover :: Int -> [TermNode] -> Set.Set AxiomData
		forDeltaTickTickCrossover accommodationCapacity nextAgentC =
			let
				-- form the crossover
				-- as described we need to crosover nextAgentC
				-- the trouble is that it need to be translated to axioms
				-- we implement here a conversion from the crossover term to the axiom as follows
				-- create eqal axiom for (left) input term and result term of the crossover
				-- create type axiom for (left) input term and result term of the crossover
				-- then filter for the complexity of the resulting axioms
				
				-- TODO< apply filter as described in the paper >
				crossoverResultAxioms = crossoverAndConvertToAxioms accommodationCapacity nextAgentC

				
				-- paper "iterates over lenths of condidates (1 to D)"
				-- PAPER ASK< maybe they mean that for the crossover it should iterate over the combinates of the crossover >
				-- NOTE< we don't have to sort here by anything because tryToFindOptimalCandidatesForDeltaTickTick does it allready >

				-- TODO< crossoverResultAxiomsSorted for deltaTick : filter it according to transistion rule from delta to deltaTick ? >

				crossoverResultAfterFilter = List.filter filterIsTransformation crossoverResultAxioms
				
			in
				Set.fromList crossoverResultAfterFilter
			where
				crossoverAndConvertToAxioms :: Int                   -> [TermNode] -> [AxiomData]
				crossoverAndConvertToAxioms    accommodationCapacity    terms      =
					let
						allTermsCrossedOverAsSet = templatedCrossover terms
						allTermsCrossedOverAsList = Set.toList allTermsCrossedOverAsSet

						unfilteredAxioms = List.concat $ List.concat [
											(map (\leftTerm -> makeAxiomsOfTerms Equi leftTerm allTermsCrossedOverAsList) terms),
											(map (\leftTerm -> makeAxiomsOfTerms Type leftTerm allTermsCrossedOverAsList) terms)
											]
						
						filteredList = List.filter filterForMaximalAccommodationCapacity unfilteredAxioms
					in
						filteredList
					where
						makeAxiomsOfTerms :: AxiomTag -> TermNode -> [TermNode] -> [AxiomData]
						makeAxiomsOfTerms    tag         right        leftList  =
							let
								axiomsWithTag = (map (createAxiomWithTag RightLeft) (combinatorialProduct [right] leftList)) ++ 
								                (map (createAxiomWithTag LeftRight) (combinatorialProduct [right] leftList))
							in
								axiomsWithTag
							where
								createAxiomWithTag :: SideTwist -> (TermNode, TermNode) -> AxiomData
								createAxiomWithTag RightLeft (right, left) = AxiomData tag left right
								createAxiomWithTag LeftRight (left, right) = AxiomData tag left right

						excessiveCrossoverOfTermsAsSet :: [TermNode] -> Set.Set TermNode
						excessiveCrossoverOfTermsAsSet terms =
							let
								result = Set.unions $ map excessiveCrossoverOfTuple $ combinatorialProduct terms terms
							in
								result
							where
								excessiveCrossoverOfTuple :: (TermNode, TermNode) -> Set.Set TermNode
								excessiveCrossoverOfTuple (a, b) = crossoverExcessive a b

						filterForMaximalAccommodationCapacity :: AxiomData -> Bool
						filterForMaximalAccommodationCapacity axiom = getTermSizeForAxiom axiom <= accommodationCapacity

				filterIsTransformation :: AxiomData -> Bool
				filterIsTransformation (AxiomData _ t tTick) = not (t == tTick)

		forDeltaTickTickMemorisation :: [Item] -> [TermNode] -> Set.Set AxiomData
		forDeltaTickTickMemorisation items nextAgentC = Set.fromList $ memorizeFromList items
			where
				memorizeFromList :: [Item] -> [AxiomData]
				memorizeFromList items =
					let
						listWithMaybeAxioms = map memorize items
						-- filter
						listWithFilteredMaybeAxioms = filter filterHelper listWithMaybeAxioms
						listWithAxioms = map mapHelper listWithFilteredMaybeAxioms
					in
						listWithAxioms
					where
						filterHelper :: Maybe AxiomData -> Bool
						filterHelper (Just _) = True
						filterHelper Nothing = False

						mapHelper :: Maybe AxiomData -> AxiomData
						mapHelper (Just axiom) = axiom



		-- returns all variables in allTermsAsSet
		getAllVariablesAsSetFromTerms :: Set.Set TermNode -> Set.Set VariableData
		getAllVariablesAsSetFromTerms allTermsAsSet =
			let
				allTermsAsList = Set.elems allTermsAsSet
				listOfSetsOfVariablesFromParameter = map getAllVariablesAsSetFromTerm allTermsAsList
				result = Set.unions listOfSetsOfVariablesFromParameter
			in
				result
			where
				getAllVariablesAsSetFromTerm :: TermNode -> Set.Set VariableData
				getAllVariablesAsSetFromTerm (LeafTag _) = Set.empty
				getAllVariablesAsSetFromTerm (LeafVariable variable) = Set.fromList [variable]

				getAllVariablesAsSetFromTerm (Branch (TermData _ leftNode rightNode)) =
					let
						setOfLeft = getAllVariablesAsSetFromTerm leftNode
						setOfRight = getAllVariablesAsSetFromTerm rightNode
					in
						Set.union setOfLeft setOfRight

		getAllSubtermFromItems :: [Item] -> [TermNode]
		getAllSubtermFromItems items =
				Set.toList $ Set.unions $ List.map getAllSubtermsOfItem items
			where
				getAllSubtermsOfItem :: Item -> Set.Set TermNode
				getAllSubtermsOfItem (Item _ t1 t2 _) = Set.union (getAllSubtermAsSet t1) (getAllSubtermAsSet t2)


		-- helper function
		-- NOTE< Set.size setOfVariables == 0 doesn't need any special treetment >
		replaceOneOrMoreLeafNodesByRandomVariableFromSet :: [TermNode] -> Set.Set VariableData -> Random.StdGen -> [TermNode]
		replaceOneOrMoreLeafNodesByRandomVariableFromSet subtreesFromIn setOfVariables random =
			let
				-- convert it to a list
				-- this saves some unnecessary conversions in the inner functions
				setOfVariablesAsList = Set.elems setOfVariables
				infiniteListOfRandomGenerators = List.iterate (\x -> snd (Random.split x)) random
			in
				map mapHelperFunction (List.zip3 subtreesFromIn infiniteListOfRandomGenerators (List.repeat setOfVariablesAsList))
			where
				mapHelperFunction :: (TermNode, Random.StdGen, [VariableData]) -> TermNode
				mapHelperFunction (term, random, setOfVariablesAsList) = replaceOneOrMoreLeafNodesByRandomVariableFromSetForTermNode term setOfVariablesAsList random

				replaceOneOrMoreLeafNodesByRandomVariableFromSetForTermNode :: TermNode -> [VariableData] -> Random.StdGen -> TermNode
				replaceOneOrMoreLeafNodesByRandomVariableFromSetForTermNode term listOfVariables random =
					let
						numberOfLeafnodes = countLeafNodesInTree term
						(countOfReplacedLeafnodesWithVariables, random2) = Random.randomR (1, numberOfLeafnodes-1) random
						indicesOfLeafnodes = getIndicesOfLeafNodesInTree term
						chosenIndicesOfLeafNodes = choseRandomElementsFromList indicesOfLeafnodes countOfReplacedLeafnodesWithVariables random2

						-- generator for an infinite list of different random number generators
						infiniteListOfRandomGenerators = List.iterate (\x -> snd (Random.split x)) random

						-- iterate over all chosenIndicesOfLeafNodes and call replaceSubtermWithRandomVariableFromSet
						-- finaly return the result
						(resultTerm, _) = List.mapAccumL mapAccuFunction term (zip chosenIndicesOfLeafNodes infiniteListOfRandomGenerators)
					in
						resultTerm
					where
						-- helper function which is used for mapAccumL
						-- gets as parameters
						-- ( 1)  current Term Tree Node
						-- ( 2)  tuple of (Index in Term of the replacement, RNG)
						--
						-- result is the Term where it got replaced plus a dummy variable
						mapAccuFunction :: TermNode -> (Int, Random.StdGen) -> (TermNode, Int)
						mapAccuFunction term (index, random) =
							let
								termWithReplacedLeaf = replaceSubtermWithRandomVariableFromSet term index listOfVariables random
							in
								(termWithReplacedLeaf, 0)

						replaceSubtermWithRandomVariableFromSet :: TermNode -> Int -> [VariableData] -> Random.StdGen -> TermNode
						replaceSubtermWithRandomVariableFromSet term index listOfVariables random
						    | List.length listOfVariables == 0 = term
							| True = 
								let
									-- choose random Variable from set
									numberOfElementsInVariableData = List.length listOfVariables
									(chosenVariableIndex, _) = Random.randomR (0, numberOfElementsInVariableData-1) random
									chosenVariableData = listOfVariables !! chosenVariableIndex

									resultTerm = replaceNthInTree index (LeafVariable chosenVariableData) term
								in
									resultTerm
















-- calculates various things of the axioms and maintains the order
-- * performance of the agent with each axiom
-- * length
-- TODO< more >
-- result - list of : tuple (added axiom, performance rating of allreadyDefinedAxioms and the added axiom on items, complexity of the axiom)
rateAxioms :: Agent -> [Item] -> [AxiomData]           -> [AxiomData] -> [(AxiomData, Int, Int)]
rateAxioms    agent    items     allreadyDefinedAxioms    axioms      =
	let
		-- calculate the performances we would get if we add one axiom to all axioms and do evaluate the performance
		ratedAxioms = List.map calculatePerformanceAndOtherRatingsOfAxiom axioms
	in
		ratedAxioms
	where
		calculatePerformanceAndOtherRatingsOfAxiom :: AxiomData -> (AxiomData, Int, Int)
		calculatePerformanceAndOtherRatingsOfAxiom axiom =
			let
				performanceOfAgentWithAxiom = calcPerformanceOfAgentWithAdditionalAxiomsPlusAxiom axiom
				complexityOfAxiom = getTermSizeForAxiom axiom
			in
				(axiom, performanceOfAgentWithAxiom, complexityOfAxiom)

		calcPerformanceOfAgentWithAdditionalAxiomsPlusAxiom :: AxiomData       -> Int
		calcPerformanceOfAgentWithAdditionalAxiomsPlusAxiom    additionalAxiom =
			let
				allAxioms = allreadyDefinedAxioms ++ [additionalAxiom]
			in
				calcPerformanceOfAgentWithAdditionalAxioms allAxioms

		calcPerformanceOfAgentWithAdditionalAxioms :: [AxiomData]      -> Int
		calcPerformanceOfAgentWithAdditionalAxioms    additionalAxioms =
			let
				(Agent agentT agentC agentWorkingMemoryCapacity agentAssimilationCapacity agentAccommodationCapacity) = agent

				modifiedAgentT = Set.union agentT (Set.fromList additionalAxioms)
				modifiedAgent = Agent modifiedAgentT agentC agentWorkingMemoryCapacity agentAssimilationCapacity agentAccommodationCapacity
			in
				calcPerformanceSumAStar modifiedAgent items

















-- misc helper
--                             list     numberOfElements    RNG
choseRandomElementsFromList :: [Int] -> Int              -> Random.StdGen -> [Int]
choseRandomElementsFromList _ 0 _ = []
choseRandomElementsFromList list numberOfElements randomParameter =
	let
		(random1, random2) = Random.split randomParameter
		(chosenElement, _) = Random.randomR (1, (List.length list) - 1) random1
		(newlist, element) = dropFromList list chosenElement
	in
		[element] ++ choseRandomElementsFromList newlist (numberOfElements-1) random2

-- helper
-- drops an element with the index from the list and returns the list without the element  plus the element
dropFromList :: (Num a) => [a] -> Int -> ([a], a)
dropFromList list index = 
	let
		(beforeSplitIndex, afterSplitIndex) = List.splitAt index list
		listWithoutElement = beforeSplitIndex ++ (List.tail afterSplitIndex)
		takenOutElement = List.head afterSplitIndex
	in 
		(listWithoutElement, takenOutElement)



-- helper for the outside
getStringOfAxiom :: AxiomData -> String
getStringOfAxiom (AxiomData tag t tTick) = show tag ++ " " ++ getStringOfTerm t ++ " " ++ getStringOfTerm tTick

getStringOfAxioms :: [AxiomData] -> String
getStringOfAxioms axioms =
	let
		stringsOfAxioms = map getStringOfAxiom axioms
	in
		List.concatMap (\x -> x ++ "\n") stringsOfAxioms

getStringOfItem :: Item -> String
getStringOfItem (Item tag t1 t2 utility) = "(" ++ show tag ++ " " ++ getStringOfTerm t1 ++ " " ++ getStringOfTerm t2 ++ " " ++ show utility ++ ")"

getStringOfItems :: [Item] -> String
getStringOfItems items =
	let
		stringOfItems = map getStringOfItem items
	in
		List.concatMap (\x -> x ++ "\n") stringOfItems





test0 randomSeed =
	let
		itemListStep1 = [(Item Type (LeafTag "1") (LeafTag "Digit") 1), (Item Type (LeafTag "0") (LeafTag "Digit") 1), (Item Type (LeafTag "2") (LeafTag "Digit") 1)]
		--(resultAgent1, memorizedAxioms1, _, _, _, _, _) = occamFunction (Random.mkStdGen randomSeed) itemListStep1 (Agent Set.empty Set.empty 8 10 6)
		(resultAgent1, afterCrossover, _) = modifiedOccamFunction (Random.mkStdGen randomSeed) itemListStep1 (Agent Set.empty Set.empty 8 10 6)

		--itemListStep2 = [(Item Type (LeafTag "1") (LeafTag "Number") 1), (Item Type (Branch (TermData "#" (LeafTag "1") (LeafTag "2"))) (LeafTag "Number") 1),     (Item Type (Branch (TermData "#" (LeafTag "1") (Branch (TermData "#" (LeafTag "2") (LeafTag "1"))))) (LeafTag "Number") (-1))]
		itemListStep2 = [(Item Type (LeafTag "1") (LeafTag "Number") 1), (Item Type (Branch (TermData "#" (LeafTag "1") (LeafTag "2"))) (LeafTag "Number") 1)]
		(resultAgent2, afterCrossover2, tempAxioms) = modifiedOccamFunction (Random.mkStdGen randomSeed) itemListStep2 resultAgent1

		--(resultAgent2, debug, debugSetOfVariables, debugTerms, debug0, nextAgentCDebug, afterCrossover) = occamFunction (Random.mkStdGen randomSeed) itemListStep2 resultAgent1
		-- TODO

		(Agent agentT agentC _ _ _) = resultAgent2
	in
		--(agentT, agentC, memorizedAxioms1, debugSetOfVariables, debugTerms, debug0, nextAgentCDebug, afterCrossover)
		(agentT, agentC, afterCrossover, tempAxioms)

-- TODO< zetaAsList must be empty for the example >
testPrint :: Int -> IO ()
testPrint randomSeed =
	let
		--(agentT, agentC, memorizedAxioms1, _, debugTerms, _, _, afterCrossover) = test0 randomSeed
		(agentT, agentC, afterCrossover, tempAxioms) = test0 randomSeed
	in
		do
			putStrLn "Agent T [Axioms]"
			putStrLn "====="
			putStr (getStringOfAxioms (Set.toList agentT))
			putStrLn ""

			putStrLn "Agent C [Terms]"
			putStrLn "====="
			putStr (getStringOfTerms (Set.toList agentC))
			putStrLn ""


			--putStrLn ""
			--putStr (getStringOfTerms (debugTerms))

			putStrLn "AXIOMS AFTER CROSSOVER"
			putStrLn $ convertAxiomsWithRatingToString afterCrossover

			putStrLn ""
			putStrLn "AXIOMS DEBUG"
			putStrLn (convertAxiomsToString (Set.toList tempAxioms))


	where
		convertAxiomsToString :: [AxiomData] -> String
		convertAxiomsToString axioms = List.concat $ map (\x -> getStringOfAxiom x ++ "     ") axioms



		convertAxiomsWithRatingToString :: [(AxiomData, Int, Int)] -> String
		convertAxiomsWithRatingToString axiomsWithRating = List.concat $ map mapHelper axiomsWithRating
			where
				mapHelper :: (AxiomData, Int, Int) -> String
				mapHelper (axiom, termsize, rating) = getStringOfAxiom axiom ++ " p=" ++ show termsize ++ " complex=" ++ show rating ++ "\n" 


testAgentComputation = doesAgentComputeItem (Agent (Set.fromList [(AxiomData Type (LeafTag "Digit") (LeafTag "Number")), (AxiomData Type (LeafTag "1") (LeafTag "Digit")) ]) (Set.empty) 8 10 6)       (Item Type (LeafTag "1") (LeafTag "Number") 1)


testAStarForPath = agentComputationWithAStar    True  (Just Type)      (Agent (Set.fromList [(AxiomData Type (LeafTag "Digit") (LeafTag "Number")), (AxiomData Type (LeafTag "1") (LeafTag "Digit")) ]) (Set.empty) 8 10 6)     (LeafTag "1")      (LeafTag "Number") 

testGetAllPossibleTransistion = getAllPossibleTransitionsOfTerms (Agent (Set.fromList [(AxiomData Type (LeafTag "Digit") (LeafTag "Number")), (AxiomData Type (LeafTag "1") (LeafTag "Digit")) ]) (Set.empty) 8 10 6) (LeafTag "1") True 10 8 [(AxiomData Type (LeafTag "Digit") (LeafTag "Number")), (AxiomData Type (LeafTag "1") (LeafTag "Digit")) ]

testRewritehelper = rewriteHelper (Agent (Set.fromList [(AxiomData Type (LeafTag "Digit") (LeafTag "Number")), (AxiomData Type (LeafTag "1") (LeafTag "Digit")) ]) (Set.empty) 8 10 6)                    True               ((AxiomData Type (LeafTag "1") (LeafTag "Digit")), (LeafTag "1"))

main = testPrint 5


rateSingleAxiom axiom =
	let
		testAxioms = [
			(AxiomData Equi (LeafTag "0") (LeafTag "1")),
			(AxiomData Equi (LeafTag "0") (LeafTag "2")),
			(AxiomData Equi (LeafTag "0") (LeafTag "Digit")),
			(AxiomData Equi (LeafTag "0") (LeafTag "Number")),

			(AxiomData Equi (LeafTag "0") (Branch (TermData "#" (LeafTag "0") (LeafTag "0")))),
			(AxiomData Equi (LeafTag "0") (Branch (TermData "#" (LeafTag "0") (LeafTag "1")))),
			(AxiomData Equi (LeafTag "0") (Branch (TermData "#" (LeafTag "0") (LeafTag "2")))),
			(AxiomData Equi (LeafTag "0") (Branch (TermData "#" (LeafTag "0") (LeafTag "Digit")))),
			(AxiomData Equi (LeafTag "0") (Branch (TermData "#" (LeafTag "0") (LeafTag "Number")))),

			(AxiomData Equi (LeafTag "0") (Branch (TermData "#" (LeafTag "1") (LeafTag "0")))),
			(AxiomData Equi (LeafTag "0") (Branch (TermData "#" (LeafTag "1") (LeafTag "1")))),
			(AxiomData Equi (LeafTag "0") (Branch (TermData "#" (LeafTag "1") (LeafTag "2")))),
			(AxiomData Equi (LeafTag "0") (Branch (TermData "#" (LeafTag "1") (LeafTag "Digit")))),
			(AxiomData Equi (LeafTag "0") (Branch (TermData "#" (LeafTag "1") (LeafTag "Number")))),

			(AxiomData Equi (LeafTag "0") (Branch (TermData "#" (LeafTag "2") (LeafTag "0")))),
			(AxiomData Equi (LeafTag "0") (Branch (TermData "#" (LeafTag "2") (LeafTag "1")))),
			(AxiomData Equi (LeafTag "0") (Branch (TermData "#" (LeafTag "2") (LeafTag "2")))),
			(AxiomData Equi (LeafTag "0") (Branch (TermData "#" (LeafTag "2") (LeafTag "Digit")))),
			(AxiomData Equi (LeafTag "0") (Branch (TermData "#" (LeafTag "2") (LeafTag "Number")))),

			(AxiomData Equi (LeafTag "0") (Branch (TermData "#" (LeafTag "Digit") (LeafTag "0")))),
			(AxiomData Equi (LeafTag "0") (Branch (TermData "#" (LeafTag "Digit") (LeafTag "1"))))
			]

		randomSeed = 5

		itemListStep1 = [(Item Type (LeafTag "1") (LeafTag "Digit") 1), (Item Type (LeafTag "0") (LeafTag "Digit") 1), (Item Type (LeafTag "2") (LeafTag "Digit") 1)]
		--(resultAgent1, memorizedAxioms1, _, _, _, _, _) = occamFunction (Random.mkStdGen randomSeed) itemListStep1 (Agent Set.empty Set.empty 8 10 6)
		(resultAgent1, afterCrossover, _) = modifiedOccamFunction (Random.mkStdGen randomSeed) itemListStep1 (Agent Set.empty Set.empty 8 10 6)

		itemListStep2 = [(Item Type (LeafTag "1") (LeafTag "Number") 1), (Item Type (Branch (TermData "#" (LeafTag "1") (LeafTag "2"))) (LeafTag "Number") 1)]

		agent = resultAgent1
		items = itemListStep2
	in
		rateAxioms agent items [] [axiom]