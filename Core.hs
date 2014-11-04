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
import Axiom
import Misc
import Rewrite

import Debug.Trace

import qualified AStar as AStar

-- BUG  the type checking is specified as only done for variable assignment, not for identifiers!!!
-- TODO FIX, TEST

-- TODO< inside evaluation function --- if the performance rating of the top candidates is 0, drop the candidates (return nothing) >

-- TODO
-- * check if connection function loops when it sees loops



-- definition 10
-- Termsize
getTermSizeForAxiom :: AxiomData -> Int
getTermSizeForAxiom (AxiomData _ t tTick) = ((getTermSize t) + (getTermSize tTick))

getTermSizeForAxioms :: [AxiomData] -> Int
getTermSizeForAxioms axioms = List.sum $ List.map getTermSizeForAxiom axioms

getTermSizeOfTheory :: [AxiomData] -> Int
getTermSizeOfTheory theory = List.sum $ List.map getTermSizeForAxiom theory

-- Definition 11 (Agent computation)
-- TODO< constraints from outside >

-- axiomTagFilter can be an axiom type which the axioms are filtered For

-- returns a list of terms of the done production/transformation

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
		allPossibleTransitions = getAllPossibleTransitionsOfTerms agent checkTypes agentAssimilationCapacity agentWorkingMemoryCapacity usedAxioms

		aStarGraphFunctionWithTransitions = aStarGraphFunction allPossibleTransitions
	in
		if (List.length allPossibleTransitions) == 0
		then
			(False, [])
		else
			let
				aStarSearchResult = AStar.aStar aStarGraphFunctionWithTransitions aStarDistanceFunction aStarheuristicDistanceFunction aStarIsGoal startTerm
			in
				case aStarSearchResult of
					Just optimalSolution -> trace (show allPossibleTransitions) (True, [startTerm] ++ optimalSolution)
					Nothing -> (False, [startTerm])
	where
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
				-- NOTE< Set.fromList reachableNodes could also work >
				Set.difference (Set.fromList reachableNodes) (Set.fromList [currentTerm])
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









getAllPossibleTransitionsOfTerms :: Agent -> Bool       -> Int                       -> Int                        -> [AxiomData] -> [(TermNode, TermNode)]
getAllPossibleTransitionsOfTerms    agent    checkTypes    agentAssimilationCapacity    agentWorkingMemoryCapacity     usedAxioms
	| List.length usedAxioms == 0 = []
	| True =
		let
			startTermAxiom = List.head usedAxioms
			(AxiomData _ startTerm _) = startTermAxiom

			-- list of nodes for which the possible transistions with the application of axioms is left to be checked
			-- the remaining searchdepth is also stored
			openSet = Set.fromList [(startTerm, agentAssimilationCapacity)]

			foundPossibleApplications = getAllTransistionsHelperProxy agent (openSet, Set.empty) (usedAxioms, agentWorkingMemoryCapacity)
		in
			Set.toList foundPossibleApplications



getAllTransistionsHelperProxy :: Agent -> (Set.Set (TermNode, Int), Set.Set (TermNode, TermNode)) -> ([AxiomData], Int) -> Set.Set (TermNode, TermNode)
getAllTransistionsHelperProxy agent initial passthrough =
	let
		(_, result) = (getAllTransistionsHelper agent initial passthrough)
	in 
		result

-- TODO< maybe too inefficient >

-- searches for all possible rewrites of the terms
-- this is done until a maximal depth is reached
getAllTransistionsHelper :: Agent -> (Set.Set (TermNode, Int), Set.Set (TermNode, TermNode)) -> ([AxiomData], Int) -> (Set.Set (TermNode, Int), Set.Set (TermNode, TermNode))
getAllTransistionsHelper agent (openSet, argumentTransistionSet) (usedAxioms, agentWorkingMemoryCapacity)
	| Set.size openSet == 0 = (openSet, argumentTransistionSet)
	| True =
		let
			currentOpenElement = List.head $ Set.toList openSet
			remainingOpenSet = Set.difference openSet $ Set.fromList [currentOpenElement]
			
			(currentOpenSetElement, currentRemainingDeep) = currentOpenElement
		in
			if not (currentRemainingDeep == 0)
			then
				let
					nextRemainingDepth = currentRemainingDeep - 1

					termsAfterApplicationOfTheorems = getResultsOfRewriteWithAxiomsUsingFilter (filterHelper agentWorkingMemoryCapacity) currentOpenSetElement usedAxioms
					termsAfterApplicationOfTheoremsAsSet = Set.fromList termsAfterApplicationOfTheorems


					termTermTransitions = List.zip (List.repeat currentOpenSetElement) termsAfterApplicationOfTheorems
					filteredTermTermTransitions = List.filter termTermTransitionFilter termTermTransitions
					termTermTransitionsAsSet = Set.fromList filteredTermTermTransitions
					--newTermTermTransitions = Set.difference termTermTransitionsAsSet argumentTransistionSet

					closedSet = Set.map getFirstTermOfTuple argumentTransistionSet
					openTerms = Set.difference termsAfterApplicationOfTheoremsAsSet closedSet

					additionalRemainingOpenSet = Set.fromList $ List.zip (Set.toList openTerms) (List.repeat nextRemainingDepth)
				in
					getAllTransistionsHelper agent (Set.union remainingOpenSet additionalRemainingOpenSet, Set.union termTermTransitionsAsSet argumentTransistionSet) (usedAxioms, agentWorkingMemoryCapacity)
			else
				getAllTransistionsHelper agent (remainingOpenSet, argumentTransistionSet) (usedAxioms, agentWorkingMemoryCapacity)
		where
			-- does ensure that the Term Size is small enought for the agent
			filterHelper :: Int -> TermNode -> Bool
			filterHelper maximum appliedTerm = (getTermSize appliedTerm) < maximum

			-- used for getting the closed set
			getFirstTermOfTuple :: (TermNode, TermNode) -> TermNode
			getFirstTermOfTuple (a, b) = a 

			getResultsOfRewriteWithAxiomsUsingFilter :: (TermNode -> Bool) -> TermNode -> [AxiomData] -> [TermNode]
			getResultsOfRewriteWithAxiomsUsingFilter filterFunction appliedTerm axioms =
				let


					-- try to rewrite the axioms
					-- [MatchResult TermNode]
					-- TODO DEBUG< parameter check types >
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

					filterHelper :: Maybe TermNode -> Bool
					filterHelper (Just _) = True
					filterHelper _ = False

					-- only defined for Success term
					convertSuccessfulMatchResultToTerm :: Maybe TermNode -> TermNode
					convertSuccessfulMatchResultToTerm (Just term) = term

			termTermTransitionFilter :: (TermNode, TermNode) -> Bool
			termTermTransitionFilter (a, b) = not $ a == b


-- TODO< eliminate the helper function and untangle mess >

-- helper, tries to rewrite the Term with the axiom
-- helper, tries to rewrite the Term with the axiom
rewriteHelper :: Agent -> Bool       -> (AxiomData, TermNode   ) -> Maybe TermNode
rewriteHelper    agent    checkTypes    (axiom    , appliedTerm) =
	let
		(Agent agentT _ _ _ _) = agent
	in
		-- we pass in agentT without filtering for the Type Axioms, because it does typechecking only with type axioms
		rewrite checkTypes (Set.toList agentT) axiom appliedTerm








-- Definition 13 (Item Computation)

-- for successful test must be true
doesAgentComputeItem_test_Negative_A = not (doesAgentComputeItem (Agent (Set.fromList [AxiomData Type (LeafTag "2") (LeafTag "Number")]) Set.empty 8 10 6 ) (Item Type (LeafTag "1") (LeafTag "Number") 1))
doesAgentComputeItem_test_Positive_A = doesAgentComputeItem (Agent (Set.fromList [AxiomData Type (LeafTag "2") (LeafTag "Number")]) Set.empty 8 10 6 ) (Item Type (LeafTag "2") (LeafTag "Number") 1)

-- this should not compute
doesAgentComputeItem_test_Negative_B = not (doesAgentComputeItem (Agent (Set.fromList [(AxiomData Type (LeafTag "0") (LeafTag "2")),(AxiomData Type (LeafTag "2") (LeafTag "1")),(AxiomData Type (LeafTag "2") (LeafTag "Digit"))]) Set.empty 8 10 6 ) (Item Type (LeafTag "1") (LeafTag "Digit") 1))

doesAgentComputeItem :: Agent -> Item -> Bool
doesAgentComputeItem agent (Item itemTag t1 t2 _) =
	let
		(doesCompute, _) = agentComputationWithAStar True (Just itemTag) agent t1 t2
	in
		doesCompute

-- Definition 14 (Performance)
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


-- NOTE< not after specification, whole algorithm producesstrange result(s) >
-- TODO< maybe use the helper in misc to get all possible combinations >

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



data Side = LeftSide | RightSide

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
		trace ("templatedCrossover=== " ++ show allPossibleCombinationsAsSet) allPossibleCombinationsAsSet
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

templatedCrossoverTest :: Set.Set TermNode
templatedCrossoverTest =
	let
		listOfTestTerms = [(LeafTag "0"), (LeafTag "1"), (LeafTag "2"), (LeafTag "Digit"), (LeafTag "Number"), (Branch (TermData "#" (LeafTag "1") (LeafTag "2")))]
	in
		templatedCrossover listOfTestTerms

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
modifiedOccamFunction :: [Item] -> Agent -> (Agent, Set.Set AxiomData)
modifiedOccamFunction    ipIn      agent =
	let
		(Agent agentT agentC workingMemoryCapacity assimilationCapacity accommodationCapacity) = agent

		-- first we calculate the set of variables in agentC
		setOfVariables = getAllVariablesAsSetFromTerms agentC

		subtreesFromIn = getAllSubtermFromItems ipIn

		-- replace one ore many leaf nodes of the subtrees by variables setOfVariables
		zetaAsList = replaceOneOrMoreLeafNodesByRandomVariableFromSet subtreesFromIn setOfVariables
		zetaAsSet = trace ("set of variables===" ++ show setOfVariables ++ "    ZetaAsList===" ++ show zetaAsList) Set.fromList zetaAsList

		-- union for the new agentC agentC and zeta
		nextAgentC = Set.union agentC zetaAsSet


		-- functions which will be executed by tryToFindOptimalCandidatesForDeltaTickTick in succession, if it failed to find any axioms which can be candidates
		appliedFunctionsForFormingOfDeltaTickTick = [
			forDeltaTickTickCrossover accommodationCapacity
			-- TODO abstraction
			-- TODO recursion
			--forDeltaTickTickMemorisation ipIn
			]

		-- DEBUG
		--debugAxiomsAfterCrossover = rateAxioms agent ipIn [] (Set.toList $ forDeltaTickTickCrossover accommodationCapacity (Set.toList nextAgentC))

		-- Maybe [AxiomData]
		maybeDeltaTickTickAxioms = tryToFindOptimalCandidatesForDeltaTickTick agent ipIn (Set.toList nextAgentC) appliedFunctionsForFormingOfDeltaTickTick

		-- if we have found solution(s) with crossover, abstraction and recursion we just ake it for deltaTickTickAxioms
		-- if all else failed we memorize everything
		deltaTickTickAxioms =
			case maybeDeltaTickTickAxioms of
				Just deltaTickTickAxioms2 ->
					deltaTickTickAxioms2
				Nothing ->
					memorizeInductionProblem ipIn
	
		agentTplus1 = Set.union agentT deltaTickTickAxioms
		resultAgent = (Agent agentTplus1 nextAgentC workingMemoryCapacity assimilationCapacity accommodationCapacity)
	in
		(resultAgent, deltaTickTickAxioms)
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
		tryToFindOptimalCandidatesForDeltaTickTick :: Agent -> [Item] -> [TermNode] -> [[TermNode] -> Set.Set AxiomData] -> Maybe (Set.Set AxiomData)

		-- if no more functions are left we return nothing because the search failed
		tryToFindOptimalCandidatesForDeltaTickTick _ _ _ [] = Nothing

		tryToFindOptimalCandidatesForDeltaTickTick agent items inputTerms (currentFunction:otherFunctions) =
			let
				numberOfMaximalCandidates = 3

				(Agent agentT agentC workingMemoryCapacity assimilationCapacity accommodationCapacity) = agent

				workingAxioms = currentFunction inputTerms

				-- PAPERQUOTE< form the set deltaTick, whose axioms satisfy a few additional conditions: e.g. all variables must appear in both terms of the axioms, or not at all >
				deltaTick = filterAxiomSetByAdditionalConditions [areAllVariablesApearingOnBothSidesInAxiom, areNoVariablesAppearingInAxiom] workingAxioms
				
				deltaTickAsList = trace ("deltaTick " ++ show (Set.toList deltaTick)) (Set.toList deltaTick)

				-- [[AxiomData]]
				allCombinationsOfAxiomsAsListList = trace "here 1" (getAllCombinations deltaTickAsList numberOfMaximalCandidates)

				-- Set.Set (Set.Set AxiomData)
				allCombinationsOfAxiomsAsSetSet = trace "here 2" (convertListsListOfAxiomsToSetSet allCombinationsOfAxiomsAsListList)
				allCombinationsOfAxiomsAsListSet = Set.toList allCombinationsOfAxiomsAsSetSet

				ratedAxiomSets = rateAxiomSets agent items (Set.toList agentT) allCombinationsOfAxiomsAsListSet

				-- TODO< we only have to take the best entry >

				-- sort it by the many criteria
				sortedRatedAxiomSets = trace ("sorted " ++ show (List.sortBy sortFunction ratedAxiomSets)) (List.reverse (List.sortBy sortFunction ratedAxiomSets))
				-- * Performance
				-- * Size/Complexity
				-- TODO< calculate other criteria and adapt the zip and sort functionality >
				-- * maximum number of variable tokens
				-- * minimal number of variable types
				-- * lexographical as small as possible
			in
				if ((List.length sortedRatedAxiomSets) == 0) || (isPerformanceZeroOrBelow (List.head sortedRatedAxiomSets))
				then
					-- if this fails we continue with the otherFunctions (recursivly)
					trace ("failed " ++ " " ++ show (List.length sortedRatedAxiomSets)) (tryToFindOptimalCandidatesForDeltaTickTick agent items inputTerms otherFunctions)
				else
					let
						bestEntry = List.head sortedRatedAxiomSets

						(resultSet, _, _) = bestEntry
					in
						Just resultSet
			where
				---isPerformanceOfFirstCandidateZero :: [(AxiomData, Int           , Int)] -> Bool
				---isPerformanceOfFirstCandidateZero    list                               =
				---	let
				---		(_        , performance   , _  ) = (List.head list)
				---	in
				---		performance == 0

				isPerformanceZeroOrBelow :: (a, Int           , Int) -> Bool
				isPerformanceZeroOrBelow    (_, performance   , _  ) =  performance <= 0

				sortFunction :: (a , Int           , Int        ) -> (a, Int         , Int        ) -> Ordering
				sortFunction    (_ , performanceL  , complexityL)    (_, performanceR, complexityR)
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

				convertListsListOfAxiomsToSetSet :: [[AxiomData]] -> Set.Set (Set.Set AxiomData)
				convertListsListOfAxiomsToSetSet listOfListOfAxioms =
						Set.fromList $ List.map convertListOfAxiomsToSet listOfListOfAxioms
					where
						convertListOfAxiomsToSet :: [AxiomData] -> Set.Set AxiomData
						convertListOfAxiomsToSet listOfAxioms = Set.fromList listOfAxioms

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
				crossoverResultAxioms = crossoverAndConvertToAxiomsWithTemplateStrategy accommodationCapacity nextAgentC
				--crossoverResultAxioms = crossoverAndConvertToAxiomsWithExcessiveStrategy accommodationCapacity nextAgentC

				
				-- paper "iterates over lenths of condidates (1 to D)"
				-- PAPER ASK< maybe they mean that for the crossover it should iterate over the combinates of the crossover >
				-- NOTE< we don't have to sort here by anything because tryToFindOptimalCandidatesForDeltaTickTick does it allready >

				-- TODO< crossoverResultAxiomsSorted for deltaTick : filter it according to transistion rule from delta to deltaTick ? >

				crossoverResultAfterFilter = List.filter filterIsTransformation crossoverResultAxioms
				
			in
				Set.fromList crossoverResultAfterFilter
			where
				crossoverAndConvertToAxiomsWithExcessiveStrategy :: Int                   -> [TermNode] -> [AxiomData]
				crossoverAndConvertToAxiomsWithExcessiveStrategy    accommodationCapacity    terms      =
					let
						-- TODO< doesn't work because we are only listing the axioms with the highest complexity >
						allTermsCrossedOverAsSet = excessiveCrossover terms accommodationCapacity
						allTermsCrossedOverAsList = Set.toList allTermsCrossedOverAsSet

						-- [(TermNode, TermNode)]
						allCombinationsOfCrossedOverTerms = combinatorialProduct allTermsCrossedOverAsList allTermsCrossedOverAsList

						unfilteredAxioms = List.concat $ List.map getPossibleAxiomsOfTermTuple allCombinationsOfCrossedOverTerms

						filteredList = List.filter filterForMaximalAccommodationCapacity unfilteredAxioms
					in
						trace (show terms ++ "\n\nallTermsCrossedOverAsSet===\n" ++ show filteredList) filteredList
					where
						getPossibleAxiomsOfTermTuple :: (TermNode, TermNode) -> [AxiomData]
						getPossibleAxiomsOfTermTuple (a, b) = [AxiomData Equi a b, AxiomData Type a b]

						filterForMaximalAccommodationCapacity :: AxiomData -> Bool
						filterForMaximalAccommodationCapacity axiom = getTermSizeForAxiom axiom <= accommodationCapacity


				crossoverAndConvertToAxiomsWithTemplateStrategy :: Int                   -> [TermNode] -> [AxiomData]
				crossoverAndConvertToAxiomsWithTemplateStrategy    accommodationCapacity    terms      =
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

		memorizeInductionProblem :: [Item] -> Set.Set AxiomData
		memorizeInductionProblem items = trace ("O*Core === MEMORIZE" ++ show items) Set.fromList $ memorizeFromList items
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







replaceOneOrMoreLeafNodesByRandomVariableFromSet_Test_emptyness = replaceOneOrMoreLeafNodesByRandomVariableFromSet [(LeafTag "?")] Set.empty == [(LeafTag "?")]
replaceOneOrMoreLeafNodesByRandomVariableFromSet_Test_one = replaceOneOrMoreLeafNodesByRandomVariableFromSet [(LeafTag "a"), (LeafTag "b")] (Set.fromList [VariableData "x" "y"])
replaceOneOrMoreLeafNodesByRandomVariableFromSet_Test_a = replaceOneOrMoreLeafNodesByRandomVariableFromSet [(Branch (TermData "+" (LeafTag "a") (LeafTag "b")))] (Set.fromList [VariableData "x" "y"])


-- helper function
--  Set.size setOfVariables == 0 has a no special treetment
--  this is because the algorithm as of now 3.11.2014 doesn't work if it does it that way
replaceOneOrMoreLeafNodesByRandomVariableFromSet :: [TermNode] -> Set.Set VariableData -> [TermNode]
replaceOneOrMoreLeafNodesByRandomVariableFromSet subtreesFromIn setOfVariables
--	| (Set.size setOfVariables == 0) = []
	| True =
		let
			-- convert it to a list
			-- this saves some unnecessary conversions in the inner functions
			setOfVariablesAsList = Set.elems setOfVariables
		in
			List.concat $ map mapHelperFunction (List.zip subtreesFromIn (List.repeat setOfVariablesAsList))
		where
			mapHelperFunction :: (TermNode, [VariableData]) -> [TermNode]
			mapHelperFunction (term, setOfVariablesAsList) = replaceOneOrMoreLeafNodesByVariablesFromSetForTermNode term setOfVariablesAsList

			replaceOneOrMoreLeafNodesByVariablesFromSetForTermNode :: TermNode -> [VariableData]  -> [TermNode]
			replaceOneOrMoreLeafNodesByVariablesFromSetForTermNode    term        listOfVariables =
				let
					indicesOfReplacedLeafnodeWithVariables = getIndicesOfLeafNodesInTree term

					-- currently we replace only one leafnode with variables
					-- TODO< iterate over all posible index combination for the leafnodes >

					resultTerms = List.concat $ List.map replaceSubtermWithVariablesFromSet indicesOfReplacedLeafnodeWithVariables
				in
					resultTerms
				where
					replaceSubtermWithVariablesFromSet :: Int -> [TermNode]
					replaceSubtermWithVariablesFromSet index
					    | List.length listOfVariables == 0 = [term]
						| True                             = List.map replaceNodeWithVariable listOfVariables
							where
								replaceNodeWithVariable :: VariableData -> TermNode
								replaceNodeWithVariable variableData = replaceNthInTree index term (LeafVariable variableData)









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

rateAxiomSets :: Agent -> [Item] -> [AxiomData]           -> [Set.Set AxiomData] -> [(Set.Set AxiomData, Int, Int)]
rateAxiomSets    agent    items     allreadyDefinedAxioms    axiomSets           =
	let
		-- calculate the performances we would get if we add one axiom to all axioms and do evaluate the performance
		ratedAxioms = List.map calculatePerformanceAndOtherRatingsOfAxiomSet axiomSets
	in
		ratedAxioms
	where
		calculatePerformanceAndOtherRatingsOfAxiomSet :: Set.Set AxiomData -> (Set.Set AxiomData, Int, Int)
		calculatePerformanceAndOtherRatingsOfAxiomSet    axiomSet          =
			let
				performanceOfAgentWithAxioms = calcPerformanceOfAgentWithAdditionalAxiomsPlusAxioms (Set.toList axiomSet)
				complexityOfAxioms = getTermSizeForAxioms (Set.toList axiomSet)
			in
				-- trace ("rateAxiomSets===" ++ show axiomSet) 
				(axiomSet, performanceOfAgentWithAxioms, complexityOfAxioms)

		calcPerformanceOfAgentWithAdditionalAxiomsPlusAxioms :: [AxiomData     ] -> Int
		calcPerformanceOfAgentWithAdditionalAxiomsPlusAxioms    additionalAxioms =
			let
				allAxioms = allreadyDefinedAxioms ++ additionalAxioms
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
		(resultAgent1, tempAxioms) = modifiedOccamFunction itemListStep1 (Agent Set.empty Set.empty 8 10 6)

		itemListStep2 = [(Item Type (LeafTag "1") (LeafTag "Number") 1), (Item Type (Branch (TermData "#" (LeafTag "1") (LeafTag "2"))) (LeafTag "Number") 1),       (Item Type (Branch (TermData "#" (LeafTag "1") (Branch (TermData "#" (LeafTag "2") (LeafTag "1"))))) (LeafTag "Number") (-1))]
		--(resultAgent2, tempAxioms) = modifiedOccamFunction itemListStep2 resultAgent1

		-- repeat step 2 to learn the 2nd axiom like in the paper
		--(resultAgent3, tempAxioms) = modifiedOccamFunction itemListStep2 resultAgent2

		(Agent agentT agentC _ _ _) = resultAgent1
	in
		--(agentT, agentC, memorizedAxioms1, debugSetOfVariables, debugTerms, debug0, nextAgentCDebug, afterCrossover)
		(agentT, agentC, tempAxioms)

-- TODO< zetaAsList must be empty for the example >
testPrint :: Int -> IO ()
testPrint randomSeed =
	let
		--(agentT, agentC, memorizedAxioms1, _, debugTerms, _, _, afterCrossover) = test0 randomSeed
		(agentT, agentC, tempAxioms) = test0 randomSeed
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

			putStrLn ""
			putStrLn "AXIOMS DEBUG"
			-----putStrLn (convertAxiomsToString (Set.toList tempAxioms))


	where
		convertAxiomsToString :: [AxiomData] -> String
		convertAxiomsToString axioms = List.concat $ map (\x -> getStringOfAxiom x ++ "     ") axioms



		convertAxiomsWithRatingToString :: [(AxiomData, Int, Int)] -> String
		convertAxiomsWithRatingToString axiomsWithRating = List.concat $ map mapHelper axiomsWithRating
			where
				mapHelper :: (AxiomData, Int, Int) -> String
				mapHelper (axiom, termsize, rating) = getStringOfAxiom axiom ++ " p=" ++ show termsize ++ " complex=" ++ show rating ++ "\n" 


testAgentComputation2 = doesAgentComputeItem (Agent (Set.fromList [(AxiomData Type (LeafTag "1") (LeafTag "Digit")), (AxiomData Type (LeafTag "Digit") (LeafTag "Number")) ]) (Set.empty) 8 10 6)       (Item Type (LeafTag "1") (LeafTag "Number") 1)


testAStarForPath = agentComputationWithAStar    True  (Just Type)      (Agent (Set.fromList [(AxiomData Type (LeafTag "Digit") (LeafTag "Number")), (AxiomData Type (LeafTag "1") (LeafTag "Digit")) ]) (Set.empty) 8 10 6)     (LeafTag "1")      (LeafTag "Number") 

testGetAllPossibleTransistion = getAllPossibleTransitionsOfTerms (Agent (Set.fromList [(AxiomData Type (LeafTag "Digit") (LeafTag "Number")), (AxiomData Type (LeafTag "1") (LeafTag "Digit")) ]) (Set.empty) 8 10 6) True 10 8 [(AxiomData Type (LeafTag "Digit") (LeafTag "Number")), (AxiomData Type (LeafTag "1") (LeafTag "Digit")) ]

main = testPrint 5

rateSingleAxiomA = rateSingleAxiom (AxiomData Equi (LeafTag "0") (LeafTag "1"))


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
		(resultAgent1, _) = modifiedOccamFunction itemListStep1 (Agent Set.empty Set.empty 8 10 6)

		itemListStep2 = [(Item Type (LeafTag "1") (LeafTag "Number") 1), (Item Type (Branch (TermData "#" (LeafTag "1") (LeafTag "2"))) (LeafTag "Number") 1)]

		agent = resultAgent1
		items = itemListStep2
	in
		rateAxioms agent items [] [axiom]