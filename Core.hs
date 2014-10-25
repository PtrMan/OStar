{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Term
import VariableData
import Item
import AxiomTag

import qualified System.Random as Random
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.List as List
import Control.Exception
import Data.Typeable


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

-- Definition 13 (Item Computation)
doesAgentComputeItem :: Random.StdGen -> Agent -> Item -> Bool
doesAgentComputeItem random agent (Item itemTag t1 t2 _) =
	let
		agentComputationResult = agentComputation True (Just itemTag) random agent t1
		t2ContainedInAgentComputationResult = t2 `List.elem` agentComputationResult
	in
		t2ContainedInAgentComputationResult

-- Definition 14 (Performance)
calcPerformanceSum :: Random.StdGen -> Agent -> [Item] -> Int
calcPerformanceSum    random           agent    items  =  List.sum (calcIndividualPerformance random agent items)


calcIndividualPerformance :: Random.StdGen -> Agent -> [Item] -> [Int]
calcIndividualPerformance    random           agent    items  =
	let
		infiniteListOfRandomGenerators = List.iterate (\x -> snd (Random.split x)) random
		
		-- is a list of the scores of the items
		listOfScoresOfItems = map mapTupleToScore (zip items infiniteListOfRandomGenerators)
	in
		listOfScoresOfItems
	where
		mapTupleToScore :: (Item, Random.StdGen) -> Int
		mapTupleToScore (item, random) = mapItemToScore random item

		-- calculates the score of an item
		mapItemToScore :: Random.StdGen -> Item -> Int
		mapItemToScore random (Item itemTag t1 t2 itemU)
			| doesAgentComputeItem random agent (Item itemTag t1 t2 itemU) = itemU
			| True                                                         = 0

-- des take a random subtree from treeA and inserts it into a random position in treeB
-- Definition 15 (Corssover)

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
		-- COULDBEWRONG
		-- create eqi axiom for (left) input term and result term of the crossover
		delta1 = Set.fromList (crossoverAndConvertToAxioms (Set.elems nextAgentC))

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

		crossoverAndConvertToAxioms :: [TermNode] -> [AxiomData]
		crossoverAndConvertToAxioms terms =
			let
				infiniteListOfRandomGenerators = List.iterate (\x -> snd (Random.split x)) random

				-- ASK< should it include _all_ combinations?
				combinationsOfTerms = combinatorialProduct terms
				crossoverResult = zipWith (\x random -> crossover random (fst x) (snd x)) combinationsOfTerms infiniteListOfRandomGenerators
				
				-- convert to axioms
				--  we zip because for the axiom we need the "orginal" term and the result of the crossover
				zipedCombinationAndCrossover = zip combinationsOfTerms crossoverResult
				result = map (\x -> AxiomData Equi (fst (fst x)) (snd x)) zipedCombinationAndCrossover
			in
				result

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

		crossoverOfAllTermsWithLimitOnSize :: [TermNode] -> Int   -> Random.StdGen -> [TermNode]
		crossoverOfAllTermsWithLimitOnSize    terms         limit    random        =
			let
				crossedOverTerms = crossoverOfAllTerms terms
				result = List.filter (\x -> (getTermSize x) <= limit) crossedOverTerms
			in
				result
			where
				crossoverOfAllTerms :: [TermNode] -> [TermNode]
				crossoverOfAllTerms    inputList  =
					let
						combinatorialOfTerms = combinatorialProduct inputList

						-- generator for an infinite list of different random number generators
						infiniteListOfRandomGenerators = List.iterate (\x -> snd (Random.split x)) random
					in
						map mappingHelper (zip combinatorialOfTerms infiniteListOfRandomGenerators)
					where
						-- does a crossover of the terms
						mappingHelper :: ((TermNode, TermNode), Random.StdGen) -> TermNode
						mappingHelper ((termA, termB), random) = crossover random termA termB

		-- helper
		-- Is symetric and excessive
		combinatorialProduct :: [TermNode] -> [(TermNode, TermNode)]
		combinatorialProduct    []         = []
		combinatorialProduct    inputList  =
			let
				singleLists = List.map internal inputList
				resultList = List.concat singleLists
			in
				resultList
			where
				internal :: TermNode -> [(TermNode, TermNode)]
				internal term = zip inputList (List.repeat term)

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
						termsizesOfTheories = List.map (\x -> getTermSizeOfTheory (allreadyDefinedAxioms ++ [(fst x)])) unorderedListOfAxiomsAndPerformanceRating

						-- TODO< calculate other criteria and adapt the zip and sort functionality >
						-- * maximum number of variable tokens
						-- * minimal number of variable types
						-- * lexographical as small as possible

						zipedList = List.zip unorderedListOfAxiomsAndPerformanceRating termsizesOfTheories
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
										calcPerformanceSum random modifiedAgent items

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
		(resultAgent1, memorizedAxioms1, _, _, _, _, _) = occamFunction (Random.mkStdGen randomSeed) itemListStep1 (Agent Set.empty Set.empty 8 10 6)

		itemListStep2 = [(Item Type (LeafTag "1") (LeafTag "Number") 1), (Item Type (Branch (TermData "#" (LeafTag "1") (LeafTag "2"))) (LeafTag "Number") 1),     (Item Type (Branch (TermData "#" (LeafTag "1") (Branch (TermData "#" (LeafTag "2") (LeafTag "1"))))) (LeafTag "Number") (-1))]
		(resultAgent2, debug, debugSetOfVariables, debugTerms, debug0, nextAgentCDebug, afterCrossover) = occamFunction (Random.mkStdGen randomSeed) itemListStep2 resultAgent1

		(Agent agentT agentC _ _ _) = resultAgent2
	in
		(agentT, agentC, memorizedAxioms1, debugSetOfVariables, debugTerms, debug0, nextAgentCDebug, afterCrossover)

-- TODO< zetaAsList must be empty for the example >
testPrint :: Int -> IO ()
testPrint randomSeed =
	let
		(agentT, agentC, memorizedAxioms1, _, debugTerms, _, _, afterCrossover) = test0 randomSeed
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




			putStrLn ""
			putStr (show agentT )

			putStrLn ""
			putStr (getStringOfTerms (debugTerms))

			putStrLn "AXIOMS AFTER CROSSOVER"
			putStr (getStringOfAxioms (Set.toList afterCrossover))


