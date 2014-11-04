{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Rewrite where

import qualified Data.Map.Strict as Map
import qualified Data.List as List

import Control.Exception
import Data.Typeable

import Term
import Axiom
import VariableData

-- Definition 6 (Assignment)  An assignmnt is a partial function from variables to terms.
-- Definition 7 (Rewrite)

data VariableNameNotFoundException = VariableNameNotFoundException {
	variable :: (String, String)
} deriving (Show, Typeable)

instance Exception VariableNameNotFoundException


-- rewriting of terms and helper functions

-- assigns variables in a tree to the values
assignmentAssignVariablesToValues :: Map.Map (String, String) TermNode -> TermNode -> TermNode
assignmentAssignVariablesToValues variableMappings appliedTerm =
		rewriteTermNode appliedTerm
	where
		-- function which does the rewriting
		-- replaces TermNodes of variables with the corresponding stored TermNodes in "variables"
		rewriteTermNode :: TermNode -> TermNode
		rewriteTermNode (Branch (TermData nodeTag leftTermNode rightTermNode))   = Branch( TermData nodeTag (rewriteTermNode leftTermNode) (rewriteTermNode rightTermNode))
		rewriteTermNode (LeafVariable (VariableData variableDelta variableTau))  = lookupAndReturnTermNode (variableDelta, variableTau)
		rewriteTermNode (LeafTag leafTag)                                        = LeafTag leafTag
		
		-- function which looks up the variable and throws a exception if it wasn't found
		lookupAndReturnTermNode :: (String, String) -> TermNode
		lookupAndReturnTermNode variableKey      =
			case (Map.lookup variableKey variableMappings) of
				Just termNode -> termNode
				Nothing -> throw (VariableNameNotFoundException variableKey)

assignmentAssignVariablesToValues_test_positive_A = assignmentAssignVariablesToValues (Map.insert ("y", "Number") (LeafTag "leafY") (Map.insert ("x", "Number") (LeafTag "leafX") Map.empty))    (Branch (TermData "+" (LeafVariable (VariableData "x" "Number")) (LeafVariable (VariableData "y" "Number")))) == (Branch (TermData "+" (LeafTag "leafX") (LeafTag "leafY")))
assignmentAssignVariablesToValues_test_positive_B = (assignmentAssignVariablesToValues (Map.empty) (LeafTag "test")) == (LeafTag "test")


-- tries to match up exactly the variables in templateTerm with the appliedTerm
-- if it doesn't match a Nothing is returned
--                templateTerm    appliedTerm
matchVariables :: TermNode     -> TermNode    -> Maybe (Map.Map (String, String) TermNode)
matchVariables    (LeafTag templateNodeTag) (LeafTag appliedNodeTag)
	| templateNodeTag == appliedNodeTag = Just Map.empty
	| True = Nothing
matchVariables    (LeafVariable (VariableData variableDelta variableTau)) term = Just $ Map.insert (variableDelta, variableTau) term Map.empty
matchVariables    (Branch (TermData templateNodeTag templateLeftTerm templateRightTerm)) (Branch (TermData appliedNodeTag appliedLeftTerm appliedRightTerm))
	| templateNodeTag == appliedNodeTag =
		let
			matchResultOfLeft = matchVariables templateLeftTerm appliedLeftTerm
			matchResultOfRight = matchVariables templateRightTerm appliedRightTerm

			leftMatched = case matchResultOfLeft of
				Just _ -> True
				Nothing -> False

			rightMatched = case matchResultOfRight of
				Just _ -> True
				Nothing -> False
		in
			if leftMatched && rightMatched
			then
				let
					Just leftMap = matchResultOfLeft
					Just rightMap = matchResultOfRight

					fusedMap = Map.union leftMap rightMap

					-- TODO< check with a helper if each variable mapping is unique, if not, throw internal error >
				in
					Just fusedMap
			else
				Nothing
	| True = Nothing

matchVariables    _ _ = Nothing

-- doesn't check everything
matchVariables_test_positive_A = matchVariables (LeafTag "x") (LeafTag "x") == Just Map.empty
matchVariables_test_positive_B = matchVariables (LeafTag "x") (LeafTag "y") == Nothing

matchVariables_test_positive_C = (matchVariables (Branch (TermData "+" (LeafTag "x") (LeafVariable (VariableData "a" "Number")))) (Branch (TermData "+" (LeafTag "x") (LeafTag "y")))) == (Just (Map.insert ("a", "Number") (LeafTag "y") Map.empty))

matchVariables_test = matchVariables_test_positive_A && matchVariables_test_positive_B && matchVariables_test_positive_C


-- tries to find outermost match of the (applied) (sub)term with the template (which can contain variables, but doesn't have to)
-- it returns the orginal term with one placeholder as the replacement, where the match succeeded
matchVariablesOutermostAndReplaceWithPlaceholder :: TermNode     -> TermNode    -> Maybe (Map.Map (String, String) TermNode, TermNode)
matchVariablesOutermostAndReplaceWithPlaceholder    templateTerm    appliedTerm =
	let
		matchResult = matchVariables templateTerm appliedTerm
	in case matchResult of
		Just variableMapping -> Just (variableMapping, Placeholder)
		Nothing -> tryToMatchChildrensAndReturnResult
	where

		-- tries to match the template with the term, returns the rewritten tree
		-- for a branch, try first on the left, then on the right
		tryToMatchChildrensAndReturnResult :: Maybe (Map.Map (String, String) TermNode, TermNode)
		tryToMatchChildrensAndReturnResult =
			case appliedTerm of
				(Branch (TermData appliedNodeTag appliedLeftTerm appliedRightTerm)) ->
					let
						leftResult = matchVariablesOutermostAndReplaceWithPlaceholder templateTerm appliedLeftTerm
						rightResult = matchVariablesOutermostAndReplaceWithPlaceholder templateTerm appliedRightTerm
					in case leftResult of
						Just (variableMapping, resultTreeAfterApplication) -> Just (variableMapping, (Branch (TermData appliedNodeTag resultTreeAfterApplication appliedRightTerm)))
						Nothing ->
							case rightResult of
								Just (variableMapping, resultTreeAfterApplication) -> Just (variableMapping, (Branch (TermData appliedNodeTag appliedLeftTerm resultTreeAfterApplication)))
								Nothing -> Nothing
				_ -> Nothing

-- test for usual mapping (like we see most of the time)
matchVariablesOutermostAndReplaceWithPlaceholder_test_positive_A = (matchVariablesOutermostAndReplaceWithPlaceholder (LeafTag "x") (LeafTag "x")) == (Just (Map.empty, Placeholder))

-- test for a usual negative mapping
matchVariablesOutermostAndReplaceWithPlaceholder_test_negative_A = (matchVariablesOutermostAndReplaceWithPlaceholder (LeafTag "x") (LeafTag "y")) == Nothing

matchVariablesOutermostAndReplaceWithPlaceholder_test_positive_B =
	let
		appiedTermTopmostTree = (Branch (TermData "*" (LeafTag "x") (LeafTag "y")))
		appliedTerm = (Branch (TermData "+" appiedTermTopmostTree (LeafTag "z")))

		templateTerm = (Branch (TermData "*" (LeafVariable (VariableData "mustBeX" "Number")) (LeafVariable (VariableData "mustBeY" "Number"))))

		matchResult = matchVariablesOutermostAndReplaceWithPlaceholder templateTerm appliedTerm

		expectedResult = Just (Map.fromList [(("mustBeX","Number"),(LeafTag "x")),(("mustBeY","Number"),(LeafTag "y"))],(Branch (TermData "+" (Placeholder) (LeafTag "z"))))
	in
		matchResult == expectedResult

-- TODO< more tests for that function >
-- NOTE< for now it only checks for direct type axioms (without a star search) >
doAllAssignmentsHaveTheCorrectType :: Bool       -> Map.Map (String, String) TermNode -> [AxiomData]        -> Bool
doAllAssignmentsHaveTheCorrectType    checkTypes    variableMap                          typecheckingAxioms
	| checkTypes = List.and $ List.map isVariableOfCorrectType $ Map.toList variableMap
	| True = True
		where
			isVariableOfCorrectType :: ((String, String), TermNode) -> Bool
			isVariableOfCorrectType ((_, variableTau), termOfVariable) =
					List.any doesAxiomMatchToVariable typecheckingAxioms
				where
					doesAxiomMatchToVariable :: AxiomData -> Bool
					doesAxiomMatchToVariable (AxiomData Type termOfVariable variableTau) = True
					doesAxiomMatchToVariable _ = False



-- throws an exception if some deep error happend
rewrite :: Bool       -> [AxiomData]        -> AxiomData -> TermNode -> Maybe TermNode
rewrite    checkTypes    typecheckingAxioms    axiom        appliedTerm =
	-- we ignore the typechecking flag because we check allways the types
	rewriteProxy typecheckingAxioms axiom appliedTerm

-- throws an exception if some deep error happend
rewriteProxy :: [AxiomData]        -> AxiomData                       -> TermNode    -> Maybe TermNode
rewriteProxy    typecheckingAxioms    (AxiomData _ axiomT axiomTTick)    appliedTerm =
	let
		appliedTermMatchResult = matchVariablesOutermostAndReplaceWithPlaceholder axiomT appliedTerm
	in case appliedTermMatchResult of
		Nothing -> Nothing
		Just (variableMap, rewrittenTemplateTerm) ->
			let
				-- rewrittenTemplateTerm contains somewhere a "Placeholder" where the replacing tree is fitted in

				allAssignmentsHaveTheCorrectType = doAllAssignmentsHaveTheCorrectType True variableMap typecheckingAxioms
				rewrittenTTick = assignmentAssignVariablesToValues variableMap axiomTTick
			in
				if (not allAssignmentsHaveTheCorrectType)
				then
					-- type of an rewritten variable is wrong / there exists no type axiom for it
					Nothing
				else
					Just rewrittenTTick

rewrite_test_negative_A = (rewrite True [] (AxiomData Type (LeafTag "2") (LeafTag "1")) (LeafTag "1")) == Nothing
rewrite_test_negative_B = (rewrite True [] (AxiomData Type (LeafTag "2") (LeafTag "1")) (LeafTag "5")) == Nothing
