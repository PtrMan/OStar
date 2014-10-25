{-# LANGUAGE OverloadedStrings #-}

import Data.Attoparsec.Text
import Data.Text
import Data.Char
import Control.Applicative
import qualified Data.List as List

import Term
import Item
import AxiomTag

-- the parser accepts for an item as utility also floating point numbers
-- TODO< remove this and read/parse numbers with negative sign >

data ItemParsed = ItemParsed {
		itemTag :: Text,
		t1 :: TermNodeParsed,
		t2 :: TermNodeParsed,
		utility :: Number
	}

-- we don't have to parse variables because they can't appear in text input, and we store all axioms and terms in a binary format
data TermNodeParsed =
	LeafTagParsed {leafTag :: Text} |
	BranchParsed {operation :: Text, left :: TermNodeParsed, right :: TermNodeParsed}
		deriving Show

isValidChar :: Char -> Bool
isValidChar char = isLetter char || isDigit char

parseOperation :: Parser Text
parseOperation =
	let
		patternList = [
			-- math
			"+", "-", "*", "/",

			-- equations
			">", ">=",
			"<", "<=",
			"==",

			-- logic???
			"<=>",

			-- misc
			"#"
			]
	in
		choice (List.map (\x -> string x) patternList)

parseIdentifier :: Parser Text
parseIdentifier = scan (pack "") isLetter
	where
		isLetter :: Text -> Char -> Maybe Text
		isLetter allreadyScaned char
			| isValidChar char = Just "a"
			| True             = Nothing

parseLeafTag :: Parser TermNodeParsed
parseLeafTag =
	do
		leafTag <- parseIdentifier
		return $ LeafTagParsed leafTag

parseTermNode = choice [parseBranch, parseBraceBranchX, parseBraceBranch, parseLeafTag]

parseTermNodeTerminal = choice [parseLeafTag, parseBranch, parseBraceBranchX, parseBraceBranch]

parseBranch :: Parser TermNodeParsed
parseBranch =
	do
		left <- parseTermNodeTerminal
		operation <- parseOperation
		right <- parseTermNode
		
		--right <- parseTermNode
		return $ BranchParsed operation left right

parseBraceBranch :: Parser TermNodeParsed
parseBraceBranch =
	do
		string "("
		left <- parseTermNodeTerminal
		operation <- parseOperation
		right <- parseTermNode
		string ")"
		return $ BranchParsed operation left right

-- combination of parseBraceBranch and the term on the right side
-- needed because the parser has problems with braces on the left
parseBraceBranchX :: Parser TermNodeParsed
parseBraceBranchX =
	do
		string "("
		left <- parseTermNode
		string ")"
		operation <- parseOperation
		right <- parseTermNode
		return $ BranchParsed operation left right

parseParserItem :: Parser ItemParsed
parseParserItem =
	do
		string "("
		itemType <- parseIdentifier
		string ","
		left <- parseTermNode
		string ","
		right <- parseTermNode
		string ","
		utility <- number
		string ")"

		return $ ItemParsed itemType left right utility
		

parseStringToParseTree input = parseOnly (parseTermNode <* endOfInput) (pack input)

parseStringToParseItem input = parseOnly (parseParserItem <* endOfInput) (pack input)

parseItem :: String -> Maybe Item
parseItem text =
	let
		parsingResult = parseStringToParseItem text
	in case parsingResult of
		Right tree -> Just (translateParseItemToItem tree)
		Left _ -> Nothing
	where
		translateParseItemToItem :: ItemParsed -> Item
		translateParseItemToItem (ItemParsed inputItemTag inputT1 inputT2 inputUtility) =
			let
				itemTag = stringToAxiomTag $ unpack inputItemTag
				t1 = translateTermParseTreeToTree inputT1
				t2 = translateTermParseTreeToTree inputT2
				utility = truncate inputUtility
			in
				(Item itemTag t1 t2 utility)


		translateTermParseTreeToTree :: TermNodeParsed -> TermNode
		translateTermParseTreeToTree (LeafTagParsed tag) = (LeafTag (unpack tag))
		translateTermParseTreeToTree (BranchParsed operation left right) =
			let
				transformedLeft  = translateTermParseTreeToTree left
				transformedRight = translateTermParseTreeToTree right
			in
				(Branch (TermData (unpack operation) transformedLeft transformedRight))


--parseTerm :: String -> Maybe TermNode
--parseTerm text =
--	let
--		parsingResult = parseStringToParseTree text
--	in case parsingResult of
--		Right tree -> Just (translateTermParseTreeToTree tree)
--		Left _ -> Nothing