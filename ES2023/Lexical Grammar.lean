/-
[12 ECMAScript Language: Lexical Grammar](https://262.ecma-international.org/14.0/#sec-ecmascript-language-lexical-grammar)
-/

#check Lean.Syntax
#check Lean.Syntax.CharLit
-- #check Lean.Parser.prattParser
-- #check Lean.Parser.getNext
-- #check Lean.Language.Lean.process
-- #check Lean.Data.Trie
-- #check Lean.PrettyPrinter.Formatter.interpretParserDescr

inductive WhiteSpace
  | TAB | VT | FF | ZWNBSP | USP

inductive LineTerminator
  | LF | CR | LS | PS

inductive DivPunctuator
  | «/» | «/=»

inductive RightBracePunctuator
  | «}»

inductive Comment
  | MultiLineComment
  | SingleLineComment

inductive CommonToken
  | IdentifierName
  | PrivateIdentifier
  | Punctuator
  | NumericLiteral
  | StringLiteral
  | Template

inductive InputElementDiv
  | WhiteSpace (terminal : WhiteSpace)
  | LineTerminator (terminal : LineTerminator)
  | Comment (comment : Comment)
  | CommonToken (commonToken : CommonToken)
  | DivPunctuator (terminal : DivPunctuator)
  | RightBracePunctuator (codePoint : RightBracePunctuator)

inductive InputElementRegExp
  | WhiteSpace (terminal : WhiteSpace)
  | LineTerminator (terminal : LineTerminator)
  | Comment (comment : Comment)
  | CommonToken (commonToken : CommonToken)
  | RightBracePunctuator (terminal : RightBracePunctuator)
  | RegularExpressionLiteral

inductive InputElementRegExpOrTemplateTail
  | WhiteSpace (terminal : WhiteSpace)
  | LineTerminator (terminal : LineTerminator)
  | Comment (comment : Comment)
  | CommonToken (commonToken : CommonToken)
  | RegularExpressionLiteral
  | TemplateSubstitutionTail

inductive InputElementTemplateTail
  | WhiteSpace
  | LineTerminator
  | Comment
  | CommonToken
  | DivPunctuator
  | TemplateSubstitutionTail

inductive InputElementHashbangOrRegExp
  | WhiteSpace
  | LineTerminator
  | Comment
  | CommonToken
  | HashbangComment
  | RegularExpressionLiteral
