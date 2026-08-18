//
// ::formally - the open-source formal methods toolchain
//
// Copyright (c) 2025 Nicola Gigante
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
//

//! The abstract syntax tree of SMT-LIBv2 source files.
//!
//! This module provides numerous types representing the grammar productions of the SMT-LIBv2
//! syntax as specified in the [specification manual](https://smt-lib.org/language.shtml).
//!
//! Each type has its implementation of [Parsable](formally::io::parse::Parsable) and
//! [Print](formally::io::print::Print) to be easily parsed and formatted.
//!
//! Even though each type is individually parsable, the most common entry points are [Script],
//! which represents a whole script file, and [Command], which represents a single command.

use crate::*;

use formally::support::*;

use derive_more::{Display, From};
use transitive::Transitive;

/// An entire SMT-LIBv2 script.
#[derive(Debug, Default, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Script {
    pub commands: Vec<Command>,
    pub span: Option<Span>,
}

/// A Boolean literal value.
#[derive(Debug, Clone, Default, Hash, PartialEq, Eq, Display, Located, Locatable)]
#[display("{value}")]
pub struct Boolean {
    pub value: bool,
    pub span: Option<Span>,
}

/// A base-10 integer literal value.
#[derive(Debug, Clone, Default, Hash, PartialEq, Eq, Display, Located, Locatable)]
#[display("{value}")]
pub struct Numeral {
    pub value: Integer,
    pub span: Option<Span>,
}

/// A base-10 rational literal value.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Display, Located, Locatable)]
#[display("{value}")]
pub struct Decimal {
    pub value: Rational,
    pub span: Option<Span>,
}

/// A base-16 integer literal value.
#[derive(Debug, Clone, Default, Hash, PartialEq, Eq, Display, Located, Locatable)]
#[display("{value:x}")]
pub struct Hexadecimal {
    pub value: Integer,
    pub span: Option<Span>,
}

/// A base-2 integer literal value.
#[derive(Debug, Clone, Default, Hash, PartialEq, Eq, Display, Located, Locatable)]
#[display("{value:b}")]
pub struct Binary {
    pub value: Integer,
    pub span: Option<Span>,
}

/// A string literal.
#[derive(Debug, Clone, Default, Hash, PartialEq, Eq, Display, Located, Locatable)]
#[display("{value}")]
pub struct StringLiteral {
    pub value: String,
    pub span: Option<Span>,
}

/// A constant value.
#[derive(Debug, Clone, Hash, PartialEq, Eq, From, Display, Located, Locatable)]
pub enum Constant {
    Numeral(Numeral),
    Decimal(Decimal),
    Hexadecimal(Hexadecimal),
    Binary(Binary),
    String(StringLiteral),
}

/// A quoted symbol (e.g. `|some:strange@symbol|`).
#[derive(Debug, Clone, Default, Hash, PartialEq, Eq, Located, Locatable)]
pub struct QuotedSymbol {
    pub value: String,
    pub span: Option<Span>,
}

/// A simple (non-quoted) symbol.
#[derive(Debug, Clone, Default, Hash, PartialEq, Eq, Located)]
pub struct SimpleSymbol {
    pub value: String,
    pub span: Option<Span>,
}

impl Locatable for SimpleSymbol {
    type Located = SimpleSymbol;

    fn over(self, span: impl Into<Option<Span>>) -> SimpleSymbol {
        SimpleSymbol {
            span: span.into(),
            ..self
        }
    }
}

/// A symbol.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub enum Symbol {
    Simple(SimpleSymbol),
    Quoted(QuotedSymbol),
}

/// A keyword.
#[derive(Debug, Clone, Default, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Keyword {
    pub symbol: SimpleSymbol,
    pub span: Option<Span>,
}

/// An element in an s-expression.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub enum SExprElement {
    Constant(Constant),
    Symbol(Symbol),
    Keyword(Keyword),
}

/// A list of elements in an s-expression.
#[derive(Debug, Default, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct SExprList {
    pub exprs: Vec<SExpr>,
    pub span: Option<Span>,
}

/// An s-expression.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub enum SExpr {
    Element(SExprElement),
    List(SExprList),
}

/// The application of a symbol to some indexes, e.g. `(_ BitVec 32)`
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct IdApplication {
    pub head: Symbol,
    pub args: Vec<Index>,
    pub span: Option<Span>,
}

/// An identifier, i.e. `Int` or `(_ BitVec 32)`.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub enum Identifier {
    Symbol(Symbol),
    Application(IdApplication),
}

/// An index in an application identifier.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub enum Index {
    Numeral(Numeral),
    Symbol(Symbol),
}

/// The application of a parametric sort, i.e. `(Array Int Int)`.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct SortApplication {
    pub head: Identifier,
    pub args: Vec<Sort>,
    pub span: Option<Span>,
}

/// A sort.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub enum Sort {
    Simple(Identifier),
    Application(SortApplication),
}

/// A qualified identifier, e.g. `x` or `(as x Int)`
#[derive(Debug, Clone, Hash, PartialEq, Eq, Transitive, Located, Locatable)]
#[transitive(from(Symbol, Identifier))]
pub struct QualifiedIdentifier {
    pub id: Identifier,
    pub sort: Option<Sort>,
    pub span: Option<Span>,
}

/// A simple data-type declaration.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct PlainDatatypeDecl {
    pub ctors: Vec<ConstructorDecl>,
    pub span: Option<Span>,
}

/// A parameterized data-type declaration.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct ParameterizedDatatypeDecl {
    pub symbols: Vec<Symbol>,
    pub ctors: Vec<ConstructorDecl>,
    pub span: Option<Span>,
}

/// A data-type declaration.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub enum DatatypeDecl {
    Plain(PlainDatatypeDecl),
    Parameterized(ParameterizedDatatypeDecl),
}

/// A constructor declaration in a data-type declaration.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct ConstructorDecl {
    pub name: Symbol,
    pub selectors: Vec<SelectorDecl>,
    pub span: Option<Span>,
}

/// A selector declaration in a data-type declaration.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct SelectorDecl {
    pub name: Symbol,
    pub sort: Sort,
    pub span: Option<Span>,
}

/// A sort declaration.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct SortDecl {
    pub name: Symbol,
    pub arity: Numeral,
    pub span: Option<Span>,
}

/// A function declaration.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct FunctionDef {
    pub name: Symbol,
    pub domain: Vec<SortedVar>,
    pub range: Sort,
    pub body: Term,
    pub span: Option<Span>,
}

/// A recursive function declaration.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct FunctionRecDef {
    pub name: Symbol,
    pub domain: Vec<SortedVar>,
    pub range: Sort,
    pub body: Term,
    pub span: Option<Span>,
}

/// A group of recursive functions declarations.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct RecFunctionsDef {
    pub defs: Vec<FunctionDef>,
    pub span: Option<Span>,
}

/// A sorted var (e.g. `(x Int)` in `(forall (x Int) (= x 0))`)
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct SortedVar {
    pub name: Symbol,
    pub sort: Sort,
    pub span: Option<Span>,
}

/// A function declaration.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct FunctionDecl {
    pub name: Symbol,
    pub parameters: Vec<SortedVar>,
    pub range: Sort,
    pub span: Option<Span>,
}

/// An info flag for `(set-info)` and `(get-info)`.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub enum InfoFlag {
    AllStatistics,
    AssertionStackLevels,
    Authors,
    ErrorBehavior,
    Name,
    ReasonUnknown,
    Version,
    Keyword(Keyword),
}

/// An attribute.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Attribute {
    pub keyword: Keyword,
    pub value: AttributeValue,
    pub span: Option<Span>,
}

/// A value for an attribute.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub enum AttributeValue {
    Constant(Constant),
    Symbol(Symbol),
    SExprList(SExprList),
}

/// An option for `(set-option)` and `(get-option)`.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub enum AstOption {
    DiagnosticOutputChannel(StringLiteral),
    GlobalDeclarations(Boolean),
    InteractiveMode(Boolean),
    PrintSuccess(Boolean),
    ProduceAssertions(Boolean),
    ProduceAssignments(Boolean),
    ProduceModels(Boolean),
    ProduceProofs(Boolean),
    ProduceUnsatAssumptions(Boolean),
    ProduceUnsatCores(Boolean),
    RandomSeed(Numeral),
    RegularOutputChannel(StringLiteral),
    ReproducibleResourceLimit(Numeral),
    Verbosity(Numeral),
    Attribute(Box<Attribute>),
}

/// A `(declare-const)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct DeclareConst {
    pub name: Symbol,
    pub sort: Sort,
    pub span: Option<Span>,
}

/// A `(declare-datatype)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct DeclareDatatype {
    pub name: Symbol,
    pub decl: DatatypeDecl,
    pub span: Option<Span>,
}

/// A `(declare-fun)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct DeclareFun {
    pub name: Symbol,
    pub domain: Vec<Sort>,
    pub range: Sort,
    pub span: Option<Span>,
}

/// A `(declare-sort)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct DeclareSort {
    pub name: Symbol,
    pub arity: Numeral,
    pub span: Option<Span>,
}

/// A `(define-const)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct DefineConst {
    pub name: Symbol,
    pub sort: Sort,
    pub body: Term,
    pub span: Option<Span>,
}

/// A `(define-sort)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct DefineSort {
    pub name: Symbol,
    pub parameters: Vec<Symbol>,
    pub body: Sort,
    pub span: Option<Span>,
}

/// A `(declare-datatypes)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct DeclareDatatypes {
    pub decls: Vec<(SortDecl, DatatypeDecl)>,
    pub span: Option<Span>,
}

/// A `(get-info)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct GetInfo {
    pub flag: InfoFlag,
    pub span: Option<Span>,
}

/// A `(get-option)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct GetOption {
    pub keyword: Keyword,
    pub span: Option<Span>,
}

/// A `(get-value)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct GetValue {
    pub terms: Vec<Term>,
    pub span: Option<Span>,
}

/// A `(pop)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Pop {
    pub levels: Numeral,
    pub span: Option<Span>,
}

/// A `(push)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Push {
    pub levels: Numeral,
    pub span: Option<Span>,
}

/// A `(set-info)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct SetInfo {
    pub attribute: Attribute,
    pub span: Option<Span>,
}

/// A `(set-logic)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct SetLogic {
    pub logic: Symbol,
    pub span: Option<Span>,
}

/// A `(set-option)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct SetOption {
    pub option: AstOption,
    pub span: Option<Span>,
}

/// An `(assert)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Assert {
    pub term: Term,
    pub span: Option<Span>,
}

/// A `(check-sat-assuming)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct CheckSatAssuming {
    pub assumptions: Vec<Term>,
    pub span: Option<Span>,
}

/// A command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, From, Located, Locatable)]
pub enum Command {
    Assert(Assert),
    #[from(skip)]
    CheckSat(Option<Span>),
    CheckSatAssuming(CheckSatAssuming),
    DeclareConst(DeclareConst),
    DeclareDatatype(DeclareDatatype),
    DeclareDatatypes(DeclareDatatypes),
    DeclareFun(DeclareFun),
    DeclareSort(DeclareSort),
    DeclareSortParameter(Symbol),
    DefineConst(DefineConst),
    DefineFun(FunctionDef),
    DefineFunRec(FunctionRecDef),
    DefineFunsRec(RecFunctionsDef),
    DefineSort(DefineSort),
    Echo(StringLiteral),
    #[from(skip)]
    Exit(Option<Span>),
    #[from(skip)]
    GetAssertions(Option<Span>),
    #[from(skip)]
    GetAssignments(Option<Span>),
    GetInfo(GetInfo),
    #[from(skip)]
    GetModel(Option<Span>),
    GetOption(GetOption),
    #[from(skip)]
    GetProof(Option<Span>),
    #[from(skip)]
    GetUnsatAssumptions(Option<Span>),
    #[from(skip)]
    GetUnsatCore(Option<Span>),
    GetValue(GetValue),
    Pop(Pop),
    Push(Push),
    #[from(skip)]
    Reset(Option<Span>),
    #[from(skip)]
    ResetAssertions(Option<Span>),
    SetInfo(SetInfo),
    SetLogic(SetLogic),
    SetOption(SetOption),
}

impl Command {
    pub fn name(&self) -> &str {
        match self {
            Command::Assert(_) => "assert",
            Command::CheckSat(_) => "check-sat",
            Command::CheckSatAssuming(_) => "check-sat-assuming",
            Command::DeclareConst(_) => "declare-const",
            Command::DeclareDatatype(_) => "declare-datatype",
            Command::DeclareDatatypes(_) => "declare-datatypes",
            Command::DeclareFun(_) => "declare-fun",
            Command::DeclareSort(_) => "declare-sort",
            Command::DeclareSortParameter(_) => "declare-sort-parameter",
            Command::DefineConst(_) => "define-const",
            Command::DefineFun(_) => "define-fun",
            Command::DefineFunRec(_) => "define-fun-rec",
            Command::DefineFunsRec(_) => "define-funs-rec",
            Command::DefineSort(_) => "define-sort",
            Command::Echo(_) => "echo",
            Command::Exit(_) => "exit",
            Command::GetAssertions(_) => "get-assertions",
            Command::GetAssignments(_) => "get-assignments",
            Command::GetInfo(_) => "get-info",
            Command::GetModel(_) => "get-model",
            Command::GetOption(_) => "get-option",
            Command::GetProof(_) => "get-proof",
            Command::GetUnsatAssumptions(_) => "get-unsat-assumptions",
            Command::GetUnsatCore(_) => "get-unsat-core",
            Command::GetValue(_) => "get-value",
            Command::Pop(_) => "pop",
            Command::Push(_) => "push",
            Command::Reset(_) => "reset",
            Command::ResetAssertions(_) => "reset-assertions",
            Command::SetInfo(_) => "set-info",
            Command::SetLogic(_) => "set-logic",
            Command::SetOption(_) => "set-option",
        }
    }
}

/// An application of an identifier to arguments, e.g. `(= a b)`
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Application {
    pub head: QualifiedIdentifier,
    pub args: Vec<Term>,
    pub span: Option<Span>,
}

/// A `let` term.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Let {
    pub bindings: Vec<Binding>,
    pub body: Box<Term>,
    pub span: Option<Span>,
}

/// A variable binding in a `let` term.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Binding {
    pub name: Symbol,
    pub body: Term,
    pub span: Option<Span>,
}

/// A `lambda` term.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Lambda {
    pub bindings: Vec<SortedVar>,
    pub body: Box<Term>,
    pub span: Option<Span>,
}

/// An existential quantifier.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Exists {
    pub bindings: Vec<SortedVar>,
    pub body: Box<Term>,
    pub span: Option<Span>,
}

/// A universal quantifier.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Forall {
    pub bindings: Vec<SortedVar>,
    pub body: Box<Term>,
    pub span: Option<Span>,
}

/// A `match` expression.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Match {
    pub head: Box<Term>,
    pub cases: Vec<MatchCase>,
    pub span: Option<Span>,
}

/// A case in a `match` expression.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct MatchCase {
    pub pattern: Pattern,
    pub body: Term,
    pub span: Option<Span>,
}

/// A symbol pattern in a `match` expression.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct SymbolPattern {
    pub symbol: Option<Symbol>,
    pub span: Option<Span>,
}

/// An application pattern in a `match` expression.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct ApplicationPattern {
    pub head: Symbol,
    pub args: Vec<SymbolPattern>,
    pub span: Option<Span>,
}

/// A pattern in a `match` expression.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub enum Pattern {
    Symbol(SymbolPattern),
    Application(ApplicationPattern),
}

/// A term with an attribute attached.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Attributed {
    pub term: Box<Term>,
    pub attributes: Vec<Attribute>,
    pub span: Option<Span>,
}

/// A term.
#[allow(clippy::duplicated_attributes)]
#[derive(Debug, Clone, Hash, PartialEq, Eq, From, Transitive, Located, Locatable)]
#[transitive(from(Numeral, Constant))]
#[transitive(from(Decimal, Constant))]
#[transitive(from(Hexadecimal, Constant))]
#[transitive(from(Binary, Constant))]
#[transitive(from(StringLiteral, Constant))]
#[transitive(from(Identifier, QualifiedIdentifier))]
#[transitive(from(Symbol, Identifier))]
pub enum Term {
    Constant(Constant),
    Identifier(QualifiedIdentifier),
    Application(Application),
    Let(Let),
    Lambda(Lambda),
    Exists(Exists),
    Forall(Forall),
    Match(Match),
    Attributed(Attributed),
}

/// An error response.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct ErrorResponse {
    pub error: StringLiteral,
    pub span: Option<Span>,
}

/// The response of a `(check-sat)` or `(check-sat-assuming)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct CheckSatResponse {
    pub response: Option<bool>,
    pub span: Option<Span>,
}

/// The response of an `(echo)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct EchoResponse {
    pub msg: StringLiteral,
    pub span: Option<Span>,
}

/// The response of a `(get-assertions)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct GetAssertionsResponse {
    pub assertions: Vec<Term>,
    pub span: Option<Span>,
}

/// The response of a `(get-assignment)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct GetAssignmentResponse {
    pub assignments: Vec<(Symbol, Boolean)>,
    pub span: Option<Span>,
}

/// The response of a `(get-info)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct GetInfoResponse {
    pub infos: Vec<Info>,
    pub span: Option<Span>,
}

/// The response of a `(get-model)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct GetModelResponse {
    pub models: Vec<Model>,
    pub span: Option<Span>,
}

/// The response of a `(get-option)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct GetOptionResponse {
    pub value: AttributeValue,
    pub span: Option<Span>,
}

/// The response of a `(get-proof)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct GetProofResponse {
    pub proof: SExpr,
    pub span: Option<Span>,
}

/// The response of a `(get-unsat-assumption)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct GetUnsatAssumptionResponse {
    pub assumption: Vec<Term>,
    pub span: Option<Span>,
}

/// The response of a `(get-unsat-core)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct GetUnsatCoreResponse {
    pub core: Vec<Symbol>,
    pub span: Option<Span>,
}

/// The response of a `(get-value)` command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct GetValueResponse {
    pub values: Vec<(Term, Term)>,
    pub span: Option<Span>,
}

/// The response to a command.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub enum Response {
    Success,
    Unsupported,
    Error(StringLiteral),
    CheckSat(CheckSatResponse),
    Echo(EchoResponse),
    GetAssertions(GetAssertionsResponse),
    GetAssignment(GetAssignmentResponse),
    GetInfo(GetInfoResponse),
    GetModel(GetModelResponse),
    GetOption(GetOptionResponse),
    GetProof(GetProofResponse),
    GetUnsatAssumption(GetUnsatAssumptionResponse),
    GetUnsatCore(GetUnsatCoreResponse),
    GetValue(GetValueResponse),
}

/// A value for the `:error-behavior` flag
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub enum ErrorBehavior {
    ImmediateExit,
    ContinuedExecution,
}

/// A value for the `:reason-unknown` flag
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub enum ReasonUnknown {
    Memout,
    Incomplete,
    SExpr(SExpr),
}

/// A value for flags.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub enum Info {
    AssertionStackLevels(Numeral),
    Authors(StringLiteral),
    ErrorBehavior(ErrorBehavior),
    Name(StringLiteral),
    ReasonUnknown(ReasonUnknown),
    Version(StringLiteral),
    Attribute(Attribute),
}

/// A model.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub enum Model {
    DefineFun(FunctionDef),
    DefineFunRec(FunctionDef),
    DefineFunsRec(RecFunctionsDef),
}

impl QuotedSymbol {
    pub fn admitted(c: char) -> bool {
        (c.is_ascii_graphic() || c.is_ascii_whitespace()) && c != '|' && c != '\\'
    }

    pub fn new(s: &str) -> Option<QuotedSymbol> {
        if s.chars().all(QuotedSymbol::admitted) {
            Some(QuotedSymbol {
                value: s.to_string(),
                span: None,
            })
        } else {
            None
        }
    }

    pub fn inner(&self) -> &str {
        &self.value
    }

    pub fn into_inner(self) -> String {
        self.value
    }
}

impl Symbol {
    pub fn new(s: &str) -> Option<Symbol> {
        if let Some(sy) = SimpleSymbol::new(s) {
            Some(Symbol::Simple(sy))
        } else {
            QuotedSymbol::new(s).map(Symbol::Quoted)
        }
    }

    pub fn simplify(self) -> Symbol {
        match self {
            Symbol::Simple(sy) => Symbol::Simple(sy),
            Symbol::Quoted(sy) => {
                if let Some(simple) = SimpleSymbol::new(sy.inner()) {
                    Symbol::Simple(simple.over(sy.span))
                } else {
                    Symbol::Quoted(sy)
                }
            }
        }
    }

    pub fn inner(&self) -> &str {
        match self {
            Symbol::Simple(sy) => sy.inner(),
            Symbol::Quoted(sy) => sy.inner(),
        }
    }

    pub fn into_inner(self) -> String {
        match self {
            Symbol::Simple(sy) => sy.into_inner(),
            Symbol::Quoted(sy) => sy.into_inner(),
        }
    }
}

impl SimpleSymbol {
    const RESERVED: [&'static str; 46] = [
        "_",
        "NUMERAL",
        "par",
        "STRING",
        "as",
        "BINARY",
        "DECIMAL",
        "exists",
        "HEXADECIMAL",
        "forall",
        "lambda",
        "let",
        "match",
        "Command",
        "names:",
        "assert",
        "check-sat",
        "check-sat-assuming",
        "declare-const",
        "declare-datatype",
        "declare-datatypes",
        "declare-fun",
        "declare-sort",
        "declare-sort-parameter",
        "define-const",
        "define-fun",
        "define-fun-rec",
        "define-sort",
        "echo",
        "exit",
        "get-assertions",
        "get-assignment",
        "get-info",
        "get-model",
        "get-option",
        "get-proof",
        "get-unsat-assumptions",
        "get-unsat-core",
        "get-value",
        "pop",
        "push",
        "reset",
        "reset-assertions",
        "set-info",
        "set-logic",
        "set-option",
    ];

    pub fn admitted(c: char) -> bool {
        matches!(c,
              'a'..='z'
            | 'A'..='Z'
            | '0'..='9'
            | '+'
            | '-'
            | '/'
            | '*'
            | '='
            | '%'
            | '?'
            | '!'
            | '.'
            | '$'
            | '_'
            | '&'
            | '^'
            | '<'
            | '>'
            | '@'
        )
    }

    pub fn invalid(s: &str) -> bool {
        s.is_empty() || s.chars().nth(0).unwrap().is_ascii_digit() || Self::RESERVED.contains(&s)
    }

    pub fn new(s: &str) -> Option<SimpleSymbol> {
        if s.chars().all(SimpleSymbol::admitted) && !SimpleSymbol::invalid(s) {
            Some(SimpleSymbol {
                value: s.to_string(),
                span: None,
            })
        } else {
            None
        }
    }

    pub fn inner(&self) -> &str {
        &self.value
    }

    pub fn into_inner(self) -> String {
        self.value
    }
}

impl From<Symbol> for Identifier {
    fn from(value: Symbol) -> Self {
        Identifier::Symbol(value)
    }
}

impl From<Identifier> for QualifiedIdentifier {
    fn from(id: Identifier) -> Self {
        QualifiedIdentifier {
            id,
            sort: None,
            span: None,
        }
    }
}

impl TryFrom<AttributeValue> for StringLiteral {
    type Error = ();

    fn try_from(value: AttributeValue) -> Result<Self, Self::Error> {
        match value {
            AttributeValue::Constant(Constant::String(s)) => Ok(s),
            _ => Err(()),
        }
    }
}

impl TryFrom<AttributeValue> for Boolean {
    type Error = ();

    fn try_from(value: AttributeValue) -> Result<Self, Self::Error> {
        let span = value.span();
        match value {
            AttributeValue::Constant(Constant::String(s)) => {
                if s.value == "true" {
                    Ok(Boolean { value: true, span })
                } else if s.value == "false" {
                    Ok(Boolean { value: false, span })
                } else {
                    Err(())
                }
            }
            _ => Err(()),
        }
    }
}

impl TryFrom<AttributeValue> for Numeral {
    type Error = ();

    fn try_from(value: AttributeValue) -> Result<Self, Self::Error> {
        match value {
            AttributeValue::Constant(Constant::Numeral(n)) => Ok(n),
            _ => Err(()),
        }
    }
}

impl TryFrom<Attribute> for AstOption {
    type Error = ();

    fn try_from(attr: Attribute) -> Result<Self, ()> {
        match attr.keyword.symbol.value.as_str() {
            "diagnostic-output-channel" => Ok(AstOption::DiagnosticOutputChannel(
                StringLiteral::try_from(attr.value)?,
            )),
            "global-declarations" => Ok(AstOption::GlobalDeclarations(Boolean::try_from(
                attr.value,
            )?)),
            "interactive-mode" => Ok(AstOption::InteractiveMode(Boolean::try_from(attr.value)?)),
            "print-success" => Ok(AstOption::PrintSuccess(Boolean::try_from(attr.value)?)),
            "produce-assertions" => {
                Ok(AstOption::ProduceAssertions(Boolean::try_from(attr.value)?))
            }
            "produce-assignments" => Ok(AstOption::ProduceAssignments(Boolean::try_from(
                attr.value,
            )?)),
            "produce-models" => Ok(AstOption::ProduceModels(Boolean::try_from(attr.value)?)),
            "produce-proofs" => Ok(AstOption::ProduceProofs(Boolean::try_from(attr.value)?)),
            "produce-unsat-assumptions" => Ok(AstOption::ProduceUnsatAssumptions(
                Boolean::try_from(attr.value)?,
            )),
            "produce-unsat-cores" => {
                Ok(AstOption::ProduceUnsatCores(Boolean::try_from(attr.value)?))
            }
            "random-seet" => Ok(AstOption::RandomSeed(Numeral::try_from(attr.value)?)),
            "regular-output-channel" => Ok(AstOption::RegularOutputChannel(
                StringLiteral::try_from(attr.value)?,
            )),
            "reproducible-resource-limit" => Ok(AstOption::ReproducibleResourceLimit(
                Numeral::try_from(attr.value)?,
            )),
            "verbosity" => Ok(AstOption::Verbosity(Numeral::try_from(attr.value)?)),
            _ => Ok(AstOption::Attribute(Box::new(attr))),
        }
    }
}
