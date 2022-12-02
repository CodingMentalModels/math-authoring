use crate::math::types::{SimpleType, CompoundType};

#[derive(Debug)]
pub struct Statement {
    quantifiers: Vec<Quantifier>,
    subject: SymbolNode,
}

impl Statement {

    pub fn new(quantifiers: Vec<Quantifier>, subject: impl Into<SymbolNode>) -> Statement {
        Statement { quantifiers, subject: subject.into() }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Quantifier {
    All(Symbol, CompoundType),
    Exists(Symbol, CompoundType),
    NotAll(Symbol, CompoundType),
    NotExists(Symbol, CompoundType),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymbolNode {
    symbol: Symbol,
    children: Vec<SymbolNode>,
}

impl From<Symbol> for SymbolNode {
    fn from(symbol: Symbol) -> Self {
        SymbolNode::singleton(symbol)
    }
}

impl SymbolNode {

    pub fn new(symbol: Symbol, children: Vec<impl Into<SymbolNode>>) -> SymbolNode {
        SymbolNode { symbol, children: children.into_iter().map(|child| child.into()).collect() }
    }

    pub fn singleton(symbol: Symbol) -> SymbolNode {
        SymbolNode::new(symbol, Vec::<SymbolNode>::new())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Symbol {
    name: String,
}

impl Symbol {

    pub fn new(name: &str) -> Symbol {
        Symbol { name: name.to_string() }
    }
}

#[cfg(test)]
mod test_statement {
    use super::*;

    #[test]
    fn test_statement_transforms() {
        
        let statement = Statement::new(
            vec![
                Quantifier::Exists(Symbol::new("*"), CompoundType::new(vec![SimpleType::Object, SimpleType::Object, SimpleType::Object])),
                Quantifier::All(Symbol::new("x"), SimpleType::Object.into()),
                Quantifier::Exists(Symbol::new("e"), SimpleType::Object.into())],
            SymbolNode::new(
                Symbol::new(
                "*",
                ),
                vec![
                    Symbol::new(
                        "x",
                    ),
                    Symbol::new(
                        "e",
                    )
                ]
            )
        );
        
        // let transformed = statement.transform(transformation);
        
    }
}