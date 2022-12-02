use crate::math::types::{CompoundType};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Transformation {
    from: Statement,
    to: Statement,
}

impl Transformation {

    pub fn new(from: Statement, to: Statement) -> Transformation {
        Transformation { from, to }
    }

    pub fn get_from(&self) -> &Statement {
        &self.from
    }

    pub fn get_to(&self) -> &Statement {
        &self.to
    }

    pub fn transform(&self, statement: &Statement) -> Result<Statement, String> {
        if statement == &self.from {
            Ok(self.to.clone())
        } else {
            Err("Cannot transform statement.".to_string())
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Statement {
    quantifiers: Vec<Quantifier>,
    subject: SymbolNode,
}

impl Statement {

    pub fn new(quantifiers: Vec<Quantifier>, subject: impl Into<SymbolNode>) -> Statement {
        Statement { quantifiers, subject: subject.into() }
    }

    pub fn substitute(&self, from_symbol: &Symbol, to_symbol: &Symbol) -> Statement {
        Statement::new(Quantifier::substitute_all(&self.quantifiers, from_symbol, to_symbol), self.subject.substitute(from_symbol, to_symbol))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Quantifier {
    All(Symbol, CompoundType),
    Exists(Symbol, CompoundType),
    NotAll(Symbol, CompoundType),
    NotExists(Symbol, CompoundType),
}

impl Quantifier {

    pub fn substitute(&self, _from_symbol: &Symbol, _to_symbol: &Symbol) -> Quantifier {
        match self {
            Quantifier::All(symbol, compound_type) => Quantifier::All(symbol.clone(), compound_type.clone()),
            Quantifier::Exists(symbol, compound_type) => Quantifier::Exists(symbol.clone(), compound_type.clone()),
            Quantifier::NotAll(symbol, compound_type) => Quantifier::NotAll(symbol.clone(), compound_type.clone()),
            Quantifier::NotExists(symbol, compound_type) => Quantifier::NotExists(symbol.clone(), compound_type.clone()),
        }
    }

    pub fn substitute_all(quantifiers: &Vec<Self>, from_symbol: &Symbol, to_symbol: &Symbol) -> Vec<Self> {
        quantifiers.iter().map(|quantifier| quantifier.substitute(from_symbol, to_symbol)).collect()
    }
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

impl From<&str> for SymbolNode {
    fn from(symbol: &str) -> Self {
        SymbolNode::singleton(symbol)
    }
}

impl SymbolNode {

    pub fn new(symbol: impl Into<Symbol>, children: Vec<impl Into<SymbolNode>>) -> SymbolNode {
        SymbolNode { symbol: symbol.into(), children: children.into_iter().map(|child| child.into()).collect() }
    }

    pub fn singleton(symbol: impl Into<Symbol>) -> SymbolNode {
        SymbolNode::new(symbol.into(), Vec::<SymbolNode>::new())
    }

    pub fn unary(symbol: impl Into<Symbol>, child: impl Into<SymbolNode>) -> SymbolNode {
        SymbolNode::new(symbol.into(), vec![child])
    }

    pub fn binary(symbol: impl Into<Symbol>, left: impl Into<SymbolNode>, right: impl Into<SymbolNode>) -> SymbolNode {
        SymbolNode::new(symbol.into(), vec![left.into(), right.into()])
    }

    pub fn ternary(symbol: impl Into<Symbol>, left: impl Into<SymbolNode>, middle: impl Into<SymbolNode>, right: impl Into<SymbolNode>) -> SymbolNode {
        SymbolNode::new(symbol.into(), vec![left.into(), middle.into(), right.into()])
    }

    pub fn substitute(&self, from_symbol: &Symbol, to_symbol: &Symbol) -> SymbolNode {
        let contents = if self.symbol == *from_symbol {
            to_symbol.clone()
        } else {
            self.symbol.clone()
        };
        SymbolNode::new(contents, self.children.iter().map(|child| child.substitute(from_symbol, to_symbol)).collect())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Symbol {
    name: String,
}

impl From<&str> for Symbol {
    fn from(name: &str) -> Self {
        Symbol::new(name)
    }
}

impl Symbol {

    pub fn new(name: &str) -> Symbol {
        Symbol { name: name.to_string() }
    }
}

#[cfg(test)]
mod test_statement {
    use crate::math::types::SimpleType;

    use super::*;

    #[test]
    fn test_statement_transforms() {
        
        let statement = Statement::new(
            vec![
                Quantifier::Exists(Symbol::new("="), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                Quantifier::All(Symbol::new("x"), SimpleType::Object.into()),
                Quantifier::All(Symbol::new("y"), SimpleType::Object.into())],
            SymbolNode::binary(
                "=",
                "x",
                "y",
            )
        );

        let x_equals_y = Statement::new(
            vec![
                Quantifier::Exists("=".into(), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                Quantifier::All("x".into(), SimpleType::Object.into()),
                Quantifier::All("y".into(), SimpleType::Object.into()),
            ],
            SymbolNode::new(
                Symbol::new("="),
                vec![
                    Into::<SymbolNode>::into("x"),
                    Into::<SymbolNode>::into("y"),
                ],
            ),
        );
        let x_equals_z = x_equals_y.substitute(&"y".into(), &"z".into());

        let transformation = Transformation::new(
            x_equals_y.clone(),
            x_equals_z.clone(),
        );

        assert_eq!(statement, x_equals_y);
        
        let transformed = transformation.transform(&statement).unwrap();
        
        assert_eq!(transformed, x_equals_z);

    }
}