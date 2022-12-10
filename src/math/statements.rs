use std::{collections::{HashMap, HashSet}, fmt::{Display, Formatter, self}, error::Error};

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

    pub fn transform_strict(&self, statement: &Statement) -> Result<Statement, String> {
        if statement == &self.from {
            Ok(self.to.clone())
        } else {
            Err(format!("Cannot transform statement: {} != {}", statement, self.from))
        }
    }

    pub fn transform(&self, statement: &Statement, mapping: &HashMap<Symbol, Symbol>) -> Result<Statement, String> {
        let mapped_transform = self.substitute_all(mapping)?;
        mapped_transform.transform_strict(statement)
    }

    pub fn substitute_all(&self, mapping: &HashMap<Symbol, Symbol>) -> Result<Transformation, String> {
        Ok(Transformation::new(self.from.substitute_all(mapping)?, self.to.substitute_all(mapping)?))
    }

}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Statement {
    quantifiers: Vec<Quantifier>,
    subject: SymbolNode,
}

impl Display for Statement {
    
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            write!(f, "{} {}", self.quantifiers.iter().map(|q| format!("{}", q)).collect::<Vec<_>>().join(" "), self.subject)
        }
}

impl Statement {

    pub fn new(quantifiers: Vec<Quantifier>, subject: impl Into<SymbolNode>) -> Statement {
        Statement { quantifiers, subject: subject.into() }
    }

    pub fn substitute(&self, from_symbol: &Symbol, to_symbol: &Symbol) -> Result<Statement, String> {
        Ok(Statement::new(Quantifier::substitute_several(&self.quantifiers, from_symbol, to_symbol)?, self.subject.substitute(from_symbol, to_symbol)))
    }

    pub fn substitute_all(&self, mapping: &HashMap<Symbol, Symbol>) -> Result<Statement, String> {
        let quantifiers = Quantifier::substitute_several_all(&self.quantifiers, mapping)?;
        let subject = self.subject.clone().substitute_all(mapping);
        Ok(Statement::new(quantifiers, subject))
    }
}


#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Quantifier {
    All(Symbol, CompoundType),
    Exists(Symbol, CompoundType),
    NotAll(Symbol, CompoundType),
    NotExists(Symbol, CompoundType),
}

impl Display for Quantifier {

    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Quantifier::All(symbol, compound_type) => write!(f, "∀{}:{}", symbol, compound_type),
            Quantifier::Exists(symbol, compound_type) => write!(f, "∃{}:{}", symbol, compound_type),
            Quantifier::NotAll(symbol, compound_type) => write!(f, "¬∀{}:{}", symbol, compound_type),
            Quantifier::NotExists(symbol, compound_type) => write!(f, "¬∃{}:{}", symbol, compound_type),
        }
    }
}

impl Quantifier {

    pub fn get_symbol(&self) -> Symbol {
        match self {
            Quantifier::All(symbol, _) => symbol.clone(),
            Quantifier::Exists(symbol, _) => symbol.clone(),
            Quantifier::NotAll(symbol, _) => symbol.clone(),
            Quantifier::NotExists(symbol, _) => symbol.clone(),
        }
    }

    pub fn substitute(&self, from_symbol: &Symbol, to_symbol: &Symbol) -> Quantifier {
        if &self.get_symbol() != from_symbol {
            return self.clone();
        }
        match self {
            Quantifier::All(_, compound_type) => Quantifier::All(to_symbol.clone(), compound_type.clone()),
            Quantifier::Exists(_, compound_type) => Quantifier::Exists(to_symbol.clone(), compound_type.clone()),
            Quantifier::NotAll(_, compound_type) => Quantifier::NotAll(to_symbol.clone(), compound_type.clone()),
            Quantifier::NotExists(_, compound_type) => Quantifier::NotExists(to_symbol.clone(), compound_type.clone()),
        }
    }

    pub fn substitute_several(quantifiers: &Vec<Self>, from_symbol: &Symbol, to_symbol: &Symbol) -> Result<Vec<Self>, String> {
        let to_return = quantifiers.iter().map(|quantifier| quantifier.substitute(from_symbol, to_symbol)).collect();
        if Self::is_duplicative(&to_return) {
            Err(format!("Quantifiers {:?} are duplicative", quantifiers))
        } else {
            Ok(to_return)
        }
    }

    pub fn substitute_several_all(quantifiers: &Vec<Self>, mapping: &HashMap<Symbol, Symbol>) -> Result<Vec<Self>, String> {
        let mut new_quantifiers = quantifiers.clone();
        for (from_symbol, to_symbol) in mapping {
            new_quantifiers = Quantifier::substitute_several(&new_quantifiers, &from_symbol, &to_symbol)?;
        }
        Ok(new_quantifiers)
    }

    pub fn is_duplicative(quantifiers: &Vec<Self>) -> bool {
        quantifiers.iter().collect::<HashSet<_>>().len() != quantifiers.len()
    }

}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct SymbolNode {
    symbol: Symbol,
    children: Vec<SymbolNode>,
}

impl Display for SymbolNode {
    
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.symbol);
            if !self.children.is_empty() {
                write!(f, "(")?;
                for (i, child) in self.children.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", child)?;
                }
                write!(f, ")")?;
            }
            Ok(())
        }
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

    pub fn substitute_all(&self, substitutions: &HashMap<Symbol, Symbol>) -> Self {
        let from_to_unambiguous: HashMap<Symbol, Symbol> = substitutions.iter().enumerate().map(|(i, (from, to))| (from.clone(), Symbol::new(&i.to_string()))).collect();
        let to_to_unambiguous: HashMap<Symbol, Symbol> = substitutions.iter().enumerate().map(|(i, (from, to))| (Symbol::new(&i.to_string()), to.clone())).collect();

        let unambiguous = self.substitute_all_unchecked(&from_to_unambiguous);
        unambiguous.substitute_all_unchecked(&to_to_unambiguous)
    }

    fn substitute_all_unchecked(&self, substitutions: &HashMap<Symbol, Symbol>) -> Self {
        let mut to_return = self.clone();
        for (from, to) in substitutions {
            to_return = to_return.substitute(&from, &to);
        }
        return to_return;
    }

}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Symbol {
    name: String,
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
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
    fn test_statement_transforms_strictly() {
        
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
        let x_equals_z = x_equals_y.substitute(&"y".into(), &"z".into()).unwrap();

        let transformation = Transformation::new(
            x_equals_y.clone(),
            x_equals_z.clone(),
        );

        assert_eq!(statement, x_equals_y);
        
        let transformed = transformation.transform_strict(&statement).unwrap();
        
        assert_eq!(transformed, x_equals_z);

    }

    #[test]
    fn test_statement_transforms() {
        
        let statement = Statement::new(
            vec![
                Quantifier::Exists(Symbol::new("="), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                Quantifier::All(Symbol::new("a"), SimpleType::Object.into()),
                Quantifier::All(Symbol::new("b"), SimpleType::Object.into()),
                ],
            SymbolNode::binary(
                "=",
                "a",
                "b",
            )
        );

        let transformation = Transformation::new(
            Statement::new(
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
            ),
            Statement::new(
                vec![
                    Quantifier::Exists("=".into(), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                    Quantifier::All("x".into(), SimpleType::Object.into()),
                ],
                SymbolNode::new(
                    Symbol::new("="),
                    vec![
                        Into::<SymbolNode>::into("x"),
                        Into::<SymbolNode>::into("x"),
                    ],
                ),
            ),
        );

        let transformed = transformation.transform(
            &statement,
            &vec![("x".into(), "a".into()), ("y".into(), "b".into())].into_iter().collect()
        ).unwrap();
        
        let expected = Statement::new(
            vec![
                Quantifier::Exists("=".into(), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                Quantifier::All("a".into(), SimpleType::Object.into()),
            ],
            SymbolNode::new(
                Symbol::new("="),
                vec![
                    Into::<SymbolNode>::into("a"),
                    Into::<SymbolNode>::into("a"),
                ],
            ),
        );

        assert_eq!(transformed, expected, "transformed != statement: {} != {}", transformed, statement);

    }

    #[test]
    fn test_statement_substitutes() {
        
        let statement = Statement::new(
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

        let x_to_a = statement.substitute(&"x".into(), &"a".into()).unwrap();

        let expected = Statement::new(
            vec![
                Quantifier::Exists("=".into(), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                Quantifier::All("a".into(), SimpleType::Object.into()),
                Quantifier::All("y".into(), SimpleType::Object.into()),
            ],
            SymbolNode::new(
                Symbol::new("="),
                vec![
                    Into::<SymbolNode>::into("a"),
                    Into::<SymbolNode>::into("y"),
                ],
            ),
        );

        assert_eq!(x_to_a, expected, "{} != {}", x_to_a, expected);

        let x_and_y_to_a = statement.substitute_all(
            &vec![
                ("x".into(), "a".into()),
                ("y".into(), "a".into()),
            ].into_iter().collect()
        ).unwrap();

        let expected = Statement::new(
            vec![
                Quantifier::Exists("=".into(), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                Quantifier::All("a".into(), SimpleType::Object.into()),
                Quantifier::All("a".into(), SimpleType::Object.into()),
            ],
            SymbolNode::new(
                Symbol::new("="),
                vec![
                    Into::<SymbolNode>::into("a"),
                    Into::<SymbolNode>::into("a"),
                ],
            ),
        );

        assert_eq!(x_and_y_to_a, expected, "{} != {}", x_and_y_to_a, expected);

    }

    #[test]
    fn test_quantifier_substitutes() {
        
        let quantifier = Quantifier::All("x".into(), SimpleType::Object.into());
        assert_eq!(quantifier.substitute(&Symbol::from("x"), &Symbol::from("a")), Quantifier::All("a".into(), SimpleType::Object.into()));
    
        let quantifiers = vec![
            Quantifier::All("x".into(), SimpleType::Object.into()),
            Quantifier::All("y".into(), SimpleType::Object.into()),
            Quantifier::All("z".into(), SimpleType::Object.into()),
        ];
        assert_eq!(Quantifier::substitute_several_all(&quantifiers, 
            &vec![
                ("x".into(), "a".into()),
                ("y".into(), "b".into()),
                ("z".into(), "c".into()),
            ].into_iter().collect(),
        ).unwrap(),
            vec![
                Quantifier::All("a".into(), SimpleType::Object.into()),
                Quantifier::All("b".into(), SimpleType::Object.into()),
                Quantifier::All("c".into(), SimpleType::Object.into()),
            ]
        );
    }
    
    #[test]
    fn test_symbol_tree_substitutes() {
        
        let symbol_tree = SymbolNode::ternary("+", "a", "b", "c");
        assert_eq!(symbol_tree.substitute(&"b".into(), &"d".into()), SymbolNode::ternary("+", "a", "d", "c"));
        assert_eq!(symbol_tree.substitute(&"c".into(), &"d".into()), SymbolNode::ternary("+", "a", "b", "d"));
        assert_eq!(symbol_tree.substitute(&"a".into(), &"d".into()), SymbolNode::ternary("+", "d", "b", "c"));

        assert_eq!(
            symbol_tree.substitute_all_unchecked(&vec![
                ("a".into(), "d".into()),
                ("b".into(), "e".into()),
                ("c".into(), "f".into()),
            ].into_iter().collect()),
            SymbolNode::ternary("+", "d", "e", "f")
        );
        assert_eq!(
            symbol_tree.substitute_all(
                &vec![("a".into(), "d".into()), ("b".into(), "e".into()), ("c".into(), "f".into())].into_iter().collect()
            ),
            SymbolNode::ternary("+", "d", "e", "f")
        );

        assert_eq!(
            symbol_tree.substitute_all(
                &vec![("a".into(), "d".into()), ("b".into(), "d".into()), ("c".into(), "d".into())].into_iter().collect()
            ),
            SymbolNode::ternary("+", "d", "d", "d")
        );

        
        assert_eq!(
            symbol_tree.substitute_all(
                &vec![("a".into(), "d".into()), ("b".into(), "d".into())].into_iter().collect()
            ),
            SymbolNode::ternary("+", "d", "d", "c")
        );

        assert_eq!(
            symbol_tree.substitute_all(
                &vec![("a".into(), "b".into()), ("b".into(), "c".into())].into_iter().collect()
            ),
            SymbolNode::ternary("+", "b", "c", "c")
        );

        assert_eq!(
            SymbolNode::ternary("+", "2", "2", "4").substitute_all(
                &vec![("2".into(), "4".into()), ("4".into(), "2".into())].into_iter().collect()
            ),
            SymbolNode::ternary("+", "4", "4", "2")
        )
    }
}